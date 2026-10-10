#!/usr/bin/env python3
"""Independent ternary regression for candidate global-forward Lemma 27.

The finite model uses the literal signature of Definition 26, the minimal
outside-cut frontiers, singleton-vector W_* admissibility from Definition 20,
and the Q tree support in Lemma 27. For the full ternary tree 3^{<3}
the canonical maps are identities. The auxiliary order is selected
consistently for the original printed and proposed global-forward
conventions.

No inference about the general Lemma 27, mixed-product Ramsey bounds,
or word/colouring part is made from these exhaustive finite checks.
"""
from itertools import product

B = 3
K = 3


def words(height):
    return [u for n in range(height) for u in product(range(B), repeat=n)]


def prefix(s, t):
    return len(s) <= len(t) and t[:len(s)] == s


def strict(s, t):
    return len(s) < len(t) and prefix(s, t)


def auxiliary(s, t, convention):
    if len(s) != len(t):
        return len(s) < len(t)
    return s >= t if convention == "printed" else s <= t


def successors(S, s):
    return [t for t in S if strict(s, t)
            and not any(strict(s, u) and strict(u, t) for u in S)]


def rank(S, s):
    return sum(strict(t, s) for t in S)


def interior(S):
    return {s for s in S if successors(S, s)}


def semicomplete(S, convention):
    if not S or not any(all(prefix(r, s) for s in S) for r in S):
        return False
    if any(rank(S, s) == rank(S, t) and s <= t and len(s) > len(t)
           for s in S for t in S):
        return False
    if any(rank(S, s) < rank(S, t) and len(s) >= len(t)
           for s in S for t in S):
        return False
    if len(S) > 1:
        valid_witness = False
        for witness in S:
            for last in range(B):
                for s in S:
                    dirs = sorted(t[len(s)] for t in successors(S, s))
                    if s != witness and auxiliary(s, witness, convention):
                        required = list(range(B))
                    elif s != witness and auxiliary(witness, s, convention):
                        required = []
                    else:
                        required = list(range(last + 1))
                    if dirs != required:
                        break
                else:
                    valid_witness = True
                    break
            if valid_witness:
                break
        if not valid_witness:
            return False
    return all(len(successors(S, s)) in (0, B) for s in S)


def signature(S, cut, convention):
    old_interior = interior(S)
    D = lambda u: auxiliary(u, cut, convention) and u != cut
    S_prime = set(old_interior)
    for t in S - old_interior:
        if prefix(cut, t):
            continue
        boundary = [t[:j] for j in range(len(t) + 1) if not D(t[:j])]
        assert boundary
        S_prime.add(boundary[0])
    R = S_prime - interior(S_prime) - {cut}
    R |= {cut + (j,) for j in range(B)}
    return old_interior, R


def run(convention):
    T = words(K)
    scanned_sources = scanned_points = failures = failed_ii = failed_iii = 0
    for mask in range(1, 1 << len(T)):
        S = {T[i] for i in range(len(T)) if mask >> i & 1}
        if not semicomplete(S, convention):
            continue
        I = interior(S)
        if not I:
            continue
        sign = -1 if convention == "printed" else 1
        cut = max(I, key=lambda s: (len(s), tuple(sign * x for x in s)))
        m = len(cut)
        if m >= K-2:
            continue
        old_interior, R = signature(S, cut, convention)
        F = [t for t in T if not auxiliary(t, cut, convention)
             and not any(strict(u, t) and not auxiliary(u, cut, convention)
                         for u in T)]
        F = sorted(F, key=lambda t:
                   (len(t), tuple(sign * x for x in t)))
        indices = {r: [j for j, f in enumerate(F) if prefix(r, f)] for r in R}
        assert all(len(v) == 1 for v in indices.values())
        d2 = sorted({v[0] for v in indices.values()})
        assert len(d2) == len(R)
        scanned_sources += 1
        for marked in product(words(K - (m+1)), repeat=len(d2)):
            # Vector 1-completeness of singleton D2 marked supports.
            if any(len(x) > len(y) for x, y in zip(marked, marked[1:])):
                continue
            Q = old_interior | {F[j] + marked[i] for i, j in enumerate(d2)}
            scanned_points += 1
            if semicomplete(Q, convention):
                continue
            failures += 1
            failed_ii += any(rank(Q, s) == rank(Q, t) and s <= t
                             and len(s) > len(t) for s in Q for t in Q)
            failed_iii += any(rank(Q, s) < rank(Q, t)
                              and len(s) >= len(t) for s in Q for t in Q)
    return (scanned_sources, scanned_points, failures, failed_ii, failed_iii)


def main():
    original = run("printed")
    repaired = run("forward")
    print(f"ternary printed: {original}")
    print(f"ternary global forward: {repaired}")
    assert original == (40, 1600, 480, 480, 0), original
    assert repaired == (40, 1600, 0, 0, 0), repaired
    print("PASS: ternary forward-lex Q regression")


if __name__ == "__main__":
    main()
