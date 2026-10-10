#!/usr/bin/env python3
"""Exhaustive finite tests of candidate Lemma 27 Q order repairs.

The paper's skew clauses (i)--(iv), semi-complete branching, signature
boundary markers, frontier enumeration, singleton-vector W_* restriction,
and intrinsic canonical support walk are modelled independently of Lean.

The three modes are:
* printed: source S, support T, and frontier order use reverse-lex ties;
* global-forward: change the auxiliary order consistently everywhere;
* frontier-only: keep the source's printed order but enumerate its
  frontiers using forward-lex ties.

A point in the starred D2 domain is a vector 1-complete family of
singletons; consequently its *local tail lengths* are nondecreasing
in the chosen coordinate order, rather than necessarily equal.

This is a finite regression and a search for counterexamples, not a
proof for arbitrary b, T, S or ambient height.
"""
from itertools import combinations, product


def nodes(k):
    return [w for h in range(k) for w in product(range(2), repeat=h)]


def prefix(a, b):
    return len(a) <= len(b) and b[:len(a)] == a


def proper(a, b):
    return len(a) < len(b) and prefix(a, b)


def auxiliary(a, b, mode):
    if len(a) != len(b):
        return len(a) < len(b)
    return (a >= b) if mode == "printed" else (a <= b)


def successors(S, a):
    return [b for b in S if proper(a, b)
            and not any(proper(a, u) and proper(u, b) for u in S)]


def height(S, a):
    return sum(proper(u, a) for u in S)


def interior(S):
    return {a for a in S if successors(S, a)}


def skew(S, mode):
    if len(S) == 1:
        return True
    if not S or not any(all(prefix(r, s) for s in S) for r in S):
        return False
    if any(height(S, a) == height(S, b) and a <= b and len(a) > len(b)
           for a in S for b in S):
        return False
    if any(height(S, a) < height(S, b) and len(a) >= len(b)
           for a in S for b in S):
        return False
    for witness in S:
        for last in range(2):
            valid = True
            for s in S:
                directions = sorted(t[len(s)] for t in successors(S, s))
                if s != witness and auxiliary(s, witness, mode):
                    if directions != [0, 1]:
                        valid = False
                        break
                elif s != witness and auxiliary(witness, s, mode):
                    if directions:
                        valid = False
                        break
                elif directions != list(range(last + 1)):
                    valid = False
                    break
            if valid:
                return True
    return False


def semi_complete(S, mode):
    return skew(S, mode) and all(len(successors(S, s)) in (0, 2) for s in S)


def complete(S, k, mode):
    return (semi_complete(S, mode)
            and {height(S, s) for s in S if not successors(S, s)} == {k-1})


def signature_markers(S, cut, mode):
    I = interior(S)
    D = lambda u: auxiliary(u, cut, mode) and u != cut
    markers = set()
    for t in S - I:
        if prefix(cut, t):
            continue
        candidates = [t[:h] for h in range(len(t)+1) if not D(t[:h])]
        assert candidates
        markers.add(candidates[0])
    signature = I | markers
    sprime_interior = interior(signature)
    R = (signature - sprime_interior - {cut})
    R |= {cut+(0,), cut+(1,)}
    return R, I


def forward_sorted(F, mode):
    sign = -1 if mode == "printed" else 1
    return sorted(F, key=lambda x: (len(x), tuple(sign*a for a in x)))


def frontier(T, cut, source_mode, frontier_mode):
    F = [t for t in T if not auxiliary(t, cut, source_mode)
         and not any(proper(u, t) and not auxiliary(u, cut, source_mode)
                     for u in T)]
    return forward_sorted(F, frontier_mode)


def canonical(T, k):
    root = next(s for s in T if all(prefix(s, t) for t in T))
    address = {(): root}
    for depth in range(k-1):
        for word, s in list(address.items()):
            if len(word) != depth:
                continue
            for t in successors(T, s):
                direction = t[len(s)]
                next_word = word + (direction,)
                assert next_word not in address
                address[next_word] = t
    assert set(address.values()) == T
    return address


def scan(T, k, source_mode, frontier_mode):
    address = canonical(T, k)
    inverse = {t: s for s, t in address.items()}
    data = {"cases": 0, "failed": 0, "ii": 0, "iii": 0, "other": 0}
    ordered_T = sorted(T)
    for mask in range(1, 1 << len(ordered_T)):
        S = {s for j, s in enumerate(ordered_T) if mask >> j & 1}
        if not semi_complete(S, source_mode):
            continue
        I = interior(S)
        if not I:
            continue
        sign = -1 if source_mode == "printed" else 1
        cut = max(I, key=lambda s: (len(s), tuple(sign*a for a in s)))
        m = height(T, cut)
        if m >= k-2:  # m' < m-1 in Lemma 27
            continue
        R, original_interior = signature_markers(S, cut, source_mode)
        F = frontier(T, cut, source_mode, frontier_mode)
        assignments = {
            s: [j for j, f in enumerate(F) if prefix(s, f)]
            for s in R
        }
        assert all(len(js) == 1 for js in assignments.values())
        d2 = sorted({js[0] for js in assignments.values()})
        assert len(d2) == len(R)
        tails = nodes(k-(m+1))  # the formally certified safe cone domain
        for chosen in product(tails, repeat=len(d2)):
            # Definition 20: vector 1-complete singleton marked points.
            if any(len(a) > len(b) for a, b in zip(chosen, chosen[1:])):
                continue
            Q = original_interior | {
                address[inverse[F[j]] + chosen[index]]
                for index, j in enumerate(d2)
            }
            data["cases"] += 1
            if semi_complete(Q, source_mode):
                continue
            data["failed"] += 1
            ii = all(not(height(Q, a) == height(Q, b)
                         and a <= b and len(a) > len(b))
                     for a in Q for b in Q)
            iii = all(not(height(Q, a) < height(Q, b)
                          and len(a) >= len(b))
                      for a in Q for b in Q)
            data["ii"] += not ii
            data["iii"] += not iii
            data["other"] += ii and iii
    return data


def full_tree(k, source_mode, frontier_mode):
    return scan(set(nodes(k)), k, source_mode, frontier_mode)


def embedded_three(ambient_n, mode):
    all_nodes = nodes(ambient_n)
    result = {"supports": 0, "cases": 0, "failed": 0, "ii": 0, "iii": 0,
              "other": 0}
    for choice in combinations(all_nodes, 7):
        T = set(choice)
        if not complete(T, 3, mode):
            continue
        result["supports"] += 1
        data = scan(T, 3, mode, mode)
        for key, n in data.items():
            result[key] += n
    return result


def main():
    results = {
        "printed3": full_tree(3, "printed", "printed"),
        "forward3": full_tree(3, "forward", "forward"),
        "printed4": full_tree(4, "printed", "printed"),
        "forward4": full_tree(4, "forward", "forward"),
        "frontierOnly4": full_tree(4, "printed", "forward"),
        "embeddedPrinted": embedded_three(4, "printed"),
        "embeddedForward": embedded_three(4, "forward"),
    }
    expected = {
        "printed3": (49, 14),
        "forward3": (49, 0),
        "printed4": (2509, 1110),
        "forward4": (2509, 0),
        "frontierOnly4": (2509, 176),
        "embeddedPrinted": (2205, 518),
        "embeddedForward": (2205, 0),
    }
    for name, data in results.items():
        print(f"{name}: {data}")
        assert (data["cases"], data["failed"]) == expected[name]
        assert data["other"] == 0, (name, data)
    assert results["printed4"]["ii"] == 1038
    assert results["printed4"]["iii"] == 88
    assert results["frontierOnly4"]["ii"] == 56
    assert results["frontierOnly4"]["iii"] == 120
    assert results["embeddedPrinted"]["supports"] == 45
    assert results["embeddedForward"]["supports"] == 45
    print("PASS: Lemma 27 finite Q repair regressions")


if __name__ == "__main__":
    main()
