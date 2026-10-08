#!/usr/bin/env python3
"""Finite exhaustive regression for Section 3 skew-tree meet closure.

These checks are independent of Lean and of the formal proofs. They test the
paper's printed auxiliary order and the proposed forward-lex correction, with
the other skew conditions unchanged. Passing them is not a theorem.
"""
from itertools import product


def nodes(b, n):
    return [w for level in range(n) for w in product(range(b), repeat=level)]


def prefix(s, t):
    return len(s) <= len(t) and t[:len(s)] == s


def proper_prefix(s, t):
    return len(s) < len(t) and prefix(s, t)


def lex_le(s, t):
    if prefix(s, t):
        return True
    if prefix(t, s):
        return False
    return s[next(i for i in range(min(len(s), len(t))) if s[i] != t[i])] < (
        t[next(i for i in range(min(len(s), len(t))) if s[i] != t[i])]
    )


def aux_le(s, t, mode):
    if len(s) != len(t):
        return len(s) < len(t)
    return lex_le(t, s) if mode == "reverse" else lex_le(s, t)


def predecessors(S, s):
    return {t for t in S if proper_prefix(t, s)}


def immediate_successors(S, s):
    return {
        t for t in S
        if proper_prefix(s, t)
        and not any(proper_prefix(s, u) and proper_prefix(u, t) for u in S)
    }


def is_skew(S, b, mode):
    if len(S) == 1:
        return True  # Explicit singleton convention in the paper.
    if not S:
        return False

    roots = [s for s in S if not predecessors(S, s)]
    if len(roots) != 1:
        return False

    h = {s: len(predecessors(S, s)) for s in S}
    for s in S:
        for t in S:
            if h[s] == h[t] and lex_le(s, t) and len(s) > len(t):
                return False
            if h[s] < h[t] and len(s) >= len(t):
                return False

    # Clause (iv): choose the final branching witness and partial direction.
    for active in S:
        for last_dir in range(b):
            valid = True
            for s in S:
                successors = immediate_successors(S, s)
                directions = {t[len(s)] for t in successors}
                if s != active and aux_le(s, active, mode):
                    if len(successors) != b or directions != set(range(b)):
                        valid = False
                        break
                elif s != active and aux_le(active, s, mode):
                    if successors:
                        valid = False
                        break
                else:
                    if (
                        len(successors) != last_dir + 1
                        or directions != set(range(last_dir + 1))
                    ):
                        valid = False
                        break
            if valid:
                return True
    return False


def is_complete(S, b):
    maximal = [s for s in S if not immediate_successors(S, s)]
    heights = {len(predecessors(S, s)) + 1 for s in maximal}
    return len(heights) == 1 and all(
        len(immediate_successors(S, s)) == b for s in S if s not in maximal
    )


def meet(s, t):
    k = 0
    while k < min(len(s), len(t)) and s[k] == t[k]:
        k += 1
    return s[:k]


def nonempty_subsets(xs):
    for mask in range(1, 1 << len(xs)):
        yield {xs[i] for i in range(len(xs)) if (mask >> i) & 1}


def run_instance(b, n, mode):
    found_skew = found_complete = 0
    for S in nonempty_subsets(nodes(b, n)):
        if not is_skew(S, b, mode):
            continue
        found_skew += 1
        if is_complete(S, b):
            found_complete += 1
        for x in S:
            for y in S:
                common = meet(x, y)
                if common not in S:
                    raise AssertionError(
                        f"meet failure: b={b} n={n} mode={mode}; "
                        f"x={x} y={y} meet={common}; S={sorted(S)}"
                    )
    return found_skew, found_complete


def main():
    expected = {
        (2, 3): (25, 17),
        (2, 4): (201, 114),
        (3, 2): (7, 5),
    }
    for (b, n), counts in expected.items():
        for mode in ("reverse", "forward"):
            actual = run_instance(b, n, mode)
            assert actual == counts, (b, n, mode, actual, counts)
            print(
                f"PASS b={b} n={n} order={mode}: "
                f"{actual[0]} skew / {actual[1]} complete, all meet-closed"
            )


if __name__ == "__main__":
    main()
