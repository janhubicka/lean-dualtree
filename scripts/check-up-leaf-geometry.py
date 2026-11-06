#!/usr/bin/env python3
"""Exhaustive small height-one up-leaf tests against the actual skew clauses.

The checked equivalence is restricted to positive branching and a root strictly
below the ambient leaf level: for an ordered list of exactly b ambient leaves,
the extended support is skew iff there is exactly one leaf in each direction
above the root. Lists with repeated leaves are included in the search.

Both auxiliary orders are tested. These independent finite checks are a
regression, not a proof of the general construction. Kernel-checked positive
and negative fixtures are in DualTree/UpLeafAudit.lean.
"""

from itertools import product


def prefix(s, t):
    return len(s) <= len(t) and t[:len(s)] == s


def strict_prefix(s, t):
    return len(s) < len(t) and prefix(s, t)


def aux_le(s, t, mode):
    if len(s) != len(t):
        return len(s) < len(t)
    return t <= s if mode == "paper" else s <= t


def skew(nodes, b, mode):
    """List implementation of SkewTree.skewB, including Nodup."""
    if len(nodes) != len(set(nodes)):
        return False
    if len(nodes) == 1:
        return True
    if not any(all(prefix(r, t) for t in nodes) for r in nodes):
        return False

    height = {s: sum(strict_prefix(t, s) for t in nodes) for s in nodes}
    if any(
        height[s] == height[t] and s <= t and len(s) > len(t)
        for s in nodes for t in nodes
    ):
        return False
    if any(
        height[s] < height[t] and len(s) >= len(t)
        for s in nodes for t in nodes
    ):
        return False

    successors = {
        s: [
            t for t in nodes if strict_prefix(s, t)
            and not any(strict_prefix(s, u) and strict_prefix(u, t) for u in nodes)
        ]
        for s in nodes
    }

    def unique_branch(s, i):
        return sum(prefix(s + (i,), t) for t in successors[s]) == 1

    for active in nodes:
        full_before = all(
            all(unique_branch(s, i) for i in range(b))
            for s in nodes if s != active and aux_le(s, active, mode)
        )
        empty_after = all(
            not successors[s]
            for s in nodes if s != active and aux_le(active, s, mode)
        )
        for last_dir in range(b):
            partial_at = (
                len(successors[active]) == last_dir + 1
                and all(unique_branch(active, i) for i in range(last_dir + 1))
            )
            if full_before and empty_after and partial_at:
                return True
    return False


def branch_representatives(root, leaves, b):
    return all(
        sum(prefix(root + (i,), t) for t in leaves) == 1
        for i in range(b)
    )


def bounded_nodes(b, n):
    return [s for length in range(n) for s in product(range(b), repeat=length)]


def run_instance(b, n, mode):
    level = list(product(range(b), repeat=n))
    checked = accepted = 0
    for root in bounded_nodes(b, n):
        for leaves in product(level, repeat=b):
            checked += 1
            actual = skew([root, *leaves], b, mode)
            expected = branch_representatives(root, leaves, b)
            assert actual == expected, (b, n, mode, root, leaves, actual, expected)
            accepted += actual

        # Canonical zero-tail padding always supplies genuine representatives.
        padded = [root + (i,) + (0,) * (n - len(root) - 1) for i in range(b)]
        assert all(len(t) == n for t in padded)
        assert len(set(padded)) == b
        assert branch_representatives(root, padded, b)
        assert skew([root, *padded], b, mode)
    return checked, accepted


def main():
    expected = {
        (1, 1): (1, 1),
        (1, 2): (2, 2),
        (1, 3): (3, 3),
        (1, 4): (4, 4),
        (2, 1): (4, 2),
        (2, 2): (48, 12),
        (2, 3): (448, 56),
        (2, 4): (3840, 240),
    }
    for (b, n), counts in expected.items():
        for mode in ("paper", "forward"):
            actual = run_instance(b, n, mode)
            assert actual == counts, (b, n, mode, actual, counts)
            print(
                f"PASS b={b} n={n} order={mode}: {actual[0]} ordered leaf lists, "
                f"{actual[1]} skew, exactly the branch representatives"
            )

    for mode in ("paper", "forward"):
        # Correct cardinality, distinct ambient leaves and rootedness do not
        # replace coverage of each direction immediately above the root.
        assert not skew([(), (0, 0), (0, 1)], 2, mode)
        assert not skew([(0,), (0, 0), (1, 0)], 2, mode)
        assert not skew([(0,), (0,)], 1, mode)
        # At b=0 the extended support is just the singleton root; the geometric
        # condition passes, but there is no selected leaf and hence no D1 point.
        assert skew([()], 0, mode)
        # A fixed genuine leaf set need not be monochromatic. A subsequent
        # Ramsey argument must select geometry suited to the coloring.
        leaves = [(0,), (1,)]
        assert skew([(), *leaves], 2, mode)
        assert len({leaf[0] for leaf in leaves}) == 2
    print("PASS boundary fixtures: missing direction, wrong cone, equal height, b=0, leaf colors")


if __name__ == "__main__":
    main()
