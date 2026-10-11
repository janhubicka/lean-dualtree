#!/usr/bin/env python3
"""Adversarial Q regression over arbitrary semi-complete source subsets.

Unlike scripts/check-q-stretched-forward.py, which builds sources from
forward-initial source interiors, enumerate ALL nonempty subsets of each
small stretched complete support T, retaining only genuinely
semi-complete skew sources whose interior is also skew.

For every admissible source, construct literal first-boundary R,
unique sorted outside-cut frontiers, injective R->D2 coordinates,
and the actual canonical-address-based projected Q support.

Verify (1) every rank-(cut+1) exceptional source terminal has a
first-cut boundary of strictly greater ambient length than cut,
and (2) each reconstructed Q is itself semi-complete skew.

Finite evidence is not a general Lean proof. Fixed RNG seed and
asserted counters make changes to test coverage visible in CI.
"""
from itertools import product, combinations_with_replacement
from random import Random

SEED = 392026
rng = Random(SEED)


def prefix(a, b):
    return len(a) <= len(b) and b[:len(a)] == a


def strict(a, b):
    return len(a) < len(b) and prefix(a, b)


def rank(support, node):
    return sum(strict(u, node) for u in support)


def forward_aux(s, t):
    return (len(s), s) <= (len(t), t)


def immediate(support, s):
    return [
        t for t in support
        if strict(s, t)
        and not any(strict(s, u) and strict(u, t) for u in support)
    ]


def interior(support):
    return {s for s in support if immediate(support, s)}


def semi_complete_skew(support, branching, just_skew=False):
    if len(support) == 1:
        return True
    if not support or not any(
        all(prefix(root, t) for t in support) for root in support
    ):
        return False
    heights = {t: rank(support, t) for t in support}
    if any(
        heights[s] == heights[t] and s < t and len(s) > len(t)
        for s in support for t in support
    ):
        return False
    if any(
        heights[s] < heights[t] and len(s) >= len(t)
        for s in support for t in support
    ):
        return False
    if not just_skew and any(
        len(immediate(support, s)) not in (0, branching)
        for s in support
    ):
        return False
    for cut in support:
        for last_direction in range(branching):
            valid = True
            for s in support:
                succs = immediate(support, s)
                if s != cut and forward_aux(s, cut):
                    expected = range(branching)
                elif s != cut and forward_aux(cut, s):
                    expected = []
                else:
                    expected = range(last_direction + 1)
                directions = []
                for t in succs:
                    if len(t) == len(s) or not prefix(s, t):
                        return False
                    directions.append(t[len(s)])
                if sorted(directions) != list(expected):
                    valid = False
                    break
            if valid:
                return True
    return False


def random_stretched_complete(height, branching):
    address_to_node = {(): ()}
    previous_max = 0
    for level in range(1, height):
        addresses = list(product(range(branching), repeat=level))
        lengths = sorted(
            previous_max + 1 + rng.randrange(3) + i // 4
            for i in range(len(addresses))
        )
        for i, address in enumerate(addresses):
            parent = address_to_node[address[:-1]]
            length = max(len(parent) + 1, lengths[i])
            address_to_node[address] = (
                parent + (address[-1],)
                + tuple(rng.randrange(branching)
                        for _ in range(length - len(parent) - 1))
            )
        previous_max = max(map(len, address_to_node.values()))
    return address_to_node


def check_support(address_to_node, branching, height):
    support = set(address_to_node.values())
    inverse = {node: address for address, node in address_to_node.items()}
    if len(support) != len(address_to_node):
        raise AssertionError("stretched embedding not injective")
    if not semi_complete_skew(support, branching):
        raise AssertionError("stretched complete support not skew")
    candidates = sorted(support, key=lambda t: (len(t), t))
    tested_subsets = valid_sources = valid_q = 0

    for mask in range(1, 1 << len(candidates)):
        source = {
            candidates[i] for i in range(len(candidates))
            if (mask >> i) & 1
        }
        tested_subsets += 1
        if len(source) < 3 or not semi_complete_skew(source, branching):
            continue
        old_interior = interior(source)
        if not old_interior or not semi_complete_skew(
            old_interior, branching, just_skew=True
        ):
            continue
        cut = max(old_interior, key=lambda t: (len(t), t))
        m = rank(support, cut)
        if m + 1 >= height:
            continue

        exceptional = [
            t for t in source - old_interior if not prefix(cut, t)
        ]
        markers = {cut + (direction,) for direction in range(branching)}
        for terminal in exceptional:
            boundary = next(
                terminal[:n] for n in range(len(terminal) + 1)
                if not (
                    forward_aux(terminal[:n], cut)
                    and terminal[:n] != cut
                )
            )
            if rank(source, terminal) == rank(source, cut) + 1:
                assert len(boundary) > len(cut), {
                    "error": "strict exceptional boundary length",
                    "source": source, "cut": cut,
                    "terminal": terminal, "boundary": boundary,
                }
            markers.add(boundary)

        frontiers = sorted((
            t for t in support
            if not forward_aux(t, cut)
            and not any(
                strict(u, t) and not forward_aux(u, cut)
                for u in support
            )
        ), key=lambda t: (len(t), t))
        marker_indices = []
        for marker in markers:
            choices = [
                j for j, frontier in enumerate(frontiers)
                if prefix(marker, frontier)
            ]
            assert len(choices) == 1, {
                "error": "frontier coordinate uniqueness",
                "source": source, "marker": marker,
                "candidates": choices,
            }
            marker_indices.append(choices[0])
        assert len(set(marker_indices)) == len(markers)
        marker_indices.sort()
        valid_sources += 1

        local_height = height - (m + 1)
        for depths in combinations_with_replacement(
            range(local_height), len(marker_indices)
        ):
            for _ in range(2):
                projected = []
                for j, depth in zip(marker_indices, depths):
                    tail = tuple(
                        rng.randrange(branching) for _ in range(depth)
                    )
                    address = inverse[frontiers[j]] + tail
                    assert address in address_to_node
                    projected.append(address_to_node[address])
                reconstructed = old_interior | set(projected)
                valid_q += 1
                # Stronger level-band matching, independent of local tails:
                # actual Q rank relative to the source cut agrees exactly
                # with the ambient T-frontier rank relative to the T cut.
                # Both differences must be 0 or 1.
                q_ranks = [rank(reconstructed, p) for p in projected]
                source_cut_rank = rank(source, cut)
                ambient_cut_rank = rank(support, cut)
                frontier_ranks = [
                    rank(support, frontiers[j]) for j in marker_indices
                ]
                for idx, p in enumerate(projected):
                    q_offset = q_ranks[idx] - source_cut_rank
                    t_offset = frontier_ranks[idx] - ambient_cut_rank
                    assert q_offset in (0, 1) and q_offset == t_offset, {
                        "error": "Q-to-T frontier band mismatch",
                        "source": source, "cut": cut,
                        "marker_indices": marker_indices,
                        "frontiers": frontiers, "projected": projected,
                        "Q_rank": q_ranks[idx],
                        "T_frontier_rank": frontier_ranks[idx],
                        "source_cut_rank": source_cut_rank,
                        "ambient_cut_rank": ambient_cut_rank,
                    }
                assert q_ranks == sorted(q_ranks), {
                    "error": "Q rank not monotone by sorted D2 index",
                    "source": source, "cut": cut,
                    "projected": projected, "Q_ranks": q_ranks,
                }
                for a, p in enumerate(projected):
                    for b, q in enumerate(projected):
                        if q_ranks[a] == q_ranks[b] and p < q:
                            assert a < b, {
                                "error": "equal-Q-rank lex/index reversal",
                                "source": source, "cut": cut,
                                "projected": projected, "Q_ranks": q_ranks,
                                "indices": marker_indices,
                            }
                # Stronger new/new rank transport candidate: a strict
                # increase in intrinsic Q rank should already appear
                # as a strict increase of ambient complete-T rank.
                # This would discharge new/new skew clause (iii)
                # directly from T's verified strict rank/length axiom.
                for p in projected:
                    for q in projected:
                        if rank(reconstructed, p) < rank(reconstructed, q):
                            assert rank(support, p) < rank(support, q), {
                                "error": "new/new ambient rank transport",
                                "source": source, "cut": cut,
                                "Q": reconstructed, "p": p, "q": q,
                                "Q_ranks": (
                                    rank(reconstructed, p),
                                    rank(reconstructed, q),
                                ),
                                "T_ranks": (
                                    rank(support, p),
                                    rank(support, q),
                                ),
                            }
                assert semi_complete_skew(reconstructed, branching), {
                    "error": "Q not semi-complete skew",
                    "support": support, "source": source, "cut": cut,
                    "markers": markers, "frontiers": frontiers,
                    "selected_indices": marker_indices,
                    "local_depths": depths, "Q": reconstructed,
                    "rank_length": [
                        (s, rank(reconstructed, s), len(s))
                        for s in sorted(reconstructed)
                    ],
                }
    return tested_subsets, valid_sources, valid_q


def main():
    totals = [0, 0, 0]
    for height, branching, repeats in ((4, 2, 4), (3, 3, 1)):
        for sample in range(repeats):
            numbers = check_support(
                random_stretched_complete(height, branching),
                branching, height
            )
            totals = [a + b for a, b in zip(totals, numbers)]
            print(f"PASS: k={height}, b={branching}, sample={sample}, "
                  f"subsets={numbers[0]}, valid_sources={numbers[1]}, "
                  f"Q_instances={numbers[2]}")
    assert totals == [139259, 538, 4292], totals
    print("PASS: arbitrary-source forward Q regression "
          f"seed={SEED}, totals={totals}")


if __name__ == "__main__":
    main()
