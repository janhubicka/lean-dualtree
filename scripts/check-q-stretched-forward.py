#!/usr/bin/env python3
"""Deterministic adversarial regression of forward-order Q on stretched trees.

Unlike the complete homogeneous supports in the earlier Q checks, these
examples take genuine *stretched* embeddings of 2^{<k} or 3^{<k}
whose ambient word length may differ across a single intrinsic level.

For each support T satisfying the full forward semi-complete skew
predicate, the test constructs source trees S by taking forward-initial
sets of interior vertices and all their immediate T-successors. Only
sources that themselves satisfy the full semi-complete skew predicate
are retained. It then constructs the actual strict-forward-cut signature
markers R, the minimal outside-inclusive-cut T frontiers F, and every
marker-to-frontier incidence; it draws nondecreasing D2 local point
lengths in the *sorted* frontier coordinate order.

The Q output uses the canonical support addresses and the selected
bounded local tails, not direct ambient string concatenation.
Consequently the test distinguishes intrinsic T rank from ambient
word length. The newly produced Q is checked against all printed
skew clauses with the globally corrected forward auxiliary order.

All samples are reproducible. Zero failures are finite computational
evidence only; the general Q theorem remains a Lean proof obligation.
"""
from itertools import product
from random import Random

SEED = 20261011
rng = Random(SEED)


def prefix(a, b):
    return len(a) <= len(b) and b[:len(a)] == a


def strict(a, b):
    return len(a) < len(b) and prefix(a, b)


def rank(nodes, s):
    return sum(strict(t, s) for t in nodes)


def forward_aux(a, b):
    return (len(a), a) <= (len(b), b)


def immediate(nodes, s):
    return [t for t in nodes if strict(s, t)
            and not any(strict(s, u) and strict(u, t) for u in nodes)]


def semi_complete_skew(nodes, branching):
    if len(nodes) == 1:
        return True
    if not nodes or not any(all(prefix(r, s) for s in nodes) for r in nodes):
        return False
    if any(rank(nodes, x) == rank(nodes, y)
           and x < y and len(x) > len(y)
           for x in nodes for y in nodes):
        return False
    if any(rank(nodes, x) < rank(nodes, y) and len(x) >= len(y)
           for x in nodes for y in nodes):
        return False
    if any(len(immediate(nodes, s)) not in (0, branching) for s in nodes):
        return False
    for cut in nodes:
        for last_direction in range(branching):
            if all(
                sorted(t[len(s)] for t in immediate(nodes, s)) ==
                (list(range(branching)) if s != cut and forward_aux(s, cut)
                 else [] if s != cut and forward_aux(cut, s)
                 else list(range(last_direction + 1)))
                for s in nodes
            ):
                return True
    return False


def random_stretched_complete(height, branching):
    tree = {(): ()}
    greatest_length = 0
    for intrinsic_level in range(1, height):
        addresses = list(product(range(branching), repeat=intrinsic_level))
        minimum = greatest_length + 1
        lengths = sorted(
            minimum + int(rng.expovariate(1.5)) + i // 3
            for i in range(len(addresses))
        )
        for index, address in enumerate(addresses):
            parent = tree[address[:-1]]
            length = max(len(parent) + 1, lengths[index])
            tree[address] = (
                parent + (address[-1],) +
                tuple(rng.randrange(branching)
                      for _ in range(length - len(parent) - 1))
            )
        greatest_length = max(len(word) for word in tree.values())
    return tree


def scan(height, branching, trials, sample_count):
    attempts = good_supports = good_sources = valid_q = 0
    for trial in range(trials):
        tree = random_stretched_complete(height, branching)
        support = set(tree.values())
        if len(support) != len(tree) or not semi_complete_skew(support, branching):
            continue
        good_supports += 1
        inverse = {v: a for a, v in tree.items()}
        interior = sorted(
            (v for a, v in tree.items() if len(a) < height - 1),
            key=lambda v: (len(v), v)
        )
        for index in range(1, len(interior) + 1):
            original_interior = set(interior[:index])
            cut = interior[index - 1]
            source = original_interior | {
                tree[inverse[s] + (i,)]
                for s in original_interior for i in range(branching)
            }
            if not semi_complete_skew(source, branching):
                continue
            good_sources += 1
            cut_rank = len(inverse[cut])
            local_height = height - (cut_rank + 1)
            if local_height <= 0:
                continue
            exceptional = [t for t in source - original_interior
                           if not prefix(cut, t)]
            markers = {cut + (i,) for i in range(branching)}
            for terminal in exceptional:
                boundary = next(
                    terminal[:p] for p in range(len(terminal) + 1)
                    if not (forward_aux(terminal[:p], cut)
                            and terminal[:p] != cut)
                )
                markers.add(boundary)
            frontiers = [
                t for t in support
                if not forward_aux(t, cut)
                and not any(
                    strict(u, t) and not forward_aux(u, cut)
                    for u in support
                )
            ]
            frontiers.sort(key=lambda t: (len(t), t))
            marker_indices = {}
            for marker in markers:
                choices = [j for j, t in enumerate(frontiers)
                           if prefix(marker, t)]
                assert len(choices) == 1, (height, branching, marker, choices)
                marker_indices[marker] = choices[0]
            indices = sorted(set(marker_indices.values()))
            assert len(indices) == len(markers)
            for sample in range(sample_count):
                local_lengths = sorted(
                    rng.randrange(local_height) for _ in indices
                )
                outputs = []
                for j, tail_length in zip(indices, local_lengths):
                    tail = tuple(rng.randrange(branching)
                                 for _ in range(tail_length))
                    address = inverse[frontiers[j]] + tail
                    assert len(address) < height
                    outputs.append(tree[address])
                q_support = original_interior | set(outputs)
                valid_q += 1
                if not semi_complete_skew(q_support, branching):
                    raise AssertionError({
                        "trial": trial, "T": tree, "source": source,
                        "cut": cut, "R": markers, "frontiers": frontiers,
                        "indices": indices, "local_lengths": local_lengths,
                        "Q": q_support,
                        "rank_and_length": [
                            (u, rank(q_support, u), len(u))
                            for u in sorted(q_support)
                        ],
                    })
    return good_supports, good_sources, valid_q


def main():
    instances = (
        (4, 2, 12, 3, (12, 84, 252)),
        (5, 2, 12, 3, (12, 180, 540)),
        (3, 3, 10, 3, (10, 40, 120)),
    )
    total = 0
    for height, branching, trials, samples, expected in instances:
        observed = scan(height, branching, trials, samples)
        assert observed == expected, (height, branching, observed, expected)
        total += observed[2]
        print(f"PASS: b={branching}, k={height}: "
              f"{observed[2]} valid Q trials across {observed[0]} "
              "stretched supports")
    assert total == 912
    print(f"PASS: {total} forward Q trials; fixed seed {SEED}")


if __name__ == "__main__":
    main()
