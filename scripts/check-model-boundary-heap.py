#!/usr/bin/env python3
"""Finite adversarial checks for the candidate corrected model A_l boundary.

The executable test is independent from the Lean proofs. It checks the
b-ary heap-address formula and the external-child model boundary
against a direct arithmetic interval for modest branching and l.
It does NOT assert equivalence with the paper's reverse-lex order
or complete the canonical A-to-R address transport.
"""

from functools import lru_cache


def index(node: tuple[int, ...], branching: int) -> int:
    value = 0
    for direction in node:
        value = branching * value + 1 + direction
    return value


@lru_cache(None)
def node_at(value: int, branching: int) -> tuple[int, ...]:
    if value == 0:
        return ()
    assert branching > 0 and value > 0
    q, r = divmod(value - 1, branching)
    return node_at(q, branching) + (r,)


def main() -> None:
    cases = 0
    for branching in range(1, 5):
        for interior_count in range(1, 30):
            interior = {
                node_at(i, branching) for i in range(interior_count)
            }
            boundary = {
                node + (direction,)
                for node in interior
                for direction in range(branching)
                if node + (direction,) not in interior
            }
            interval = {
                node_at(i, branching)
                for i in range(interior_count, branching * interior_count + 1)
            }
            assert boundary == interval, (
                branching, interior_count, boundary ^ interval
            )
            for value in range(branching * interior_count + 1):
                assert index(node_at(value, branching), branching) == value
            for node in interior:
                for k in range(len(node) + 1):
                    assert node[:k] in interior
            cases += 1

    print(
        f"PASS: {cases} positive-branching model boundary cases; "
        "heap inverse, exact interval and prefix closure"
    )


if __name__ == "__main__":
    main()
