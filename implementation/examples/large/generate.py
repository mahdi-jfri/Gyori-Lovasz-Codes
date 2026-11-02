#!/usr/bin/env python3
"""Reproduce the five larger inputs, each with guaranteed terminal connectivity."""

from pathlib import Path
import random


# name, vertices, part sizes, include reverse cycle edges, extra-edge probability
CASES = [
    ("directed-50", 50, [8, 17, 25], False, 0.0),
    ("bidirected-75", 75, [9, 16, 22, 28], True, 0.0),
    ("chorded-100", 100, [8, 12, 20, 25, 35], False, 0.01),
    ("chorded-150", 150, [10, 20, 30, 40, 50], False, 0.02),
    ("chorded-200", 200, [10, 20, 30, 40, 45, 55], False, 0.02),
]


def main():
    for name, n, sizes, bidirectional, density in CASES:
        k = len(sizes)
        generator = random.Random(260830945 + n)
        labels = list(range(n))
        generator.shuffle(labels)

        # Join each vertex to its next k successors around a directed cycle.
        # After deleting fewer than k vertices, the surviving cycle can still
        # be traversed, so the graph is k-connected to any k terminals.
        steps = list(range(1, k + 1))
        if bidirectional:
            steps += list(range(-k, 0))
        edges = {(labels[u], labels[(u + step) % n])
                 for u in range(n) for step in steps}
        edges |= {(u, v) for u in range(n) for v in range(n)
                  if u != v and generator.random() < density}

        # Terminals 0..k-1 are sinks, as in the implementation.
        edges = sorted((u, v) for u, v in edges if u >= k)
        lines = [f"{n} {len(edges)} {k}", " ".join(map(str, sizes))]
        lines += [f"{u} {v}" for u, v in edges]
        path = Path(__file__).parent / f"{name}.txt"
        path.write_text("\n".join(lines) + "\n")
        print(f"{path.name}: {n} vertices, {len(edges)} edges, {k} terminals")


if __name__ == "__main__":
    main()
