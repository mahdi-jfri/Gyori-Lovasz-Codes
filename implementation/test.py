#!/usr/bin/env python3
"""Independent small-instance oracle and end-to-end partition checks (stdlib only)."""

import itertools
from pathlib import Path
import random
import subprocess
import sys
import tempfile


def encode(n, k, sizes, edges):
    lines = [f"{n} {len(edges)} {k}", " ".join(map(str, sizes))]
    return "\n".join(lines + [f"{u} {v}" for u, v in edges]) + "\n"


def connectivity(n, k, edges, source, deleted=None):
    """Enumerate vertex separators, independently of the C++ flow algorithm."""
    candidates = [v for v in range(n) if v != source and v != deleted]
    for size in range(k + 1):
        for cut in itertools.combinations(candidates, size):
            blocked = set(cut) | {deleted}
            reached = {source}
            stack = [source]
            while stack:
                u = stack.pop()
                for x, v in edges:
                    if x == u and v not in blocked and v not in reached:
                        reached.add(v)
                        stack.append(v)
            if not any(t in reached for t in range(k)):
                return size
    raise AssertionError("deleting all terminals must separate the source")


def applicable(n, k, sizes, edges):
    states = {tuple(0 for _ in range(k))}
    capacity = tuple(size - 1 for size in sizes)
    for v in range(k, n):
        value = connectivity(n, k, edges, v)
        essential = [t for t in range(k)
                     if connectivity(n, k, edges, v, t) < value]
        next_states = set()
        for state in states:
            for t in essential:
                if state[t] < capacity[t]:
                    updated = list(state)
                    updated[t] += 1
                    next_states.add(tuple(updated))
        states = next_states
    return capacity in states


def check(binary, n, k, sizes, edges, expected=None):
    # Terminals are sinks, as in the manuscript and the input normalization.
    normalized = sorted({(u, v) for u, v in edges if u >= k and u != v})
    if expected is None:
        expected = applicable(n, k, sizes, normalized)
    data = encode(n, k, sizes, edges)
    result = subprocess.run([binary], input=data, text=True, capture_output=True, timeout=20)
    assert result.returncode == (0 if expected else 1), (data, result)
    if not expected:
        assert result.stdout.strip() == "Flow-essential assignment condition does not hold."
        return
    lines = result.stdout.splitlines()
    assert lines[0] == "Flow-essential assignment condition holds.", (data, result)
    assert len(lines) == k + 1, (data, result)
    all_vertices = []
    for t, line in enumerate(lines[1:]):
        prefix = f"Part {t}:"
        assert line.startswith(prefix), (data, result)
        part = list(map(int, line[len(prefix):].split()))
        assert len(part) == sizes[t] and t in part, (data, result)
        # Reverse search in the ORIGINAL graph, restricted to this output part.
        reached = {t}
        while True:
            new = {u for u, v in normalized if u in part and v in reached}
            if new <= reached:
                break
            reached |= new
        assert reached == set(part), (data, result)
        all_vertices.extend(part)
    assert sorted(all_vertices) == list(range(n)), (data, result)


def compositions(n, k):
    for cuts in itertools.combinations(range(1, n), k - 1):
        ends = (0,) + cuts + (n,)
        yield [ends[i + 1] - ends[i] for i in range(k)]


def main():
    binary = str(Path(sys.argv[1]).resolve())
    count = 0
    for n in range(1, 5):
        for k in range(1, n + 1):
            possible = [(u, v) for u in range(k, n) for v in range(n) if u != v]
            for mask in range(1 << len(possible)):
                edges = [edge for i, edge in enumerate(possible) if mask & (1 << i)]
                for sizes in compositions(n, k):
                    check(binary, n, k, sizes, edges)
                    count += 1

    random_generator = random.Random(2026)
    for _ in range(500):
        n = random_generator.randint(5, 8)
        k = random_generator.randint(1, min(n, 4))
        sizes = random_generator.choice(list(compositions(n, k)))
        density = random_generator.uniform(0.15, 0.8)
        edges = [(u, v) for u in range(n) for v in range(n)
                 if random_generator.random() < density]
        check(binary, n, k, sizes, edges)
        count += 1

    # A larger k-connected family: bidirectional powers of a cycle, with the
    # first k vertices as terminals. Removing fewer than k vertices leaves it connected.
    n, k = 80, 4
    edges = [(u, (u + step) % n) for u in range(n)
             for step in range(-k, k + 1) if step != 0]
    check(binary, n, k, [20] * k, edges, expected=True)

    examples = Path(__file__).parent / "examples"
    for path in sorted(examples.glob("*.txt")):
        data = list(map(int, path.read_text().split()))
        n, m, k = data[:3]
        edges = list(zip(data[3 + k::2], data[4 + k::2]))
        assert len(edges) == m
        check(binary, n, k, data[3:3 + k], edges)
        # Exercise argv file input and compare it with stdin.
        from_file = subprocess.run([binary, str(path)], capture_output=True, text=True)
        from_stdin = subprocess.run([binary], input=path.read_text(), capture_output=True, text=True)
        assert (from_file.returncode, from_file.stdout) == (from_stdin.returncode, from_stdin.stdout)

    malformed = ["", "0 0 0", "2 -1 1", "2 0 3", "2 0 1\n0", "2 0 1\n1",
                 "2 1 1\n2\n1 2", "2 1 1\n2\n-1 0", "2 1 1\n2\n1",
                 "2 0 1\n2\nextra", "2 0 1\n2147483648"]
    for data in malformed:
        result = subprocess.run([binary], input=data, text=True, capture_output=True)
        assert result.returncode == 2 and result.stderr.startswith("Error:"), (data, result)
    with tempfile.TemporaryDirectory() as directory:
        missing = str(Path(directory) / "missing.txt")
        assert subprocess.run([binary, missing], capture_output=True).returncode == 2
        assert subprocess.run([binary, "a", "b"], capture_output=True).returncode == 2
    assert subprocess.run([binary, "--help"], capture_output=True).returncode == 0
    print(f"Passed {count} exhaustive/random oracle cases, a larger graph, examples, and input checks.")


if __name__ == "__main__":
    main()
