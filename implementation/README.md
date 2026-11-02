# Directed, unweighted Győri–Lovász partition

This is a direct C++17 implementation of **GLPartition** and
**ShiftAssignment** from the paper. It uses ordinary graph operations,
capacitated matching, and max flow. The implementation follows the sections
*Flow-Essential Assignment* and *The Polynomial-Time Algorithm* of `gyori.tex`,
including the proposition *Computing essential terminals for one vertex*.

## Build and run

From the repository root, with a C++17 compiler:

```sh
mkdir -p build
g++ -std=c++17 -O2 -Wall -Wextra -pedantic implementation/main.cpp -o build/gl_partition
./build/gl_partition implementation/examples/cycle.txt
./build/gl_partition < implementation/examples/small.txt
```

Run `./build/gl_partition` to enter the same format directly on standard input.
Finish the input with EOF (Ctrl+D on Linux/macOS). Run with `--help` for a format
reminder.

## Input and output

```text
n m k
size_0 size_1 ... size_(k-1)
u_1 v_1
...
u_m v_m
```

Vertices are numbered **0 through n-1**. Terminals are **0 through k-1**;
all remaining vertices are non-terminals. Each pair `u v` is the directed edge
`u -> v`. Every part size is positive, **includes its terminal**, and the sizes
sum to `n`. Thus the paper's capacity is `capacity[t] = size[t] - 1`.
The graph is unweighted. As in the paper's preliminaries, self-loops and duplicate
edges are discarded, and outgoing edges of terminals are discarded to make them
sinks. An undirected graph can be supplied by listing each edge in both directions.

For example:

```text
4 4 2
2 2
2 0
2 1
3 0
3 1
```

produces:

```text
Flow-essential assignment condition holds.
Part 0: 0 2
Part 1: 1 3
```

Each output line lists the original vertices of one part. Every vertex in
`Part t` has a directed path to terminal `t` using only vertices in that part.
The program exits with code **0** on success, **1** when the flow-essential
assignment condition fails, and **2** for invalid input or file errors.
Failure of this sufficient condition does not imply that no partition exists.

## How the code follows the paper

A terminal is **essential** for a non-terminal vertex if deleting that terminal
decreases the maximum number of paths from the vertex to distinct terminals,
where the paths share only their starting vertex. A **flow-essential assignment**
assigns every non-terminal to an essential terminal and fills each capacity exactly.

The program first computes essential terminals by vertex splitting and max flow.
A reverse search in the residual graph finds the tightest minimum cut, whose
terminal separator is precisely the essential-terminal set. One capacitated
bipartite matching then checks the assignment condition and supplies a witness.

`gl_partition` maintains that witness and performs the paper's three operations:

1. Remove a terminal whose remaining capacity is zero.
2. Contract a pre-terminal with one outgoing edge into its terminal, add it to
   that terminal's part, and decrease the remaining capacity.
3. Otherwise, call `shift_assignment` and delete the non-critical edge it returns.

`shift_assignment` matches distinct pre-terminals to all active terminals and
chooses one secondary outgoing edge for each matched pre-terminal. If deleting
one of these edges preserves all current assignments, it returns that edge.
Otherwise, a vertex witnessing criticality for each secondary edge defines an
edge in the reassignment graph. Shifting assignments around a directed cycle
preserves capacities and decreases the paper's criticality potential. Repeating
this step eventually produces a non-critical edge.

The recursive GLPartition is written as a loop, with original vertex IDs retained
and contracted vertices recorded directly in their parts. Adjacency sets handle
duplicate edges during contraction. Essential-terminal sets after secondary-edge
deletions are computed as needed and reused throughout a call to ShiftAssignment.

There are at most `n + m` reduction steps. Each ShiftAssignment call performs at
most `k * (n-k)` cycle shifts and computes at most that many essential-terminal
sets, each using one max-flow call. The implementation uses standard Dinic max
flow; the paper's faster theoretical max-flow bounds require a different solver.
The cache can store up to `O(n k²)` Boolean entries. This version emphasizes a
short, readable implementation of the original algorithm.

## Files and tests

| File | Purpose |
| --- | --- |
| [main.cpp](main.cpp) | Essential terminals, matching, ShiftAssignment, GLPartition |
| [maxflow.h](maxflow.h) | Dinic max flow and reverse residual reachability |
| [io.h](io.h) | File/stdin input, validation, normalization, and output |
| [test.py](test.py) | Independent applicability oracle and output checks |

`examples/small.txt` is a small applicable instance.
`examples/cycle.txt` is the paper's nine-vertex running example, renumbered from
zero, and exercises cycle reassignment. `examples/not-applicable.txt` has a
non-terminal with no essential terminal, so it fails the initial check.

Run the tests using Python 3, with no extra packages:

```sh
python3 implementation/test.py ./build/gl_partition
```

The tests enumerate every normalized directed graph with up to four vertices and
every positive size vector, then check seeded random instances against an
independent oracle that enumerates vertex separators and assignments. They also
check a larger connected instance, both input modes, and malformed input.
Every returned partition is checked for vertex coverage, prescribed sizes,
terminal membership, and directed reachability within each part in the original
graph.
