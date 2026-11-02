# Győri–Lovász: Implementation and Lean formalization

The **Győri–Lovász theorem** says that a $k$-connected undirected graph can be partitioned
into $k$ connected parts of any prescribed positive sizes, with a prescribed
root in each part. More precisely, given distinct roots $t_1,\ldots,t_k$ and
positive integers $n_1,\ldots,n_k$ summing to $|V(G)|$, there is a partition
$V_1,\ldots,V_k$ such that $t_i\in V_i$, $|V_i|=n_i$, and each induced subgraph
$G[V_i]$ is connected. We call the prescribed roots **terminals**.

In our paper, [*Breaking the Exponential Barrier: The First Polynomial-Time
Algorithm for the Győri–Lovász Theorem*](https://arxiv.org/abs/2608.30945),
we give the first polynomial-time algorithm for constructing these partitions.
The central idea is a **flow-essential assignment**, which brings together graph
connectivity and the prescribed part sizes, allowing us to build the partition
step by step. The same framework also handles Lovász's stronger directed version
and weighted generalizations.

This repository makes the results available as a readable **C++ implementation**,
a **Lean formalization** of the theorems and algorithms, and code checking the
**appendix counterexample**. The sections below explain how to run each component.

## Lean formalization (`lean/`)

The [`Lean project`](lean/) includes proofs of the rooted partition theorem,
its weighted generalization, and polynomial bounds for the formalized programs.
It uses **Lean 4.19.0** and **Mathlib 4.19.0**.

With [Elan](https://github.com/leanprover/elan) installed, run:

```sh
cd lean
lake exe cache get
lake build
```

The build checks all proofs and runs an axiom audit. The proofs contain no
`sorry` or `admit`. See the [Lean documentation](lean/README.md) for the formal
statements and scope.

## Implementation (`implementation/`)

The [C++17 implementation](implementation/) follows the paper's original
algorithm for **directed, unweighted graphs**. It first checks whether the
flow-essential assignment condition holds and, when it does, finds the partition.
The code keeps the main algorithm in one readable source file, with separate
headers for max flow and input/output.

```sh
mkdir -p build
g++ -std=c++17 -O2 -Wall -Wextra -pedantic implementation/main.cpp -o build/gl_partition
./build/gl_partition implementation/examples/cycle.txt
./build/gl_partition < implementation/examples/small.txt
```

With no filename, the program reads from standard input, so input can also be
typed directly. See the [implementation guide](implementation/README.md) for the
input format, algorithm explanation, examples, and tests.

Five [larger examples](implementation/README.md#larger-examples) with **50–200
vertices** demonstrate the implementation on sparse and denser graphs, with
unequal part sizes. To run them, check the partitions, and print timings:

```sh
python3 implementation/test.py ./build/gl_partition --large-only
```

One run on an Intel Core i7-12700H with GCC 13.3 (`-std=c++17 -O2`) gave:

| Input | Vertices | Directed edges | Terminals | Time (s) |
| --- | ---: | ---: | ---: | ---: |
| [directed-50.txt](implementation/examples/large/directed-50.txt) | 50 | 141 | 3 | 0.03 |
| [bidirected-75.txt](implementation/examples/large/bidirected-75.txt) | 75 | 568 | 4 | 0.67 |
| [chorded-100.txt](implementation/examples/large/chorded-100.txt) | 100 | 579 | 5 | 1.45 |
| [chorded-150.txt](implementation/examples/large/chorded-150.txt) | 150 | 1,180 | 5 | 5.36 |
| [chorded-200.txt](implementation/examples/large/chorded-200.txt) | 200 | 1,944 | 6 | 17.13 |

## Appendix counterexample (`counterexample/`)

The appendix explores **compact connectivity** and **local connectivity** as
alternatives to the flow-essential assignment condition used by our algorithm.
The code here demonstrates why compact connectivity cannot be maintained in
the contraction/edge-removal framework: it constructs an instance satisfying
the condition where every edge deletion and every contraction of a pre-terminal
into an adjacent terminal destroys it.

A vertex is compact-connected to a terminal $t$ if it has
$k$ internally vertex-disjoint paths to the terminal set, with at most one path
ending at each terminal other than $t$. Following the appendix's convention,
a vertex with a direct edge to $t$ is also compact-connected to $t$.
The compact connectivity condition asks for an assignment of every non-terminal
to a compact-connected terminal that fills every capacity exactly.

### The instance

Terminals are $t_1, \dots, t_9$. For each pair $i < j$ there are three
pre-terminals $p^1_{i,j}, p^2_{i,j}, p^3_{i,j}$, each with out-edges to $t_i$
and $t_j$ and no others. Write $P_{i,j} = \{p^1_{i,j}, p^2_{i,j}, p^3_{i,j}\}$,
with $P_{j,i}=P_{i,j}$ and $p^r_{j,i}=p^r_{i,j}$.

For each edge $e = (p^r_{x,y}, t_y)$, let $a < b < c < d$ be the four smallest
indices in $[9] \setminus \{x, y\}$. Add $17$ vertices, each with out-neighborhood
$$P_{a,b} \cup P_{a,c} \cup \{p^1_{d,x}, p^2_{d,x}, p^r_{x,y}\}$$
and no in-edges.

Capacities: assign $p^1_{i,j}$ and $p^3_{i,j}$ to $t_j$, assign $p^2_{i,j}$ to
$t_i$, and assign the $17$ vertices of the edge $e$ to $t_a$. Then $\mathrm{cap}_t$
is the number of vertices assigned to $t$.

### Running

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install networkx
python counterexample/counterexample.py
```

The script builds the instance and checks that the compact connectivity
condition holds, that it fails after deleting any one edge, and that it fails
after contracting any pre-terminal into either of its terminals. It exits with
status 1 at the first failed check.

The implementation groups the 17 identical source vertices of each gadget
using a multiplicity, preserving their contribution to the capacity checks.
