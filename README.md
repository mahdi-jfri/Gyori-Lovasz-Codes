# Győri–Lovász: Lean formalization and code

This repository contains a **Lean 4.19 formalization** and code
accompanying *Breaking the Exponential Barrier: The First
Polynomial-Time Algorithm for the Győri–Lovász Theorem*.

The Győri–Lovász theorem states that, given a $k$-connected undirected graph $G$,
distinct roots $t_1,\ldots,t_k$, and positive integers $n_1,\ldots,n_k$ with
$\sum_i n_i=|V(G)|$, the vertices can be partitioned into sets $V_1,\ldots,V_k$
such that $t_i\in V_i$, $|V_i|=n_i$, and each induced subgraph $G[V_i]$ is connected.
The paper gives a polynomial-time algorithm for finding such a partition.
Its directed version assumes that every non-terminal has $k$ directed paths to
distinct terminals, pairwise disjoint except at their starting vertex; each
vertex must then reach its terminal within its own part.

The algorithm maintains a **flow-essential assignment**: every non-terminal is
assigned to a terminal whose deletion decreases its terminal connectivity, and
each terminal receives its prescribed number of vertices. This combines cut
structure with capacity constraints. The paper also gives a weighted extension,
allowing each part's non-terminal weight to exceed its capacity by at most
$w_{\max}-1$, where $w_{\max}$ is the largest non-terminal weight.

## Lean formalization (`lean/`)

The 138 modules in [`lean/GyoriLovasz/`](lean/GyoriLovasz/) contain the rooted
partition proofs, the generalized weighted theorem, and programs with proved
polynomial bounds on their explicit cost counters. Lean and Mathlib are pinned
to **4.19.0**.

With [Elan](https://github.com/leanprover/elan) installed, run:

```sh
cd lean
lake exe cache get
lake build
```

The default build imports every module and runs [`CheckAxioms.lean`](lean/CheckAxioms.lean).
This audits all project proofs, safe definitions, and their dependencies,
rejecting proof placeholders and any axioms other than `propext`, `Classical.choice`, and
`Quot.sound`. The formalization has no `sorry` or `admit` proofs and introduces
no additional axioms.

The formal statement of the classical undirected theorem matches the prescribed
roots, positive sizes, exact cardinalities, and connectivity conclusion above.
The generalized directed results use the paper's **minimum-cut formulation** of
essentiality. The bridge to its path-based definition via Menger's theorem is
not formalized; the connectivity corollaries use ordinary vertex connectivity,
which is stronger than the paper's directed terminal-connectivity hypothesis.
The paper's separate near-linear DAG algorithm and appendix results are outside
this formalization. See [`lean/README.md`](lean/README.md) for theorem entry points,
the correspondence with the paper, and the cost model.

## Appendix counterexample (`counterexample/`)

The appendix considers **compact connectivity** and **local connectivity** as
alternative conditions to our flow-essential assignment condition. The code here
checks a counterexample specifically to **maintaining compact connectivity**:
the condition holds initially, but deleting any edge or contracting any
pre-terminal into an adjacent terminal destroys it. Thus this alternative
condition cannot support the paper's contraction/edge-removal framework, even
though it guarantees a valid partition. The example does not refute the
Győri–Lovász theorem or the flow-essential assignment condition.

For completeness, a vertex is compact-connected to a terminal $t$ if it has
$k$ internally vertex-disjoint paths to the terminal set, with at most one path
ending at each terminal other than $t$. Following the appendix's convention,
a vertex with a direct edge to $t$ is also compact-connected to $t$.
The compact connectivity condition asks for an assignment of every non-terminal
to a compact-connected terminal that fills every capacity exactly. Local
connectivity is another condition discussed in the appendix; this script does
not provide a counterexample to its contraction conjecture.

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
