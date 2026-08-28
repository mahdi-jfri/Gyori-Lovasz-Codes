# Gyori-Lovasz-Codes

Code for the appendix of "Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem".
Definitions and notation are those of the appendix.

## counterexample/

An instance on which the compact connectivity condition holds, but deleting any
edge or contracting any pre-terminal into a terminal breaks it.

### The instance

Terminals are $t_1, \dots, t_9$. For each pair $i < j$ there are three
pre-terminals $p^1_{i,j}, p^2_{i,j}, p^3_{i,j}$, each with out-edges to $t_i$
and $t_j$ and no others. Write $P_{i,j} = \{p^1_{i,j}, p^2_{i,j}, p^3_{i,j}\}$.

For each edge $e = (p^r_{x,y}, t_y)$, let $a < b < c < d$ be the four smallest
indices in $[9] \setminus \{x, y\}$. Add $17$ vertices, each with out-neighborhood
$$P_{a,b} \cup P_{a,c} \cup \{p^1_{d,x}, p^2_{d,x}, p^r_{x,y}\}$$
and no in-edges.

Capacities: assign $p^1_{i,j}$ and $p^3_{i,j}$ to $t_j$, assign $p^2_{i,j}$ to
$t_i$, and assign the $17$ vertices of the edge $e$ to $t_a$. Then $\mathrm{cap}_t$
is the number of vertices assigned to $t$.

### Running

    pip install networkx
    python counterexample/counterexample.py

The script builds the instance and checks that the compact connectivity
condition holds, that it fails after deleting any one edge, and that it fails
after contracting any pre-terminal into either of its terminals. It exits with
status 1 at the first failed check.
