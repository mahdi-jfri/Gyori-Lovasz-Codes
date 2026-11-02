# Lean formalization

This project uses **Lean 4.19.0** and **Mathlib 4.19.0**. Dependencies are pinned
in [`lake-manifest.json`](lake-manifest.json).

From this directory, run:

```sh
lake exe cache get
lake build
```

[`GyoriLovasz.lean`](GyoriLovasz.lean) imports every module, including
the runtime development. The default build also compiles
[`CheckAxioms.lean`](CheckAxioms.lean), which audits every safe project declaration
and all transitive dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed; a proof placeholder or an additional axiom fails the
build. Classical choice is used in the mathematical development.
Compiler-generated unsafe implementations are excluded from this logical audit.

## Statements and correspondence with the paper

All names below are in namespace `GyoriLovasz`, with `WordInstance.` added
where shown.

| Formal result | Content and paper correspondence |
| --- | --- |
| [`gyori_lovasz`](GyoriLovasz/Main.lean) | Classical undirected rooted partition theorem from the introduction: distinct roots, positive sizes summing to the vertex count, and connected parts of exactly those sizes. Its specification is `MainTheoremStatement` in [`Specification.lean`](GyoriLovasz/Specification.lean). This statement alone asserts existence. |
| [`feasible_partition`](GyoriLovasz/Main.lean) | Directed partition from a capacity-exact, cut-essential assignment, corresponding to `thm:ess-assign-cond` without its running-time assertion. Part sizes are `capacity i + 1`. |
| [`generalized_weighted_gyori_lovasz`](GyoriLovasz/WeightedMain.lean) | Generalized weighted existence theorem (`gyori-weighted-poly-theorem`) under `SplitFeasible`, the integral split-assignment condition defined in [`Weighted.lean`](GyoriLovasz/Weighted.lean), using cut essentiality. |
| [`WordInstance.unweighted_polynomial_time`](GyoriLovasz/RuntimeUnweightedProgram.lean) | Computed labels with exact prescribed sizes and a polynomial bound on the explicit cost counter, under ordinary vertex connectivity. |
| [`WordInstance.generalized_weighted_input_polynomial_time`](GyoriLovasz/RuntimeInputSize.lean) | Directed weighted program, correctness, and polynomial cost in stored input size under the cut-based split-assignment condition. |
| [`WordInstance.weighted_input_polynomial_time`](GyoriLovasz/RuntimeInputSize.lean) | Weighted connectivity corollary with total non-terminal weight at most total capacity; its connectivity assumption is ordinary vertex connectivity. |

The definitions make the following conventions explicit:

- Vertices and terminals are indexed by `Fin n` and `Fin k`. A total label
  function assigns every vertex to exactly one part. Each root has its own
  label, and `ReachWithin` certifies a directed path to that root entirely
  inside the part.
- `KConnected E k` requires `k < n` and reachability between every pair of
  surviving vertices after deleting fewer than `k` vertices.
  `MainTheoremStatement` also requires `0 < k` and a simple undirected graph.
- Capacities count non-terminals, so a part of size `sizes i` has capacity
  `sizes i - 1`. Weighted loads also exclude terminals.
- The weighted parameter `bound` is any positive upper bound on non-terminal
  weights. Taking it to be the maximum weight gives the paper's additive
  allowance `w_max - 1`; if there are no non-terminals, one can take `bound = 1`.

## Scope of the verification

The classical undirected theorem has the paper's hypotheses and conclusion.
The generalized directed statements implement its cut formulation:
[`CutEssential`](GyoriLovasz/Criticality.lean) means that the terminal belongs
to the separator of some minimum cut. The paper proves its equivalence to
path-based flow essentiality using Menger's theorem and the tightest minimum
cut. That path/cut equivalence is not formalized here.

The paper's directed connectivity hypothesis is **k-T-connectivity**: each
non-terminal has `k` paths to distinct terminals, disjoint except at their
source. The formal connectivity corollaries instead use `KConnected`, a stronger
assumption. Consequently, those corollaries do not directly state the full
path-based directed theorems `thm:k-t-conn` and `thm:weighted-k-t-conn`.
The generalized cut-based assignment results apply to directed graphs without
assuming ordinary vertex connectivity.

The polynomial bounds concern the natural-number counters returned by
[`Costed.Computation`](GyoriLovasz/RuntimeCostedScan.lean). Inputs use Boolean
adjacency matrices and binary lists for weights and capacities.
[`inputSize`](GyoriLovasz/RuntimeInputSize.lean) counts their stored Boolean
and reference/index cells. These are proofs in the explicit cost model encoded
by the programs, rather than measurements of Lean's compiled execution time.

The separate `O(m log n)` DAG algorithm, the appendix's relaxed-connectivity
theorems, and the Python counterexample are not formalized by these modules.
