"""Checks the instance of README.md.

The instance satisfies the compact connectivity condition, and the condition
fails after deleting any edge and after contracting any pre-terminal into
either of its terminals.
"""

import argparse
import sys
import time

from compact_connectivity import (Instance, compact_sets, contract, delete_edge,
                                  satisfies_condition)

K = 9


def build(copies):
    out_adj = [[] for _ in range(K)]
    mult = [1] * K
    name = ["t%d" % (i + 1) for i in range(K)]
    home = {}

    def add(label, targets, weight, assigned):
        v = len(out_adj)
        out_adj.append(list(targets))
        mult.append(weight)
        name.append(label)
        home[v] = assigned
        return v

    P = {}
    for i in range(K):
        for j in range(i + 1, K):
            # p^1 and p^3 are assigned to t_j, p^2 to t_i.
            P[i, j] = P[j, i] = [
                add("p^%d_{%d,%d}" % (r + 1, i + 1, j + 1), [i, j], 1, i if r % 2 else j)
                for r in range(3)]

    for p, y in [(p, t) for p in range(K, len(out_adj)) for t in out_adj[p]]:
        x = out_adj[p][0] if out_adj[p][1] == y else out_adj[p][1]
        a, b, c, d = [i for i in range(K) if i not in (x, y)][:4]
        add("v(%s->t%d)" % (name[p], y + 1),
            P[a, b] + P[a, c] + P[d, x][:2] + [p], copies, a)

    cap = [0] * K
    for v, t in home.items():
        cap[t] += mult[v]
    return Instance(K, out_adj, mult, cap), name


def fails(inst, suspects):
    """Whether inst violates the condition.

    `suspects` are the vertices whose compact sets the last modification may
    have changed; if one of them is empty, the condition fails at once.
    """
    sets = compact_sets(inst, suspects)
    return any(not sets[v] for v in suspects) or not satisfies_condition(inst)


def report(label, done, total, start):
    if done % 10 and done != total:
        return
    sys.stderr.write("\r%s %d/%d (%.0fs)%s"
                     % (label, done, total, time.time() - start,
                        "\n" if done == total else ""))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--copies", type=int, default=17,
                    help="number of vertices added per edge (default 17)")
    ap.add_argument("--skip-contractions", action="store_true")
    args = ap.parse_args()
    start = time.time()

    inst, name = build(args.copies)
    pre = [v for v in inst.non_terminals() if all(t < K for t in inst.out_adj[v])]
    others = sorted(set(inst.non_terminals()) - set(pre))
    edges = [(u, v) for u in inst.non_terminals() for v in inst.out_adj[u]]
    print("k = %d, %d pre-terminals, %d distinct edges, %d x %d other vertices, cap = %s"
          % (K, len(pre), len(edges), len(others), args.copies, inst.cap))

    assert all(len(inst.out_adj[v]) == 2 for v in pre)
    assert all(len(inst.out_adj[v]) == K for v in others)
    assert inst.total_cap() == inst.total_mult()

    sets = compact_sets(inst)
    assert satisfies_condition(inst, sets)
    print("compact connectivity holds")

    for i, (u, v) in enumerate(edges):
        if not fails(delete_edge(inst, u, v), [u] + inst.in_adj[u]):
            sys.exit("deleting %s -> %s preserves the condition" % (name[u], name[v]))
        report("edge deletions", i + 1, len(edges), start)
    print("all %d edge deletions break the condition" % len(edges))

    if args.skip_contractions:
        return
    pairs = [(p, t) for p in pre for t in inst.out_adj[p]]
    for i, (p, t) in enumerate(pairs):
        smaller, new_id = contract(inst, p, t)
        if not fails(smaller, [new_id[w] for w in inst.in_adj[p]]):
            sys.exit("contracting %s into %s preserves the condition" % (name[p], name[t]))
        report("contractions", i + 1, len(pairs), start)
    print("all %d contractions break the condition (%.0fs)" % (len(pairs), time.time() - start))


if __name__ == "__main__":
    main()
