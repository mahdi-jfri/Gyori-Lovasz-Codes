"""Compact connectivity via maximum flows.

Vertices are 0, ..., n-1, the terminals are 0, ..., k-1, and terminals have no
out-edges.  mult[v] is the number of identical copies of v; a vertex with
mult[v] > 1 must have in-degree 0.
"""

import networkx as nx
from networkx.algorithms.flow import shortest_augmenting_path


class Instance:
    def __init__(self, k, out_adj, mult, cap):
        self.k = k
        self.n = len(out_adj)
        self.out_adj = [list(vs) for vs in out_adj]
        self.mult = list(mult)
        self.cap = list(cap)
        self.in_adj = [[] for _ in range(self.n)]
        for u in range(self.n):
            for v in self.out_adj[u]:
                self.in_adj[v].append(u)
        assert all(self.mult[v] == 1 or not self.in_adj[v] for v in range(self.n))

    def terminals(self):
        return range(self.k)

    def non_terminals(self):
        return range(self.k, self.n)

    def total_mult(self):
        return sum(self.mult[v] for v in self.non_terminals())

    def total_cap(self):
        return sum(self.cap)


def compact_connected(inst, v, t):
    """Whether v is in C(t).

    Split every vertex x into an arc x_in -> x_out of capacity mult[x], except
    v and t whose arcs get capacity k.  Add source -> v_in and s_out -> sink for
    every terminal s, and give all other arcs capacity k.  Then v is in C(t)
    exactly when the maximum flow is k.
    """
    k = inst.k
    net = nx.DiGraph()
    net.add_edge("source", ("in", v), capacity=k)
    stack, seen = [v], {v}
    while stack:
        x = stack.pop()
        net.add_edge(("in", x), ("out", x),
                     capacity=k if x in (v, t) else inst.mult[x])
        if x < k:
            net.add_edge(("out", x), "sink", capacity=k)
            continue
        for y in inst.out_adj[x]:
            net.add_edge(("out", x), ("in", y), capacity=k)
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return nx.maximum_flow_value(net, "source", "sink", cutoff=k,
                                 flow_func=shortest_augmenting_path) >= k


def compact_sets(inst, vertices=None):
    """{v: {t : v in C(t)}} for the given non-terminals, by default all of them."""
    if vertices is None:
        vertices = inst.non_terminals()
    return {v: frozenset(t for t in inst.terminals() if compact_connected(inst, v, t))
            for v in vertices}


def satisfies_condition(inst, sets=None):
    """Whether the compact connectivity condition holds.

    Network: source -> v of capacity mult[v], v -> t of capacity mult[v] when v
    is in C(t), and t -> sink of capacity cap_t.  The condition holds exactly
    when a flow of value sum_v mult[v] exists.
    """
    if inst.total_cap() != inst.total_mult():
        return False
    if sets is None:
        sets = compact_sets(inst)
    net = nx.DiGraph()
    for t in inst.terminals():
        net.add_edge(("terminal", t), "sink", capacity=inst.cap[t])
    for v in inst.non_terminals():
        if not sets[v]:
            return False
        net.add_edge("source", v, capacity=inst.mult[v])
        for t in sets[v]:
            net.add_edge(v, ("terminal", t), capacity=inst.mult[v])
    return nx.maximum_flow_value(net, "source", "sink") == inst.total_mult()


def delete_edge(inst, u, v):
    """G - (u, v), with T and cap unchanged."""
    out_adj = [list(vs) for vs in inst.out_adj]
    out_adj[u].remove(v)
    return Instance(inst.k, out_adj, inst.mult, inst.cap)


def contract(inst, p, t):
    """Contract the pre-terminal p into the terminal t.

    The in-edges of p are redirected to t and cap_t drops by mult[p].  Returns
    the new instance and the map from old to new vertex numbers.
    """
    assert t in inst.out_adj[p] and t < inst.k <= p
    new_id = {x: (x if x < p else x - 1) for x in range(inst.n) if x != p}
    out_adj = [[] for _ in range(inst.n - 1)]
    for x in new_id:
        targets = []
        for y in inst.out_adj[x]:
            z = new_id[t if y == p else y]
            if z != new_id[x] and z not in targets:
                targets.append(z)
        out_adj[new_id[x]] = targets
    mult = [inst.mult[x] for x in new_id]
    cap = list(inst.cap)
    cap[t] -= inst.mult[p]
    return Instance(inst.k, out_adj, mult, cap), new_id
