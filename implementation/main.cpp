#include "io.h"
#include "maxflow.h"

#include <cassert>
#include <string>
#include <utility>

using namespace std;

using Edge = pair<int, int>;

// Keep original vertex IDs throughout; inactive vertices have no incident edges.
struct Graph {
    int n, k;
    vector<set<int>> out;
    vector<bool> active;

    explicit Graph(const Instance& input)
        : n(input.n), k(input.k), out(input.out), active(n, true) {}

    void remove_vertex(int v) {
        out[v].clear();
        active[v] = false;
        for (int u = k; u < n; ++u)
            out[u].erase(v);
    }

    void contract(int preterminal, int terminal) {
        for (int u = k; u < n; ++u)
            if (out[u].count(preterminal)) out[u].insert(terminal);
        remove_vertex(preterminal);
    }
};

// Proposition "Computing essential terminals for one vertex": one max flow,
// followed by a reverse residual search for the tightest minimum cut.
vector<bool> essential_terminals(const Graph& graph, int v, Edge skip = {-1, -1}) {
    int sink = 2 * graph.n;
    int infinity = graph.k + 1;
    MaxFlow flow(sink + 1);
    // Vertex x has copies x_in = 2*x and x_out = 2*x+1; the source is v_in.
    for (int x = 0; x < graph.n; ++x) {
        if (!graph.active[x]) continue;
        flow.add_edge(2 * x, 2 * x + 1, x == v ? infinity : 1);
        if (x < graph.k) flow.add_edge(2 * x + 1, sink, infinity);
        for (int y : graph.out[x])
            if (Edge{x, y} != skip) flow.add_edge(2 * x + 1, 2 * y, infinity);
    }
    flow.run(2 * v, sink);
    auto reach = flow.can_reach(sink);
    vector<bool> essential(graph.k, false);
    for (int t = 0; t < graph.k; ++t)
        essential[t] = graph.active[t] && !reach[2 * t] && reach[2 * t + 1];
    return essential;
}

// Capacitated bipartite matching, used for both the initial assignment and
// the pre-terminal matching in ShiftAssignment. Unmatched vertices get -1.
vector<int> matching(const vector<vector<int>>& choices,
                     const vector<int>& capacity) {
    int n = static_cast<int>(choices.size());
    int k = static_cast<int>(capacity.size());
    int source = n + k;
    int sink = source + 1;
    MaxFlow flow(sink + 1);
    for (int v = 0; v < n; ++v) {
        if (choices[v].empty()) continue;
        flow.add_edge(source, v, 1);
        for (int t : choices[v]) flow.add_edge(v, n + t, 1);
    }
    for (int t = 0; t < k; ++t) flow.add_edge(n + t, sink, capacity[t]);
    flow.run(source, sink);
    vector<int> assignment(n, -1);
    for (int v = 0; v < n; ++v) {
        for (const auto& e : flow.graph[v]) {
            if (e.to >= n && e.to < n + k && e.capacity == 0)
                assignment[v] = e.to - n;
        }
    }
    return assignment;
}

// ShiftAssignment from the paper: fix a pre-terminal matching and secondary
// edges, then shift assignments around cycles until an edge is non-critical.
Edge shift_assignment(const Graph& graph, vector<int>& assignment) {
    vector<vector<int>> choices(graph.n);
    vector<int> unit(graph.k, 0);
    for (int t = 0; t < graph.k; ++t) unit[t] = graph.active[t] ? 1 : 0;
    for (int p = graph.k; p < graph.n; ++p) {
        for (int t : graph.out[p])
            if (t < graph.k) choices[p].push_back(t);
    }
    auto matched = matching(choices, unit);
    vector<Edge> secondary(graph.k, {-1, -1});
    for (int p = graph.k; p < graph.n; ++p) {
        int t = matched[p];
        if (t == -1) continue;
        auto q = graph.out[p].begin();
        if (*q == t) ++q;
        assert(q != graph.out[p].end());
        secondary[t] = {p, *q};
    }
    for (int t = 0; t < graph.k; ++t)
        assert(!graph.active[t] || secondary[t].first != -1);

    // The graph and secondary edges stay fixed during the shifts. Cache each
    // essential-terminal set after deleting e_t; an empty vector means unknown.
    vector<vector<vector<bool>>> after_removal(
        graph.k, vector<vector<bool>>(graph.n));
    while (true) {
        vector<int> witness(graph.k, -1);
        vector<int> predecessor(graph.k, -1);
        for (int t = 0; t < graph.k; ++t) {
            if (!graph.active[t]) continue;
            for (int v = graph.k; v < graph.n; ++v) {
                if (!graph.active[v]) continue;
                auto& essential = after_removal[t][v];
                if (essential.empty()) essential = essential_terminals(graph, v, secondary[t]);
                if (!essential[assignment[v]]) {
                    witness[t] = v;
                    predecessor[t] = assignment[v]; // Reassignment edge: predecessor -> t.
                    break;
                }
            }
            if (witness[t] == -1) return secondary[t];
        }

        // Follow incoming edges to enter a cycle, then shift its distinct labels.
        int t = 0;
        while (!graph.active[t]) ++t;
        vector<bool> seen(graph.k, false);
        while (!seen[t]) {
            seen[t] = true;
            t = predecessor[t];
        }
        int start = t;
        do {
            assignment[witness[t]] = t;
            t = predecessor[t];
        } while (t != start);
        // The paper's integer potential (number of critical vertex/edge pairs)
        // strictly decreases, so at most k * (n-k) cycle shifts are needed.
    }
}

// GLPartition written as a loop: record contractions directly in the parts,
// instead of reconstructing them while returning from recursive calls.
vector<vector<int>> gl_partition(Graph graph, vector<int> capacity,
                                 vector<int> assignment) {
    vector<vector<int>> parts(graph.k);
    for (int t = 0; t < graph.k; ++t) parts[t].push_back(t);
    int remaining = graph.n;
    while (remaining > 0) {
        // 1. Remove a terminal whose part is complete.
        int saturated = -1;
        for (int t = 0; t < graph.k; ++t) {
            if (graph.active[t] && capacity[t] == 0) {
                saturated = t;
                break;
            }
        }
        if (saturated != -1) {
            graph.remove_vertex(saturated);
            --remaining;
            continue;
        }

        // 2. Contract a pre-terminal with only one outgoing edge.
        int leaf = -1;
        for (int p = graph.k; p < graph.n; ++p) {
            if (graph.active[p] && graph.out[p].size() == 1 && *graph.out[p].begin() < graph.k) {
                leaf = p;
                break;
            }
        }
        if (leaf != -1) {
            int t = *graph.out[leaf].begin();
            assert(assignment[leaf] == t && capacity[t] > 0);
            parts[t].push_back(leaf);
            --capacity[t];
            graph.contract(leaf, t);
            --remaining;
            continue;
        }

        // 3. Shift the assignment if needed, then delete a non-critical edge.
        auto [p, q] = shift_assignment(graph, assignment);
        graph.out[p].erase(q);
    }
    return parts;
}

int main(int argc, char** argv) {
    try {
        if (argc == 2 && string(argv[1]) == "--help") {
            print_usage();
            return 0;
        }
        auto input = read_input(argc, argv);
        Graph graph(input);
        vector<vector<int>> choices(graph.n);
        for (int v = graph.k; v < graph.n; ++v) {
            auto essential = essential_terminals(graph, v);
            for (int t = 0; t < graph.k; ++t)
                if (essential[t]) choices[v].push_back(t);
        }
        auto assignment = matching(choices, input.capacity);
        for (int v = graph.k; v < graph.n; ++v) {
            if (assignment[v] != -1) continue;
            cout << "Flow-essential assignment condition does not hold.\n";
            return 1;
        }
        print_partition(gl_partition(move(graph), input.capacity, move(assignment)));
        return 0;
    } catch (const exception& error) {
        cerr << "Error: " << error.what() << '\n';
        return 2;
    }
}
