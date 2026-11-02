#pragma once

#include <algorithm>
#include <limits>
#include <queue>
#include <vector>

// Dinic's algorithm. Each edge stores its remaining (residual) capacity.
struct MaxFlow {
    struct Edge {
        int to, reverse, capacity;
    };
    std::vector<std::vector<Edge>> graph;
    std::vector<int> level, next;

    explicit MaxFlow(int n) : graph(n), level(n), next(n) {}

    void add_edge(int u, int v, int capacity) {
        int a = static_cast<int>(graph[u].size());
        int b = static_cast<int>(graph[v].size());
        graph[u].push_back({v, b, capacity});
        graph[v].push_back({u, a, 0});
    }

    bool build_levels(int source, int sink) {
        std::fill(level.begin(), level.end(), -1);
        std::queue<int> queue;
        queue.push(source);
        level[source] = 0;
        while (!queue.empty()) {
            int u = queue.front();
            queue.pop();
            for (const auto& e : graph[u]) {
                if (e.capacity > 0 && level[e.to] == -1) {
                    level[e.to] = level[u] + 1;
                    queue.push(e.to);
                }
            }
        }
        return level[sink] != -1;
    }

    int send(int u, int sink, int amount) {
        if (u == sink) return amount;
        for (int& i = next[u]; i < static_cast<int>(graph[u].size()); ++i) {
            auto& e = graph[u][i];
            if (e.capacity == 0 || level[e.to] != level[u] + 1) continue;
            int sent = send(e.to, sink, std::min(amount, e.capacity));
            if (sent == 0) continue;
            e.capacity -= sent;
            graph[e.to][e.reverse].capacity += sent;
            return sent;
        }
        return 0;
    }

    int run(int source, int sink) {
        int total = 0;
        while (build_levels(source, sink)) {
            std::fill(next.begin(), next.end(), 0);
            while (int sent = send(source, sink, std::numeric_limits<int>::max()))
                total += sent;
        }
        return total;
    }

    // Reverse residual search: vertices FROM WHICH the sink is reachable.
    std::vector<bool> can_reach(int sink) const {
        std::vector<bool> reached(graph.size(), false);
        std::queue<int> queue;
        queue.push(sink);
        reached[sink] = true;
        while (!queue.empty()) {
            int u = queue.front();
            queue.pop();
            for (const auto& e : graph[u]) {
                if (!reached[e.to] && graph[e.to][e.reverse].capacity > 0) {
                    reached[e.to] = true;
                    queue.push(e.to);
                }
            }
        }
        return reached;
    }
};
