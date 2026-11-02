#pragma once

#include <fstream>
#include <iostream>
#include <limits>
#include <set>
#include <stdexcept>
#include <vector>

struct Instance {
    int n, k;
    std::vector<int> capacity;
    std::vector<std::set<int>> out;
};

inline Instance read_instance(std::istream& input) {
    int n, m, k;
    if (!(input >> n >> m >> k) || n < 1 || m < 0 || k < 1 || k > n ||
        n > (std::numeric_limits<int>::max() - 2) / 2)
        throw std::runtime_error("expected n m k, with n >= k >= 1 and m >= 0");
    Instance instance{n, k, std::vector<int>(k), std::vector<std::set<int>>(n)};
    long long total = 0;
    for (int& c : instance.capacity) {
        int size;
        if (!(input >> size) || size < 1 || size > n)
            throw std::runtime_error("expected k positive part sizes, each at most n");
        total += size;
        c = size - 1;  // Paper capacities count non-terminals only.
    }
    if (total != n) throw std::runtime_error("part sizes must sum to n");
    for (int i = 0; i < m; ++i) {
        int u, v;
        if (!(input >> u >> v) || u < 0 || u >= n || v < 0 || v >= n)
            throw std::runtime_error("expected m directed edges with endpoints in 0..n-1");
        // As in the paper: simple graph, with terminals made into sinks.
        if (u >= k && u != v) instance.out[u].insert(v);
    }
    input >> std::ws;
    if (!input.eof()) throw std::runtime_error("unexpected data after the edge list");
    return instance;
}

inline Instance read_input(int argc, char** argv) {
    if (argc > 2) throw std::runtime_error("usage: gl_partition [input-file]");
    if (argc == 1) return read_instance(std::cin);
    std::ifstream file(argv[1]);
    if (!file) throw std::runtime_error("cannot open input file");
    return read_instance(file);
}

inline void print_usage() {
    std::cout << "Usage: gl_partition [input-file]\n"
              << "Without a file, read from stdin. Input:\n"
              << "  n m k\n  size_0 ... size_(k-1)\n  m lines: u v\n"
              << "Vertices: 0..n-1. Terminals: 0..k-1. Sizes include terminals.\n";
}

inline void print_partition(const std::vector<std::vector<int>>& parts) {
    std::cout << "Flow-essential assignment condition holds.\n";
    for (int t = 0; t < static_cast<int>(parts.size()); ++t) {
        std::cout << "Part " << t << ":";
        for (int v : parts[t]) std::cout << ' ' << v;
        std::cout << '\n';
    }
}
