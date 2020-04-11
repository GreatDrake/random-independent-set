#include <iostream>
#include <vector>
#include <random>
#include <unordered_set>
#include <array>
#include <cmath>
#include <cassert>

using namespace std;

typedef unordered_set<int> EdgeIdSet;

template<int K>
using Edge = array<int, K>;

template<int K>
class Hypergraph
{
public:
    Hypergraph() = delete;

    explicit Hypergraph(int n) : m(0)
    {
        neighbours.resize(n);
    }

    const Edge<K> &getEdge(int edgeId) const
    {
        return edges[edgeId];
    }

    void addEdge(const Edge<K> &e)
    {
        ++m;
        for (int v : e) {
            neighbours[v].insert(edges.size());
        }
        edges.push_back(e);
    }

    void removeEdge(int edgeId)
    {
        --m;
        for (int v : edges[edgeId]) {
            neighbours[v].erase(edgeId);
        }
    }

    const EdgeIdSet &getNeighbourEdgesIds(int v) const
    {
        return neighbours[v];
    }

    int numberOfEdges() const
    {
        return edges.size();
    }

    int numberOfVertices() const
    {
        return neighbours.size();
    }

private:
    vector<Edge<K>> edges;
    vector<EdgeIdSet> neighbours;
    int m;
};

vector<vector<long long>> binom;

void calculateBinomials(int n, int k) {
    binom.resize(n + 1, vector<long long>(k + 1, 0));
    binom[0][0] = 1;
    for (int i = 1; i <= n; ++i) {
        binom[i][1] = i;
        binom[i][0] = 1;
    }
    for (int i = 1; i <= n; ++i) {
        for (int j = 2; j <= k; ++j) {
            binom[i][j] = binom[i - 1][j - 1] + binom[i - 1][j];
        }
    }
}

enum RandomMode
{
    randomEdgeCount,
    fixedEdgeCount
};

template<int K>
Hypergraph<K> generate(int n, double c, RandomMode edgeMode)
{
    static std::random_device rd;
    static std::mt19937 gen(rd());

    std::uniform_int_distribution<int> vertexDist(0, n - 1);
    Hypergraph<K> result(n);
    int cnt = 0;

    long long m;
    if (edgeMode == randomEdgeCount) {
        std::binomial_distribution<long long> edgeDist(binom[n][K], c / (double)binom[n - 1][K - 1]);
        m = edgeDist(gen);
    } else if (edgeMode == fixedEdgeCount) {
        m = round(c * n / K);
    } else {
        abort();
    }

    while (cnt < m) {
        Edge<K> cur;
        for (int j = 0; j < K; ++j) {
            cur[j] = vertexDist(gen);
        }
        bool ok = true;
        for (int i = 0; i < K; ++i) {
            for (int j = i + 1; j < K; ++j) {
                if (cur[i] == cur[j]) {
                    ok = false;
                    break;
                }
            }
        }
        if (ok) {
            ++cnt;
            result.addEdge(cur);
        }
    }
    return result;
}

template<int K>
void dfs(int v, const Hypergraph<K> &g, vector<int> &dist)
{
    for (int edgeId : g.getNeighbourEdgesIds(v)) {
        for (int u : g.getEdge(edgeId)) {
            if (dist[u] == -1) {
                dist[u] = dist[v] + 1;
                dfs(u, g, dist);
            }
        }
    }
}

template<int K>
vector<int> maxIndependentSet(Hypergraph<K> g)
{
    int n = g.numberOfVertices();
    vector<int> dist(n, -1);
    vector<int> deleted(n, 0);
    vector<int> result;
    for (int i = 0; i < n; ++i) {
        if (dist[i] == -1) {
            dist[i] = 0;
            dfs(i, g, dist);
        }
    }
    vector<vector<int>> distVertices(n);
    for (int i = 0; i < n; ++i) {
        distVertices[dist[i]].push_back(i);
    }

    for (int d = n - 1; d >= 0; --d) {
        while (!distVertices[d].empty()) {
            int cur = distVertices[d].back();
            distVertices[d].pop_back();
            if (deleted[cur]) {
                continue;
            }
            if (g.getNeighbourEdgesIds(cur).empty()) {
                deleted[cur] = 1;
                result.push_back(cur);
            } else if (g.getNeighbourEdgesIds(cur).size() == 1) {
                int w = -1;
                bool fail = false;
                Edge<K> cur_edge = g.getEdge(*g.getNeighbourEdgesIds(cur).begin());
                for (int u : cur_edge) {
                    if (g.getNeighbourEdgesIds(u).size() > 1) {
                        if (w == -1) {
                            w = u;
                        } else {
                            fail = true;
                        }
                    }
                }
                if (fail) {
                    continue;
                }
                if (w == -1) {
                    w = cur_edge[0];
                }
                for (int u : cur_edge) {
                    if (u != w) {
                        deleted[u] = 1;
                        result.push_back(u);
                    }
                }
                deleted[w] = 1;
                while (!g.getNeighbourEdgesIds(w).empty()) {
                    g.removeEdge(*g.getNeighbourEdgesIds(w).begin());
                }
            } else {
                continue;
            }
        }
    }

    return result;
}

double f(double x, double c, int k)
{
    return exp(-c * pow(x, k - 1));
}

double expectedLimit(double c, int k)
{
    constexpr double eps = 1e-8;
    double l = 0, r = 1;
    while (r - l > eps) {
        double m = (r + l) / 2;
        if (f(m, c, k) > m) {
            l = m;
        } else {
            r = m;
        }
    }
    return r + c * (k - 1) / k * pow(r, k);
}

int main()
{
    // size of edge
    constexpr int K = 3;
    // number of tries
    constexpr int iters = 40;
    // number of vertices
    constexpr int n = 10000;
    // probability of taking the edge into hypergraph will be equal to c / C(n - 1, k - 1)
    constexpr double c = 0.5;

    // if set to randomEdgeCount, generated graphs will have random amount of edges from binomial distribution
    // if set to fixedEdgeCount, generated graphs will have fixed amount of edges equal to the expected one
    constexpr RandomMode edgeMode = fixedEdgeCount;

    long long setSizeSum = 0;
    long long edgeSum = 0;

    calculateBinomials(n, K);

    for (int it = 0; it < iters; ++it) {
        auto g = generate<K>(n, c, edgeMode);
        edgeSum += g.numberOfEdges();
        auto result = maxIndependentSet<K>(g);
        setSizeSum += result.size();

        /*
        * Independent set validation
        *
        vector<char> in(n + 1, 0);
        for (int v : result) {
            ++in[v];
            assert(in[v] <= 1);
        }
        for (int i = 0; i < g.numberOfEdges(); ++i) {
            int cnt = 0;
            for (int u : g.getEdge(i)) {
                cnt += in[u];
            }
            assert(cnt < K);
        }
        */
    }

    cout << "Expected limit: " << expectedLimit(c, K) << endl;
    cout << "Actual average: " << (double)setSizeSum / iters / n << endl;
    cout << "Parameters:" << endl;
    cout << "Number of tries: " << iters << endl;
    cout << "Number of vertices: " << n << endl;
    cout << "Size of edge: " << K << endl;
    cout << "Constant c: " << c << endl;
    cout << "Probability p of taking the edge into hypergraph: " << c / binom[n - 1][K - 1] << endl;
    cout << "Expected number of edges: " << c * n / K << endl;
    cout << "Actual average number of edges: " << (double)edgeSum / iters << endl;

    return 0;
}
