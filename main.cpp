#include <iostream>
#include <vector>
#include <random>
#include <array>
#include <cmath>
#include <cassert>
#include <algorithm>
#include <queue>
#include <chrono>

using namespace std;

typedef vector<int> EdgeIdSet;

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
            neighbours[v].push_back(edges.size());
        }
        edges.push_back(e);
    }

    void removeEdge(int edgeId)
    {
        --m;
        for (int v : edges[edgeId]) {
            neighbours[v].erase(find(neighbours[v].begin(), neighbours[v].end(), edgeId));
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

enum RandomMode
{
    randomEdgeCount,
    fixedEdgeCount
};

vector<vector<unsigned long long>> binom;

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
        for (int i = 0; ok && i < K; ++i) {
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
bool isLeaf(const Hypergraph<K> &g, const Edge<K> &edge)
{
    int cnt = 0;
    for (int v : edge) {
        if (g.getNeighbourEdgesIds(v).size() == 1) {
            ++cnt;
        }
    }
    return cnt >= K - 1;
}

template<int K>
pair<vector<int>, int> maxIndependentSet(Hypergraph<K> g)
{
    int n = g.numberOfVertices();
    int m = g.numberOfEdges();
    vector<char> deletedVert(n, 0);
    vector<char> queuedEdges(m, 0);
    vector<int> result;
    queue<int> edgeQueue;
    for (int id = 0; id < m; ++id) {
        if (isLeaf<K>(g, g.getEdge(id))) {
            queuedEdges[id] = 1;
            edgeQueue.push(id);
        }
    }
    while (!edgeQueue.empty()) {
        if (!queuedEdges[edgeQueue.front()]) {
            edgeQueue.pop();
            continue;
        }
        Edge<K> curEdge = g.getEdge(edgeQueue.front());
        edgeQueue.pop();
        int w = -1;
        for (int v : curEdge) {
            if (g.getNeighbourEdgesIds(v).size() > 1) {
                w = v;
                break;
            }
        }
        if (w == -1) {
            w = curEdge[0];
        }
        for (int v : curEdge) {
            assert(!deletedVert[v]);
            deletedVert[v] = 1;
            if (v != w) {
                result.push_back(v);
            }
        }
        while (!g.getNeighbourEdgesIds(w).empty()) {
            int curId = *g.getNeighbourEdgesIds(w).begin();
            g.removeEdge(curId);
            queuedEdges[curId] = 0;
            for (int v : g.getEdge(curId)) {
                for (int id : g.getNeighbourEdgesIds(v)) {
                    if (!queuedEdges[id] && isLeaf<K>(g, g.getEdge(id))) {
                        queuedEdges[id] = 1;
                        edgeQueue.push(id);
                    }
                }
            }
        }
    }
    int verticesLeft = 0;
    for (int v = 0; v < n; ++v) {
        if (!deletedVert[v] && g.getNeighbourEdgesIds(v).empty()) {
            result.push_back(v);
        } else if (!deletedVert[v]) {
            ++verticesLeft;
        }
    }
    return {result, verticesLeft};
}

void calculateBinomials(int n, int k) {
    binom.resize(n + 1, vector<unsigned long long>(k + 1, 0));
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
    constexpr int iters = 20;
    // number of vertices
    constexpr int n = 200000;
    // probability of taking the edge into hypergraph will be equal to c / C(n - 1, k - 1)
    constexpr double c = 1.3;

    // if set to randomEdgeCount, generated graphs will have random amount of edges from binomial distribution
    // if set to fixedEdgeCount, generated graphs will have fixed amount of edges equal to the expected one
    constexpr RandomMode edgeMode = fixedEdgeCount;

    auto start = std::chrono::high_resolution_clock::now();

    long long setSizeSum = 0;
    long long edgeSum = 0;
    long long leftVerticesSum = 0;

    calculateBinomials(n, K);

    for (int it = 0; it < iters; ++it) {
        auto g = generate<K>(n, c, edgeMode);
        edgeSum += g.numberOfEdges();
        auto result = maxIndependentSet<K>(std::move(g));
        setSizeSum += result.first.size();
        leftVerticesSum += result.second;

        /*
        * Independent set validation
        *
        vector<char> in(n + 1, 0);
        for (int v : result.first) {
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
    cout << "Average portion of vertices left after execution of algorithm: " << (double)leftVerticesSum / iters / n << endl;
    cout << "Parameters:" << endl;
    cout << "Number of tries: " << iters << endl;
    cout << "Number of vertices: " << n << endl;
    cout << "Size of edge: " << K << endl;
    cout << "Constant c: " << c << endl;
    cout << "Probability p of taking the edge into hypergraph: " << c / binom[n - 1][K - 1] << endl;
    cout << "Expected number of edges: " << c * n / K << endl;
    cout << "Actual average number of edges: " << (double)edgeSum / iters << endl;

    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << endl << "Time taken: " << duration.count() / 1000.0 << " milliseconds" << endl;

    return 0;
}
