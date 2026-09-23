#include <iostream>
#include <fstream>
#include <deque>
#include <queue>
#include <algorithm>
#include <functional>
#include <climits>
#include <cstdint>
#include <iomanip>
#include <string>
#include <chrono>
#include <sstream>
#include <vector>
#include <unordered_map>
#include <unordered_set>

const std::uint64_t GOAL = 0x123456789ABCDEF0ULL;

// ============================================================
//  timeout
// ============================================================
std::chrono::steady_clock::time_point g_deadline;
bool g_timeoutEnabled = false;

inline bool timeIsUp()
{
    if (!g_timeoutEnabled) return false;
    return std::chrono::steady_clock::now() >= g_deadline;
}

// ============================================================
//  64-bit mixer hash
// ============================================================
struct Hash64
{
    std::size_t operator()(std::uint64_t x) const noexcept
    {
        x ^= x >> 33; x *= 0xff51afd7ed558ccdULL;
        x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL;
        x ^= x >> 33;
        return (std::size_t)x;
    }
};

// ============================================================
//  move tables
// ============================================================
static int  neighborPos[16][4];
static char neighborMove[16][4];
static int  neighborCnt[16];
static char oppositeMove[128];
static int  mvToDir[128];

static void initTables()
{
    int dr[] = { -1, 1, 0, 0 };
    int dc[] = { 0, 0,-1, 1 };
    char mv[] = { 'U','D','L','R' };
    for (int b = 0; b < 16; ++b)
    {
        int r = b >> 2, c = b & 3, cnt = 0;
        for (int i = 0; i < 4; ++i)
        {
            int nr = r + dr[i], nc = c + dc[i];
            if (nr < 0 || nr >= 4 || nc < 0 || nc >= 4) continue;
            neighborPos[b][cnt] = nr * 4 + nc;
            neighborMove[b][cnt] = mv[i];
            ++cnt;
        }
        neighborCnt[b] = cnt;
    }
    for (int i = 0; i < 128; ++i) { oppositeMove[i] = 0; mvToDir[i] = 0; }
    oppositeMove[(int)'U'] = 'D'; mvToDir[(int)'U'] = 0;
    oppositeMove[(int)'D'] = 'U'; mvToDir[(int)'D'] = 1;
    oppositeMove[(int)'L'] = 'R'; mvToDir[(int)'L'] = 2;
    oppositeMove[(int)'R'] = 'L'; mvToDir[(int)'R'] = 3;
}

inline std::uint64_t swapped(std::uint64_t state, int i, int j)
{
    int si = 4 * (15 - i);
    int sj = 4 * (15 - j);
    std::uint64_t d = ((state >> si) ^ (state >> sj)) & 0xFULL;
    return state ^ (d << si) ^ (d << sj);
}

inline int findBlank(std::uint64_t state)
{
    for (int i = 0; i < 16; ++i)
        if (((state >> (4 * (15 - i))) & 0xF) == 0) return i;
    return -1;
}

// ============================================================
//  THE heuristic — exactly JS heuristicCornerConflict:
//  Manhattan + linear conflicts + corner checks
//  (admissible, but NOT consistent)
// ============================================================
inline int heuristic(std::uint64_t state)
{
    int field[16];
    for (int i = 0; i < 16; ++i)
        field[i] = (int)((state >> (4 * (15 - i))) & 0xF);

    bool rowConflict[16] = {};
    bool colConflict[16] = {};
    int t = 0;

    for (int s = 0; s < 4; ++s)
        for (int n = 0; n < 4; ++n)
        {
            int h = field[s * 4 + n];
            if (!h) continue;
            h -= 1;
            const int f = h & 3;
            const int l = h >> 2;

            t += std::abs(l - s) + std::abs(f - n);

            if (l == s)
                for (int u = n + 1; u < 4; ++u)
                {
                    int c = field[s * 4 + u];
                    if (!c) continue;
                    c -= 1;
                    if ((c >> 2) == s && c < h)
                    {
                        t += 2;
                        rowConflict[h] = rowConflict[c] = true;
                    }
                }
            if (f == n)
                for (int u = s + 1; u < 4; ++u)
                {
                    int c = field[u * 4 + n];
                    if (!c) continue;
                    c -= 1;
                    if ((c & 3) == n && c < h)
                    {
                        t += 2;
                        colConflict[h] = colConflict[c] = true;
                    }
                }
        }

    if (field[3] != 4 && field[3] != 0)
    {
        if (!rowConflict[2] && field[2] == 3) t += 2;
        if (!colConflict[7] && field[7] == 8) t += 2;
    }
    if (field[0] != 1 && field[0] != 0)
    {
        if (!rowConflict[1] && field[1] == 2) t += 2;
        if (!colConflict[4] && field[4] == 5) t += 2;
    }
    if (field[12] != 13 && field[12] != 0)
    {
        if (!rowConflict[13] && field[13] == 14) t += 2;
        if (!colConflict[8] && field[8] == 9) t += 2;
    }

    return t;
}

// ============================================================
//  solvability
// ============================================================
bool isSolvable(std::uint64_t state)
{
    int seq[15], n = 0, blankRow = 0;
    for (int i = 0; i < 16; ++i)
    {
        int tile = (state >> (4 * (15 - i))) & 0xF;
        if (tile == 0) blankRow = i >> 2;
        else seq[n++] = tile;
    }
    int inv = 0;
    for (int i = 0; i < 15; ++i)
        for (int j = i + 1; j < 15; ++j)
            if (seq[i] > seq[j]) ++inv;
    return (inv + (3 - blankRow)) % 2 == 0;
}

// ============================================================
//  output
// ============================================================
char tileChar(int v)
{
    return v < 10 ? (char)('0' + v) : (char)('A' + v - 10);
}

void printBoard(std::uint64_t state, std::ostream& os)
{
    os << "Hex: 0x" << std::hex << std::setw(16) << std::setfill('0')
        << state << std::dec << std::setfill(' ') << '\n';
    for (int r = 0; r < 4; ++r)
    {
        for (int c = 0; c < 4; ++c)
        {
            int tile = (state >> (4 * (15 - (r * 4 + c)))) & 0xF;
            if (tile == 0) os << "   ";
            else           os << tileChar(tile) << ' ';
        }
        os << '\n';
    }
    os << '\n';
}

// ============================================================
//  Node inside deque; parent = index in the same deque.
// ============================================================
struct Node
{
    std::uint64_t state;
    std::uint32_t parent;
    std::uint8_t  g;
    std::uint8_t  h;
    char          move;
    std::uint8_t  blank;
};

inline void reconstruct(std::uint32_t leafId,
    const std::deque<Node>& pool,
    std::vector<std::uint64_t>& states,
    std::vector<char>& moves)
{
    std::vector<std::uint32_t> ids;
    for (std::uint32_t id = leafId; id != UINT32_MAX; id = pool[id].parent)
        ids.push_back(id);
    std::reverse(ids.begin(), ids.end());

    states.reserve(ids.size());
    moves.reserve(ids.size() ? ids.size() - 1 : 0);
    for (std::size_t k = 0; k < ids.size(); ++k) states.push_back(pool[ids[k]].state);
    for (std::size_t k = 1; k < ids.size(); ++k) moves.push_back(pool[ids[k]].move);
}

// ============================================================
//  BFS (bidirectional)
// ============================================================
int solveBFS(std::uint64_t start,
    std::vector<std::uint64_t>& solutionStates,
    std::vector<char>& solutionMoves,
    std::size_t nodeLimit,
    std::size_t& visitedOut)
{
    solutionStates.clear(); solutionMoves.clear(); visitedOut = 0;
    if (start == GOAL) { solutionStates.push_back(start); return 0; }

    std::deque<Node> fwdPool, bwdPool;
    std::unordered_map<std::uint64_t, std::uint32_t, Hash64> fwdSeen, bwdSeen;
    fwdSeen.reserve(1 << 16);
    bwdSeen.reserve(1 << 16);

    std::vector<std::uint32_t> fwdFrontier, fwdNext;
    std::vector<std::uint32_t> bwdFrontier, bwdNext;

    auto pushFwd = [&](std::uint64_t s, std::uint32_t parent,
        std::uint8_t g, char mv, int blank) -> std::uint32_t
        {
            std::uint32_t id = (std::uint32_t)fwdPool.size();
            fwdPool.push_back({ s, parent, g, 0, mv, (std::uint8_t)blank });
            fwdSeen.emplace(s, id);
            return id;
        };
    auto pushBwd = [&](std::uint64_t s, std::uint32_t parent,
        std::uint8_t g, char mv, int blank) -> std::uint32_t
        {
            std::uint32_t id = (std::uint32_t)bwdPool.size();
            bwdPool.push_back({ s, parent, g, 0, mv, (std::uint8_t)blank });
            bwdSeen.emplace(s, id);
            return id;
        };

    std::uint32_t fwdRoot = pushFwd(start, UINT32_MAX, 0, 0, findBlank(start));
    std::uint32_t bwdRoot = pushBwd(GOAL, UINT32_MAX, 0, 0, findBlank(GOAL));
    fwdFrontier.push_back(fwdRoot);
    bwdFrontier.push_back(bwdRoot);

    int depthF = 0, depthB = 0;
    int bestLen = INT_MAX;
    std::uint32_t meetF = UINT32_MAX, meetB = UINT32_MAX;
    std::size_t   expanded = 0;

    while (!fwdFrontier.empty() && !bwdFrontier.empty())
    {
        if ((expanded & 0xFFF) == 0 && timeIsUp()) { visitedOut = expanded; return 1; }
        if (depthF + depthB >= bestLen) break;

        bool doFwd = fwdFrontier.size() <= bwdFrontier.size();

        if (doFwd)
        {
            fwdNext.clear();
            std::uint8_t newG = (std::uint8_t)(depthF + 1);
            for (std::uint32_t cid : fwdFrontier)
            {
                ++expanded;
                if (expanded > nodeLimit) { visitedOut = expanded; return 2; }

                std::uint64_t cur = fwdPool[cid].state;
                int           blank = fwdPool[cid].blank;
                int           nc = neighborCnt[blank];

                for (int i = 0; i < nc; ++i)
                {
                    int nblank = neighborPos[blank][i];
                    std::uint64_t next = swapped(cur, blank, nblank);
                    if (fwdSeen.find(next) != fwdSeen.end()) continue;

                    std::uint32_t nid = pushFwd(next, cid, newG,
                        neighborMove[blank][i], nblank);
                    fwdNext.push_back(nid);

                    auto itB = bwdSeen.find(next);
                    if (itB != bwdSeen.end())
                    {
                        int cand = newG + bwdPool[itB->second].g;
                        if (cand < bestLen) { bestLen = cand; meetF = nid; meetB = itB->second; }
                    }
                }
            }
            fwdFrontier.swap(fwdNext);
            ++depthF;
        }
        else
        {
            bwdNext.clear();
            std::uint8_t newG = (std::uint8_t)(depthB + 1);
            for (std::uint32_t cid : bwdFrontier)
            {
                ++expanded;
                if (expanded > nodeLimit) { visitedOut = expanded; return 2; }

                std::uint64_t cur = bwdPool[cid].state;
                int           blank = bwdPool[cid].blank;
                int           nc = neighborCnt[blank];

                for (int i = 0; i < nc; ++i)
                {
                    int nblank = neighborPos[blank][i];
                    std::uint64_t next = swapped(cur, blank, nblank);
                    if (bwdSeen.find(next) != bwdSeen.end()) continue;

                    std::uint32_t nid = pushBwd(next, cid, newG,
                        neighborMove[blank][i], nblank);
                    bwdNext.push_back(nid);

                    auto itF = fwdSeen.find(next);
                    if (itF != fwdSeen.end())
                    {
                        int cand = newG + fwdPool[itF->second].g;
                        if (cand < bestLen) { bestLen = cand; meetF = itF->second; meetB = nid; }
                    }
                }
            }
            bwdFrontier.swap(bwdNext);
            ++depthB;
        }
    }

    visitedOut = expanded;
    if (bestLen == INT_MAX) return 2;

    std::vector<std::uint32_t> fpath, bpath;
    for (std::uint32_t id = meetF; id != UINT32_MAX; id = fwdPool[id].parent)
        fpath.push_back(id);
    std::reverse(fpath.begin(), fpath.end());
    for (std::uint32_t id = meetB; id != UINT32_MAX; id = bwdPool[id].parent)
        bpath.push_back(id);

    for (std::uint32_t id : fpath) solutionStates.push_back(fwdPool[id].state);
    for (std::size_t i = 1; i < fpath.size(); ++i)
        solutionMoves.push_back(fwdPool[fpath[i]].move);
    for (std::size_t i = 0; i + 1 < bpath.size(); ++i)
    {
        solutionMoves.push_back(oppositeMove[(int)bwdPool[bpath[i]].move]);
        solutionStates.push_back(bwdPool[bpath[i + 1]].state);
    }
    return 0;
}

// ============================================================
//  transposition table (shared by IDS + IDA*)
// ============================================================
static constexpr std::size_t TT_BITS = 23;
static constexpr std::size_t TT_SIZE = std::size_t(1) << TT_BITS;
static constexpr std::size_t TT_MASK = TT_SIZE - 1;

struct TTEntry
{
    std::uint64_t key;
    std::uint32_t gen;
    std::uint8_t  g;
    std::uint8_t  pad[3];
};
static_assert(sizeof(TTEntry) == 16, "");

static std::vector<TTEntry> g_tt;
static std::uint32_t        g_ttGen = 0;

static void initTT()
{
    g_tt.assign(TT_SIZE, TTEntry{ 0, 0, 255, {0,0,0} });
    g_ttGen = 0;
}

inline std::size_t ttHash(std::uint64_t s)
{
    s ^= s >> 33; s *= 0xff51afd7ed558ccdULL;
    s ^= s >> 33; s *= 0xc4ceb9fe1a85ec53ULL;
    s ^= s >> 33;
    return (std::size_t)s & TT_MASK;
}

// ============================================================
//  IDS — iterative deepening, shared TT (budget-based)
// ============================================================
int idsSearch(std::uint64_t state, int blank, int g, int depthLimit, int prevMove,
    std::vector<char>& path, std::vector<std::uint64_t>& states,
    std::uint64_t& nodeCount)
{
    ++nodeCount;
    if ((nodeCount & 0xFFF) == 0 && timeIsUp()) return -2;
    if (state == GOAL) return -1;

    int budget = depthLimit - g;
    if (budget <= 0) return 0;

    std::size_t k = ttHash(state);
    if (g_tt[k].gen == g_ttGen && g_tt[k].key == state && g_tt[k].g >= budget)
        return 0;

    int nc = neighborCnt[blank];
    for (int i = 0; i < nc; ++i)
    {
        char mv = neighborMove[blank][i];
        int dir = mvToDir[(int)mv];
        if (prevMove != -1 && dir == (prevMove ^ 1)) continue;

        int nblank = neighborPos[blank][i];
        std::uint64_t next = swapped(state, blank, nblank);
        path.push_back(mv);
        states.push_back(next);
        int t = idsSearch(next, nblank, g + 1, depthLimit, dir, path, states, nodeCount);
        if (t == -1) return -1;
        if (t == -2) { states.pop_back(); path.pop_back(); return -2; }
        states.pop_back();
        path.pop_back();
    }

    if (g_tt[k].gen != g_ttGen || g_tt[k].key != state || g_tt[k].g < budget)
    {
        g_tt[k].gen = g_ttGen;
        g_tt[k].key = state;
        g_tt[k].g = (std::uint8_t)budget;
    }
    return 0;
}

int solveIDS(std::uint64_t start,
    std::vector<std::uint64_t>& solutionStates,
    std::vector<char>& solutionMoves,
    int maxDepth,
    std::size_t& expandedOut)
{
    solutionStates.clear(); solutionMoves.clear(); expandedOut = 0;
    if (start == GOAL) { solutionStates.push_back(start); return 0; }

    std::vector<char> path;
    std::vector<std::uint64_t> states;
    states.reserve(128); path.reserve(128);
    states.push_back(start);
    int blank = findBlank(start);
    std::uint64_t nodes = 0;

    ++g_ttGen;
    for (int depth = 1; depth <= maxDepth; ++depth)
    {
        int t = idsSearch(start, blank, 0, depth, -1, path, states, nodes);
        if (t == -1)
        {
            solutionMoves = path;
            solutionStates = states;
            expandedOut = (std::size_t)nodes;
            return 0;
        }
        if (t == -2) { expandedOut = (std::size_t)nodes; return 1; }
    }
    expandedOut = (std::size_t)nodes;
    return 2;
}

// ============================================================
//  A*  —  reopen-based, optimal for admissible-but-inconsistent h
// ============================================================
int solveAStar(std::uint64_t start,
    std::vector<std::uint64_t>& solutionStates,
    std::vector<char>& solutionMoves,
    std::size_t& expandedOut)
{
    solutionStates.clear(); solutionMoves.clear(); expandedOut = 0;
    if (start == GOAL) { solutionStates.push_back(start); return 0; }

    struct PQItem
    {
        int f, h;
        std::uint32_t id;
        bool operator>(const PQItem& o) const
        {
            if (f != o.f) return f > o.f;
            if (h != o.h) return h > o.h;   // among equal f: smaller h (deeper) first
            return id > o.id;               // deterministic final tie-break
        }
    };

    std::deque<Node> pool;

    // best g seen so far per state (dedup + reopen bookkeeping)
    std::unordered_map<std::uint64_t, std::uint8_t, Hash64> bestG;
    bestG.reserve(1 << 22);

    std::vector<PQItem> heapBuf;
    heapBuf.reserve(1 << 22);
    std::priority_queue<PQItem, std::vector<PQItem>, std::greater<PQItem>>
        pq(std::greater<PQItem>(), std::move(heapBuf));

    // root
    {
        int h0 = heuristic(start);
        pool.push_back({ start, UINT32_MAX, 0, (std::uint8_t)h0, 0,
                         (std::uint8_t)findBlank(start) });
        bestG.emplace(start, 0);
        pq.push({ h0, h0, 0 });
    }

    std::size_t expanded = 0;
    while (!pq.empty())
    {
        if ((expanded & 0xFFF) == 0 && timeIsUp()) { expandedOut = expanded; return 1; }

        PQItem top = pq.top(); pq.pop();
        std::uint32_t cid = top.id;
        std::uint64_t s = pool[cid].state;
        int           gc = pool[cid].g;

        // stale?  a shorter path to `s` was found after this node was queued
        auto itG = bestG.find(s);
        if (itG != bestG.end() && itG->second < gc) continue;

        ++expanded;
        if (s == GOAL)
        {
            reconstruct(cid, pool, solutionStates, solutionMoves);
            expandedOut = expanded;
            return 0;
        }

        int blank = pool[cid].blank;
        int nc = neighborCnt[blank];
        for (int i = 0; i < nc; ++i)
        {
            int nblank = neighborPos[blank][i];
            std::uint64_t ns = swapped(s, blank, nblank);
            int ng = gc + 1;

            auto it2 = bestG.find(ns);
            if (it2 != bestG.end() && it2->second <= ng) continue;   // no improvement

            bestG[ns] = (std::uint8_t)ng;
            int nh = heuristic(ns);
            std::uint32_t nid = (std::uint32_t)pool.size();
            pool.push_back({ ns, cid, (std::uint8_t)ng, (std::uint8_t)nh,
                             neighborMove[blank][i], (std::uint8_t)nblank });
            pq.push({ ng + nh, nh, nid });
        }
    }
    expandedOut = expanded;
    return 2;
}

// ============================================================
//  IDA*  — recursive, TT, move ordering
// ============================================================
int idaSearch(std::uint64_t state, int blank, int g, int bound, int prevMove, int h,
    std::vector<char>& path, std::vector<std::uint64_t>& states,
    std::uint64_t& nodeCount)
{
    ++nodeCount;
    if ((nodeCount & 0xFFF) == 0 && timeIsUp()) return -2;
    if (state == GOAL) return -1;

    int f = g + h;
    if (f > bound) return f;

    std::size_t k = ttHash(state);
    if (g_tt[k].gen == g_ttGen && g_tt[k].key == state && g_tt[k].g <= g)
        return INT_MAX;

    struct Ch { int h; int i; };
    Ch ch[4];
    int m = 0;
    int nc = neighborCnt[blank];
    for (int i = 0; i < nc; ++i)
    {
        char mv = neighborMove[blank][i];
        int dir = mvToDir[(int)mv];
        if (prevMove != -1 && dir == (prevMove ^ 1)) continue;
        int nblank = neighborPos[blank][i];
        std::uint64_t next = swapped(state, blank, nblank);
        ch[m].h = heuristic(next);
        ch[m].i = i;
        ++m;
    }
    std::sort(ch, ch + m, [](const Ch& a, const Ch& b) { return a.h < b.h; });

    int min = INT_MAX;
    for (int j = 0; j < m; ++j)
    {
        int i = ch[j].i;
        int nh = ch[j].h;
        char mv = neighborMove[blank][i];
        int dir = mvToDir[(int)mv];
        int nblank = neighborPos[blank][i];
        std::uint64_t next = swapped(state, blank, nblank);
        path.push_back(mv);
        states.push_back(next);
        int t = idaSearch(next, nblank, g + 1, bound, dir, nh,
            path, states, nodeCount);
        if (t == -1) return -1;
        if (t == -2) { states.pop_back(); path.pop_back(); return -2; }
        if (t < min) min = t;
        states.pop_back();
        path.pop_back();
    }

    if (g_tt[k].gen != g_ttGen || g_tt[k].key != state || g_tt[k].g > g)
    {
        g_tt[k].gen = g_ttGen;
        g_tt[k].key = state;
        g_tt[k].g = (std::uint8_t)g;
    }
    return min;
}

int solveIDAStar(std::uint64_t start,
    std::vector<std::uint64_t>& solutionStates,
    std::vector<char>& solutionMoves,
    std::size_t& expandedOut)
{
    solutionStates.clear(); solutionMoves.clear(); expandedOut = 0;
    if (start == GOAL) { solutionStates.push_back(start); return 0; }

    int bound = heuristic(start);
    std::vector<char> path;
    std::vector<std::uint64_t> states;
    states.reserve(128); path.reserve(128);
    states.push_back(start);
    int blank = findBlank(start);
    std::uint64_t nodes = 0;

    while (true)
    {
        ++g_ttGen;
        int t = idaSearch(start, blank, 0, bound, -1, bound,
            path, states, nodes);
        if (t == -1)
        {
            solutionMoves = path;
            solutionStates = states;
            expandedOut = (std::size_t)nodes;
            return 0;
        }
        if (t == -2) { expandedOut = (std::size_t)nodes; return 1; }
        if (t == INT_MAX) break;
        bound = t;
    }
    expandedOut = (std::size_t)nodes;
    return 2;
}

// ============================================================
//  main
// ============================================================
struct AlgoResult
{
    bool solved = false;
    bool timedOut = false;
    bool skipped = false;
    int length = -1;
    std::size_t nodes = 0;
    double ms = 0.0;
    std::string note;
};

int main(int argc, char** argv)
{
    initTables();
    initTT();

    struct TestCase { const char* hex; int expectedLen; };
    std::vector<TestCase> tests = {
        {"123456789AFB0EDC", -1},
        {"F2345678A0BE91CD", -1},
        {"123456789ABCDEF0",  0},
        {"1234067859ACDEBF",  5},
        {"5134207896ACDEBF",  8},
        {"16245A3709C8DEBF", 10},
        {"1723068459ACDEBF", 13},
        {"0723168459ACDEBF", 14},
        {"7023168459ACDEBF", 15},
        {"7203168459ACDEBF", 16},
        {"7283160459ACDEBF", 17},
        {"7283106459ACDEBF", 18},
        {"12345678A0BE9FCD", 19},
        {"51247308A6BE9FCD", 27},
        {"F2345678A0BE91DC", 33},
        {"75123804A6BE9FCD", 35},
        {"75AB2C416D389F0E", 45},
        {"04582E1DF79BCA36", 48},
        {"FE169B4C0A73D852", 52},
        {"D79F2E8A45106C3B", 55},
        {"DBE87A2C91F65034", 58},
        {"BAC0F478E19623D5", 61}
    };

    double timeoutSec = 10.0;
    if (argc > 1)
    {
        try { double v = std::stod(argv[1]); if (v > 0.0) timeoutSec = v; }
        catch (...) {}
    }

    const std::size_t BFS_NODE_LIMIT = 200000000;
    const int         LIGHT_MAX_LEN = 19;
    const int         IDS_MAX_DEPTH = 80;

    std::ofstream out("solution.txt");
    if (!out) { std::cerr << "Cannot open solution.txt\n"; return 1; }

    out << "Heuristic: Manh+LC+CornerConflict (JS-style)\n";
    out << "BFS: bidirectional, Hash64, node limit = " << BFS_NODE_LIMIT
        << ", run only if expected length <= " << LIGHT_MAX_LEN << "\n";
    out << "IDS: depth-limited DFS iterated, shared TT, max depth = "
        << IDS_MAX_DEPTH
        << ", run only if expected length <= " << LIGHT_MAX_LEN << "\n";
    out << "A*: PQ (tie: smaller h first), closed map bestG (reopen), Hash64\n";
    out << "IDA*: recursive, TT " << TT_BITS << " bits, move ordering\n\n";

    struct Row
    {
        std::string pos; int expected;
        AlgoResult bfs, ids, astar, ida;
    };
    std::vector<Row> rows;
    rows.reserve(tests.size());

    auto runWithTimeout = [&](int algo, std::uint64_t start,
        std::vector<std::uint64_t>& st,
        std::vector<char>& mv,
        std::size_t& nodesOut) -> AlgoResult
        {
            AlgoResult r;
            g_timeoutEnabled = true;
            g_deadline = std::chrono::steady_clock::now() +
                std::chrono::milliseconds((long long)(timeoutSec * 1000.0));

            auto t0 = std::chrono::high_resolution_clock::now();
            int rc = 2;
            std::size_t expanded = 0;
            if (algo == 0) rc = solveBFS(start, st, mv, BFS_NODE_LIMIT, nodesOut);
            else if (algo == 1) rc = solveIDS(start, st, mv, IDS_MAX_DEPTH, expanded);
            else if (algo == 2) rc = solveAStar(start, st, mv, expanded);
            else                rc = solveIDAStar(start, st, mv, expanded);
            auto t1 = std::chrono::high_resolution_clock::now();

            g_timeoutEnabled = false;
            r.ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
            r.nodes = (algo == 0) ? nodesOut : expanded;

            if (rc == 0) { r.solved = true; r.length = (int)mv.size(); }
            else if (rc == 1) { r.timedOut = true; r.skipped = true; r.note = "TIMEOUT"; }
            else
            {
                r.skipped = true;
                r.note = (algo == 0) ? "node-limit" : "exhausted";
            }
            return r;
        };

    auto cellFmt = [](const AlgoResult& r) -> std::string
        {
            if (r.note == "n/a")     return "n/a";
            if (r.note == "...")     return "...";
            if (r.note == "skipped") return "skipped";
            std::ostringstream oss;
            if (r.solved)
            {
                oss << r.length << " (" << r.nodes << "n, "
                    << std::fixed << std::setprecision(1) << r.ms << "ms)";
                return oss.str();
            }
            if (r.timedOut) return "TIMEOUT";
            if (!r.note.empty()) return r.note;
            return "-";
        };

    auto rowLine = [&](const Row& row) -> std::string
        {
            std::string expStr = (row.expected < 0) ? "uns." : std::to_string(row.expected);
            std::ostringstream oss;
            oss << std::left
                << std::setw(18) << row.pos
                << std::setw(6) << expStr
                << std::setw(24) << cellFmt(row.bfs)
                << std::setw(24) << cellFmt(row.ids)
                << std::setw(24) << cellFmt(row.astar)
                << std::setw(24) << cellFmt(row.ida);
            return oss.str();
        };

    auto headerLine = []() -> std::string
        {
            std::ostringstream oss;
            oss << std::left
                << std::setw(18) << "Position"
                << std::setw(6) << "Exp."
                << std::setw(24) << "BFS(bidi)"
                << std::setw(24) << "IDS"
                << std::setw(24) << "A*"
                << std::setw(24) << "IDA*";
            return oss.str();
        };

    std::cout << std::string(120, '=') << "\n";
    std::cout << "Solving (timeout = " << timeoutSec << " s per call)\n";
    std::cout << std::string(120, '=') << "\n";
    std::cout << headerLine() << "\n";
    std::cout << std::string(120, '-') << "\n";

    for (const TestCase& tc : tests)
    {
        std::uint64_t start = std::stoull(std::string(tc.hex), nullptr, 16);

        Row row;
        row.pos = tc.hex;
        row.expected = tc.expectedLen;

        bool solvable = isSolvable(start);
        row.bfs.note = row.ids.note = row.astar.note = row.ida.note =
            solvable ? "..." : "n/a";

        out << "================================================\n";
        out << "Position: " << tc.hex << "\n";
        out << "Expected length: ";
        if (tc.expectedLen < 0) out << "unsolvable\n";
        else                    out << tc.expectedLen << "\n\n";
        printBoard(start, out);

        if (!solvable)
        {
            out << "Unsolvable.\n\n";
            rows.push_back(row);
            std::cout << rowLine(row) << "\n";
            continue;
        }

        bool runLight = (tc.expectedLen >= 0 && tc.expectedLen <= LIGHT_MAX_LEN);

        // ---- BFS ----
        if (runLight)
        {
            std::vector<std::uint64_t> st; std::vector<char> mv;
            std::size_t visited = 0;
            row.bfs = runWithTimeout(0, start, st, mv, visited);
            out << "BFS: " << cellFmt(row.bfs) << "\n";
        }
        else
        {
            row.bfs.skipped = true;
            row.bfs.note = "skipped";
            out << "BFS: skipped (expected length > " << LIGHT_MAX_LEN << ")\n";
        }

        // ---- IDS ----
        if (runLight)
        {
            std::vector<std::uint64_t> st; std::vector<char> mv;
            std::size_t dummy = 0;
            row.ids = runWithTimeout(1, start, st, mv, dummy);
            out << "IDS: " << cellFmt(row.ids) << "\n";
        }
        else
        {
            row.ids.skipped = true;
            row.ids.note = "skipped";
            out << "IDS: skipped (expected length > " << LIGHT_MAX_LEN << ")\n";
        }

        // ---- A* ----
        {
            std::vector<std::uint64_t> st; std::vector<char> mv;
            std::size_t dummy = 0;
            row.astar = runWithTimeout(2, start, st, mv, dummy);
            out << "A*: " << cellFmt(row.astar) << "\n";
        }

        // ---- IDA* ----
        {
            std::vector<std::uint64_t> st; std::vector<char> mv;
            std::size_t dummy = 0;
            row.ida = runWithTimeout(3, start, st, mv, dummy);
            out << "IDA*: " << cellFmt(row.ida) << "\n\n";
        }

        rows.push_back(row);
        std::cout << rowLine(row) << "\n";
    }

    std::cout << std::string(120, '-') << "\n";

    out << std::string(120, '=') << "\n";
    out << "Summary\n";
    out << std::string(120, '=') << "\n";
    out << headerLine() << "\n";
    out << std::string(120, '-') << "\n";
    for (const Row& row : rows) out << rowLine(row) << "\n";
    out << std::string(120, '-') << "\n";
    out.close();

    std::cout << "\nResults written to solution.txt\n";
    return 0;
}