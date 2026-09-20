#include <iostream>
#include <fstream>
#include <vector>
#include <queue>
#include <algorithm>
#include <functional>
#include <climits>
#include <cstdint>
#include <iomanip>
#include <string>
#include <chrono>
#include <sstream>
#include <cstdlib>

const std::uint64_t GOAL = 0x123456789ABCDEF0ULL;

// ---------- timeout ----------
std::chrono::steady_clock::time_point g_deadline;
bool g_timeoutEnabled = false;
bool g_timeoutHit = false;

inline bool timeIsUp()
{
    if (!g_timeoutEnabled) return false;
    if (std::chrono::steady_clock::now() >= g_deadline)
    {
        g_timeoutHit = true;
        return true;
    }
    return false;
}

// 1=Hamming, 2=Manh+2*LC, 3=Manh+2*LC+CornerConflict (classic),
// 4=CornerConflict only (classic), 5=JS-style (Manh+LC+corner-from-script)
int g_heuristicMode = 5;

// ---------- precomputed tables ----------
static int manhTable[16][16];
static int tgtRow[16];
static int tgtCol[16];
static const int cornerPos[4] = { 0, 3, 12, 15 };
static const int cornerTile[4] = { 1, 4, 13, 16 };
static int cornerRevTile[17];

static int  neighborPos[16][4];
static char neighborMove[16][4];
static int  neighborCnt[16];

static char oppositeMove[128];

static void initTables()
{
    for (int pos = 0; pos < 16; ++pos)
    {
        int r = pos >> 2, c = pos & 3;
        manhTable[pos][0] = 0;
        for (int tile = 1; tile < 16; ++tile)
        {
            int target = tile - 1;
            manhTable[pos][tile] =
                std::abs(r - (target >> 2)) + std::abs(c - (target & 3));
        }
    }
    for (int t = 0; t < 15; ++t) { tgtRow[t] = t >> 2; tgtCol[t] = t & 3; }
    for (int i = 0; i < 17; ++i) cornerRevTile[i] = -1;
    for (int i = 0; i < 4; ++i) cornerRevTile[cornerTile[i]] = i;

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

    for (int i = 0; i < 128; ++i) oppositeMove[i] = 0;
    oppositeMove[(int)'U'] = 'D';
    oppositeMove[(int)'D'] = 'U';
    oppositeMove[(int)'L'] = 'R';
    oppositeMove[(int)'R'] = 'L';
}

// ---------- 4-bit tile access ----------
inline int getTile(std::uint64_t state, int pos)
{
    return (state >> (4 * (15 - pos))) & 0xF;
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

// ---------- heuristics ----------
inline int manhattan(std::uint64_t state)
{
    int sum = 0;
    for (int i = 15; i >= 0; --i) { sum += manhTable[i][state & 0xF]; state >>= 4; }
    return sum;
}

inline int hamming(std::uint64_t state)
{
    int cnt = 0;
    for (int i = 15; i >= 0; --i)
    {
        int tile = state & 0xF; state >>= 4;
        if (tile != 0 && tile - 1 != i) ++cnt;
    }
    return cnt;
}

inline int linearConflict(std::uint64_t state)
{
    int t[16];
    for (int i = 15; i >= 0; --i) { t[i] = state & 0xF; state >>= 4; }
    int lc = 0;
    for (int r = 0; r < 4; ++r)
    {
        int base = r << 2;
        for (int c1 = 0; c1 < 4; ++c1)
        {
            int a = t[base + c1];
            if (!a || tgtRow[a - 1] != r) continue;
            int ac = tgtCol[a - 1];
            for (int c2 = c1 + 1; c2 < 4; ++c2)
            {
                int b = t[base + c2];
                if (!b || tgtRow[b - 1] != r) continue;
                if (ac > tgtCol[b - 1]) lc += 2;
            }
        }
    }
    for (int c = 0; c < 4; ++c)
    {
        for (int r1 = 0; r1 < 4; ++r1)
        {
            int a = t[(r1 << 2) + c];
            if (!a || tgtCol[a - 1] != c) continue;
            int ar = tgtRow[a - 1];
            for (int r2 = r1 + 1; r2 < 4; ++r2)
            {
                int b = t[(r2 << 2) + c];
                if (!b || tgtCol[b - 1] != c) continue;
                if (ar > tgtRow[b - 1]) lc += 2;
            }
        }
    }
    return lc;
}

inline int cornerConflict(std::uint64_t state)
{
    int cc = 0;
    for (int i = 0; i < 4; ++i)
    {
        int t = (state >> (4 * (15 - cornerPos[i]))) & 0xF;
        if (t == 0 || t == cornerTile[i]) continue;
        int ti = cornerRevTile[t];
        if (ti <= i) continue;
        if (((state >> (4 * (15 - cornerPos[ti]))) & 0xF) == cornerTile[i]) cc += 2;
    }
    return cc;
}

// ---------- heuristic ported from the JS script ----------
// Equivalent to JS "heuristicCornerConflict":
//   Manhattan + linear conflicts + JS-specific corner checks.
inline int heuristicFromScript(std::uint64_t state)
{
    int field[16];
    for (int i = 0; i < 16; ++i)
        field[i] = static_cast<int>((state >> (4 * (15 - i))) & 0xF);

    bool rowConflict[16] = {};
    bool colConflict[16] = {};
    int t = 0;

    for (int s = 0; s < 4; ++s)             // row
    {
        for (int n = 0; n < 4; ++n)         // col
        {
            int h = field[s * 4 + n];
            if (!h) continue;
            h -= 1;                         // 0-based tile index
            const int f = h & 3;            // target col
            const int l = h >> 2;           // target row

            t += std::abs(l - s) + std::abs(f - n);

            if (l == s)                     // tile in its target row
            {
                for (int u = n + 1; u < 4; ++u)
                {
                    int c = field[s * 4 + u];
                    if (!c) continue;
                    c -= 1;
                    if ((c >> 2) == s && c < h)
                    {
                        t += 2;
                        rowConflict[h] = true;
                        rowConflict[c] = true;
                    }
                }
            }
            if (f == n)                     // tile in its target col
            {
                for (int u = s + 1; u < 4; ++u)
                {
                    int c = field[u * 4 + n];
                    if (!c) continue;
                    c -= 1;
                    if ((c & 3) == n && c < h)
                    {
                        t += 2;
                        colConflict[h] = true;
                        colConflict[c] = true;
                    }
                }
            }
        }
    }

    // --- corner-specific checks (JS-specific) ---
    // corner 3 (top-right; goal tile = 4)
    if (field[3] != 4 && field[3] != 0)
    {
        if (!rowConflict[2] && field[2] == 3) t += 2;
        if (!colConflict[7] && field[7] == 8) t += 2;
    }
    // corner 0 (top-left; goal tile = 1)
    if (field[0] != 1 && field[0] != 0)
    {
        if (!rowConflict[1] && field[1] == 2) t += 2;
        if (!colConflict[4] && field[4] == 5) t += 2;
    }
    // corner 12 (bottom-left; goal tile = 13)
    if (field[12] != 13 && field[12] != 0)
    {
        if (!rowConflict[13] && field[13] == 14) t += 2;
        if (!colConflict[8] && field[8] == 9) t += 2;
    }

    return t;
}

inline int heuristic(std::uint64_t state)
{
    if (g_heuristicMode == 1) return hamming(state);
    if (g_heuristicMode == 4) return cornerConflict(state);
    if (g_heuristicMode == 5) return heuristicFromScript(state);
    int m = manhattan(state);
    if (g_heuristicMode >= 2) m += linearConflict(state);
    if (g_heuristicMode >= 3) m += cornerConflict(state);
    return m;
}

// ---------- solvability ----------
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

// ---------- output ----------
char tileChar(int v)
{
    return v < 10 ? static_cast<char>('0' + v) : static_cast<char>('A' + v - 10);
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

// ---------- fast open-addressing hash set ----------
struct FastHashSet
{
    std::vector<std::uint64_t> keys;
    std::vector<std::uint32_t> vals;
    std::size_t mask = 0, count = 0;

    void init(std::size_t cap)
    {
        std::size_t sz = 16;
        while (sz < cap) sz <<= 1;
        keys.assign(sz, 0);
        vals.assign(sz, UINT32_MAX);
        mask = sz - 1;
        count = 0;
    }
    static inline std::size_t hashKey(std::uint64_t k)
    {
        k ^= k >> 33; k *= 0xff51afd7ed558ccdULL;
        k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL;
        k ^= k >> 33;
        return static_cast<std::size_t>(k);
    }
    inline std::uint32_t* find(std::uint64_t key)
    {
        std::size_t h = hashKey(key) & mask;
        for (;;)
        {
            if (vals[h] == UINT32_MAX) return nullptr;
            if (keys[h] == key)        return &vals[h];
            h = (h + 1) & mask;
        }
    }
    inline void insert(std::uint64_t key, std::uint32_t val)
    {
        if ((count + 1) * 4 >= (mask + 1) * 3) grow();
        std::size_t h = hashKey(key) & mask;
        while (vals[h] != UINT32_MAX)
        {
            if (keys[h] == key) { vals[h] = val; return; }
            h = (h + 1) & mask;
        }
        keys[h] = key; vals[h] = val; ++count;
    }
    void grow()
    {
        std::size_t newSize = (mask + 1) << 1;
        std::vector<std::uint64_t> nk(newSize, 0);
        std::vector<std::uint32_t> nv(newSize, UINT32_MAX);
        std::size_t nm = newSize - 1;
        for (std::size_t i = 0; i <= mask; ++i)
        {
            if (vals[i] == UINT32_MAX) continue;
            std::size_t h = hashKey(keys[i]) & nm;
            while (nv[h] != UINT32_MAX) h = (h + 1) & nm;
            nk[h] = keys[i]; nv[h] = vals[i];
        }
        keys.swap(nk); vals.swap(nv); mask = nm;
    }
};

// ============================================================
//  Transposition table for IDA* (generation-based)
// ============================================================
static constexpr std::size_t TT_BITS = 22;
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
    return static_cast<std::size_t>(s) & TT_MASK;
}

// ---------- node pool ----------
struct NodeData
{
    std::uint64_t state;
    std::uint32_t parent;
    std::uint8_t  g;
    std::uint8_t  h;
    char          move;
    std::uint8_t  blank;
};
static_assert(sizeof(NodeData) == 16, "NodeData must be 16 bytes");

inline void reconstruct(std::uint32_t leafId,
    const std::vector<NodeData>& pool,
    std::vector<std::uint64_t>& states,
    std::vector<char>& moves)
{
    std::vector<std::uint32_t> ids;
    std::uint32_t id = leafId;
    while (id != UINT32_MAX) { ids.push_back(id); id = pool[id].parent; }
    std::reverse(ids.begin(), ids.end());
    states.reserve(ids.size());
    moves.reserve(ids.size() ? ids.size() - 1 : 0);
    for (std::size_t k = 0; k < ids.size(); ++k) states.push_back(pool[ids[k]].state);
    for (std::size_t k = 1; k < ids.size(); ++k) moves.push_back(pool[ids[k]].move);
}

// ============================================================
//  BIDIRECTIONAL BFS
// ============================================================
int solveBFS(std::uint64_t start,
    std::vector<std::uint64_t>& solutionStates,
    std::vector<char>& solutionMoves,
    std::size_t nodeLimit,
    std::size_t& visitedOut)
{
    solutionStates.clear();
    solutionMoves.clear();
    visitedOut = 0;
    if (start == GOAL) { solutionStates.push_back(start); return 0; }

    std::vector<NodeData> fwdPool, bwdPool;
    fwdPool.reserve(1 << 12);
    bwdPool.reserve(1 << 12);

    FastHashSet fwdSeen, bwdSeen;
    fwdSeen.init(1024);
    bwdSeen.init(1024);

    std::vector<std::uint32_t> fwdFrontier, fwdNext;
    std::vector<std::uint32_t> bwdFrontier, bwdNext;
    fwdFrontier.reserve(256); fwdNext.reserve(256);
    bwdFrontier.reserve(256); bwdNext.reserve(256);

    auto pushFwd = [&](std::uint64_t s, std::uint32_t parent,
        std::uint8_t g, char mv, int blank) -> std::uint32_t
        {
            std::uint32_t id = static_cast<std::uint32_t>(fwdPool.size());
            fwdPool.push_back({ s, parent, g, 0, mv, static_cast<std::uint8_t>(blank) });
            fwdSeen.insert(s, id);
            return id;
        };
    auto pushBwd = [&](std::uint64_t s, std::uint32_t parent,
        std::uint8_t g, char mv, int blank) -> std::uint32_t
        {
            std::uint32_t id = static_cast<std::uint32_t>(bwdPool.size());
            bwdPool.push_back({ s, parent, g, 0, mv, static_cast<std::uint8_t>(blank) });
            bwdSeen.insert(s, id);
            return id;
        };

    std::uint32_t fwdRoot = pushFwd(start, UINT32_MAX, 0, 0, findBlank(start));
    std::uint32_t bwdRoot = pushBwd(GOAL, UINT32_MAX, 0, 0, findBlank(GOAL));
    fwdFrontier.push_back(fwdRoot);
    bwdFrontier.push_back(bwdRoot);

    int  depthF = 0, depthB = 0;
    int  bestLen = INT_MAX;
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
            std::uint8_t newG = static_cast<std::uint8_t>(depthF + 1);
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
                    if (fwdSeen.find(next)) continue;
                    std::uint32_t nid = pushFwd(next, cid, newG,
                        neighborMove[blank][i], nblank);
                    fwdNext.push_back(nid);

                    std::uint32_t* slot = bwdSeen.find(next);
                    if (slot)
                    {
                        int cand = newG + bwdPool[*slot].g;
                        if (cand < bestLen)
                        {
                            bestLen = cand; meetF = nid; meetB = *slot;
                        }
                    }
                }
            }
            fwdFrontier.swap(fwdNext);
            ++depthF;
        }
        else
        {
            bwdNext.clear();
            std::uint8_t newG = static_cast<std::uint8_t>(depthB + 1);
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
                    if (bwdSeen.find(next)) continue;
                    std::uint32_t nid = pushBwd(next, cid, newG,
                        neighborMove[blank][i], nblank);
                    bwdNext.push_back(nid);

                    std::uint32_t* slot = fwdSeen.find(next);
                    if (slot)
                    {
                        int cand = newG + fwdPool[*slot].g;
                        if (cand < bestLen)
                        {
                            bestLen = cand; meetF = *slot; meetB = nid;
                        }
                    }
                }
            }
            bwdFrontier.swap(bwdNext);
            ++depthB;
        }
    }

    visitedOut = expanded;
    if (bestLen == INT_MAX) return 2;

    // ---- reconstruct ----
    std::vector<std::uint32_t> fpath;
    for (std::uint32_t id = meetF; id != UINT32_MAX; id = fwdPool[id].parent)
        fpath.push_back(id);
    std::reverse(fpath.begin(), fpath.end());

    std::vector<std::uint32_t> bpath;
    for (std::uint32_t id = meetB; id != UINT32_MAX; id = bwdPool[id].parent)
        bpath.push_back(id);

    solutionStates.reserve(bestLen + 1);
    solutionMoves.reserve(bestLen);

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
//  A*
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
        int f; int h; std::uint32_t id;
        bool operator>(const PQItem& o) const
        {
            if (f != o.f) return f > o.f;
            return h < o.h;
        }
    };

    std::vector<NodeData> pool;
    pool.reserve(1 << 22);

    FastHashSet seen;
    seen.init(4096);

    std::vector<PQItem> heapBuf;
    heapBuf.reserve(1 << 22);
    std::priority_queue<PQItem, std::vector<PQItem>, std::greater<PQItem>>
        pq(std::greater<PQItem>(), std::move(heapBuf));

    auto push = [&](std::uint64_t s, std::uint32_t parent,
        std::uint8_t g, std::uint8_t h, char mv, int blank) -> std::uint32_t
        {
            std::uint32_t id = static_cast<std::uint32_t>(pool.size());
            pool.push_back({ s, parent, g, h, mv, static_cast<std::uint8_t>(blank) });
            seen.insert(s, id);
            return id;
        };

    int h0 = heuristic(start);
    std::uint32_t rootId = push(start, UINT32_MAX, 0,
        static_cast<std::uint8_t>(h0), 0, findBlank(start));
    pq.push({ h0, h0, rootId });

    std::size_t expanded = 0;
    while (!pq.empty())
    {
        if ((expanded & 0xFFF) == 0 && timeIsUp()) { expandedOut = expanded; return 1; }

        PQItem top = pq.top(); pq.pop();
        std::uint32_t cid = top.id;
        int gc = pool[cid].g, hc = pool[cid].h;
        if (gc + hc != top.f) continue;

        ++expanded;
        std::uint64_t curState = pool[cid].state;
        if (curState == GOAL)
        {
            reconstruct(cid, pool, solutionStates, solutionMoves);
            expandedOut = expanded;
            return 0;
        }

        int blank = pool[cid].blank;
        int nc = neighborCnt[blank];
        for (int i = 0; i < nc; ++i)
        {
            int  nblank = neighborPos[blank][i];
            char mv = neighborMove[blank][i];
            std::uint64_t nextState = swapped(curState, blank, nblank);
            int ng = gc + 1;

            std::uint32_t* slot = seen.find(nextState);
            if (!slot)
            {
                int nh = heuristic(nextState);
                std::uint32_t nid = push(nextState, cid,
                    static_cast<std::uint8_t>(ng),
                    static_cast<std::uint8_t>(nh), mv, nblank);
                pq.push({ ng + nh, nh, nid });
            }
            else
            {
                std::uint32_t nid = *slot;
                if (ng < static_cast<int>(pool[nid].g))
                {
                    pool[nid].g = static_cast<std::uint8_t>(ng);
                    pool[nid].parent = cid;
                    pool[nid].move = mv;
                    int nh = pool[nid].h;
                    pq.push({ ng + nh, nh, nid });
                }
            }
        }
    }
    expandedOut = expanded;
    return 2;
}

// ============================================================
//  IDA*  with transposition table
// ============================================================
int idaSearch(std::uint64_t state, int blank, int g, int bound, int prevMove,
    std::vector<char>& path, std::vector<std::uint64_t>& states,
    std::uint64_t& nodeCount)
{
    ++nodeCount;
    if (timeIsUp()) return -2;
    if (state == GOAL) return -1;

    // -------- TT lookup --------
    std::size_t k = ttHash(state);
    if (g_tt[k].gen == g_ttGen && g_tt[k].key == state && g_tt[k].g <= g)
        return INT_MAX;

    int h = heuristic(state);
    int f = g + h;
    if (f > bound) return f;

    int min = INT_MAX;
    int nc = neighborCnt[blank];
    for (int i = 0; i < nc; ++i)
    {
        char mv = neighborMove[blank][i];
        int dir;
        switch (mv)
        {
        case 'U': dir = 0; break; case 'D': dir = 1; break;
        case 'L': dir = 2; break; default: dir = 3;
        }
        if (prevMove != -1 && dir == (prevMove ^ 1)) continue;

        int nblank = neighborPos[blank][i];
        std::uint64_t next = swapped(state, blank, nblank);
        path.push_back(mv);
        states.push_back(next);
        int t = idaSearch(next, nblank, g + 1, bound, dir, path, states, nodeCount);
        if (t == -1) return -1;
        if (t == -2) { states.pop_back(); path.pop_back(); return -2; }
        if (t < min) min = t;
        states.pop_back();
        path.pop_back();
    }

    // -------- TT store --------
    if (g_tt[k].gen != g_ttGen || g_tt[k].key != state || g_tt[k].g > g)
    {
        g_tt[k].gen = g_ttGen;
        g_tt[k].key = state;
        g_tt[k].g = static_cast<std::uint8_t>(g);
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
    states.reserve(128);
    path.reserve(128);
    states.push_back(start);
    int blank = findBlank(start);
    std::uint64_t nodes = 0;

    while (true)
    {
        ++g_ttGen;
        int t = idaSearch(start, blank, 0, bound, -1, path, states, nodes);
        if (t == -1)
        {
            solutionMoves = path;
            solutionStates = states;
            expandedOut = static_cast<std::size_t>(nodes);
            return 0;
        }
        if (t == -2) { expandedOut = static_cast<std::size_t>(nodes); return 1; }
        if (t == INT_MAX) break;
        bound = t;
    }
    expandedOut = static_cast<std::size_t>(nodes);
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
    auto tInitStart = std::chrono::high_resolution_clock::now();
    initTables();
    initTT();
    auto tInitEnd = std::chrono::high_resolution_clock::now();
    std::cerr << "Init done in "
        << std::chrono::duration<double>(tInitEnd - tInitStart).count()
        << " s\n";

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

    const char* hName =
        (g_heuristicMode == 1) ? "Hamming" :
        (g_heuristicMode == 2) ? "Manhattan+2*LC" :
        (g_heuristicMode == 3) ? "Manhattan+2*LC+CornerConflict" :
        (g_heuristicMode == 4) ? "CornerConflict only" :
        (g_heuristicMode == 5) ? "JS-style (Manh+LC+CornerConflict)" :
        "Manhattan";

    const std::size_t BFS_NODE_LIMIT = 200000000;
    const int         BFS_MAX_LEN = 35;

    std::ofstream out("solution.txt");
    if (!out) { std::cerr << "Cannot open solution.txt\n"; return 1; }

    out << "Heuristic: " << hName
        << ", timeout per call: " << timeoutSec << " s\n";
    out << "BFS: bidirectional, node limit = " << BFS_NODE_LIMIT
        << ", max expected length = " << BFS_MAX_LEN << "\n";
    out << "IDA*: TT " << TT_BITS << " bits (" << TT_SIZE << " entries)\n\n";

    struct Row { std::string pos; int expected; AlgoResult bfs, astar, ida; };
    std::vector<Row> rows;
    rows.reserve(tests.size());

    auto runWithTimeout = [&](int algo, std::uint64_t start,
        std::vector<std::uint64_t>& st,
        std::vector<char>& mv,
        std::size_t& bfsVisited) -> AlgoResult
        {
            AlgoResult r;
            g_timeoutHit = false;
            g_timeoutEnabled = true;
            g_deadline = std::chrono::steady_clock::now() +
                std::chrono::milliseconds(static_cast<long long>(timeoutSec * 1000.0));

            auto t0 = std::chrono::high_resolution_clock::now();
            int rc = 2;
            std::size_t expanded = 0;
            if (algo == 0)      rc = solveBFS(start, st, mv, BFS_NODE_LIMIT, bfsVisited);
            else if (algo == 1) rc = solveAStar(start, st, mv, expanded);
            else                rc = solveIDAStar(start, st, mv, expanded);
            auto t1 = std::chrono::high_resolution_clock::now();

            g_timeoutEnabled = false;
            r.ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
            r.nodes = (algo == 0) ? bfsVisited : expanded;

            if (rc == 0) { r.solved = true; r.length = static_cast<int>(mv.size()); }
            else if (rc == 1) { r.timedOut = true; r.skipped = true; r.note = "TIMEOUT"; }
            else { r.skipped = true; r.note = (algo == 0) ? "node-limit" : "exhausted"; }
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
            std::string b = cellFmt(row.bfs);
            std::string a = cellFmt(row.astar);
            std::string i = cellFmt(row.ida);
            std::string expStr = (row.expected < 0) ? "uns." : std::to_string(row.expected);
            std::ostringstream oss;
            oss << std::left
                << std::setw(18) << row.pos
                << std::setw(6) << expStr
                << std::setw(28) << b
                << std::setw(28) << a
                << std::setw(28) << i;
            return oss.str();
        };

    auto redrawRow = [&](const Row& row)
        {
            std::cout << "\033[1A\r" << rowLine(row) << "\n";
            std::cout.flush();
        };

    std::cout << "========================================================================================\n";
    std::cout << "Solving (heuristic = " << hName
        << ", timeout = " << timeoutSec << " s)\n";
    std::cout << "BFS: bidirectional (skip if d > " << BFS_MAX_LEN
        << "), IDA*: TT " << TT_BITS << " bits\n";
    std::cout << "========================================================================================\n";
    std::cout << std::left
        << std::setw(18) << "Position"
        << std::setw(6) << "Exp."
        << std::setw(28) << "BFS(bidi)"
        << std::setw(28) << "A*"
        << std::setw(28) << "IDA*" << "\n";
    std::cout << std::string(108, '-') << "\n";
    std::cout.flush();

    for (std::size_t ti = 0; ti < tests.size(); ++ti)
    {
        const TestCase& tc = tests[ti];
        std::uint64_t start = std::stoull(std::string(tc.hex), nullptr, 16);

        Row row;
        row.pos = tc.hex;
        row.expected = tc.expectedLen;

        bool solvable = isSolvable(start);
        if (!solvable) row.bfs.note = row.astar.note = row.ida.note = "n/a";
        else           row.bfs.note = row.astar.note = row.ida.note = "...";

        out << "================================================\n";
        out << "Position: " << tc.hex << "\n";
        out << "Expected length: ";
        if (tc.expectedLen < 0) out << "unsolvable\n";
        else                    out << tc.expectedLen << "\n\n";
        printBoard(start, out);

        std::cout << rowLine(row) << "\n";
        std::cout.flush();

        if (!solvable)
        {
            out << "Unsolvable.\n\n";
            rows.push_back(row);
            continue;
        }

        // -------- BFS (skipped if expected length > BFS_MAX_LEN) --------
        bool runBfs = (tc.expectedLen >= 0 && tc.expectedLen <= BFS_MAX_LEN);
        if (!runBfs)
        {
            row.bfs.skipped = true;
            row.bfs.note = "skipped";
            redrawRow(row);
            out << "BFS: skipped (expected length > " << BFS_MAX_LEN << ")\n";
        }
        else
        {
            std::vector<std::uint64_t> st; std::vector<char> mv;
            std::size_t visited = 0;
            AlgoResult r = runWithTimeout(0, start, st, mv, visited);
            row.bfs = r;
            redrawRow(row);

            out << "BFS (bidirectional): ";
            if (r.solved)
                out << "length = " << r.length
                << ", nodes = " << visited
                << ", time = " << r.ms << " ms\n";
            else if (r.timedOut)
                out << "TIMEOUT, nodes = " << visited
                << ", time = " << r.ms << " ms\n";
            else
                out << "node limit (" << visited << " states), time = "
                << r.ms << " ms\n";
        }

        // -------- A* --------
        {
            std::vector<std::uint64_t> st; std::vector<char> mv;
            std::size_t dummy = 0;
            AlgoResult r = runWithTimeout(1, start, st, mv, dummy);
            row.astar = r;
            redrawRow(row);
            out << "A*: ";
            if (r.solved)
            {
                out << "length = " << r.length
                    << ", nodes = " << r.nodes
                    << ", time = " << r.ms << " ms\n";
                for (std::size_t i = 0; i < mv.size(); ++i)
                {
                    out << "Move " << (i + 1) << ": " << mv[i] << "\n";
                    printBoard(st[i + 1], out);
                }
            }
            else if (r.timedOut) out << "TIMEOUT, nodes = " << r.nodes << "\n";
            else out << "exhausted, nodes = " << r.nodes
                << ", time = " << r.ms << " ms\n";
        }

        // -------- IDA* --------
        {
            std::vector<std::uint64_t> st; std::vector<char> mv;
            std::size_t dummy = 0;
            AlgoResult r = runWithTimeout(2, start, st, mv, dummy);
            row.ida = r;
            redrawRow(row);
            out << "IDA*: ";
            if (r.solved) out << "length = " << r.length
                << ", nodes = " << r.nodes
                << ", time = " << r.ms << " ms\n";
            else if (r.timedOut) out << "TIMEOUT, nodes = " << r.nodes << "\n";
            else out << "exhausted, nodes = " << r.nodes
                << ", time = " << r.ms << " ms\n";
        }

        out << "\n";
        rows.push_back(row);
    }

    std::cout << std::string(108, '-') << "\n";
    std::cout.flush();

    // ---------- summary ----------
    out << "========================================================================================\n";
    out << "Summary (heuristic = " << hName
        << ", timeout = " << timeoutSec << " s)\n";
    out << "========================================================================================\n";
    out << std::left
        << std::setw(18) << "Position"
        << std::setw(6) << "Exp."
        << std::setw(28) << "BFS(bidi)"
        << std::setw(28) << "A*"
        << std::setw(28) << "IDA*" << "\n";
    out << std::string(108, '-') << "\n";

    for (const Row& row : rows)
    {
        std::string b = cellFmt(row.bfs);
        std::string a = cellFmt(row.astar);
        std::string i = cellFmt(row.ida);
        std::string expStr = (row.expected < 0) ? "uns." : std::to_string(row.expected);
        out << std::left
            << std::setw(18) << row.pos
            << std::setw(6) << expStr
            << std::setw(28) << b
            << std::setw(28) << a
            << std::setw(28) << i << "\n";
    }
    out << std::string(108, '-') << "\n";
    out.close();
    std::cout << "\nResults written to solution.txt\n";
    return 0;
}