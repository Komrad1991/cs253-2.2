#include <algorithm>
#include <array>
#include <chrono>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <queue>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

using State = std::uint64_t;
using NodeId = std::uint32_t;

constexpr int kBoardSide = 4;
constexpr int kCellCount = kBoardSide * kBoardSide;
constexpr int kTileBits = 4;
constexpr int kTileMask = 0xF;
constexpr State kGoalState = 0x123456789ABCDEF0ULL;
constexpr NodeId kNoParent = 0xFFFFFFFFu;

//where is tile
inline int tileAt(State state, int pos) {
    return static_cast<int>((state >> (kTileBits * (kCellCount - 1 - pos))) & kTileMask);
}

//swap is swap
inline State swapTiles(State state, int a, int b) {
    const int shiftA = kTileBits * (kCellCount - 1 - a);
    const int shiftB = kTileBits * (kCellCount - 1 - b);
    const State diff = ((state >> shiftA) ^ (state >> shiftB)) & kTileMask;
    return state ^ (diff << shiftA) ^ (diff << shiftB);
}

//wheres blank
inline int blankPos(State state) {
    for (int i = 0; i < kCellCount; ++i)
        if (tileAt(state, i) == 0) return i;
    return -1;
}

inline std::array<int, kCellCount> unpack(State state) {
    std::array<int, kCellCount> cells{};
    for (int i = 0; i < kCellCount; ++i)
        cells[i] = tileAt(state, i);
    return cells;
}

//faster abs
inline int absDiff(int a, int b) {
    const int d = a - b;
    const int mask = d >> 31;
    return (d + mask) ^ mask;
}

// Move tables
//precomputed for faster answers
std::array<std::array<int, 4>, kCellCount> g_neighborPos{};
std::array<std::array<char, 4>, kCellCount> g_neighborMove{};
std::array<int, kCellCount> g_neighborCount{};
std::array<char, 128> g_oppositeMove{};
std::array<int, 128> g_moveToDir{};

void initMoveTables() {
    constexpr int dr[] = { -1, 1, 0, 0 };
    constexpr int dc[] = { 0, 0, -1, 1 };
    constexpr char moveChar[] = { 'U', 'D', 'L', 'R' };

    for (int pos = 0; pos < kCellCount; ++pos) {
        const int row = pos / kBoardSide;
        const int col = pos % kBoardSide;
        int count = 0;
        for (int d = 0; d < 4; ++d) {
            const int nr = row + dr[d];
            const int nc = col + dc[d];
            if (nr < 0 || nr >= kBoardSide || nc < 0 || nc >= kBoardSide) continue;
            g_neighborPos[pos][count] = nr * kBoardSide + nc;
            g_neighborMove[pos][count] = moveChar[d];
            ++count;
        }
        g_neighborCount[pos] = count;
    }

    g_oppositeMove.fill(0);
    g_moveToDir.fill(0);
    g_oppositeMove[static_cast<int>('U')] = 'D';
    g_moveToDir[static_cast<int>('U')] = 0;
    g_oppositeMove[static_cast<int>('D')] = 'U';
    g_moveToDir[static_cast<int>('D')] = 1;
    g_oppositeMove[static_cast<int>('L')] = 'R';
    g_moveToDir[static_cast<int>('L')] = 2;
    g_oppositeMove[static_cast<int>('R')] = 'L';
    g_moveToDir[static_cast<int>('R')] = 3;
}

//stolen hash

struct Hash64 {
    std::size_t operator()(std::uint64_t x) const noexcept {
        x ^= x >> 33; x *= 0xff51afd7ed558ccdULL;
        x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL;
        x ^= x >> 33;
        return static_cast<std::size_t>(x);
    }
};

//stolen heurisitic
//heuristic = Manhattan + Linear Conflict + Corner Conflict


int heuristicRaw(State state) {
    const auto cells = unpack(state);

    std::array<bool, kCellCount> rowConflict{};
    std::array<bool, kCellCount> colConflict{};
    int total = 0;

    for (int row = 0; row < kBoardSide; ++row) {
        for (int col = 0; col < kBoardSide; ++col) {
            const int tile = cells[row * kBoardSide + col];
            if (tile == 0) continue;
            const int zeroBased = tile - 1;
            const int targetCol = zeroBased & 3;
            const int targetRow = zeroBased >> 2;

            total += absDiff(targetRow, row) + absDiff(targetCol, col);

            if (targetRow == row) {
                for (int c2 = col + 1; c2 < kBoardSide; ++c2) {
                    const int other = cells[row * kBoardSide + c2];
                    if (other == 0) continue;
                    const int otherZero = other - 1;
                    if ((otherZero >> 2) == row && otherZero < zeroBased) {
                        total += 2;
                        rowConflict[zeroBased] = true;
                        rowConflict[otherZero] = true;
                    }
                }
            }
            if (targetCol == col) {
                for (int r2 = row + 1; r2 < kBoardSide; ++r2) {
                    const int other = cells[r2 * kBoardSide + col];
                    if (other == 0) continue;
                    const int otherZero = other - 1;
                    if ((otherZero & 3) == col && otherZero < zeroBased) {
                        total += 2;
                        colConflict[zeroBased] = true;
                        colConflict[otherZero] = true;
                    }
                }
            }
        }
    }

    if (cells[3] != 4 && cells[3] != 0) {
        if (!rowConflict[2] && cells[2] == 3) total += 2;
        if (!colConflict[7] && cells[7] == 8) total += 2;
    }
    if (cells[0] != 1 && cells[0] != 0) {
        if (!rowConflict[1] && cells[1] == 2) total += 2;
        if (!colConflict[4] && cells[4] == 5) total += 2;
    }
    if (cells[12] != 13 && cells[12] != 0) {
        if (!rowConflict[13] && cells[13] == 14) total += 2;
        if (!colConflict[8] && cells[8] == 9) total += 2;
    }

    return total;
}

constexpr std::size_t kHCacheBits = 20;
constexpr std::size_t kHCacheSize = std::size_t(1) << kHCacheBits;
constexpr std::size_t kHCacheMask = kHCacheSize - 1;

//cache struct
struct HCacheEntry {
    State state;
    int value;
};

//caching
inline int heuristic(State state) {
    static std::array<HCacheEntry, kHCacheSize> cache{};
    const std::size_t idx =
        static_cast<std::size_t>(Hash64{}(state)) & kHCacheMask;
    HCacheEntry& e = cache[idx];
    if (e.state == state) return e.value;
    const int v = heuristicRaw(state);
    e.state = state;
    e.value = v;
    return v;
}

bool isSolvable(State state) {
    std::array<int, kCellCount - 1> sequence{};
    int n = 0;
    int blankRow = 0;
    for (int i = 0; i < kCellCount; ++i) {
        const int tile = tileAt(state, i);
        if (tile == 0) blankRow = i / kBoardSide;
        else sequence[n++] = tile;
    }

    int inversions = 0;
    for (int i = 0; i < kCellCount - 1; ++i)
        for (int j = i + 1; j < kCellCount - 1; ++j)
            if (sequence[i] > sequence[j]) ++inversions;

    return (inversions + (kBoardSide - 1 - blankRow)) % 2 == 0;
}

//out

char tileChar(int value) {
    return value < 10 ? static_cast<char>('0' + value)
        : static_cast<char>('A' + value - 10);
}

void printBoard(State state, std::ostream& os) {
    os << "Hex: 0x" << std::hex << std::setw(16) << std::setfill('0')
        << state << std::dec << std::setfill(' ') << '\n';
    for (int row = 0; row < kBoardSide; ++row) {
        for (int col = 0; col < kBoardSide; ++col) {
            const int tile = tileAt(state, row * kBoardSide + col);
            if (tile == 0) os << "   ";
            else os << tileChar(tile) << ' ';
        }
        os << '\n';
    }
    os << '\n';
}



struct Node {
    State state;
    NodeId parent;
    std::uint8_t g;
    std::uint8_t h;
    char move;
    std::uint8_t blank;
};

//depricated
class Timeout {
public:
    using Clock = std::chrono::steady_clock;

    explicit Timeout(double seconds)
        : deadline_(Clock::now() + std::chrono::milliseconds(
            static_cast<long long>(seconds * 1000.0))) {
    }

    bool expired() const { return Clock::now() >= deadline_; }

private:
    Clock::time_point deadline_;
};


enum class SolveStatus {
    Solved,
    Timeout,
    NodeLimit,
    Exhausted,
    Skipped,
    Unsolvable,
};

struct SolveResult {
    SolveStatus status = SolveStatus::Skipped;
    std::vector<State> states;
    std::vector<char> moves;
    double ms = 0.0;

    bool solved() const { return status == SolveStatus::Solved; }
};

//BFS(bidir)

SolveResult solveBFS(State start, const Timeout& timeout, std::size_t nodeLimit) {
    SolveResult result;

    if (start == kGoalState) {
        result.status = SolveStatus::Solved;
        result.states.push_back(start);
        return result;
    }
    //->  <-
    std::deque<Node> forwardPool, backwardPool;
    std::unordered_map<State, NodeId, Hash64> forwardSeen, backwardSeen;
    forwardSeen.reserve(1 << 16);
    backwardSeen.reserve(1 << 16);

    std::vector<NodeId> forwardFrontier, forwardNext;
    std::vector<NodeId> backwardFrontier, backwardNext;


    //back and forth
    auto pushForward = [&](State s, NodeId parent, std::uint8_t g, char move, int blank) -> NodeId {
        const NodeId id = static_cast<NodeId>(forwardPool.size());
        forwardPool.push_back({ s, parent, g, 0, move, static_cast<std::uint8_t>(blank) });
        forwardSeen.emplace(s, id);
        return id;
        };
    auto pushBackward = [&](State s, NodeId parent, std::uint8_t g, char move, int blank) -> NodeId {
        const NodeId id = static_cast<NodeId>(backwardPool.size());
        backwardPool.push_back({ s, parent, g, 0, move, static_cast<std::uint8_t>(blank) });
        backwardSeen.emplace(s, id);
        return id;
        };

    const NodeId forwardRoot = pushForward(start, kNoParent, 0, 0, blankPos(start));
    const NodeId backwardRoot = pushBackward(kGoalState, kNoParent, 0, 0, blankPos(kGoalState));
    forwardFrontier.push_back(forwardRoot);
    backwardFrontier.push_back(backwardRoot);

    int forwardDepth = 0;
    int backwardDepth = 0;
    int bestLength = INT_MAX;
    NodeId meetForward = kNoParent;
    NodeId meetBackward = kNoParent;
    std::size_t expanded = 0;

    while (!forwardFrontier.empty() && !backwardFrontier.empty()) {
        if ((expanded & 0xFFF) == 0 && timeout.expired()) {
            result.status = SolveStatus::Timeout;
            return result;
        }
        if (forwardDepth + backwardDepth >= bestLength) break;

        const bool expandForward = forwardFrontier.size() <= backwardFrontier.size();

        if (expandForward) {
            forwardNext.clear();
            const auto newG = static_cast<std::uint8_t>(forwardDepth + 1);

            for (NodeId currentId : forwardFrontier) {
                ++expanded;
                if (expanded > nodeLimit) {
                    result.status = SolveStatus::NodeLimit;
                    return result;
                }

                const State current = forwardPool[currentId].state;
                const int blank = forwardPool[currentId].blank;
                const int count = g_neighborCount[blank];

                for (int i = 0; i < count; ++i) {
                    const int nextBlank = g_neighborPos[blank][i];
                    const State nextState = swapTiles(current, blank, nextBlank);
                    if (forwardSeen.find(nextState) != forwardSeen.end()) continue;

                    const NodeId nextId = pushForward(nextState, currentId, newG,
                        g_neighborMove[blank][i], nextBlank);
                    forwardNext.push_back(nextId);

                    const auto itBack = backwardSeen.find(nextState);
                    if (itBack != backwardSeen.end()) {
                        const int candidate = newG + backwardPool[itBack->second].g;
                        if (candidate < bestLength) {
                            bestLength = candidate;
                            meetForward = nextId;
                            meetBackward = itBack->second;
                        }
                    }
                }
            }
            forwardFrontier.swap(forwardNext);
            ++forwardDepth;
        }
        else {
            backwardNext.clear();
            const auto newG = static_cast<std::uint8_t>(backwardDepth + 1);

            for (NodeId currentId : backwardFrontier) {
                ++expanded;
                if (expanded > nodeLimit) {
                    result.status = SolveStatus::NodeLimit;
                    return result;
                }

                const State current = backwardPool[currentId].state;
                const int blank = backwardPool[currentId].blank;
                const int count = g_neighborCount[blank];

                for (int i = 0; i < count; ++i) {
                    const int nextBlank = g_neighborPos[blank][i];
                    const State nextState = swapTiles(current, blank, nextBlank);
                    if (backwardSeen.find(nextState) != backwardSeen.end()) continue;

                    const NodeId nextId = pushBackward(nextState, currentId, newG,
                        g_neighborMove[blank][i], nextBlank);
                    backwardNext.push_back(nextId);

                    const auto itForward = forwardSeen.find(nextState);
                    if (itForward != forwardSeen.end()) {
                        const int candidate = newG + forwardPool[itForward->second].g;
                        if (candidate < bestLength) {
                            bestLength = candidate;
                            meetForward = itForward->second;
                            meetBackward = nextId;
                        }
                    }
                }
            }
            backwardFrontier.swap(backwardNext);
            ++backwardDepth;
        }
    }

    if (bestLength == INT_MAX) {
        result.status = SolveStatus::Exhausted;
        return result;
    }

    //from start to meet
    std::vector<NodeId> forwardPath;
    for (NodeId id = meetForward; id != kNoParent; id = forwardPool[id].parent)
        forwardPath.push_back(id);
    std::reverse(forwardPath.begin(), forwardPath.end());

    //from meet to goal.
    std::vector<NodeId> backwardPath;
    for (NodeId id = meetBackward; id != kNoParent; id = backwardPool[id].parent)
        backwardPath.push_back(id);

    for (NodeId id : forwardPath) result.states.push_back(forwardPool[id].state);
    for (std::size_t i = 1; i < forwardPath.size(); ++i)
        result.moves.push_back(forwardPool[forwardPath[i]].move);

    for (std::size_t i = 0; i + 1 < backwardPath.size(); ++i) {
        result.moves.push_back(
            g_oppositeMove[static_cast<int>(backwardPool[backwardPath[i]].move)]);
        result.states.push_back(backwardPool[backwardPath[i + 1]].state);
    }

    result.status = SolveStatus::Solved;
    return result;
}


// IDS
enum class SearchOutcome {
    Found,
    Timeout,
    Continue,
};

SearchOutcome idsSearch(State state, int blank, int g, int depthLimit, int prevMove,
    const Timeout& timeout,
    std::vector<char>& path,
    std::vector<State>& states,
    std::uint64_t& tick)
{
    ++tick;
    if ((tick & 0xFFF) == 0 && timeout.expired()) return SearchOutcome::Timeout;
    if (state == kGoalState) return SearchOutcome::Found;

    //budget for iter search
    const int budget = depthLimit - g;
    if (budget <= 0) return SearchOutcome::Continue;

    const int count = g_neighborCount[blank];
    for (int i = 0; i < count; ++i) {
        const char move = g_neighborMove[blank][i];
        const int dir = g_moveToDir[static_cast<int>(move)];
        if (prevMove != -1 && dir == (prevMove ^ 1)) continue;

        const int nextBlank = g_neighborPos[blank][i];
        const State nextState = swapTiles(state, blank, nextBlank);

        path.push_back(move);
        states.push_back(nextState);

        const auto outcome = idsSearch(nextState, nextBlank, g + 1, depthLimit, dir,
            timeout, path, states, tick);

        if (outcome == SearchOutcome::Found) return outcome;
        if (outcome == SearchOutcome::Timeout) {
            states.pop_back();
            path.pop_back();
            return outcome;
        }

        states.pop_back();
        path.pop_back();
    }

    return SearchOutcome::Continue;
}


//iterations themselfs + maxdepth limit + depricated timeout
SolveResult solveIDS(State start, const Timeout& timeout, int maxDepth) {
    SolveResult result;
    if (start == kGoalState) {
        result.status = SolveStatus::Solved;
        result.states.push_back(start);
        return result;
    }

    std::vector<char> path;
    std::vector<State> states;
    states.reserve(128);
    path.reserve(128);
    states.push_back(start);

    const int blank = blankPos(start);
    std::uint64_t tick = 0;

    for (int depth = 1; depth <= maxDepth; ++depth) {
        const auto outcome = idsSearch(start, blank, 0, depth, -1,
            timeout, path, states, tick);
        if (outcome == SearchOutcome::Found) {
            result.status = SolveStatus::Solved;
            result.moves = path;
            result.states = states;
            return result;
        }
        if (outcome == SearchOutcome::Timeout) {
            result.status = SolveStatus::Timeout;
            return result;
        }
    }

    result.status = SolveStatus::Exhausted;
    return result;
}

// A*

//pq is for priority queue eh
struct PQItem {
    int f;
    int h;
    NodeId id;

    bool operator>(const PQItem& other) const {
        if (f != other.f) return f > other.f;
        if (h != other.h) return h > other.h;
        return id > other.id;
    }
};

//reconstruct is reconstruct, speaks for itself
void reconstructPath(NodeId leafId, const std::deque<Node>& pool,
    std::vector<State>& states, std::vector<char>& moves)
{
    std::vector<NodeId> ids;
    for (NodeId id = leafId; id != kNoParent; id = pool[id].parent)
        ids.push_back(id);
    std::reverse(ids.begin(), ids.end());

    states.reserve(ids.size());
    moves.reserve(ids.empty() ? 0 : ids.size() - 1);
    for (std::size_t i = 0; i < ids.size(); ++i)
        states.push_back(pool[ids[i]].state);
    for (std::size_t i = 1; i < ids.size(); ++i)
        moves.push_back(pool[ids[i]].move);
}

SolveResult solveAStar(State start, const Timeout& timeout) {
    SolveResult result;
    if (start == kGoalState) {
        result.status = SolveStatus::Solved;
        result.states.push_back(start);
        return result;
    }

    //all states
    std::deque<Node> pool;
    std::unordered_map<State, std::uint8_t, Hash64> bestG;
    bestG.reserve(1 << 22);

    std::vector<PQItem> heapBuffer;
    heapBuffer.reserve(1 << 22);
    std::priority_queue<PQItem, std::vector<PQItem>, std::greater<PQItem>>
        queue(std::greater<PQItem>(), std::move(heapBuffer));

    {
        const int h0 = heuristic(start);
        pool.push_back({ start, kNoParent, 0, static_cast<std::uint8_t>(h0), 0,
                        static_cast<std::uint8_t>(blankPos(start)) });
        bestG.emplace(start, 0);
        queue.push({ h0, h0, 0 });
    }

    std::size_t expanded = 0;
    while (!queue.empty()) {
        if ((expanded & 0xFFF) == 0 && timeout.expired()) {
            result.status = SolveStatus::Timeout;
            return result;
        }

        const PQItem top = queue.top();
        queue.pop();
        const NodeId currentId = top.id;
        const State currentState = pool[currentId].state;
        const int currentG = pool[currentId].g;

        //skip if already better
        const auto itBest = bestG.find(currentState);
        if (itBest != bestG.end() && itBest->second < currentG) continue;

        ++expanded;
        if (currentState == kGoalState) {
            reconstructPath(currentId, pool, result.states, result.moves);
            result.status = SolveStatus::Solved;
            return result;
        }

        const int blank = pool[currentId].blank;
        const int count = g_neighborCount[blank];

        for (int i = 0; i < count; ++i) {
            const int nextBlank = g_neighborPos[blank][i];
            const State nextState = swapTiles(currentState, blank, nextBlank);
            const int nextG = currentG + 1;

            const auto itNext = bestG.find(nextState);
            if (itNext != bestG.end() && itNext->second <= nextG) continue;

            bestG[nextState] = static_cast<std::uint8_t>(nextG);

            //
            const int nextH = heuristic(nextState);
            const NodeId nextId = static_cast<NodeId>(pool.size());
            pool.push_back({ nextState, currentId, static_cast<std::uint8_t>(nextG),
                            static_cast<std::uint8_t>(nextH),
                            g_neighborMove[blank][i],
                            static_cast<std::uint8_t>(nextBlank) });
            queue.push({ nextG + nextH, nextH, nextId });
        }
    }

    result.status = SolveStatus::Exhausted;
    return result;
}

// IDA*

int idaSearch(State state, int blank, int g, int bound, int prevMove, int h,
    const Timeout& timeout,
    std::vector<char>& path, std::vector<State>& states,
    std::uint64_t& tick)
{
    ++tick;
    if ((tick & 0xFFF) == 0 && timeout.expired()) return -2;
    if (state == kGoalState) return -1;

    const int f = g + h;
    if (f > bound) return f;

    struct Child {
        int h;
        int index;
    };
    std::array<Child, 4> children{};
    int childCount = 0;

    const int count = g_neighborCount[blank];
    for (int i = 0; i < count; ++i) {
        const char move = g_neighborMove[blank][i];
        const int dir = g_moveToDir[static_cast<int>(move)];
        if (prevMove != -1 && dir == (prevMove ^ 1)) continue;

        const int nextBlank = g_neighborPos[blank][i];
        const State nextState = swapTiles(state, blank, nextBlank);
        children[childCount].h = heuristic(nextState);
        children[childCount].index = i;
        ++childCount;
    }

    if (childCount > 1) {
        for (int i = 1; i < childCount; ++i) {
            const Child key = children[i];
            int j = i - 1;
            while (j >= 0 && children[j].h > key.h) {
                children[j + 1] = children[j];
                --j;
            }
            children[j + 1] = key;
        }
    }

    int min = INT_MAX;
    for (int j = 0; j < childCount; ++j) {
        const int i = children[j].index;
        const int nextH = children[j].h;
        const char move = g_neighborMove[blank][i];
        const int dir = g_moveToDir[static_cast<int>(move)];
        const int nextBlank = g_neighborPos[blank][i];
        const State nextState = swapTiles(state, blank, nextBlank);

        path.push_back(move);
        states.push_back(nextState);

        const int t = idaSearch(nextState, nextBlank, g + 1, bound, dir, nextH,
            timeout, path, states, tick);

        if (t == -1) return -1;
        if (t == -2) {
            states.pop_back();
            path.pop_back();
            return -2;
        }
        if (t < min) min = t;

        states.pop_back();
        path.pop_back();
    }

    return min;
}

//iterations for ida*
SolveResult solveIDAStar(State start, const Timeout& timeout) {
    SolveResult result;
    if (start == kGoalState) {
        result.status = SolveStatus::Solved;
        result.states.push_back(start);
        return result;
    }

    int bound = heuristic(start);

    std::vector<char> path;
    std::vector<State> states;
    states.reserve(128);
    path.reserve(128);
    states.push_back(start);

    const int blank = blankPos(start);
    std::uint64_t tick = 0;

    while (true) {
        const int t = idaSearch(start, blank, 0, bound, -1, bound,
            timeout, path, states, tick);
        if (t == -1) {
            result.status = SolveStatus::Solved;
            result.moves = path;
            result.states = states;
            return result;
        }
        if (t == -2) {
            result.status = SolveStatus::Timeout;
            return result;
        }
        if (t == INT_MAX) break;
        bound = t;
    }

    result.status = SolveStatus::Exhausted;
    return result;
}


enum class Algorithm { BFS, IDS, AStar, IDAStar };

struct RunConfig {
    double timeoutSeconds = 10.0;
    std::size_t bfsNodeLimit = 200'000'000;
    int idsMaxDepth = 80;
};

SolveResult runWithTimeout(Algorithm algo, State start, const RunConfig& cfg) {
    const Timeout timeout(cfg.timeoutSeconds);
    const auto t0 = std::chrono::high_resolution_clock::now();

    SolveResult result;
    switch (algo) {
    case Algorithm::BFS:     result = solveBFS(start, timeout, cfg.bfsNodeLimit); break;
    case Algorithm::IDS:     result = solveIDS(start, timeout, cfg.idsMaxDepth); break;
    case Algorithm::AStar:   result = solveAStar(start, timeout); break;
    case Algorithm::IDAStar: result = solveIDAStar(start, timeout); break;
    }

    const auto t1 = std::chrono::high_resolution_clock::now();
    result.ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
    return result;
}


//cases

struct TestCase {
    std::string hex;
    int expectedLength;
};

std::vector<TestCase> makeTests() {
    return {
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
        //{"D79F2E8A45106C3B", 55},
        //{"DBE87A2C91F65034", 58},
        //{"BAC0F478E19623D5", 61}
    };
}


struct Row {
    std::string position;
    int expected = -1;
    SolveResult bfs;
    SolveResult ids;
    SolveResult astar;
    SolveResult ida;
};

std::string formatCell(const SolveResult& r) {
    switch (r.status) {
    case SolveStatus::Unsolvable: return "n/a";
    case SolveStatus::Skipped:    return "skipped";
    case SolveStatus::Timeout:    return "TIMEOUT";
    case SolveStatus::NodeLimit:  return "node-limit";
    case SolveStatus::Exhausted:  return "exhausted";
    case SolveStatus::Solved: {
        std::ostringstream oss;
        oss << r.moves.size() << " (" << std::fixed << std::setprecision(1)
            << r.ms << "ms)";
        return oss.str();
    }
    }
    return "-";
}

std::string headerLine() {
    std::ostringstream oss;
    oss << std::left
        << std::setw(18) << "Position"
        << std::setw(6) << "Exp."
        << std::setw(20) << "BFS(bidi)"
        << std::setw(20) << "IDS"
        << std::setw(20) << "A*"
        << std::setw(20) << "IDA*";
    return oss.str();
}

std::string rowLine(const Row& row) {
    std::ostringstream oss;
    oss << std::left
        << std::setw(18) << row.position
        << std::setw(6) << (row.expected < 0 ? "uns." : std::to_string(row.expected))
        << std::setw(20) << formatCell(row.bfs)
        << std::setw(20) << formatCell(row.ids)
        << std::setw(20) << formatCell(row.astar)
        << std::setw(20) << formatCell(row.ida);
    return oss.str();
}

//void writeReportHeader(std::ostream& os, const RunConfig& cfg) {
//    os << "Heuristic: Manh+LC+CornerConflict (stolen)\n";
//    os << "BFS: bidirectional, Hash64, node limit = " << cfg.bfsNodeLimit
//        << ", run only if expected length <= 19\n";
//    os << "IDS: depth-limited DFS iterated, max depth = " << cfg.idsMaxDepth
//        << ", run only if expected length <= 19\n";
//    os << "A*: PQ (tie: smaller h first), closed map bestG (reopen), Hash64\n";
//    os << "IDA*: recursive, move ordering, heuristic memoization\n\n";
//}


//main


int main(int argc, char** argv) {
    initMoveTables();

    RunConfig cfg;
    if (argc > 1) {
        try {
            const double v = std::stod(argv[1]);
            if (v > 0.0) cfg.timeoutSeconds = v;
        }
        catch (...) {
            
        }
    }

    constexpr int kLightMaxLength = 19;

    const auto tests = makeTests();

    std::ofstream out("solution.txt");
    if (!out) {
        std::cerr << "Cannot open solution.txt\n";
        return 1;
    }

    //writeReportHeader(out, cfg);

    std::vector<Row> rows;
    rows.reserve(tests.size());

    const std::string separator(120, '=');
    const std::string divider(120, '-');

    std::cout << separator << "\n";
    std::cout << "Solving (timeout = " << cfg.timeoutSeconds << " s per call)\n";
    std::cout << separator << "\n";
    std::cout << headerLine() << "\n";
    std::cout << divider << "\n";

    for (const TestCase& tc : tests) {
        const State start = std::stoull(tc.hex, nullptr, 16);

        Row row;
        row.position = tc.hex;
        row.expected = tc.expectedLength;

        const bool solvable = isSolvable(start);

        out << "================================================\n";
        out << "Position: " << tc.hex << "\n";
        out << "Expected length: ";
        if (tc.expectedLength < 0) out << "unsolvable\n";
        else out << tc.expectedLength << "\n";
        out << "\n";
        printBoard(start, out);

        if (!solvable) {
            row.bfs.status = row.ids.status = row.astar.status = row.ida.status
                = SolveStatus::Unsolvable;
            out << "Unsolvable.\n\n";
            rows.push_back(row);
            std::cout << rowLine(row) << "\n";
            continue;
        }

        const bool runLight = (tc.expectedLength >= 0
            && tc.expectedLength <= kLightMaxLength);

        // ---- BFS ----
        if (runLight) {
            row.bfs = runWithTimeout(Algorithm::BFS, start, cfg);
            out << "BFS: " << formatCell(row.bfs) << "\n";
        }
        else {
            row.bfs.status = SolveStatus::Skipped;
            out << "BFS: skipped (expected length > " << kLightMaxLength << ")\n";
        }

        // ---- IDS ----
        if (runLight) {
            row.ids = runWithTimeout(Algorithm::IDS, start, cfg);
            out << "IDS: " << formatCell(row.ids) << "\n";
        }
        else {
            row.ids.status = SolveStatus::Skipped;
            out << "IDS: skipped (expected length > " << kLightMaxLength << ")\n";
        }

        // ---- A* ----
        row.astar = runWithTimeout(Algorithm::AStar, start, cfg);
        out << "A*: " << formatCell(row.astar) << "\n";

        // ---- IDA* ----
        row.ida = runWithTimeout(Algorithm::IDAStar, start, cfg);
        out << "IDA*: " << formatCell(row.ida) << "\n\n";

        rows.push_back(row);
        std::cout << rowLine(row) << "\n";
    }

    std::cout << divider << "\n";

    out << separator << "\n";
    out << "Summary\n";
    out << separator << "\n";
    out << headerLine() << "\n";
    out << divider << "\n";
    for (const Row& row : rows) out << rowLine(row) << "\n";
    out << divider << "\n";
    out.close();
    return 0;
}