#include <cmath>
#include <format>
#include <iostream>
#include <utility>

template <typename... Args>
void println(std::format_string<Args...> fmt, Args&&... args) {
    std::cout << std::format(fmt, std::forward<Args>(args)...) << std::endl;
}

template <typename T>
auto numToPair(T z) -> std::pair<T, T> {
    T w = floor((sqrt(8 * z + 1) - 1) / 2);
    T y = z - (w * w + w) / 2;
    T x = w - y;
    return {x, y};
}

template <typename T, typename U>
struct std::formatter<std::pair<T, U>> : std::formatter<std::string_view> {
    auto format(const std::pair<T, U>& p, format_context& cx) const {
        return std::format_to(cx.out(), "({}, {})", p.first, p.second);
    }
};

template <typename T>
auto pairToNum(std::pair<T, T> pair) -> T {
    auto [x, y] = pair;
    return ((x + y) * (x + y + 1) / 2) + y;
}

void explainPair(int x) {
    auto pair = numToPair(x);
    auto num = pairToNum(pair);
    println("{} ↔ {}", std::move(pair), pairToNum(pair));
}

auto recursivePrint(std::pair<int, int> pair, int limit = 0) -> std::string {
    auto format = [](auto&& t) {
        return std::format("{}", t);
    };
    if (limit == 1) {  // For limit=1, print pairs without going into recursion
        return format(pair);
    }

    auto [x, y] = pair;
    auto a = x > 1 ? recursivePrint(numToPair(x), limit - 1) : format(x);
    auto b = y > 1 ? recursivePrint(numToPair(y), limit - 1) : format(y);

    return format(std::pair{a, b});
}

int main() {
    // Test pairs
    std::pair<int, int> test_pairs[] = {{0, 0},   {1, 1},   {1, 2},  {2, 2},
                                        {10, 10}, {23, 42}, {42, 23}};

    for (auto p : test_pairs) {
        int num = pairToNum(p);
        std::pair<int, int> pair = numToPair(num);
        println("{0} ↦ {1} | {1} ↦ {0}", p, num);

        // Проверяем, что преобразование работает верно
        if (pair != p) {
            println("Error: expected pair {}, but got {}", p, pair); // it's a panic???
            return -1;
        }
    }

    std::cout << "Entering the deep" << std::endl;

    std::cout << "Atoms:" << std::endl;

    explainPair(0);
    explainPair(1);

    std::cout << "Composites:" << std::endl;

    explainPair(2);
    explainPair(3);
    explainPair(4);
    explainPair(5);
    explainPair(6);
    explainPair(7);
    explainPair(8);

    auto pair2187 = numToPair(2187);
    std::cout << "Level 0: " << 2187 << std::endl;
    for (int i = 1; i <= 5; i++) {
        println("Level {}: {}", i, recursivePrint(pair2187, i));
    }

    for (int i = 0; i <= 8; i++) {
        println("{} ↔ {}", i, recursivePrint(numToPair(i), 0));
    }
}
