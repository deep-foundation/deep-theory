#include <utility>
#include <cmath>
#include <iostream>
#include <sstream>

std::pair<int, int> numToPair(int z) {
    int w = floor((sqrt(8*z+1)-1)/2);
    int y = z - (w*w + w) / 2;
    int x = w - y;
    return std::make_pair(x, y);
}

int pairToNum(int x, int y) {
    return ((x + y) * (x + y + 1) / 2) + y;
}

template<typename T1, typename T2>
std::string printPair(const T1& first, const T2& second) {
  std::ostringstream oss;
  oss << "(" << first << ", " << second << ")";
  return oss.str();
}

std::string recursivePrint(int x, int y, int limit = 0) {
    if (limit == 1) { // For limit=1, print pairs without going into recursion
        return printPair(x, y);
    }
    if (x > 1 && y > 1) {
        auto pairX = numToPair(x);
        auto pairY = numToPair(y);
        std::ostringstream oss;
        oss << "(" << recursivePrint(pairX.first, pairX.second, limit-1) << ", " << recursivePrint(pairY.first, pairY.second, limit-1) << ")" << ")";
        return oss.str();
    } else if(x > 1) {
        auto pairX = numToPair(x);
        std::ostringstream oss;
        oss << "(" << recursivePrint(pairX.first, pairX.second, limit-1) << ", " << y << ")" << ")";
        return oss.str();
    } else if(y > 1) {
        auto pairY = numToPair(y);
        std::ostringstream oss;
        oss << "(" << x << ", " << recursivePrint(pairY.first, pairY.second, limit-1) << ")" << ")";
        return oss.str();
    } else {
        return printPair(x, y);
    }
}

void explainPair(int x) {
    auto pair = numToPair(x);
    auto num = pairToNum(pair.first, pair.second);
    std::cout << printPair(pair.first, pair.second) << " ↔ " << num << std::endl;  
}

int main() {
    // Test pairs
    std::pair<int, int> test_pairs[] = { {0, 0}, {1, 1}, {1, 2}, {2, 2}, {10, 10}, {23, 42}, {42, 23} };

    for (auto &p : test_pairs) {
        int num = pairToNum(p.first, p.second); 
        std::pair<int, int> pair = numToPair(num);
        std::cout << "(" << p.first << ", " << p.second << ") ↦ " << num << std::endl;
        std::cout << "" << num << " ↦ (" << pair.first << ", " << pair.second << ")" << std::endl;
        
        // Проверяем, что преобразование работает верно
        if (pair != p) {
            std::cout << "Error: expected pair (" << p.first << ", " << p.second << "), but got (" << pair.first << ", " << pair.second << ")\n";
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
    for (int i = 1; i <= 5; ++i) {
        std::cout << "Level " << i << ": " << recursivePrint(pair2187.first, pair2187.second, i) << std::endl;
    }

    for (int i = 0; i <= 8; ++i) {
        auto pair = numToPair(i);
        std::cout << i << " ↔ " << recursivePrint(pair.first, pair.second, 0) << std::endl;
    }

    return 0;
}
