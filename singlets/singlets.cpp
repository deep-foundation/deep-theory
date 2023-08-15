#include <utility>
#include <cmath>
#include <iostream>
#include <sstream>

std::pair<int, int> numToPair(int z) {
    int w = floor((sqrt(8*z+1)-1)/2);
    int t = (w*w + w) / 2;
    int y = z - t;
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

std::string recursivePrint(int x, int y) {
    if (x > 0 && y > 0) {
        auto pairX = numToPair(x);
        auto pairY = numToPair(y);
        std::ostringstream oss;
        oss << "(" << recursivePrint(pairX.first, pairX.second) << ", " << recursivePrint(pairY.first, pairY.second) << ")" << ")";
        return oss.str();
    } else {
        return printPair(x, y);
    }
}

void explainPair(int x) {
    auto pair = numToPair(x);
    auto num = pairToNum(pair.first, pair.second);
    std::cout << printPair(pair.first, pair.second) << " = " << num << std::endl;  
}

int main() {
    // Тестовые пары
    std::pair<int, int> test_pairs[] = { {0, 0}, {1, 1}, {1, 2}, {2, 2}, {10, 10}, {23, 42}, {42, 23} };

    for (auto &p : test_pairs) {
        int num = pairToNum(p.first, p.second); 
        std::pair<int, int> pair = numToPair(num);
        std::cout << "Номер пары (" << p.first << ", " << p.second << "): " << num << std::endl;
        std::cout << "Пара из номера " << num << ": (" << pair.first << ", " << pair.second << ")" << std::endl;
        
        // Проверяем, что преобразование работает верно
        if (pair != p) {
            std::cout << "Ошибка: ожидалась пара (" << p.first << ", " << p.second << "), а было получено (" << pair.first << ", " << pair.second << ")\n";
            return -1;
        }
    }

    std::cout << "Входим в глубину" << std::endl;

    std::cout << "Атомы:" << std::endl;

    explainPair(0);
    explainPair(1);
    explainPair(2);
    explainPair(3);

    std::cout << "Композиты:" << std::endl;

    explainPair(4);
    explainPair(5);
    explainPair(6);
    explainPair(7);
    explainPair(8);

    auto pair2187 = numToPair(2187);
    std::cout << printPair(pair2187.first, pair2187.second) << std::endl;
    std::cout <<  recursivePrint(pair2187.first, pair2187.second) << std::endl;

    return 0;
}
