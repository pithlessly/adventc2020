#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <cstdint>

template<class T>
static bool which(T x, T a, T b) {
    if (x == a) return true;
    if (x == b) return false;
    throw std::runtime_error("invalid element");
}

static int compute_id(const char *s) {
    int res = 0;
    res |= which(s[0], 'B', 'F') << 9;
    res |= which(s[1], 'B', 'F') << 8;
    res |= which(s[2], 'B', 'F') << 7;
    res |= which(s[3], 'B', 'F') << 6;
    res |= which(s[4], 'B', 'F') << 5;
    res |= which(s[5], 'B', 'F') << 4;
    res |= which(s[6], 'B', 'F') << 3;
    res |= which(s[7], 'R', 'L') << 2;
    res |= which(s[8], 'R', 'L') << 1;
    res |= which(s[9], 'R', 'L') << 0;
    return res;
}

int main(int argc, char **argv) {
    if (argc != 2)
        throw std::runtime_error("no file name supplied");

    std::string line;
    std::ifstream infile(argv[1]);

    bool present[1 << 10] = {false};

    int min_id = (1 << 10) - 1;
    int max_id = 0;

    while (std::getline(infile, line)) {
        int id = compute_id(line.c_str());
        present[id] = true;
        max_id = std::max(max_id, id);
        min_id = std::min(min_id, id);
    }

    std::cout << "Maximum ID: " << max_id << '\n';

    for (int id = min_id; id <= max_id; id++)
        if (!present[id]) {
            std::cout << "ID not present: " << id << '\n';
            break;
        }
}
