#include <iostream>
#include <fstream>
#include <string>
#include <vector>

class State {
    int _width;
    int _cur_x;
    int _trees;
    int _delta;

public:
    State(int delta): _width(0), _cur_x(0), _trees(0), _delta(delta) {};

    void update(const char *line, int len);
    int trees() { return _trees; }
};

void State::update(const char *line, int len) {
    if (_width == 0)
        _width = len;
    else if (_width != len)
        throw std::runtime_error("input line lengths are not consistent");

    switch (line[_cur_x]) {
        case '#':
            _trees++;
            break;
        case '.':
            break;
        default:
            throw std::runtime_error("bad character");
    }
    _cur_x = (_cur_x + _delta) % _width;
}

int main(int argc, char **argv) {
    if (argc != 2)
        throw std::runtime_error("no file name supplied");

    std::vector<State> sts = {1, 3, 5, 7, 1};

    {
        std::ifstream infile(argv[1]);
        std::string line;

        for (int i = 0; std::getline(infile, line); i++)
            for (decltype(sts)::size_type j = 0; j < sts.size(); j++)
                if (!(j == 4 && i % 2 > 0))
                    sts[j].update(line.c_str(), line.size());
    }

    long product = 1;
    for (State& st : sts) product *= st.trees();

    std::cout
        << "Number of trees encountered:\n"
        << "  In part 1: " << sts[1].trees() << '\n'
        << "  In part 2: " << product << '\n';
}
