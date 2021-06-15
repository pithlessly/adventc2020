#include <iostream> // for cout
#include <fstream> // for ifstream
#include <string> // for string
#include <cstring> // for memset

#define LETTER 26

class State {
    int _any_yes_current;
    int _all_yes_current;
    // questions where someone in the current group answered yes
    bool _any_yes[LETTER];
    // questions where everyone in the current group answered yes
    bool _all_yes[LETTER];

    void reset_group() {
        _any_yes_current = 0;
        _all_yes_current = LETTER;
        std::memset(_any_yes, false, LETTER);
        std::memset(_all_yes, true, LETTER);
    }

public:

    int _any_yes_total;
    int _all_yes_total;

    State() { _any_yes_total = 0; _all_yes_total = 0; reset_group(); }

    void finish_group() {
        _any_yes_total += _any_yes_current;
        _all_yes_total += _all_yes_current;
        reset_group();
    }

    void process_line(const std::string& line) {
        if (line.size() == 0) {
            finish_group();
            return;
        }
        bool cur_yes[LETTER] = {false};
        for (const char& c : line)
            if ('a' <= c && c <= 'z')
                cur_yes[c - 'a'] = true;
            else
                throw std::runtime_error("invalid character");

        for (int i = 0; i < LETTER; i++) {
            if (cur_yes[i]) {
                if (!_any_yes[i]) {
                    _any_yes_current++;
                    _any_yes[i] = true;
                }
            } else {
                if (_all_yes[i]) {
                    _all_yes_current--;
                    _all_yes[i] = false;
                }
            }
        }
    }
};

int main(int argc, char **argv) {
    if (argc != 2) throw std::runtime_error("no file name provided");

    State st;
    {
        std::string line;
        std::ifstream infile(argv[1]);

        while (std::getline(infile, line))
            st.process_line(line);
        st.finish_group();
    }

    std::cout
        << "Number of times...\n"
        << "  Someone answered 'yes' to a question: " << st._any_yes_total << '\n'
        << "  Everyone answered 'yes' to a question: " << st._all_yes_total << '\n';
}
