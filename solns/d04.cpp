#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <array>
#include <cstdint>
#include <cstring>
#include <cctype>

const char *rem_prefix(const char *p, const char *s) {
    for (;;) {
        char xp = *p++;
        if (!xp) return s;
        char xs = *s++;
        if (xs != xp) return nullptr;
    }
}

const char *parse_int(const char *s, int *i) {
    char *rest;
    *i = (int) std::strtoll(s, &rest, 10);
    return rest == s ? nullptr : rest;
}

bool is_hex_format(const char *s) {
    size_t i = 0;

    if (s[i++] != '#')
        return false;

    while (i < 7)
        if (!std::isxdigit(s[i++]))
            return false;

    if (s[i] != '\0')
        return false;

    return true;
}

class State {
    int& _n_valid;
    int& _n_valid_strict;

    uint8_t _fields;
    uint8_t _fields_strict;

    void reset() {
        if (_fields == 0xff)
            _n_valid++;
        if (_fields_strict == 0xff)
            _n_valid_strict++;
        _fields = _fields_strict = 0x01;
    }

    void set_valid(uint8_t field, bool strict) {
        _fields        |=      1 << field;
        _fields_strict |= strict << field;
    }

    void update_field(const std::string& word);

public:
    State(int& n_valid, int& n_valid_strict):
        _n_valid(n_valid),
        _n_valid_strict(n_valid_strict),
        _fields(0x01) {}
    void process_line(const std::string& line, std::string& word_buf);
    void finish() { reset(); }
};

void State::update_field(const std::string& word) {
    const char *str = word.c_str();
    const char *rest;

    if ((rest = rem_prefix("byr:", str))) {
        int i;
        set_valid(7, parse_int(rest, &i) && 1920 <= i && i <= 2002);
    } else

    if ((rest = rem_prefix("iyr:", str))) {
        int i;
        set_valid(6, parse_int(rest, &i) && 2010 <= i && i <= 2020);
    } else

    if ((rest = rem_prefix("eyr:", str))) {
        int i;
        set_valid(5, parse_int(rest, &i) && 2020 <= i && i <= 2030);
    } else

    if ((rest = rem_prefix("hgt:", str))) {
        int i;
        rest = parse_int(rest, &i);
        set_valid(4, rest &&
            ((std::strcmp(rest, "cm") == 0 && 150 <= i && i <= 193) ||
             (std::strcmp(rest, "in") == 0 &&  59 <= i && i <= 76)));
    } else

    if ((rest = rem_prefix("hcl:", str))) {
        set_valid(3, is_hex_format(rest));
    } else

    if ((rest = rem_prefix("ecl:", str))) {
        static const std::array<char [4], 7> cols =
            {"amb", "blu", "brn", "gry", "grn", "hzl", "oth"};
        bool valid = false;
        for (const char *col : cols)
            if (strcmp(col, rest) == 0) {
                valid = true;
                break;
            }
        set_valid(2, valid);
    } else

    if ((rest = rem_prefix("pid:", str))) {
        bool valid = true;
        for (int i = 0; i < 9; i++)
            if (!std::isdigit(rest[i])) {
                valid = false;
                break;
            }
        set_valid(1, valid);
    } else

    if ((rest = rem_prefix("cid:", str))) {}

    else
        throw std::runtime_error("unknown field");
}

void State::process_line(const std::string& line, std::string& word_buf) {
    if (line.size() == 0) {
        reset();
        return;
    }

    std::stringstream linewords(line);
    while (std::getline(linewords, word_buf, ' '))
        update_field(word_buf.c_str());
}

int main(int argc, char **argv) {
    if (argc != 2)
        throw std::runtime_error("no file name supplied");

    int n_valid = 0, n_valid_strict = 0;
    {
        std::ifstream infile(argv[1]);
        std::string line;
        std::string word_buf;
        State st(n_valid, n_valid_strict);

        while (std::getline(infile, line))
            st.process_line(line, word_buf);
        st.finish();
    }

    std::cout
        << "Number of valid passports:\n"
        << "  According to relaxed rules: " << n_valid << '\n'
        << "  According to strict rules: " << n_valid_strict << '\n';
}
