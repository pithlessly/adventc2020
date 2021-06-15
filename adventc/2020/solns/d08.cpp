#include <stdexcept> // for runtime_error
#include <iostream> // for cout
#include <fstream> // for ifstream
#include <cstdlib> // for strtoll
#include <cstddef> // for size_t
#include <string> // for string
#include <vector> // for vector

enum Operation { acc, jmp, nop };

struct Instruction {
    Operation op;
    int arg;

    static Instruction parse(const char *line) {
        Instruction i;

        switch (line[0]) {
            case 'a': i.op = acc; break;
            case 'j': i.op = jmp; break;
            case 'n': i.op = nop; break;
            default: throw std::runtime_error("invalid operator");
        }

        char *end;
        i.arg = std::strtoll(&line[5], &end, 10);
        if (end == &line[5]) throw std::runtime_error("invalid number");

        switch (line[4]) {
            case '+': break;
            case '-': i.arg = -i.arg; break;
            default: throw std::runtime_error("invalid sign");
        }

        return i;
    }
};

enum ExecResult { loop, fail, ok };

ExecResult run(const std::vector<Instruction>& pgm, int& ax) {
    size_t size = pgm.size();
    std::vector<bool> executed(size);
    int ip = 0;
    for (;;) {
        if (!(0 <= ip && ip < (int) size))
            return fail;

        if (executed[ip])
            return loop;

        executed[ip] = true;
        Instruction ins = pgm[ip];
        switch (ins.op) {
            case acc:
                ax += ins.arg;
                ip++;
                break;
            case jmp:
                ip += ins.arg;
                if (ip == (int) size)
                    return ok;
                break;
            case nop:
                ip++;
                break;
        }
    }
}

bool toggle(Operation& op) {
    switch (op) {
        case acc: return false;
        case jmp: op = nop; break;
        case nop: op = jmp; break;
    }
    return true;
}

int main(int argc, char **argv) {
    if (argc != 2)
        throw std::runtime_error("no file name supplied");

    std::vector<Instruction> pgm;
    {
        std::ifstream infile(argv[1]);
        std::string line;

        while (std::getline(infile, line))
            pgm.push_back(Instruction::parse(line.c_str()));
    }

    std::cout << "Number of instructions: " << pgm.size() << '\n';

    {
        int ax = 0;
        if (run(pgm, ax) != loop)
            throw std::runtime_error("expected infinite loop");
        std::cout << "  Accumulator value before infinite loop: " << ax << '\n';
    }

    for (size_t i = 0; i < pgm.size(); i++) {
        Operation& op = pgm[i].op;
        if (!toggle(op)) continue;

        int ax = 0;
        if (run(pgm, ax) == ok) {
            std::cout
                << "Toggling instruction at position " << i+1
                << " causes program to exit successfully\n"
                   "  Accumulator value when this happens: "
                << ax << '\n';
            break;
        }

        toggle(op);
    }
}
