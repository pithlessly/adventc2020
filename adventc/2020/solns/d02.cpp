#include <iostream>
#include <fstream>
#include <string>

void expect(std::istream& is, char ex) {
    char c = 0;
    is.get(c);
    if (c != ex) {
        std::cerr << "expected '" << ex << "', got '" << c << "'\n";
        exit(1);
    }
}

int main(int argc, char **argv) {
    if (argc != 2) {
        std::cerr << "Please supply a file name\n";
        return 1;
    }

    std::ifstream infile(argv[1]);
    int n_valid_1 = 0; // number valid for policy in part 1
    int n_valid_2 = 0; // number valid for policy in part 2

    std::string pw;

    for (;;) {
        int a, b;
        char target_letter;

        if (!(infile >> a)) break;
        expect(infile, '-');
        infile >> b;
        expect(infile, ' ');
        infile.get(target_letter);
        expect(infile, ':');
        expect(infile, ' ');

        std::getline(infile, pw);

        int occurrences = 0;
        for (char& ch : pw)
            if (ch == target_letter)
                occurrences++;

        if (a <= occurrences && occurrences <= b)
            n_valid_1++;

        if ((pw[a - 1] == target_letter) != (pw[b - 1] == target_letter))
            n_valid_2++;
    }

    std::cout << "Number of valid passwords:\n";
    std::cout << "  According to policy 1: " << n_valid_1 << '\n';
    std::cout << "  According to policy 2: " << n_valid_2 << '\n';
}
