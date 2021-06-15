#include <iostream>
#include <fstream>
#include <vector>

using std::ifstream;

int main(int argc, char **argv) {
    if (argc != 2) {
        std::cerr << "Please supply a file name\n";
        return 1;
    }

    std::vector<int> nums;
    {
        ifstream infile(argv[1]);
        for (int a; infile >> a;)
            nums.push_back(a);
    }

    int size = nums.size();

    for (int i = 0; i < size; i++)
        for (int j = i + 1; j < size; j++) {
            int ni = nums[i];
            int nj = nums[j];
            int sum_ij = ni + nj;
            // part 1
            if (sum_ij == 2020)
                std::cout << ni << " * " << nj << " = " << ni*nj << '\n';
            // part 2
            for (int k = j + 1; k < size; k++) {
                int nk = nums[k];
                if (sum_ij + nk == 2020)
                    std::cout
                        << ni << " * " << nk << " * " << nj
                        << " = " << ni*nk*nj << '\n';
            }
        }
}
