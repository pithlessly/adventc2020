#include <stdexcept> // for runtime_error
#include <algorithm> // for max, min
#include <iostream> // for cout
#include <fstream> // for ifstream
#include <cstddef> // for size_t
#include <climits> // for INT_MAX
#include <vector> // for vector

const int WINDOW_SZ = 25;

bool find_valid(const long *nums) {
    long target = nums[WINDOW_SZ];

    for (size_t i = 0; i < WINDOW_SZ; i++) {
        long a = nums[i];

        for (size_t j = i + 1; j < WINDOW_SZ; j++) {
            long b = nums[j];

            if (a + b == target) {
                std::cout << a << " + " << b << " = " << target << std::endl;
                return true;
            }
        }
    }

    std::cout << "Found invalid target number: " << target << '\n';
    return false;
}

int main(int argc, char **argv) {
    if (argc != 2)
        throw std::runtime_error("no file name supplied");

    std::vector<long> nums;
    {
        std::ifstream infile(argv[1]);
        for (long a; infile >> a;)
            nums.push_back(a);
    }

    long target = -1;
    for (size_t i = 0; i < nums.size() - WINDOW_SZ; i++) {
        long *suffix = &nums.data()[i];
        if (!find_valid(suffix)) {
            target = suffix[WINDOW_SZ];
            break;
        }
    }

    if (target == -1)
        throw std::runtime_error("no invalid target number found");

    // find the weakness
    for (size_t i = 0; i < nums.size(); i++) {
        for (size_t j = 0; j < nums.size(); j++) {

            // this is way less efficient than it could be;
            // we could use only a doubly nested loop by just
            // adding up numbers until it exceeds the target
            long subrange_sum = 0;
            long max = 0, min = INT_MAX;
            for (size_t k = i; k <= j; k++) {
                long num = nums[k];
                subrange_sum += num;
                max = std::max(max, num);
                min = std::min(min, num);
            }

            if (subrange_sum == target) {
                long start = nums[i], end = nums[j];
                std::cout
                    << "Found weakness:\n"
                    << "  " << start << " + ... + " << end << " = " << target << '\n'
                    << "  Range: [" << min << ", " << max << "]; "
                    << "min + max = " << min + max << '\n';

                return 0;
            }
        }
    }

    throw std::runtime_error("no weakness found");
}
