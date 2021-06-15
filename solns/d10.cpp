#include <algorithm> // for sort
#include <iostream> // for cout
#include <fstream> // for ifstream
#include <cstddef> // for size_t
#include <cstdint> // for uint64_t
#include <vector> // for vector
#include <memory> // for unique_ptr

void report_differences(const std::vector<int>& nums) {
    int delta_counts[3] = {0, 0, 0};
    for (size_t i = 1; i < nums.size(); i++) {
        int delta = nums[i] - nums[i - 1];
        if (1 <= delta && delta <= 3)
            delta_counts[delta - 1]++;
        else
            throw std::runtime_error("no connecting joltage");
    }

    std::cout
        << "Differences of 1 jolt: " << delta_counts[0] << '\n'
        << "Differences of 2 jolts: " << delta_counts[1] << '\n'
        << "Differences of 3 jolts: " << delta_counts[2] << '\n'
        << delta_counts[0] << " * " << delta_counts[2] << " = "
        << delta_counts[0] * delta_counts[2] << '\n';
}

void report_paths(const std::vector<int>& nums) {
    int max = nums.back();
    std::vector<uint64_t> paths(max + 1);
    for (int idx : nums) {
        if (idx == 0) {
            paths[idx] = 1;
        } else {
            uint64_t total = 0;
            total += idx < 1 ? 0 : paths[idx - 1];
            total += idx < 2 ? 0 : paths[idx - 2];
            total += idx < 3 ? 0 : paths[idx - 3];
            paths[idx] = total;
        }
    }

    std::cout << "Number of paths to the final adapter: " << paths[max] << '\n';
}

int main(int argc, char **argv) {
    if (argc != 2)
        throw std::runtime_error("no file name supplied");

    std::vector<int> nums = {0};
    {
        std::ifstream infile(argv[1]);
        for (int a; infile >> a;)
            nums.push_back(a);
    }
    std::sort(nums.begin(), nums.end());
    nums.push_back(nums.back() + 3);

    report_differences(nums);
    report_paths(nums);
}
