#include <unordered_map> // for unordered_map
#include <stdexcept> // for runtime_error
#include <iostream> // for cout, istream
#include <utility> // for move
#include <fstream> // for ifstream
#include <sstream> // for istringstream
#include <cstdint> // for uint64_t, uint16_t, uint8_t
#include <cstddef> // for size_t
#include <vector> // for vector
#include <string> // for string

#define MAX_WORD_SIZE 15

void get_word(std::istream& is, char *tmp) {
    is.width(MAX_WORD_SIZE);
    is >> tmp;
    if (strlen(tmp) >= MAX_WORD_SIZE - 1)
        throw std::runtime_error("word is too long");
}

std::string get_color(std::istream& is, char *tmp) {
    std::string color;
    get_word(is, tmp);
    color += tmp;
    color += ' ';
    get_word(is, tmp);
    color += tmp;
    return color; // does this need std::move? stack overflow says probably not
}

typedef uint16_t ColorId;

struct BagDependency {
    ColorId id;
    uint16_t qty;
};

typedef std::vector<BagDependency> BagDepList;

class BagData {
    std::unordered_map<std::string, ColorId> m_colors;
    std::vector<BagDepList> m_deps;

public:

    BagData(): m_colors{}, m_deps{} {}

    size_t size() const {
        size_t size1 = m_colors.size();
        size_t size2 = m_deps.size();
        if (size1 != size2)
            throw std::runtime_error("invariant borked, the lengths are bad");
        return size1;
    }

    const BagDepList& get_deps(ColorId id) const {
        return m_deps[id];
    }

    ColorId get_or_new_id(const std::string& name) {
        {
            auto search = m_colors.find(name);
            if (search != m_colors.end())
                return search->second;
        }
        ColorId id = m_deps.size();
        m_deps.push_back(BagDepList());
        m_colors[name] = id;
        return id;
    }

    void add_deps(ColorId id, BagDepList deps) {
        BagDepList& deps_vec = m_deps[id];
        if (!deps_vec.empty())
            throw std::runtime_error("dependencies have already been added");
        deps_vec = std::move(deps);
    }

    void compute_quantity(uint64_t cache[], ColorId id) const {
        if (cache[id] > 0) return;
        uint64_t quantity = 1;
        for (BagDependency dep : m_deps[id]) {
            compute_quantity(cache, dep.id);
            quantity += cache[dep.id] * dep.qty;
        }
        cache[id] = quantity;
    }

    uint64_t compute_quantity(ColorId id) const {
        std::vector<uint64_t> cache(size());
        compute_quantity(cache.data(), id);
        return cache[id];
    }
};

void parse_line(BagData& bags, const std::string& line, char *tmp) {
    std::istringstream is(line);

    ColorId main_id = bags.get_or_new_id(get_color(is, tmp));
    get_word(is, tmp); // "bags"
    get_word(is, tmp); // "contain"

    BagDepList deps;
    for (;;) {
        BagDependency dep;
        is >> dep.qty;
        if (!is.good()) break; // halt if it was EOF or the word "no"
        dep.id = bags.get_or_new_id(get_color(is, tmp));
        deps.push_back(dep);
        get_word(is, tmp); // "bags," "bag," "bags." "bag."
    }

    bags.add_deps(main_id, std::move(deps));
}

int main(int argc, char **argv) {
    if (argc != 2)
        throw std::runtime_error("no file name provided");

    // parse the input file

    BagData bags;
    {
        std::ifstream infile(argv[1]);
        char tmp[MAX_WORD_SIZE];
        std::string line;

        while (std::getline(infile, line))
            parse_line(bags, line, tmp);
    }

    size_t n_colors = bags.size();
    ColorId shiny_gold = bags.get_or_new_id("shiny gold");

    if (shiny_gold >= n_colors)
        throw std::runtime_error("no shiny gold bag found");

    std::cout << "ID of shiny gold bag: " << shiny_gold << '\n';

    // construct a reverse dependency graph

    std::vector<std::vector<ColorId>> rev_deps(n_colors);

    for (ColorId id = 0; id < n_colors; id++)
        for (BagDependency dep : bags.get_deps(id))
            rev_deps[dep.id].push_back(id);

    // use DFS to find bags that transitively contain the shiny gold one

    int n_reachable = 0;
    {
        std::vector<bool> reachable(n_colors);
        std::vector<ColorId> frontier = {shiny_gold};

        while (!frontier.empty()) {
            ColorId id = frontier.back();
            frontier.pop_back();

            if (!reachable[id]) {
                reachable[id] = true;
                n_reachable++;
                for (ColorId rev_dep : rev_deps[id])
                    frontier.push_back(rev_dep);
            }
        }
    }

    std::cout
        << "  Number of other kinds of bags transitively containing it: "
        // subtract 1, because the spec requires we ignore the gold bag itself
        << n_reachable - 1 << '\n';

    uint64_t quantity = bags.compute_quantity(shiny_gold);

    std::cout
        << "  Quantity of bags that must be transitively contained in it: "
        << quantity - 1 << '\n';
}
