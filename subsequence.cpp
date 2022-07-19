#include <vector>
#include <string>
#include <iostream>
#include <map>
#include <set>
#include <cstring>
#include <cassert>

struct DASG_N {
    using StateId = int;
    using Letter = int;
    using Word = std::vector<Letter>;
    //using Letter = char;
    //using Word   = std::string;
    using State = std::map<Letter, StateId>;
    struct Substring {
        Letter const* data;
        int           size;
    };
    struct Suffix {
        int word_index;
        int sub_start;
        bool operator<(Suffix const& rhs) const { return std::make_pair(word_index, sub_start) < std::make_pair(rhs.word_index, rhs.sub_start); }
    };
    using R_Set = std::set<Suffix>;
    Substring substring_from_suffix(Suffix const& suff) {
        Substring ret;
        auto& w = words[suff.word_index];
        ret.data = w.data() + suff.sub_start;
        ret.size = (int)w.size() - suff.sub_start;
        return ret;
    }
    void add_transition(StateId s, Letter c, StateId next) {
        states[s][c] = next;
    }
    DASG_N(std::vector<DASG_N::Word> const& words) : words(words), size((int)words.size()) {
        for (auto const& w : words) f += w.size();
        states.resize(f + 1);
        Dj.resize(size);
        for (int i = 0, start = 0; i < size; ++i) {
            Dj[i] = words[i].size();
            dasg_1_starts.push_back(start);
            make_dasg_1(words[i], start);
            start += words[i].size();
        }
        dictionary[R_Set{}] = f;
        std::vector<int> positions(size, 0);
        starting_state = merge(positions);
        // remove Dj states
        for (int i = 0; i < size; ++i) {
            for (int j = 0; j < Dj[i]; ++j) {
                states[dasg_1_starts[i] + j].clear();
                states[dasg_1_starts[i] + j][-1] = -1;
            }
        }
    }
    void make_step_by_x_if_can(int& pos, int i, Letter x) {
        if (pos == (int)words[i].size()) return;
        auto const& s = states[dasg_1_starts[i] + pos];
        auto it = s.find(x);
        if (it == s.end() || it->second == f) pos = (int)words[i].size();
        else pos = it->second - dasg_1_starts[i];
    }
    StateId merge(std::vector<int> const& positions) {
        //std::cout << "pos:"; for (auto e : positions) std::cout << " " << e; std::cout << "\n";
        //print_me();
        assert(positions.size() == size);
        // мы тут предполагаем что нет повторяющихся строк во входе,
        // по идее надо просто (todo) отфильтровать в самом начале, но пока что лень
        int n_nonfinished = 0;
        int not_null_i = -1;
        // positions[i] == words[i].size() эквивалентно тому что на i-м месте стоит пусто
        for (int i = 0; i < size; ++i) {
            if (positions[i] < words[i].size()) {
                ++n_nonfinished;
                not_null_i = i;
            }
        }

        if (n_nonfinished == 0) return f;

        R_Set rset = make_r_set(positions);
        //for (auto e : rset) std::cout << ", " << e.sub_start << " " << e.word_index; std::cout << "\n";
        {
            auto it = dictionary.find(rset);
            if (it != dictionary.end()) {
                //std::cout << "found state\n";
                return it->second;
            }
        }

        if (n_nonfinished == 1) {
            int pos = positions[not_null_i];
            if (pos < Dj[not_null_i]) Dj[not_null_i] = pos;
            //std::cout << "only one nonfinished\n";
            return dasg_1_starts[not_null_i] + pos;
        }

        StateId s = states.size(); states.emplace_back();
        dictionary[rset] = s;
        for (int i = 0; i < size; ++i) {
            int pos = positions[i];
            if (pos == words[i].size()) continue;

            StateId local_state = dasg_1_starts[i] + pos;
            for (auto [x, next] : states[local_state]) {
                auto it = states[s].find(x);
                if (it != states[s].end()) continue;
                auto q = positions;
                for (int j = 0; j < q.size(); ++j) make_step_by_x_if_can(q[j], j, x);
                states[s][x] = merge(q);
            }
        }
        return s;
    }
    bool check_suff1_in_suff2(Suffix const& suff1, Suffix const& suff2) {
        auto s = substring_from_suffix(suff1);
        // тут я надеюсь что состояния построенные в начале никуда не пропадут,
        // и что можно проверить является ли строка подстрокой суффиксa
        // просто начав с состояния соответствующему началу этого суффикса
        return walk_from_state(s.data, s.size, dasg_1_starts[suff2.word_index] + suff2.sub_start);
    }
    R_Set make_r_set(std::vector<int> const& starts) {
        assert((int)starts.size() == size);
        std::vector<Suffix> o;
        for (int i = 0; i < starts.size(); ++i) {
            Suffix next;
            next.sub_start  = starts[i];
            next.word_index = i;
            bool next_was_added = false;
            if (starts[i] == (int)words[i].size()) goto skip; // пропускаем пустые
            for (int j = 0; j < o.size(); ++j) if (check_suff1_in_suff2(next, o[j])) goto skip;
            for (int j = 0; j < o.size(); ++j) if (check_suff1_in_suff2(o[j], next)) {
                if (next_was_added) {
                    o[j] = o.back();
                    o.pop_back();
                } else {
                    o[j] = next;
                    next_was_added = true;
                }
            }
            if (!next_was_added) o.push_back(next);
            skip:;
        }
        R_Set ret;
        for (auto& s : o) ret.insert(s);
        return ret;
    }
    void make_dasg_1(Word const& word, StateId start) {
        // DASG занимает состояния от start до (start + n-1) включительно, и ещё общее конечное состояние f
        int n = (int)word.size();
        assert(n > 0);

        std::map<Letter, StateId> d;
        StateId end = start + n-1;
        add_transition(end, word[n-1], f);
        for (StateId i = n-1; i > 0; --i) {
            add_transition(start + i-1, word[i-1], start + i);
        }

        for (StateId i = (int)word.size(); i > 0; --i) {
            auto c = word[i-1];
            auto s = start + i-1;
            d[c] = s;
            for (auto& [l, next] : d) {
                if (l != c) add_transition(s, l, next == end ? f : next+1);
            }
        }
    };
    bool walk_from_state(Letter const* data, int size, StateId state) const {
        if (size == 0) return true;
        if (states.empty()) return size == 0;
        StateId it = state;
        for (int i = 0; i < size; ++i) {
            auto c = data[i];
            auto t = states[it].find(c);
            if (t == states[it].end()) return false;
            it = t->second;
        }
        return true;
    }
    bool check(Word const& word) const {
        return walk_from_state(&word[0], (int)word.size(), starting_state);
    };
    void print_me() {
        std::cout << "start=" << starting_state << "\n";
        int i = 0;
        for (auto const& s : states) {
            std::cout << i++ << ":";
            for (auto [l, n] : s) {
                std::cout << " " << (char)l << "->" << n;
            }
            std::cout << "\n";
        }
    }
    int starting_state = 0;
    int f = 0;
    int size;
    std::vector<int> Dj;
    std::map<R_Set, StateId> dictionary;
    std::vector<DASG_N::Word> const& words;
    std::vector<StateId> dasg_1_starts;
    std::vector<State> states;
};

DASG_N::Word convert(char* s) {
    DASG_N::Word ret;
    ret.reserve(strlen(s) + 1);
    while (*s) ret.push_back(*s++);
    return ret;
}

int main(int n, char** args) {
    if (n <= 2) { std::cout << "gimme at least two cmdargs\n"; return 0; }

    int total_size = 1;
    std::vector<DASG_N::Word> words;
    words.reserve(n - 2);
    for (int i = 2; i < n; ++i) {
        words.emplace_back(convert(args[i]));
    }
    {int i = 2; for (auto& w : words) std::cout << w.size() << ": '" << args[i++] << "'\n";}
    DASG_N s(words);
    //s.print_me();
    bool check = s.check(convert(args[1]));
    std::cout <<
              "  '" <<args[1]<< "'\n"
              "is" <<(check ? "" : "n't")<<
              " a subsequence of one of a \n";
    for (int i = 2; i < n; ++i) {
        std::cout << "  '" <<args[i]<< "'\n";
    }
    for (int i = 2; i < n; ++i) {
        std::string args_i = args[i];
        char* c = args[1];
        for (char& it : args_i) {
            if (it != *c) it = '_';
            else ++c;
        }
        if (check && *c) for (char& it : args_i) it = '_';
        std::cout << "\n  '" << args_i << "'";
    }
    return 0;
};
