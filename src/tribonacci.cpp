#include <chrono>
#include <cstdint>
#include <cctype>
#include <iostream>
#include <limits>
#include <string>
#include <vector>
#include <cstdlib>
#include <algorithm>

using namespace std;

static const int64_t MOD = 1'000'000'007;

// ============================================================
// Timer: prints elapsed time to stderr when leaving the scope
// ============================================================
class LogDuration {
public:
    explicit LogDuration(string msg)
        : msg_(std::move(msg)), start_(chrono::steady_clock::now()) {}

    ~LogDuration() {
        auto finish = chrono::steady_clock::now();
        auto dur = chrono::duration_cast<chrono::milliseconds>(finish - start_).count();
        cerr << msg_ << ": " << dur << " ms" << endl;
    }

private:
    string msg_;
    chrono::steady_clock::time_point start_;
};

#define LOG_DURATION(msg) LogDuration UNIQUE_VAR_NAME(__LINE__)(msg)
#define UNIQUE_VAR_NAME(line) UNIQUE_VAR_NAME_IMPL(line)
#define UNIQUE_VAR_NAME_IMPL(line) logdur_##line

// ============================================================
// Helpers
// ============================================================
static bool WillOverflowAdd3(int64_t a, int64_t b, int64_t c) {
    __int128 s = (__int128)a + b + c;
    return s > numeric_limits<int64_t>::max() || s < numeric_limits<int64_t>::min();
}

// Result of one method:
// - exact_ok=true  => exact is valid (exact Tribonacci in int64)
// - exact_ok=false => exact is impossible (overflow), mod is still valid
struct MethodResult {
    bool exact_ok = true;
    int overflow_at = -1;     // first n where exact became impossible (if we know it)
    int64_t exact = 0;        // valid if exact_ok
    int64_t mod = 0;          // always: T(n) % MOD

    // What we compare across different methods:
    // If exact exists => compare exact % MOD
    // Else            => compare mod
    int64_t comparable() const {
        return exact_ok ? (exact % MOD) : mod;
    }
};

// ============================================================
// Method 1) Iteration (rolling 3 values)
// Time: O(N), Memory: O(1)
// Exact until overflow, then mod.
// ============================================================
MethodResult Trib_Iter_Auto(int64_t n) {
    MethodResult r;

    if (n <= 1) { r.exact = 0; r.mod = 0; return r; }
    if (n == 2) { r.exact = 1; r.mod = 1; return r; }

    // exact chain
    int64_t t0 = 0, t1 = 0, t2 = 1;

    // mod chain
    int64_t m0 = 0, m1 = 0, m2 = 1;

    for (int64_t k = 3; k <= n; ++k) {
        // mod step always possible
        int64_t mnext = (m0 + m1 + m2) % MOD;
        m0 = m1; m1 = m2; m2 = mnext;

        // exact step while possible
        if (r.exact_ok) {
            if (WillOverflowAdd3(t0, t1, t2)) {
                r.exact_ok = false;
                r.overflow_at = (int)k;
            } else {
                int64_t next = t0 + t1 + t2;
                t0 = t1; t1 = t2; t2 = next;
            }
        }
    }

    if (r.exact_ok) r.exact = t2;
    r.mod = m2;
    return r;
}

// ============================================================
// Method 2) DP Table (tabulation)
// Time: O(N), Memory: O(N)
// Exact until overflow, then mod.
// (Table is useful if you want all T(0..n), not only T(n).)
// ============================================================
MethodResult Trib_Table_Auto(int64_t n) {
    MethodResult r;

    if (n <= 1) { r.exact = 0; r.mod = 0; return r; }
    if (n == 2) { r.exact = 1; r.mod = 1; return r; }

    vector<int64_t> modv((size_t)n + 1, 0);
    modv[0] = 0; modv[1] = 0; modv[2] = 1;

    vector<int64_t> exactv;
    exactv.resize((size_t)n + 1, 0);
    exactv[0] = 0; exactv[1] = 0; exactv[2] = 1;

    for (int64_t k = 3; k <= n; ++k) {
        // mod table always
        modv[(size_t)k] = (modv[(size_t)k - 1] + modv[(size_t)k - 2] + modv[(size_t)k - 3]) % MOD;

        // exact table while possible
        if (r.exact_ok) {
            int64_t a = exactv[(size_t)k - 1];
            int64_t b = exactv[(size_t)k - 2];
            int64_t c = exactv[(size_t)k - 3];
            if (WillOverflowAdd3(a, b, c)) {
                r.exact_ok = false;
                r.overflow_at = (int)k;
            } else {
                exactv[(size_t)k] = a + b + c;
            }
        }
    }

    if (r.exact_ok) r.exact = exactv[(size_t)n];
    r.mod = modv[(size_t)n];
    return r;
}

// ============================================================
// Method 3) Matrix fast power
// Time: O(log N), Memory: O(1)
// Exact attempt may overflow earlier due to intermediate values,
// then we fall back to mod.
// ============================================================
struct Mat3Exact {
    int64_t a[3][3]{};
};

static Mat3Exact IdentityExact() {
    Mat3Exact I;
    for (int i = 0; i < 3; ++i) I.a[i][i] = 1;
    return I;
}

static bool MulExactOverflow(const Mat3Exact& x, const Mat3Exact& y, Mat3Exact& out) {
    for (int i = 0; i < 3; ++i) {
        for (int j = 0; j < 3; ++j) {
            __int128 sum = 0;
            for (int k = 0; k < 3; ++k) {
                sum += (__int128)x.a[i][k] * y.a[k][j];
            }
            if (sum > numeric_limits<int64_t>::max() || sum < numeric_limits<int64_t>::min()) {
                return true;
            }
            out.a[i][j] = (int64_t)sum;
        }
    }
    return false;
}

static bool PowExactOverflow(Mat3Exact base, int64_t p, Mat3Exact& out) {
    Mat3Exact res = IdentityExact();
    while (p > 0) {
        if (p & 1) {
            Mat3Exact tmp;
            if (MulExactOverflow(res, base, tmp)) return true;
            res = tmp;
        }
        p >>= 1;
        if (p > 0) {
            Mat3Exact tmp;
            if (MulExactOverflow(base, base, tmp)) return true;
            base = tmp;
        }
    }
    out = res;
    return false;
}

// mod matrix
struct Mat3Mod {
    int64_t a[3][3]{};
    static Mat3Mod Identity() {
        Mat3Mod I;
        for (int i = 0; i < 3; ++i) I.a[i][i] = 1;
        return I;
    }
};

static Mat3Mod MulMod(const Mat3Mod& x, const Mat3Mod& y) {
    Mat3Mod r;
    for (int i = 0; i < 3; ++i) {
        for (int j = 0; j < 3; ++j) {
            __int128 sum = 0;
            for (int k = 0; k < 3; ++k) {
                sum += (__int128)x.a[i][k] * y.a[k][j];
            }
            r.a[i][j] = (int64_t)(sum % MOD);
        }
    }
    return r;
}

static Mat3Mod PowMod(Mat3Mod base, int64_t p) {
    Mat3Mod res = Mat3Mod::Identity();
    while (p > 0) {
        if (p & 1) res = MulMod(res, base);
        base = MulMod(base, base);
        p >>= 1;
    }
    return res;
}

static int64_t Trib_Mat_Mod(int64_t n) {
    if (n <= 1) return 0;
    if (n == 2) return 1;

    Mat3Mod M;
    // [T(n),T(n-1),T(n-2)]^T = M * [T(n-1),T(n-2),T(n-3)]^T
    M.a[0][0] = 1; M.a[0][1] = 1; M.a[0][2] = 1;
    M.a[1][0] = 1; M.a[1][1] = 0; M.a[1][2] = 0;
    M.a[2][0] = 0; M.a[2][1] = 1; M.a[2][2] = 0;

    Mat3Mod P = PowMod(M, n - 2);
    return P.a[0][0];
}

MethodResult Trib_Mat_Auto(int64_t n) {
    MethodResult r;

    if (n <= 1) { r.exact = 0; r.mod = 0; return r; }
    if (n == 2) { r.exact = 1; r.mod = 1; return r; }

    // exact attempt
    Mat3Exact M{};
    M.a[0][0] = 1; M.a[0][1] = 1; M.a[0][2] = 1;
    M.a[1][0] = 1; M.a[1][1] = 0; M.a[1][2] = 0;
    M.a[2][0] = 0; M.a[2][1] = 1; M.a[2][2] = 0;

    Mat3Exact P{};
    bool overflow = PowExactOverflow(M, n - 2, P);

    if (!overflow) {
        r.exact_ok = true;
        r.exact = P.a[0][0];
    } else {
        r.exact_ok = false;
        r.overflow_at = -1; // exact overflow inside matrix multiplications
    }

    r.mod = Trib_Mat_Mod(n);
    return r;
}

// ============================================================
// UI helpers: header / parsing / clear
// ============================================================
void PrintHeader() {
    cout << "Трибоначчи T(n).\n"
            "Каждый метод считает ТОЧНО в int64, пока не переполнится.\n"
            "Если переполнение — выводит значение по модулю " << MOD << " (это уже НЕ точное число).\n"
            "Ввод: 1000000 или 1 000 000 или 1_000_000.\n"
            "Управление:\n"
            "  Enter      - очистить экран (шапка остаётся)\n"
            "  q / exit   - выход\n\n" << flush;
}

bool ParseLine(const string& line, int64_t& n_out, string& out_cmd) {
    out_cmd.clear();

    auto is_space = [](unsigned char c) { return std::isspace(c); };

    size_t L = 0;
    while (L < line.size() && is_space((unsigned char)line[L])) ++L;

    size_t R = line.size();
    while (R > L && is_space((unsigned char)line[R - 1])) --R;

    string trimmed = line.substr(L, R - L);

    if (trimmed.empty()) { out_cmd = "clean"; return false; }

    if (trimmed == "q" || trimmed == "quit" || trimmed == "exit") {
        out_cmd = "exit";
        return false;
    }

    if (trimmed == "clean" || trimmed == "cls" || trimmed == "clear") {
        out_cmd = "clean";
        return false;
    }

    string cleaned;
    for (char ch : trimmed) {
        if (ch == ' ' || ch == '_' || ch == '\'') continue;
        cleaned.push_back(ch);
    }
    if (cleaned.empty()) return false;

    for (char ch : cleaned) {
        if (!isdigit((unsigned char)ch)) return false;
    }

    try {
        long long v = stoll(cleaned);
        if (v < 0) return false;
        n_out = (int64_t)v;
        return true;
    } catch (...) {
        return false;
    }
}

void ClearScreen() {
#ifdef _WIN32
    system("cls");
#else
    system("clear");
#endif
}

static void PrintOne(const string& title, const MethodResult& r) {
    cout << title << ":\n";
    if (r.exact_ok) {
        cout << "  exact int64     = " << r.exact << "\n";
        cout << "  exact % MOD     = " << (r.exact % MOD) << "\n";
    } else {
        if (r.overflow_at != -1) {
            cout << "  exact int64     = (overflow from n = " << r.overflow_at << ")\n";
        } else {
            cout << "  exact int64     = (overflow inside method)\n";
        }
        cout << "  mod (NOT exact) = " << r.mod << "\n";
    }
    cout << "  compare value   = " << r.comparable() << "\n";
}

static string FormatWithSpaces(int64_t x) {
    // формат: 1000000 -> "1 000 000"
    string s = to_string(x);
    string out;
    int cnt = 0;
    for (int i = (int)s.size() - 1; i >= 0; --i) {
        out.push_back(s[i]);
        ++cnt;
        if (cnt == 3 && i != 0) {
            out.push_back(' ');
            cnt = 0;
        }
    }
    reverse(out.begin(), out.end());
    return out;
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    PrintHeader();

    // DP table allocates O(n) memory; limit it so user can't kill RAM.
    const int64_t TABLE_LIMIT = 2'000'000;

    while (true) {
        const string prompt = "Введите n (или clean/q/Enter): ";
    	cout << prompt << flush;

        string line;
        if (!getline(cin, line)) break;
        
        // стираем строку ввода: prompt + на строку выше
		cout << "\x1b[1A\x1b[2K\r" << flush;
		cout << "\x1b[1A\x1b[2K\r" << flush;

        int64_t n = 0;
        string cmd;
        if (!ParseLine(line, n, cmd)) {
            if (cmd == "exit") break;
            if (cmd == "clean") {
                ClearScreen();
                PrintHeader();
                continue;
            }
            cout << "Ошибка: введите целое n >= 0 (можно с пробелами/_/'), либо clean, либо q.\n\n";
            continue;
        }

        cout << "\nВы ввели n = " << FormatWithSpaces(n) << "\n\n";

        MethodResult it, tb, mx;
        bool table_ran = false;

        {
            LOG_DURATION("1) Iteration (exact->mod)");
            it = Trib_Iter_Auto(n);
        }

        if (n <= TABLE_LIMIT) {
            LOG_DURATION("2) DP table (exact->mod)");
            tb = Trib_Table_Auto(n);
            table_ran = true;
        } else {
            cerr << "2) DP table: skipped (n too large -> too much memory)\n";
        }

        {
            LOG_DURATION("3) Matrix (exact->mod)");
            mx = Trib_Mat_Auto(n);
        }

        cout << "T(" << FormatWithSpaces(n) << ") results:\n\n";

        PrintOne("1) Iteration", it);
        cout << "\n";
        if (table_ran) {
            PrintOne("2) DP table", tb);
            cout << "\n";
        } else {
            cout << "2) DP table: skipped\n\n";
        }
        PrintOne("3) Matrix", mx);

        // Compare by "comparable value" (exact%MOD or mod)
        int64_t c_it = it.comparable();
        int64_t c_mx = mx.comparable();
        bool ok = (c_it == c_mx) && (!table_ran || c_it == tb.comparable());

        cout << "\n" << (ok ? "OK: compare values match (exact%MOD == mod).\n\n"
                           : "WARNING: compare values differ.\n\n");
    }

    cout << "Выход.\n";
    return 0;
}
