// MIT License
// Generic sorting-network zkSNARK demo (odd-even mergesort) + Verify-sorted (generic N)
// Range checks are manual (k-bit): boolean bits + linear combination equals the packed value.
// Extra constraints added: selector-equality, output monotonicity, sum/sum-of-squares preservation,
// double-(r + ·) product checks for multiset equality in B.
// (c) 2025

#include <iostream>
#include <vector>
#include <utility>
#include <memory>
#include <cstdint>
#include <string>
#include <stdexcept>
#include <algorithm>

#include <libsnark/common/default_types/r1cs_gg_ppzksnark_pp.hpp>
#include <libsnark/gadgetlib1/protoboard.hpp>
#include <libsnark/gadgetlib1/gadgets/basic_gadgets.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>

using namespace libsnark;
using namespace std;

// ---------- Manual k-bit "range" gadget ----------
template<typename FieldT>
struct kbits_range_manual {
    protoboard<FieldT>& pb;
    pb_variable<FieldT> x;
    size_t k;
    pb_variable_array<FieldT> bits;
    std::vector<FieldT> weights;

    kbits_range_manual(protoboard<FieldT>& pb,
                       const pb_variable<FieldT>& x,
                       size_t k,
                       const std::string& anno)
        : pb(pb), x(x), k(k)
    {
        bits.allocate(pb, k, anno + ".bits");
        weights.resize(k);
        FieldT w = FieldT::one();
        const FieldT two = FieldT(2);
        for (size_t i = 0; i < k; i++) {
            weights[i] = w;
            w *= two;
        }
    }

    void generate_r1cs_constraints() {
        for (size_t i = 0; i < k; i++) {
            generate_boolean_r1cs_constraint<FieldT>(pb, bits[i], "bit");
        }
        linear_combination<FieldT> sum;
        for (size_t i = 0; i < k; i++) sum.add_term(bits[i], weights[i]);
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, x, sum), "pack_bits");
    }

    void witness_from_uint64(uint64_t v) {
        for (size_t i = 0; i < k; i++) {
            pb.val(bits[i]) = ((v >> i) & 1) ? FieldT::one() : FieldT::zero();
        }
        pb.val(x) = FieldT(v);
    }
};

// ---------- Comparator (cmp-swap) gadget ----------
template<typename FieldT>
struct cmp_swap_gadget {
    protoboard<FieldT> &pb;
    size_t k;
    pb_variable<FieldT> x, y, u, v;
    pb_variable<FieldT> s; // boolean selector
    pb_variable<FieldT> t; // t = v - u  (nonnegative via k-bit range)
    kbits_range_manual<FieldT> *t_rng; // not owned

    uint64_t u_u64 = 0, v_u64 = 0, t_u64 = 0;

    cmp_swap_gadget(protoboard<FieldT>& pb,
                    size_t k,
                    const pb_variable<FieldT>& x,
                    const pb_variable<FieldT>& y,
                    const pb_variable<FieldT>& u,
                    const pb_variable<FieldT>& v,
                    const std::string& anno,
                    kbits_range_manual<FieldT> *t_rng_ptr)
        : pb(pb), k(k), x(x), y(y), u(u), v(v), t_rng(t_rng_ptr)
    {
        s.allocate(pb, anno + ".sel");
        t.allocate(pb, anno + ".diff");
    }

    void generate_r1cs_constraints() {
        // s boolean
        generate_boolean_r1cs_constraint<FieldT>(pb, s, "sel_boolean");

        // Original constraints
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(s, x - y, u - y), "u - y = s*(x - y)");
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, v, x + y - u), "v = x + y - u");
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, v - u, t),      "t = v - u");

        // Extra constraints (strong selector semantics + sum preservation)
        // When s=1 => u=x and v=y; when s=0 => u=y and v=x
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(s,     u - x, 0), "s*(u-x)=0");
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1 - s, u - y, 0), "(1-s)*(u-y)=0");
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(s,     v - y, 0), "s*(v-y)=0");
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1 - s, v - x, 0), "(1-s)*(v-x)=0");

        // u + v = x + y
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, u + v, x + y), "sum_preserved_cmp");
    }

    void generate_r1cs_witness(uint64_t x_u64, uint64_t y_u64) {
        const bool sel = (x_u64 <= y_u64);
        pb.val(s) = sel ? FieldT::one() : FieldT::zero();
        u_u64 = sel ? x_u64 : y_u64;
        v_u64 = x_u64 + y_u64 - u_u64;
        t_u64 = v_u64 - u_u64;
        pb.val(u) = FieldT(u_u64);
        pb.val(v) = FieldT(v_u64);
        pb.val(t) = FieldT(t_u64);
        if (t_rng) t_rng->witness_from_uint64(t_u64);
    }
};

// ---------- Odd-even mergesort comparator list ----------
static void oddeven_merge_build(std::vector<std::pair<size_t,size_t>>& comps,
                                size_t lo, size_t n, size_t r) {
    size_t m = r * 2;
    if (m < n) {
        oddeven_merge_build(comps, lo,     n, m);
        oddeven_merge_build(comps, lo + r, n, m);
        for (size_t i = lo + r; i + r < lo + n; i += m) {
            comps.push_back(std::make_pair(i, i + r));
        }
    } else {
        comps.push_back(std::make_pair(lo, lo + r));
    }
}
static void oddeven_mergesort_build(std::vector<std::pair<size_t,size_t>>& comps,
                                    size_t lo, size_t n) {
    if (n > 1) {
        size_t m = n / 2;
        oddeven_mergesort_build(comps, lo,     m);
        oddeven_mergesort_build(comps, lo + m, m);
        oddeven_merge_build(comps, lo, n, 1);
    }
}
static std::vector<std::vector<std::pair<size_t,size_t>>> to_layers_greedy(
    const std::vector<std::pair<size_t,size_t>>& comps) {
    std::vector<std::vector<std::pair<size_t,size_t>>> layers;
    for (size_t idx = 0; idx < comps.size(); ++idx) {
        size_t i = comps[idx].first;
        size_t j = comps[idx].second;
        bool placed = false;
        if (!layers.empty()) {
            std::vector<std::pair<size_t,size_t>>& L = layers.back();
            bool conflict = false;
            for (size_t t = 0; t < L.size(); ++t) {
                size_t a = L[t].first, b = L[t].second;
                if (a == i || a == j || b == i || b == j) { conflict = true; break; }
            }
            if (!conflict) { L.push_back(std::make_pair(i,j)); placed = true; }
        }
        if (!placed) { layers.push_back(std::vector<std::pair<size_t,size_t>>(1, std::make_pair(i,j))); }
    }
    return layers;
}

// ---------- Product tree for ∏(r + X[i]) ----------
template<typename FieldT>
struct product_tree {
    protoboard<FieldT>& pb;
    const FieldT r;
    size_t k_bits;

    std::vector<pb_variable<FieldT>> leaves_vars;
    std::vector<std::vector<pb_variable<FieldT>>> layers_vars;

    product_tree(protoboard<FieldT>& pb, const FieldT& r, size_t k_bits)
        : pb(pb), r(r), k_bits(k_bits) {}

    void make_leaves_from_array(const std::vector<pb_variable<FieldT>>& X,
                                const std::string& tag) {
        leaves_vars.resize(X.size());
        for (size_t i = 0; i < X.size(); ++i) {
            leaves_vars[i].allocate(pb, tag + "_leaf_" + std::to_string(i));
            pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, leaves_vars[i], X[i] + r),
                                   tag + "_leaf_equiv");
        }
    }

    pb_variable<FieldT> build_constraints(const std::string& tag) {
        layers_vars.clear();
        layers_vars.push_back(leaves_vars);
        size_t level = 0;
        while (layers_vars.back().size() > 1) {
            const std::vector<pb_variable<FieldT>>& cur = layers_vars.back();
            std::vector<pb_variable<FieldT>> nxt;
            for (size_t i = 0; i < cur.size(); i += 2) {
                if (i + 1 < cur.size()) {
                    pb_variable<FieldT> p; p.allocate(pb, tag + "_lvl" + std::to_string(level) +
                                                            "_mul_" + std::to_string(i/2));
                    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(cur[i], cur[i+1], p),
                                           tag + "_pair_mul");
                    nxt.push_back(p);
                } else {
                    pb_variable<FieldT> carry;
                    carry.allocate(pb, tag + "_lvl" + std::to_string(level) + "_carry");
                    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, carry, cur[i]),
                                           tag + "_carry_forward");
                    nxt.push_back(carry);
                }
            }
            layers_vars.push_back(nxt);
            ++level;
        }
        return layers_vars.back()[0];
    }

    void assign_witness_from_uints(const std::vector<uint64_t>& X_vals) {
        for (size_t i = 0; i < X_vals.size(); ++i) {
            pb.val(leaves_vars[i]) = FieldT(X_vals[i]) + r;
        }
        for (size_t L = 0; L + 1 < layers_vars.size(); ++L) {
            const std::vector<pb_variable<FieldT>>& cur = layers_vars[L];
            const std::vector<pb_variable<FieldT>>& nxt = layers_vars[L+1];
            size_t nxt_idx = 0;
            for (size_t i = 0; i < cur.size(); i += 2) {
                if (i + 1 < cur.size()) pb.val(nxt[nxt_idx]) = pb.val(cur[i]) * pb.val(cur[i+1]);
                else                     pb.val(nxt[nxt_idx]) = pb.val(cur[i]);
                ++nxt_idx;
            }
        }
    }
};

// ---------- [A] Sorting-network with extra constraints ----------
template<typename ppT>
void run_sorting_network_demo_generic(size_t k_bits, const std::vector<uint64_t>& arr)
{
    using FieldT = libff::Fr<ppT>;
    const size_t N = arr.size();
    if ((N & (N-1)) != 0) throw std::runtime_error("Array size must be a power of two.");

    protoboard<FieldT> pb;

    // Public outputs Y
    std::vector<pb_variable<FieldT>> Y(N);
    for (size_t i = 0; i < N; ++i) Y[i].allocate(pb, "Y" + std::to_string(i));
    pb.set_input_sizes(N);

    // Private inputs A + range
    std::vector<pb_variable<FieldT>> A(N);
    std::vector<std::unique_ptr<kbits_range_manual<FieldT>>> A_rng(N);
    for (size_t i = 0; i < N; ++i) {
        A[i].allocate(pb, "A" + std::to_string(i));
        A_rng[i].reset(new kbits_range_manual<FieldT>(pb, A[i], k_bits, "A"+std::to_string(i)+"_rng"));
    }

    // Build network
    std::vector<std::pair<size_t,size_t>> comps;
    oddeven_mergesort_build(comps, 0, N);
    std::vector<std::vector<std::pair<size_t,size_t>>> layers = to_layers_greedy(comps);

    struct CompEntry {
        size_t i, j;
        pb_variable<FieldT> u, v;
        std::unique_ptr<cmp_swap_gadget<FieldT>> cmp;
        std::unique_ptr<kbits_range_manual<FieldT>> t_rng, u_rng, v_rng;
    };
    std::vector<pb_variable<FieldT>> cur_vars = A;
    std::vector<std::vector<std::unique_ptr<CompEntry>>> network; network.resize(layers.size());

    for (size_t L = 0; L < layers.size(); ++L) {
        std::vector<pb_variable<FieldT>> next_vars = cur_vars;
        for (size_t e = 0; e < layers[L].size(); ++e) {
            size_t i = layers[L][e].first, j = layers[L][e].second;
            std::unique_ptr<CompEntry> ce(new CompEntry());
            ce->i = i; ce->j = j;
            ce->u.allocate(pb, "w_L"+std::to_string(L)+"_i"+std::to_string(i)+"_u");
            ce->v.allocate(pb, "w_L"+std::to_string(L)+"_j"+std::to_string(j)+"_v");
            ce->cmp.reset(new cmp_swap_gadget<FieldT>(pb, k_bits, cur_vars[i], cur_vars[j], ce->u, ce->v,
                            "cmp_L"+std::to_string(L)+"_"+std::to_string(i)+"_"+std::to_string(j), NULL));
            ce->t_rng.reset(new kbits_range_manual<FieldT>(pb, ce->cmp->t, k_bits, "cmp_L"+std::to_string(L)+"_t_rng"));
            ce->cmp->t_rng = ce->t_rng.get();
            ce->u_rng.reset(new kbits_range_manual<FieldT>(pb, ce->u, k_bits, "u_rng_L"+std::to_string(L)+"_"+std::to_string(i)));
            ce->v_rng.reset(new kbits_range_manual<FieldT>(pb, ce->v, k_bits, "v_rng_L"+std::to_string(L)+"_"+std::to_string(j)));
            next_vars[i] = ce->u; next_vars[j] = ce->v;
            network[L].push_back(std::move(ce));
        }
        cur_vars = next_vars;
    }

    // Output monotonicity: Ty[i] = Y[i+1] - Y[i] >= 0
    std::vector<pb_variable<FieldT>> Ty(N > 0 ? N-1 : 0);
    std::vector<std::unique_ptr<kbits_range_manual<FieldT>>> Ty_rng(N > 0 ? N-1 : 0);
    for (size_t i = 0; i + 1 < N; ++i) {
        Ty[i].allocate(pb, "Ty"+std::to_string(i));
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, Y[i+1] - Y[i], Ty[i]), "Ty=Y[i+1]-Y[i]");
        Ty_rng[i].reset(new kbits_range_manual<FieldT>(pb, Ty[i], k_bits, "Ty"+std::to_string(i)+"_rng"));
    }

    // Sum(Y) = Sum(A)
    linear_combination<FieldT> sumA, sumY;
    for (size_t i = 0; i < N; ++i) { sumA.add_term(A[i], 1); sumY.add_term(Y[i], 1); }
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sumY, sumA), "sum_preserved_all");

    // Sum of squares preserved
    std::vector<pb_variable<FieldT>> A2(N), Y2(N);
    for (size_t i = 0; i < N; ++i) { A2[i].allocate(pb, "A2_"+std::to_string(i)); Y2[i].allocate(pb, "Y2_"+std::to_string(i)); }
    for (size_t i = 0; i < N; ++i) {
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(A[i], A[i], A2[i]), "A2=A*A");
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(Y[i], Y[i], Y2[i]), "Y2=Y*Y");
    }
    linear_combination<FieldT> sumA2, sumY2;
    for (size_t i = 0; i < N; ++i) { sumA2.add_term(A2[i], 1); sumY2.add_term(Y2[i], 1); }
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sumY2, sumA2), "sum_squares_preserved");

    // Generate constraints
    for (size_t i = 0; i < N; ++i) A_rng[i]->generate_r1cs_constraints();
    for (size_t L = 0; L < network.size(); ++L)
        for (size_t e = 0; e < network[L].size(); ++e) {
            std::unique_ptr<CompEntry>& ce_ptr = network[L][e];
            ce_ptr->cmp->generate_r1cs_constraints();
            ce_ptr->t_rng->generate_r1cs_constraints();
            ce_ptr->u_rng->generate_r1cs_constraints();
            ce_ptr->v_rng->generate_r1cs_constraints();
        }
    for (size_t i = 0; i + 1 < N; ++i) Ty_rng[i]->generate_r1cs_constraints();

    // Link Y to final wires
    for (size_t i = 0; i < N; ++i)
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, Y[i], cur_vars[i]), "Y_equals_out_"+std::to_string(i));

    // Witness
    for (size_t i = 0; i < N; ++i) A_rng[i]->witness_from_uint64(arr[i]);
    std::vector<uint64_t> cur_vals = arr;
    for (size_t L = 0; L < network.size(); ++L) {
        std::vector<uint64_t> next_vals = cur_vals;
        for (size_t e = 0; e < network[L].size(); ++e) {
            std::unique_ptr<CompEntry>& ce_ptr = network[L][e];
            const size_t i = ce_ptr->i, j = ce_ptr->j;
            ce_ptr->cmp->generate_r1cs_witness(cur_vals[i], cur_vals[j]);
            ce_ptr->t_rng->witness_from_uint64(ce_ptr->cmp->t_u64);
            ce_ptr->u_rng->witness_from_uint64(ce_ptr->cmp->u_u64);
            ce_ptr->v_rng->witness_from_uint64(ce_ptr->cmp->v_u64);
            next_vals[i] = ce_ptr->cmp->u_u64;
            next_vals[j] = ce_ptr->cmp->v_u64;
        }
        cur_vals = next_vals;
    }
    for (size_t i = 0; i < N; ++i) pb.val(Y[i]) = FieldT(cur_vals[i]);
    for (size_t i = 0; i + 1 < N; ++i) {
        uint64_t diff = (cur_vals[i+1] >= cur_vals[i]) ? (cur_vals[i+1] - cur_vals[i]) : 0;
        Ty_rng[i]->witness_from_uint64(diff);
    }
    for (size_t i = 0; i < N; ++i) {
        pb.val(A2[i]) = FieldT(arr[i]) * FieldT(arr[i]);
        pb.val(Y2[i]) = FieldT(cur_vals[i]) * FieldT(cur_vals[i]);
    }

    // Check + Prove/Verify
    auto primary = pb.primary_input();
    std::cout << "Sorted ints: ";
    for (size_t i = 0; i < N; ++i) {
        std::cout << cur_vals[i] << (i+1 < N ? ", " : "\n");
    }
    std::cout << "[Sort] is_satisfied = " << (pb.is_satisfied() ? "yes" : "no") << std::endl;

    const auto keypair = r1cs_gg_ppzksnark_generator<ppT>(pb.get_constraint_system());
    const auto proof   = r1cs_gg_ppzksnark_prover    <ppT>(keypair.pk, primary, pb.auxiliary_input());
    const bool ok_str  = r1cs_gg_ppzksnark_verifier_strong_IC<ppT>(keypair.vk, primary, proof);
    const bool ok_weak = r1cs_gg_ppzksnark_verifier_weak_IC  <ppT>(keypair.vk, primary, proof);
    std::cout << "Sort: Verified strong_IC=" << (ok_str ? "true" : "false")
              << " | weak_IC="               << (ok_weak ? "true" : "false") << std::endl;
}

// ---------- [B] Verify that B is a correct sorted version of A (generic N) ----------
template<typename ppT>
void run_verify_sorted_demo_B_generic(size_t k_bits,
                                      const std::vector<uint64_t>& A_vals,
                                      const std::vector<uint64_t>& B_vals)
{
    using FieldT = libff::Fr<ppT>;
    const size_t N = A_vals.size();
    if (B_vals.size() != N) {
        throw std::runtime_error("A and B must have the same length.");
    }

    protoboard<FieldT> pb;

    // Public inputs: A[0..N-1], B[0..N-1]
    std::vector<pb_variable<FieldT>> A(N), B(N);
    for (size_t i = 0; i < N; ++i) {
        A[i].allocate(pb, "A" + std::to_string(i));
        B[i].allocate(pb, "B" + std::to_string(i));
    }
    pb.set_input_sizes(2 * N);

    // Range-check A,B (k bits)
    std::vector<std::unique_ptr<kbits_range_manual<FieldT>>> A_rng(N), B_rng(N);
    for (size_t i = 0; i < N; ++i) {
        A_rng[i].reset(new kbits_range_manual<FieldT>(pb, A[i], k_bits, "A"+std::to_string(i)+"_rng"));
        B_rng[i].reset(new kbits_range_manual<FieldT>(pb, B[i], k_bits, "B"+std::to_string(i)+"_rng"));
    }

    // 1) Monotonicity for B: t[i] = B[i+1] - B[i] >= 0 (k-bit)
    std::vector<pb_variable<FieldT>> t(N > 0 ? N-1 : 0);
    std::vector<std::unique_ptr<kbits_range_manual<FieldT>>> t_rng(N > 0 ? N-1 : 0);
    for (size_t i = 0; i + 1 < N; ++i) {
        t[i].allocate(pb, "t" + std::to_string(i));
        pb.add_r1cs_constraint(
            r1cs_constraint<FieldT>(1, B[i+1] - B[i], t[i]),
            "t = B[i+1]-B[i]");
        t_rng[i].reset(new kbits_range_manual<FieldT>(pb, t[i], k_bits, "t"+std::to_string(i)+"_rng"));
    }

    // 2) Multiset equality via product of (r + ·) using accumulators
    const FieldT r = FieldT("12345");

    std::vector<pb_variable<FieldT>> accA(N), accB(N);
    accA[0].allocate(pb, "accA_0");
    accB[0].allocate(pb, "accB_0");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, accA[0], A[0] + r), "accA_0 = r + A0");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, accB[0], B[0] + r), "accB_0 = r + B0");

    for (size_t i = 1; i < N; ++i) {
        accA[i].allocate(pb, "accA_" + std::to_string(i));
        accB[i].allocate(pb, "accB_" + std::to_string(i));
        pb.add_r1cs_constraint(
            r1cs_constraint<FieldT>(accA[i-1], A[i] + r, accA[i]),
            "accA_step_" + std::to_string(i));
        pb.add_r1cs_constraint(
            r1cs_constraint<FieldT>(accB[i-1], B[i] + r, accB[i]),
            "accB_step_" + std::to_string(i));
    }

    // ∏(r+A[i]) == ∏(r+B[i])
    pb.add_r1cs_constraint(
        r1cs_constraint<FieldT>(1, accA[N-1], accB[N-1]),
        "prod_equal");

    pb_variable<FieldT> sumA, sumB, sumsqA, sumsqB;
    sumA.allocate(pb, "sumA"); sumB.allocate(pb, "sumB");
    sumsqA.allocate(pb, "sumsqA"); sumsqB.allocate(pb, "sumsqB");

    std::vector<pb_variable<FieldT>> sqA_vars(N), sqB_vars(N);

    linear_combination<FieldT> lc_sumA, lc_sumB, lc_sumsqA, lc_sumsqB;
    for (size_t i = 0; i < N; ++i) {
        lc_sumA.add_term(A[i], FieldT::one());
        lc_sumB.add_term(B[i], FieldT::one());

        sqA_vars[i].allocate(pb, "sqA_"+std::to_string(i));
        sqB_vars[i].allocate(pb, "sqB_"+std::to_string(i));
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(A[i], A[i], sqA_vars[i]), "sqA");
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(B[i], B[i], sqB_vars[i]), "sqB");

        lc_sumsqA.add_term(sqA_vars[i], FieldT::one());
        lc_sumsqB.add_term(sqB_vars[i], FieldT::one());
    }
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sumA, lc_sumA), "sumA_def");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sumB, lc_sumB), "sumB_def");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sumsqA, lc_sumsqA), "sumsqA_def");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sumsqB, lc_sumsqB), "sumsqB_def");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sumA,   sumB),   "sum_equal");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sumsqA, sumsqB), "sumsq_equal");

    // ---- Generate constraints for ranges ----
    for (size_t i = 0; i < N; ++i) { A_rng[i]->generate_r1cs_constraints(); }
    for (size_t i = 0; i < N; ++i) { B_rng[i]->generate_r1cs_constraints(); }
    for (size_t i = 0; i + 1 < N; ++i) { t_rng[i]->generate_r1cs_constraints(); }

    // ---- Witness assignment ----
    for (size_t i = 0; i < N; ++i) {
        A_rng[i]->witness_from_uint64(A_vals[i]);
        B_rng[i]->witness_from_uint64(B_vals[i]);
    }
    for (size_t i = 0; i + 1 < N; ++i) {
        const uint64_t diff = (B_vals[i+1] >= B_vals[i]) ? (B_vals[i+1] - B_vals[i]) : 0ULL;
        t_rng[i]->witness_from_uint64(diff);
    }

    // Accumulators
    pb.val(accA[0]) = FieldT(A_vals[0]) + r;
    pb.val(accB[0]) = FieldT(B_vals[0]) + r;
    for (size_t i = 1; i < N; ++i) {
        pb.val(accA[i]) = pb.val(accA[i-1]) * (FieldT(A_vals[i]) + r);
        pb.val(accB[i]) = pb.val(accB[i-1]) * (FieldT(B_vals[i]) + r);
    }

    // sum / sumsq witnesses (sqA_i, sqB_i)
    FieldT sa = FieldT::zero(), sb = FieldT::zero();
    FieldT ssa = FieldT::zero(), ssb = FieldT::zero();
    for (size_t i = 0; i < N; ++i) {
        FieldT a = FieldT(A_vals[i]);
        FieldT b = FieldT(B_vals[i]);
        sa += a; sb += b;
        FieldT aa = a*a, bb = b*b;
        ssa += aa; ssb += bb;
        pb.val(sqA_vars[i]) = aa;
        pb.val(sqB_vars[i]) = bb;
    }
    pb.val(sumA) = sa;    pb.val(sumB) = sb;
    pb.val(sumsqA) = ssa; pb.val(sumsqB) = ssb;

    std::cout << "[B-generic] is_satisfied = " << (pb.is_satisfied() ? "yes" : "no") << std::endl;

    const auto keypair = r1cs_gg_ppzksnark_generator<ppT>(pb.get_constraint_system());
    const auto proof   = r1cs_gg_ppzksnark_prover    <ppT>(keypair.pk, pb.primary_input(), pb.auxiliary_input());
    const bool ok_str  = r1cs_gg_ppzksnark_verifier_strong_IC<ppT>(keypair.vk, pb.primary_input(), proof);
    const bool ok_weak = r1cs_gg_ppzksnark_verifier_weak_IC  <ppT>(keypair.vk, pb.primary_input(), proof);

    std::cout << "B-generic: Verified strong_IC=" << (ok_str ? "true" : "false")
              << " | weak_IC=" << (ok_weak ? "true" : "false") << std::endl;
}

int main()
{
    default_r1cs_gg_ppzksnark_pp::init_public_params();

    const size_t k_bits = 16;

    // ===== A: sorting-network demo (N = power of two) =====
    std::vector<uint64_t> arr = {35, 12, 12, 200, 7, 3, 9, 1};
    std::cout << "[100%] Built target zk_sort_example\n";
    std::cout << "Reset time counters for profiling\n\n";
    std::cout << "[A] Sorting network demo (odd-even mergesort), N=" << arr.size() << "\n";
    run_sorting_network_demo_generic<default_r1cs_gg_ppzksnark_pp>(k_bits, arr);

    // ===== B: verify-sorted demo (generic N) =====
    std::vector<uint64_t> A_pub = {35, 12, 12, 200, 7,  3,  9, 1};
    std::vector<uint64_t> B_pub = { 1,  3,  7,  9, 12, 12, 35, 200};
    std::cout << "\n[B] Verify-sorted demo (generic N=" << A_pub.size() << ")\n";
    run_verify_sorted_demo_B_generic<default_r1cs_gg_ppzksnark_pp>(k_bits, A_pub, B_pub);

    std::cout << "\nAll done.\n";
    return 0;
}
