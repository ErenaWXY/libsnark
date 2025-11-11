// MIT License
// Verify-sorted (generic N) with monotonicity + product-of-(r+·) multiset check.
// Range checks are manual (k-bit): boolean bits + linear combination equals the packed value.
// (c) 2025

#include <iostream>
#include <vector>
#include <memory>
#include <cstdint>
#include <string>
#include <stdexcept>

#include <libsnark/common/default_types/r1cs_gg_ppzksnark_pp.hpp>
#include <libsnark/gadgetlib1/protoboard.hpp>
#include <libsnark/gadgetlib1/gadgets/basic_gadgets.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>

using namespace libsnark;
using namespace std;

// ---------- Manual k-bit "range" gadget: bits are boolean and sum(bits*2^i) = x ----------
template<typename FieldT>
struct kbits_range_manual {
    protoboard<FieldT>& pb;
    pb_variable<FieldT> x;
    size_t k;
    pb_variable_array<FieldT> bits;
    std::vector<FieldT> weights; // 2^i precomputed

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
        // sum_i bits[i]*2^i = x   ⇒  1 * x = sum
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

// ---------- Build ∏(r + X[i]) via a pairwise product tree ----------
template<typename FieldT>
struct product_tree {
    protoboard<FieldT>& pb;
    const FieldT r;
    size_t k_bits;

    // Leaves: enc[i] = r + X[i]
    std::vector<pb_variable<FieldT>> leaves_vars;   // vars for (r + X[i])
    std::vector<std::vector<pb_variable<FieldT>>> layers_vars; // product layers

    product_tree(protoboard<FieldT>& pb, const FieldT& r, size_t k_bits)
        : pb(pb), r(r), k_bits(k_bits) {}

    // create leaves for array X (pb vars X[i] already exist)
    void make_leaves_from_array(const std::vector<pb_variable<FieldT>>& X,
                                const std::string& tag) {
        leaves_vars.resize(X.size());
        for (size_t i = 0; i < X.size(); ++i) {
            leaves_vars[i].allocate(pb, tag + "_leaf_" + std::to_string(i));
            // 1 * leaf = X[i] + r
            pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, leaves_vars[i], X[i] + r),
                                   tag + "_leaf_equiv");
        }
    }

    // Build constraints for pairwise multiplication up to a single product.
    // Returns the final product variable.
    pb_variable<FieldT> build_constraints(const std::string& tag) {
        layers_vars.clear();
        layers_vars.push_back(leaves_vars);

        size_t level = 0;
        while (layers_vars.back().size() > 1) {
            const auto& cur = layers_vars.back();
            std::vector<pb_variable<FieldT>> nxt;
            for (size_t i = 0; i < cur.size(); i += 2) {
                if (i + 1 < cur.size()) {
                    pb_variable<FieldT> p; p.allocate(pb, tag + "_lvl" + std::to_string(level) +
                                                            "_mul_" + std::to_string(i/2));
                    // cur[i] * cur[i+1] = p
                    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(cur[i], cur[i+1], p),
                                           tag + "_pair_mul");
                    nxt.push_back(p);
                } else {
                    // carry forward: 1 * carry = cur[i]
                    pb_variable<FieldT> carry;
                    carry.allocate(pb, tag + "_lvl" + std::to_string(level) + "_carry");
                    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, carry, cur[i]),
                                           tag + "_carry_forward");
                    nxt.push_back(carry);
                }
            }
            layers_vars.push_back(std::move(nxt));
            ++level;
        }
        return layers_vars.back()[0];
    }

    // Assign witnesses given concrete integer values X_vals (uint64)
    void assign_witness_from_uints(const std::vector<uint64_t>& X_vals) {
        // leaves
        for (size_t i = 0; i < X_vals.size(); ++i) {
            pb.val(leaves_vars[i]) = FieldT(X_vals[i]) + r;
        }
        // levels
        for (size_t L = 0; L + 1 < layers_vars.size(); ++L) {
            const auto& cur = layers_vars[L];
            const auto& nxt = layers_vars[L+1];
            size_t nxt_idx = 0;
            for (size_t i = 0; i < cur.size(); i += 2) {
                if (i + 1 < cur.size()) {
                    pb.val(nxt[nxt_idx]) = pb.val(cur[i]) * pb.val(cur[i+1]);
                } else {
                    pb.val(nxt[nxt_idx]) = pb.val(cur[i]); // carry
                }
                ++nxt_idx;
            }
        }
    }
};

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

    // Optional: range-check A[i], B[i] to k-bits (safer integer semantics)
    std::vector<std::unique_ptr<kbits_range_manual<FieldT>>> A_rng(N), B_rng(N);
    for (size_t i = 0; i < N; ++i) {
        A_rng[i].reset(new kbits_range_manual<FieldT>(pb, A[i], k_bits, "A"+std::to_string(i)+"_rng"));
        B_rng[i].reset(new kbits_range_manual<FieldT>(pb, B[i], k_bits, "B"+std::to_string(i)+"_rng"));
    }

    // 1) Monotonicity for B: create t[i] = B[i+1] - B[i] and range-check t[i] in k bits
    std::vector<pb_variable<FieldT>> t(N > 0 ? N-1 : 0);
    std::vector<std::unique_ptr<kbits_range_manual<FieldT>>> t_rng(N > 0 ? N-1 : 0);
    for (size_t i = 0; i + 1 < N; ++i) {
        t[i].allocate(pb, "t" + std::to_string(i));
        // 1 * (B[i+1] - B[i]) = t[i]
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, B[i+1] - B[i], t[i]), "t = B[i+1]-B[i]");
        t_rng[i].reset(new kbits_range_manual<FieldT>(pb, t[i], k_bits, "t"+std::to_string(i)+"_rng"));
    }

    // 2) Multiset equality via product of (r + ·)
    //    Use a public constant r (can be replaced by a public input if desired)
    const FieldT r = FieldT("12345");

    product_tree<FieldT> prodA(pb, r, k_bits);
    product_tree<FieldT> prodB(pb, r, k_bits);

    prodA.make_leaves_from_array(A, "Aprod");
    prodB.make_leaves_from_array(B, "Bprod");

    const pb_variable<FieldT> prodA_var = prodA.build_constraints("Aprod");
    const pb_variable<FieldT> prodB_var = prodB.build_constraints("Bprod");

    // Enforce equality: ∏(r + A[i]) = ∏(r + B[i])
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, prodA_var, prodB_var),
                           "prod_equality");

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
        const uint64_t diff = (B_vals[i+1] >= B_vals[i])
                                ? (B_vals[i+1] - B_vals[i])
                                : (uint64_t)0; // if unsorted, constraints will fail anyway
        t_rng[i]->witness_from_uint64(diff);
    }

    prodA.assign_witness_from_uints(A_vals);
    prodB.assign_witness_from_uints(B_vals);

    // ---- Check + Prove/Verify ----
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

    const size_t k_bits = 16; // change to 32/64 if needed (< 2^k)

    // ====== EDIT YOUR PUBLIC ARRAYS HERE ======
    // Example: A (unsorted) and B (its sorted version)
    std::vector<uint64_t> A_pub = {35, 12, 12, 200, 7,  3,  9, 1};
    std::vector<uint64_t> B_pub = { 1,  3,  7,  9, 12, 12, 35, 200};

    std::cout << "[100%] Built target zk_sort_example\n";
    std::cout << "Reset time counters for profiling\n\n";

    std::cout << "[B] Verify-sorted demo (generic N=" << A_pub.size() << ")\n";
    run_verify_sorted_demo_B_generic<default_r1cs_gg_ppzksnark_pp>(k_bits, A_pub, B_pub);

    std::cout << "\nAll done.\n";
    return 0;
}
