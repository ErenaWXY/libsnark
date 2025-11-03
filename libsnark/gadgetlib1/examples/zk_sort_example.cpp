// MIT License
// Sorting-network zkSNARK demo without packing_gadgets.hpp
// Range checks are manual: boolean bits + linear combination equals the packed value.
// (c) 2025

#include <iostream>
#include <vector>
#include <algorithm>
#include <cstdint>

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
        generate_boolean_r1cs_constraint<FieldT>(pb, s, "sel_boolean");

        // u - y = s * (x - y)   (valid R1CS: (a= s) * (b= x-y) = (c= u-y))
        pb.add_r1cs_constraint(
            r1cs_constraint<FieldT>(s, x - y, u - y),
            "u - y = s*(x - y)");

        // v = x + y - u        ⇒ 1 * v = x + y - u
        pb.add_r1cs_constraint(
            r1cs_constraint<FieldT>(1, v, x + y - u),
            "v = x + y - u");

        // t = v - u            ⇒ 1 * (v - u) = t
        pb.add_r1cs_constraint(
            r1cs_constraint<FieldT>(1, v - u, t),
            "t = v - u");
        // t range is enforced outside by t_rng
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

// ---------- [A] 4-input odd-even sorting network with full k-bit range checks ----------
template<typename ppT>
void run_sorting_network_demo_A(size_t k_bits)
{
    using FieldT = libff::Fr<ppT>;
    protoboard<FieldT> pb;

    // Public outputs Y1..Y4 (primary)
    pb_variable<FieldT> Y1, Y2, Y3, Y4;
    Y1.allocate(pb, "Y1");
    Y2.allocate(pb, "Y2");
    Y3.allocate(pb, "Y3");
    Y4.allocate(pb, "Y4");
    pb.set_input_sizes(4);

    // Private inputs A1..A4
    pb_variable<FieldT> A1, A2, A3, A4;
    A1.allocate(pb, "A1");
    A2.allocate(pb, "A2");
    A3.allocate(pb, "A3");
    A4.allocate(pb, "A4");

    // Range constraints for inputs
    kbits_range_manual<FieldT> A1_rng(pb, A1, k_bits, "A1_rng");
    kbits_range_manual<FieldT> A2_rng(pb, A2, k_bits, "A2_rng");
    kbits_range_manual<FieldT> A3_rng(pb, A3, k_bits, "A3_rng");
    kbits_range_manual<FieldT> A4_rng(pb, A4, k_bits, "A4_rng");

    // Intermediates
    pb_variable<FieldT> b1, b2, b3, b4;
    pb_variable<FieldT> c1, c2, c3, c4;
    pb_variable<FieldT> d2, d3;

    b1.allocate(pb, "b1"); b2.allocate(pb, "b2"); b3.allocate(pb, "b3"); b4.allocate(pb, "b4");
    c1.allocate(pb, "c1"); c2.allocate(pb, "c2"); c3.allocate(pb, "c3"); c4.allocate(pb, "c4");
    d2.allocate(pb, "d2"); d3.allocate(pb, "d3");

    // Range gadgets for all intermediates
    kbits_range_manual<FieldT> b1_rng(pb, b1, k_bits, "b1_rng");
    kbits_range_manual<FieldT> b2_rng(pb, b2, k_bits, "b2_rng");
    kbits_range_manual<FieldT> b3_rng(pb, b3, k_bits, "b3_rng");
    kbits_range_manual<FieldT> b4_rng(pb, b4, k_bits, "b4_rng");
    kbits_range_manual<FieldT> c1_rng(pb, c1, k_bits, "c1_rng");
    kbits_range_manual<FieldT> c2_rng(pb, c2, k_bits, "c2_rng");
    kbits_range_manual<FieldT> c3_rng(pb, c3, k_bits, "c3_rng");
    kbits_range_manual<FieldT> c4_rng(pb, c4, k_bits, "c4_rng");
    kbits_range_manual<FieldT> d2_rng(pb, d2, k_bits, "d2_rng");
    kbits_range_manual<FieldT> d3_rng(pb, d3, k_bits, "d3_rng");

    // Stage 1: (A1,A2)->(b1,b2), (A3,A4)->(b3,b4)
    cmp_swap_gadget<FieldT> cmp12(pb, k_bits, A1, A2, b1, b2, "cmp12", nullptr);
    cmp_swap_gadget<FieldT> cmp34(pb, k_bits, A3, A4, b3, b4, "cmp34", nullptr);

    // Stage 2: (b1,b3)->(c1,c3), (b2,b4)->(c2,c4)
    cmp_swap_gadget<FieldT> cmp13(pb, k_bits, b1, b3, c1, c3, "cmp13", nullptr);
    cmp_swap_gadget<FieldT> cmp24(pb, k_bits, b2, b4, c2, c4, "cmp24", nullptr);

    // Stage 3: (c2,c3)->(d2,d3)
    cmp_swap_gadget<FieldT> cmp23(pb, k_bits, c2, c3, d2, d3, "cmp23", nullptr);

    // t-range gadgets (now that t vars exist)
    kbits_range_manual<FieldT> cmp12_t_rng(pb, cmp12.t, k_bits, "cmp12.t_rng"); cmp12.t_rng = &cmp12_t_rng;
    kbits_range_manual<FieldT> cmp34_t_rng(pb, cmp34.t, k_bits, "cmp34.t_rng"); cmp34.t_rng = &cmp34_t_rng;
    kbits_range_manual<FieldT> cmp13_t_rng(pb, cmp13.t, k_bits, "cmp13.t_rng"); cmp13.t_rng = &cmp13_t_rng;
    kbits_range_manual<FieldT> cmp24_t_rng(pb, cmp24.t, k_bits, "cmp24.t_rng"); cmp24.t_rng = &cmp24_t_rng;
    kbits_range_manual<FieldT> cmp23_t_rng(pb, cmp23.t, k_bits, "cmp23.t_rng"); cmp23.t_rng = &cmp23_t_rng;

    // Constraints
    A1_rng.generate_r1cs_constraints();
    A2_rng.generate_r1cs_constraints();
    A3_rng.generate_r1cs_constraints();
    A4_rng.generate_r1cs_constraints();

    cmp12.generate_r1cs_constraints();
    cmp34.generate_r1cs_constraints();
    cmp13.generate_r1cs_constraints();
    cmp24.generate_r1cs_constraints();
    cmp23.generate_r1cs_constraints();

    cmp12_t_rng.generate_r1cs_constraints();
    cmp34_t_rng.generate_r1cs_constraints();
    cmp13_t_rng.generate_r1cs_constraints();
    cmp24_t_rng.generate_r1cs_constraints();
    cmp23_t_rng.generate_r1cs_constraints();

    b1_rng.generate_r1cs_constraints();
    b2_rng.generate_r1cs_constraints();
    b3_rng.generate_r1cs_constraints();
    b4_rng.generate_r1cs_constraints();
    c1_rng.generate_r1cs_constraints();
    c2_rng.generate_r1cs_constraints();
    c3_rng.generate_r1cs_constraints();
    c4_rng.generate_r1cs_constraints();
    d2_rng.generate_r1cs_constraints();
    d3_rng.generate_r1cs_constraints();

    // Example private inputs (< 2^k_bits)
    uint64_t a1 = 9, a2 = 1, a3 = 7, a4 = 3;

    // Witness for inputs
    A1_rng.witness_from_uint64(a1);
    A2_rng.witness_from_uint64(a2);
    A3_rng.witness_from_uint64(a3);
    A4_rng.witness_from_uint64(a4);

    // Stage 1
    cmp12.generate_r1cs_witness(a1, a2);
    b1_rng.witness_from_uint64(cmp12.u_u64);
    b2_rng.witness_from_uint64(cmp12.v_u64);

    cmp34.generate_r1cs_witness(a3, a4);
    b3_rng.witness_from_uint64(cmp34.u_u64);
    b4_rng.witness_from_uint64(cmp34.v_u64);

    // Stage 2
    cmp13.generate_r1cs_witness(cmp12.u_u64, cmp34.u_u64);
    c1_rng.witness_from_uint64(cmp13.u_u64);
    c3_rng.witness_from_uint64(cmp13.v_u64);

    cmp24.generate_r1cs_witness(cmp12.v_u64, cmp34.v_u64);
    c2_rng.witness_from_uint64(cmp24.u_u64);
    c4_rng.witness_from_uint64(cmp24.v_u64);

    // Stage 3
    cmp23.generate_r1cs_witness(cmp24.u_u64, cmp13.v_u64);
    d2_rng.witness_from_uint64(cmp23.u_u64);
    d3_rng.witness_from_uint64(cmp23.v_u64);

    // Public outputs
    pb.val(Y1) = pb.val(c1);
    pb.val(Y2) = pb.val(d2);
    pb.val(Y3) = pb.val(d3);
    pb.val(Y4) = pb.val(c4);

    auto primary = pb.primary_input();
    std::cout << "Primary (Y1..Y4): "
              << primary[0] << ", "
              << primary[1] << ", "
              << primary[2] << ", "
              << primary[3] << std::endl;

    std::cout << "[A] is_satisfied = " << (pb.is_satisfied() ? "yes" : "no") << std::endl;

    // Prove & verify (Groth16)
    const auto keypair = r1cs_gg_ppzksnark_generator<ppT>(pb.get_constraint_system());
    const auto proof   = r1cs_gg_ppzksnark_prover    <ppT>(keypair.pk, primary, pb.auxiliary_input());
    const bool ok_str  = r1cs_gg_ppzksnark_verifier_strong_IC<ppT>(keypair.vk, primary, proof);
    const bool ok_weak = r1cs_gg_ppzksnark_verifier_weak_IC  <ppT>(keypair.vk, primary, proof);
    std::cout << "A: Verified strong_IC=" << (ok_str ? "true" : "false")
              << " | weak_IC=" << (ok_weak ? "true" : "false") << std::endl;
}

// ---------- [B] Verify that B is a correct sorted version of A ----------
template<typename ppT>
void run_verify_sorted_demo_B_full(size_t k_bits)
{
    using FieldT = libff::Fr<ppT>;
    protoboard<FieldT> pb;

    // Public values
    pb_variable<FieldT> A1, A2, A3, A4;
    pb_variable<FieldT> B1, B2, B3, B4;
    A1.allocate(pb, "A1"); A2.allocate(pb, "A2");
    A3.allocate(pb, "A3"); A4.allocate(pb, "A4");
    B1.allocate(pb, "B1"); B2.allocate(pb, "B2");
    B3.allocate(pb, "B3"); B4.allocate(pb, "B4");
    pb.set_input_sizes(8);  // public inputs: A1..A4, B1..B4

    // Range gadgets for sorted B
    pb_variable<FieldT> t12, t23, t34;
    t12.allocate(pb, "t12"); t23.allocate(pb, "t23"); t34.allocate(pb, "t34");
    kbits_range_manual<FieldT> t12_rng(pb, t12, k_bits, "t12_rng");
    kbits_range_manual<FieldT> t23_rng(pb, t23, k_bits, "t23_rng");
    kbits_range_manual<FieldT> t34_rng(pb, t34, k_bits, "t34_rng");

    // --- 1️⃣ Monotonicity check: ensure B1 ≤ B2 ≤ B3 ≤ B4 ---
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, B2 - B1, t12), "t12 = B2 - B1");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, B3 - B2, t23), "t23 = B3 - B2");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, B4 - B3, t34), "t34 = B4 - B3");

    t12_rng.generate_r1cs_constraints();
    t23_rng.generate_r1cs_constraints();
    t34_rng.generate_r1cs_constraints();

    // --- 2️⃣ Multiset equality check: ∏(r + A[i]) = ∏(r + B[i]) ---
    const FieldT r = FieldT("12345"); // public challenge constant

    // Intermediate variables for partial products
    pb_variable<FieldT> pA12, pA34, pB12, pB34;
    pA12.allocate(pb, "pA12"); pA34.allocate(pb, "pA34");
    pB12.allocate(pb, "pB12"); pB34.allocate(pb, "pB34");

    pb_variable<FieldT> prodA, prodB;
    prodA.allocate(pb, "prodA");
    prodB.allocate(pb, "prodB");

    // Step 1: (r + Ai) * (r + Aj)
    pb.add_r1cs_constraint(
        r1cs_constraint<FieldT>(A1 + r, A2 + r, pA12),
        "pA12 = (r+A1)*(r+A2)");
    pb.add_r1cs_constraint(
        r1cs_constraint<FieldT>(A3 + r, A4 + r, pA34),
        "pA34 = (r+A3)*(r+A4)");

    pb.add_r1cs_constraint(
        r1cs_constraint<FieldT>(B1 + r, B2 + r, pB12),
        "pB12 = (r+B1)*(r+B2)");
    pb.add_r1cs_constraint(
        r1cs_constraint<FieldT>(B3 + r, B4 + r, pB34),
        "pB34 = (r+B3)*(r+B4)");

    // Step 2: combine partials
    pb.add_r1cs_constraint(
        r1cs_constraint<FieldT>(pA12, pA34, prodA),
        "prodA = pA12 * pA34");
    pb.add_r1cs_constraint(
        r1cs_constraint<FieldT>(pB12, pB34, prodB),
        "prodB = pB12 * pB34");

    // Step 3: enforce equality
    pb.add_r1cs_constraint(
        r1cs_constraint<FieldT>(1, prodA, prodB),
        "∏(r + A[i]) = ∏(r + B[i])");

    // --- Witness assignment ---
    uint64_t A_vals[4] = {35, 12, 12, 200};
    uint64_t B_vals[4] = {12, 12, 35, 200};

    pb.val(A1) = FieldT(A_vals[0]);
    pb.val(A2) = FieldT(A_vals[1]);
    pb.val(A3) = FieldT(A_vals[2]);
    pb.val(A4) = FieldT(A_vals[3]);
    pb.val(B1) = FieldT(B_vals[0]);
    pb.val(B2) = FieldT(B_vals[1]);
    pb.val(B3) = FieldT(B_vals[2]);
    pb.val(B4) = FieldT(B_vals[3]);

    // Compute differences for monotonicity
    t12_rng.witness_from_uint64(B_vals[1] - B_vals[0]);
    t23_rng.witness_from_uint64(B_vals[2] - B_vals[1]);
    t34_rng.witness_from_uint64(B_vals[3] - B_vals[2]);

    // Compute product values
    FieldT pA_12 = (r + FieldT(A_vals[0])) * (r + FieldT(A_vals[1]));
    FieldT pA_34 = (r + FieldT(A_vals[2])) * (r + FieldT(A_vals[3]));
    FieldT pB_12 = (r + FieldT(B_vals[0])) * (r + FieldT(B_vals[1]));
    FieldT pB_34 = (r + FieldT(B_vals[2])) * (r + FieldT(B_vals[3]));

    pb.val(pA12) = pA_12;
    pb.val(pA34) = pA_34;
    pb.val(pB12) = pB_12;
    pb.val(pB34) = pB_34;

    pb.val(prodA) = pA_12 * pA_34;
    pb.val(prodB) = pB_12 * pB_34;

    // --- Verify ---
    std::cout << "[B-full] is_satisfied = "
              << (pb.is_satisfied() ? "yes" : "no") << std::endl;

    const auto keypair = r1cs_gg_ppzksnark_generator<ppT>(pb.get_constraint_system());
    const auto proof   = r1cs_gg_ppzksnark_prover<ppT>(
        keypair.pk, pb.primary_input(), pb.auxiliary_input());
    const bool ok_str  = r1cs_gg_ppzksnark_verifier_strong_IC<ppT>(
        keypair.vk, pb.primary_input(), proof);
    const bool ok_weak = r1cs_gg_ppzksnark_verifier_weak_IC<ppT>(
        keypair.vk, pb.primary_input(), proof);

    std::cout << "B-full: Verified strong_IC=" << (ok_str ? "true" : "false")
              << " | weak_IC=" << (ok_weak ? "true" : "false") << std::endl;
}


int main()
{
    default_r1cs_gg_ppzksnark_pp::init_public_params();

    const size_t k_bits = 16; // change to 32/64 if needed (< 2^k)

    std::cout << "[100%] Built target zk_sort_example\n";
    std::cout << "Reset time counters for profiling\n\n";

    std::cout << "[A] Sorting network demo\n";
    run_sorting_network_demo_A<default_r1cs_gg_ppzksnark_pp>(k_bits);

    std::cout << "\n[B] Verify-sorted demo\n";
    run_verify_sorted_demo_B_full<default_r1cs_gg_ppzksnark_pp>(k_bits);

    std::cout << "\nAll done.\n";
    return 0;
}
