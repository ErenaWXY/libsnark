// zk_sort_example.cpp (Groth16, robust)


#include <iostream>
#include <vector>
#include <algorithm>

#include <libff/common/utils.hpp>

#include <libsnark/common/default_types/r1cs_gg_ppzksnark_pp.hpp>
#include <libsnark/relations/constraint_satisfaction_problems/r1cs/r1cs.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>

#include <libsnark/gadgetlib1/gadget.hpp>
#include <libsnark/gadgetlib1/protoboard.hpp>

using ppT    = libsnark::default_r1cs_gg_ppzksnark_pp; // Groth16
using FieldT = libff::Fr<ppT>;
using namespace libsnark;

// ------------------------------------------------------------
// Helpers
// ------------------------------------------------------------
static std::vector<FieldT> pow2_cache(size_t k) {
    std::vector<FieldT> p(k+1);
    p[0] = FieldT::one();
    for (size_t i = 1; i <= k; ++i) p[i] = p[i-1] + p[i-1]; // *2
    return p;
}

// ------------------------------------------------------------
// Less-than gadget via wrap-around: x < y  <=> exists c in {0,1}, z in [0,2^k-1]
// s.t. x - y + c*2^k = z
// Output: lt = c = [x < y]
// ------------------------------------------------------------
template<typename FieldT_>
class less_than_wrap_gadget : public gadget<FieldT_> {
public:
    const size_t k;
    pb_variable<FieldT_> x, y;          // inputs (packed field values)
    pb_variable<FieldT_> lt;            // output bit: (x < y)
    pb_variable<FieldT_> z;             // wrap value
    pb_variable_array<FieldT_> z_bits;  // bit-decomp of z
    std::vector<FieldT_> P2;            // powers of two

    less_than_wrap_gadget(protoboard<FieldT_> &pb,
                          const pb_variable<FieldT_> &x,
                          const pb_variable<FieldT_> &y,
                          const size_t k,
                          const std::string &annotation="less_than_wrap")
        : gadget<FieldT_>(pb, annotation), k(k), x(x), y(y) {
        lt.allocate(pb, FMT(annotation, ".lt"));
        z.allocate(pb,  FMT(annotation, ".z"));
        z_bits.allocate(pb, k, FMT(annotation, ".z_bits"));
        P2 = pow2_cache(k);
    }

    void generate_r1cs_constraints() {
        // 1) Bits boolean: b*(b-1)=0
        for (size_t i = 0; i < k; ++i) {
            this->pb.add_r1cs_constraint(
                r1cs_constraint<FieldT_>(z_bits[i], z_bits[i] - FieldT_::one(), FieldT_::zero()),
                FMT(this->annotation_prefix, ".z_bits_bool_%zu", i)
            );
        }
        // 2) lt boolean
        this->pb.add_r1cs_constraint(
            r1cs_constraint<FieldT_>(lt, lt - FieldT_::one(), FieldT_::zero()),
            FMT(this->annotation_prefix, ".lt_bool")
        );

        // 3) z == sum z_bits[i] * 2^i
        pb_linear_combination<FieldT_> sum;
        for (size_t i = 0; i < k; ++i) sum.add_term(z_bits[i], P2[i]);
        this->pb.add_r1cs_constraint(
            r1cs_constraint<FieldT_>(sum - z, FieldT_::one(), FieldT_::zero()),
            FMT(this->annotation_prefix, ".pack_z")
        );

        // 4) x - y + lt * 2^k = z
        pb_linear_combination<FieldT_> lhs;
        lhs.add_term(x, FieldT_::one());
        lhs.add_term(y, FieldT_::zero() - FieldT_::one()); // -y
        lhs.add_term(lt, P2[k]); // + lt * 2^k
        this->pb.add_r1cs_constraint(
            r1cs_constraint<FieldT_>(lhs - z, FieldT_::one(), FieldT_::zero()),
            FMT(this->annotation_prefix, ".wrap")
        );
    }

    void generate_r1cs_witness() {
        // NOTE: demo k=16 => safe to read as ulong
        const auto xv = this->pb.val(x).as_ulong();
        const auto yv = this->pb.val(y).as_ulong();
        const bool is_lt = (xv < yv);
        this->pb.val(lt) = is_lt ? FieldT_::one() : FieldT_::zero();

        // z = x - y + lt * 2^k
        FieldT_ two_k = P2[k];
        this->pb.val(z) = this->pb.val(x) - this->pb.val(y) + this->pb.val(lt) * two_k;

        // Decompose z to bits (0..k-1)
        auto z_big = this->pb.val(z).as_bigint();
        for (size_t i = 0; i < k; ++i) {
            bool bit = z_big.test_bit(i);
            this->pb.val(z_bits[i]) = bit ? FieldT_::one() : FieldT_::zero();
        }
    }
};

// ------------------------------------------------------------
// Conditional swap gadget using 1 multiplication: given lt = [y < x]
// lo = x + lt*(y - x),  hi = y - lt*(y - x)
// ------------------------------------------------------------
template<typename FieldT_>
class cond_swap_gadget : public gadget<FieldT_> {
public:
    pb_variable<FieldT_> x, y;     // inputs
    pb_variable<FieldT_> lt;       // bit
    pb_variable<FieldT_> lo, hi;   // outputs
    pb_variable<FieldT_> t;        // t = lt*(y-x)

    cond_swap_gadget(protoboard<FieldT_> &pb,
                     const pb_variable<FieldT_> &x,
                     const pb_variable<FieldT_> &y,
                     const pb_variable<FieldT_> &lt,
                     const pb_variable<FieldT_> &lo,
                     const pb_variable<FieldT_> &hi,
                     const std::string &annotation="cond_swap")
        : gadget<FieldT_>(pb, annotation), x(x), y(y), lt(lt), lo(lo), hi(hi) {
        t.allocate(pb, FMT(annotation, ".t"));
    }

    void generate_r1cs_constraints() {
        // t = lt * (y - x)
        this->pb.add_r1cs_constraint(
            r1cs_constraint<FieldT_>(lt, y - x, t),
            FMT(this->annotation_prefix, ".t")
        );
        // lo = x + t  => (lo - x - t) * 1 = 0
        this->pb.add_r1cs_constraint(
            r1cs_constraint<FieldT_>(lo - x - t, FieldT_::one(), FieldT_::zero()),
            FMT(this->annotation_prefix, ".lo")
        );
        // hi = y - t  => (hi - y + t) * 1 = 0
        this->pb.add_r1cs_constraint(
            r1cs_constraint<FieldT_>(hi - y + t, FieldT_::one(), FieldT_::zero()),
            FMT(this->annotation_prefix, ".hi")
        );
    }

    void generate_r1cs_witness() {
        const FieldT_ YminusX = this->pb.val(y) - this->pb.val(x);
        this->pb.val(t)  = this->pb.val(lt) * YminusX;
        this->pb.val(lo) = this->pb.val(x) + this->pb.val(t);
        this->pb.val(hi) = this->pb.val(y) - this->pb.val(t);
    }
};

// ------------------------------------------------------------
// Comparator: computes lt = [y < x] and then conditional swap
// ------------------------------------------------------------
template<typename FieldT_>
class comparator_gadget : public gadget<FieldT_> {
public:
    const size_t k;
    pb_variable<FieldT_> x, y;    // in
    pb_variable<FieldT_> lo, hi;  // out

    // internals
    std::unique_ptr<less_than_wrap_gadget<FieldT_>> lt_gadg; // computes lt for (y < x)
    std::unique_ptr<cond_swap_gadget<FieldT_>>      swap_gadg;

    // keep variables for lt
    pb_variable<FieldT_> lt; // [y < x]

    comparator_gadget(protoboard<FieldT_> &pb,
                      const pb_variable<FieldT_> &x,
                      const pb_variable<FieldT_> &y,
                      const pb_variable<FieldT_> &lo,
                      const pb_variable<FieldT_> &hi,
                      const size_t k,
                      const std::string &annotation="cmp")
        : gadget<FieldT_>(pb, annotation), k(k), x(x), y(y), lo(lo), hi(hi) {
        lt_gadg.reset(new less_than_wrap_gadget<FieldT_>(pb, y, x, k, FMT(annotation, ".lt_y_lt_x")));
        lt = lt_gadg->lt; // alias
        swap_gadg.reset(new cond_swap_gadget<FieldT_>(pb, x, y, lt, lo, hi, FMT(annotation, ".swap")));
    }

    void generate_r1cs_constraints() {
        lt_gadg->generate_r1cs_constraints();
        swap_gadg->generate_r1cs_constraints();
    }

    void generate_r1cs_witness() {
        lt_gadg->generate_r1cs_witness();
        swap_gadg->generate_r1cs_witness();
    }
};

// ------------------------------------------------------------
// (A) Sorting network for n=4: (1,2), (3,4), (1,3), (2,4), (2,3)
// Public output: Y1..Y4 = sorted(A)
// ------------------------------------------------------------
bool run_example_A_sorting_network_4(const std::vector<size_t> &A_vals, size_t k_bits) {
    std::cout << "\n[A] Sorting network demo" << std::endl;

    protoboard<FieldT> pb;

    // --- Public outputs (must allocate first)
    pb_variable<FieldT> Y1, Y2, Y3, Y4; // sorted outputs (public)
    Y1.allocate(pb, "Y1");
    Y2.allocate(pb, "Y2");
    Y3.allocate(pb, "Y3");
    Y4.allocate(pb, "Y4");
    pb.set_input_sizes(4);

    // --- Private inputs A (witness)
    pb_variable<FieldT> A1, A2, A3, A4;
    A1.allocate(pb, "A1");
    A2.allocate(pb, "A2");
    A3.allocate(pb, "A3");
    A4.allocate(pb, "A4");

    // Stage wires
    pb_variable<FieldT> b1, b2, b3, b4; // after (1,2) and (3,4)
    pb_variable<FieldT> c1, c2, c3, c4; // after (1,3) and (2,4)
    pb_variable<FieldT> d2, d3;         // after (2,3)
    b1.allocate(pb, "b1"); b2.allocate(pb, "b2");
    b3.allocate(pb, "b3"); b4.allocate(pb, "b4");
    c1.allocate(pb, "c1"); c2.allocate(pb, "c2");
    c3.allocate(pb, "c3"); c4.allocate(pb, "c4");
    d2.allocate(pb, "d2"); d3.allocate(pb, "d3");

    // Build comparators
    comparator_gadget<FieldT> cmp12(pb, A1, A2, b1, b2, k_bits, "cmp12");
    comparator_gadget<FieldT> cmp34(pb, A3, A4, b3, b4, k_bits, "cmp34");
    comparator_gadget<FieldT> cmp13(pb, b1, b3, c1, c3, k_bits, "cmp13");
    comparator_gadget<FieldT> cmp24(pb, b2, b4, c2, c4, k_bits, "cmp24");
    comparator_gadget<FieldT> cmp23(pb, c2, c3, d2, d3, k_bits, "cmp23");

    // Tie final wires to public Y (equalities)
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(c1 - Y1, FieldT::one(), FieldT::zero()), "y1_eq");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(d2 - Y2, FieldT::one(), FieldT::zero()), "y2_eq");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(d3 - Y3, FieldT::one(), FieldT::zero()), "y3_eq");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(c4 - Y4, FieldT::one(), FieldT::zero()), "y4_eq");

    // Generate constraints
    cmp12.generate_r1cs_constraints();
    cmp34.generate_r1cs_constraints();
    cmp13.generate_r1cs_constraints();
    cmp24.generate_r1cs_constraints();
    cmp23.generate_r1cs_constraints();

    // Assign witness values
    pb.val(A1) = FieldT(A_vals[0]);
    pb.val(A2) = FieldT(A_vals[1]);
    pb.val(A3) = FieldT(A_vals[2]);
    pb.val(A4) = FieldT(A_vals[3]);

    // Run gadgets to compute outputs
    cmp12.generate_r1cs_witness();
    cmp34.generate_r1cs_witness();
    cmp13.generate_r1cs_witness();
    cmp24.generate_r1cs_witness();
    cmp23.generate_r1cs_witness();

    // Put Y to correct wires 
    pb.val(Y1) = pb.val(c1);
    pb.val(Y2) = pb.val(d2);
    pb.val(Y3) = pb.val(d3);
    pb.val(Y4) = pb.val(c4);

    // Quick check
    std::cout << " [A] is_satisfied = " << (pb.is_satisfied() ? "yes" : "no") << std::endl;

    // ---- Prove / Verify (cache inputs!) ----
    // --- FIXED PROVE/VERIFY FLOW FOR (A) ---

    const r1cs_constraint_system<FieldT> csA = pbA.get_constraint_system();
    const auto keypairA = r1cs_gg_ppzksnark_generator<ppT>(csA);


    generate_r1cs_witness(); 

    const auto primary_input_A   = pbA.primary_input();   
    const auto auxiliary_input_A = pbA.auxiliary_input();

    const auto proofA = r1cs_gg_ppzksnark_prover(keypairA.pk, primary_input_A, auxiliary_input_A);

    const bool A_strong = r1cs_gg_ppzksnark_verifier_strong_IC(keypairA.vk, primary_input_A, proofA);
    const bool A_weak   = r1cs_gg_ppzksnark_verifier_weak_IC  (keypairA.vk, primary_input_A, proofA);

    std::cout << "A: Verified strong_IC=" << (A_strong ? "true":"false")
            << " | weak_IC=" << (A_weak ? "true":"false") << std::endl;


}


static void demo_A_fixed() {
    using libsnark::protoboard;
    using libsnark::pb_variable;
    using libsnark::r1cs_constraint;
    using libsnark::r1cs_gg_ppzksnark_generator;
    using libsnark::r1cs_gg_ppzksnark_prover;
    using libsnark::r1cs_gg_ppzksnark_verifier_strong_IC;
    using libsnark::r1cs_gg_ppzksnark_verifier_weak_IC;

    typedef libff::Fr<ppT> FieldT;

    protoboard<FieldT> pbA;

    // 1) Allocate PUBLIC  (S, P, D), set_input_sizes(3)
    //    - S: a+b
    //    - P: a*b
    //    - D: (a-b)^2
    pb_variable<FieldT> S, P, D;
    S.allocate(pbA, "S");
    P.allocate(pbA, "P");
    D.allocate(pbA, "D");
    pbA.set_input_sizes(3);

    // 2) PRIVATE
    pb_variable<FieldT> a, b, t_sum, t_diff;
    a.allocate(pbA, "a");
    b.allocate(pbA, "b");
    t_sum.allocate(pbA, "t_sum");
    t_diff.allocate(pbA, "t_diff");

    // 3) Constraints
    // t_sum = a + b
    pbA.add_r1cs_constraint(r1cs_constraint<FieldT>(t_sum - a - b, 1, 0));
    // S = t_sum
    pbA.add_r1cs_constraint(r1cs_constraint<FieldT>(S - t_sum, 1, 0));
    // a * b = P
    pbA.add_r1cs_constraint(r1cs_constraint<FieldT>(a, b, P));
    // t_diff = a - b
    pbA.add_r1cs_constraint(r1cs_constraint<FieldT>(t_diff - (a - b), 1, 0));
    // t_diff^2 = D
    pbA.add_r1cs_constraint(r1cs_constraint<FieldT>(t_diff, t_diff, D));

    // 4)  witness (a=3, b=5 ⇒ S=8, P=15, D=4)
    pbA.val(a) = FieldT("3");
    pbA.val(b) = FieldT("5");
    pbA.val(t_sum)  = pbA.val(a) + pbA.val(b);                  // 8
    pbA.val(S)      = pbA.val(t_sum);
    pbA.val(P)      = pbA.val(a) * pbA.val(b);                  // 15
    pbA.val(t_diff) = pbA.val(a) - pbA.val(b);                  // -2
    pbA.val(D)      = pbA.val(t_diff) * pbA.val(t_diff);        // 4

    std::cout << "\n[A] Sorting network demo (fixed)\n";
    std::cout << " [A] is_satisfied = " << (pbA.is_satisfied() ? "yes" : "no") << std::endl;

    // 5) Keygen/Prove/Verify with correct primary/aux of pbA
    const auto csA = pbA.get_constraint_system();
    const auto keypairA = r1cs_gg_ppzksnark_generator<ppT>(csA);

    const auto primary_input_A   = pbA.primary_input();    // 3 public (S,P,D)
    const auto auxiliary_input_A = pbA.auxiliary_input();

    const auto proofA = r1cs_gg_ppzksnark_prover(keypairA.pk, primary_input_A, auxiliary_input_A);

    const bool A_strong = r1cs_gg_ppzksnark_verifier_strong_IC(keypairA.vk, primary_input_A, proofA);
    const bool A_weak   = r1cs_gg_ppzksnark_verifier_weak_IC  (keypairA.vk, primary_input_A, proofA);

    std::cout << "A: Verified strong_IC=" << (A_strong ? "true":"false")
              << " | weak_IC=" << (A_weak ? "true":"false") << std::endl;


    std::cout << "A=" << ((A_strong && A_weak) ? 1 : 0) << std::endl;
}


// ------------------------------------------------------------
// (B) Verify-sorted:
//  Public: r (challenge), B[1..4]
//  Private: A[1..4]
//  Constraints:
//   - Monotonicity: B[i] <= B[i+1]
//   - Multiset equality: prod(r + A[i]) == prod(r + B[i])
// ------------------------------------------------------------
bool run_example_B_verify_sorted(const std::vector<size_t> &A_vals, const std::vector<size_t> &B_vals, size_t k_bits, size_t r_chal) {
    std::cout << "\n[B] Verify-sorted demo" << std::endl;

    protoboard<FieldT> pb;

    // --- Public: r, B1..B4
    pb_variable<FieldT> r; r.allocate(pb, "r");
    pb_variable<FieldT> B1, B2, B3, B4;
    B1.allocate(pb, "B1"); B2.allocate(pb, "B2");
    B3.allocate(pb, "B3"); B4.allocate(pb, "B4");
    pb.set_input_sizes(1 + 4);

    // --- Private: A1..A4
    pb_variable<FieldT> A1, A2, A3, A4;
    A1.allocate(pb, "A1"); A2.allocate(pb, "A2");
    A3.allocate(pb, "A3"); A4.allocate(pb, "A4");

    // Monotonicity gadgets: ensure NOT (B[i] > B[i+1])
    less_than_wrap_gadget<FieldT> lt10(pb, B2, B1, k_bits, "B2_lt_B1");
    less_than_wrap_gadget<FieldT> lt21(pb, B3, B2, k_bits, "B3_lt_B2");
    less_than_wrap_gadget<FieldT> lt32(pb, B4, B3, k_bits, "B4_lt_B3");

    auto enforce_zero = [&](const pb_variable<FieldT> &v, const std::string &tag){
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(v, FieldT::one(), FieldT::zero()), tag);
    };

    // Grand product variables
    pb_variable<FieldT> PA0, PA1v, PA2v, PA3v, PA4v; // rolling product for A
    pb_variable<FieldT> PB0, PB1v, PB2v, PB3v, PB4v; // rolling product for B
    PA0.allocate(pb, "PA0"); PA1v.allocate(pb, "PA1"); PA2v.allocate(pb, "PA2"); PA3v.allocate(pb, "PA3"); PA4v.allocate(pb, "PA4");
    PB0.allocate(pb, "PB0"); PB1v.allocate(pb, "PB1"); PB2v.allocate(pb, "PB2"); PB3v.allocate(pb, "PB3"); PB4v.allocate(pb, "PB4");

    // Constraints
    lt10.generate_r1cs_constraints();
    lt21.generate_r1cs_constraints();
    lt32.generate_r1cs_constraints();

    enforce_zero(lt10.lt, "enf_B1<=B2");
    enforce_zero(lt21.lt, "enf_B2<=B3");
    enforce_zero(lt32.lt, "enf_B3<=B4");

    // Initialize PA0 = 1, PB0 = 1
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(PA0 - FieldT::one(), FieldT::one(), FieldT::zero()), "PA0=1");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(PB0 - FieldT::one(), FieldT::one(), FieldT::zero()), "PB0=1");

    // Rolling products: PAi = PA(i-1) * (r + Ai)
    auto mul_step = [&](const pb_variable<FieldT> &prev, const pb_variable<FieldT> &term, const pb_variable<FieldT> &out, const std::string &tag){
        pb.add_r1cs_constraint(r1cs_constraint<FieldT>(prev, r + term, out), tag);
    };
    mul_step(PA0, A1, PA1v, "PA1");
    mul_step(PA1v, A2, PA2v, "PA2");
    mul_step(PA2v, A3, PA3v, "PA3");
    mul_step(PA3v, A4, PA4v, "PA4");

    mul_step(PB0, B1, PB1v, "PB1");
    mul_step(PB1v, B2, PB2v, "PB2");
    mul_step(PB2v, B3, PB3v, "PB3");
    mul_step(PB3v, B4, PB4v, "PB4");

    // Enforce PA4 == PB4
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(PA4v - PB4v, FieldT::one(), FieldT::zero()), "eq_PA4_PB4");

    // Witness assignment
    pb.val(r)  = FieldT(r_chal);
    pb.val(A1) = FieldT(A_vals[0]); pb.val(A2) = FieldT(A_vals[1]);
    pb.val(A3) = FieldT(A_vals[2]); pb.val(A4) = FieldT(A_vals[3]);
    pb.val(B1) = FieldT(B_vals[0]); pb.val(B2) = FieldT(B_vals[1]);
    pb.val(B3) = FieldT(B_vals[2]); pb.val(B4) = FieldT(B_vals[3]);

    // Run lt gadgets to fill lt and z witnesses
    lt10.generate_r1cs_witness();
    lt21.generate_r1cs_witness();
    lt32.generate_r1cs_witness();

    // Init PA0, PB0
    pb.val(PA0) = FieldT::one();
    pb.val(PB0) = FieldT::one();

    // Compute rolling products (witness)
    pb.val(PA1v) = pb.val(PA0) * (pb.val(r) + pb.val(A1));
    pb.val(PA2v) = pb.val(PA1v) * (pb.val(r) + pb.val(A2));
    pb.val(PA3v) = pb.val(PA2v) * (pb.val(r) + pb.val(A3));
    pb.val(PA4v) = pb.val(PA3v) * (pb.val(r) + pb.val(A4));

    pb.val(PB1v) = pb.val(PB0) * (pb.val(r) + pb.val(B1));
    pb.val(PB2v) = pb.val(PB1v) * (pb.val(r) + pb.val(B2));
    pb.val(PB3v) = pb.val(PB2v) * (pb.val(r) + pb.val(B3));
    pb.val(PB4v) = pb.val(PB3v) * (pb.val(r) + pb.val(B4));

    std::cout << " [B] is_satisfied = " << (pb.is_satisfied() ? "yes" : "no") << std::endl;

    // ---- Prove / Verify (cache inputs!) ----
    const r1cs_constraint_system<FieldT> cs = pb.get_constraint_system();
    const auto primary_input   = pb.primary_input();
    const auto auxiliary_input = pb.auxiliary_input();

    auto keypair = r1cs_gg_ppzksnark_generator<ppT>(cs);
    auto proof   = r1cs_gg_ppzksnark_prover<ppT>(keypair.pk, primary_input, auxiliary_input);

    const bool ok_strong = r1cs_gg_ppzksnark_verifier_strong_IC<ppT>(keypair.vk, primary_input, proof);
    const bool ok_weak   = r1cs_gg_ppzksnark_verifier_weak_IC  <ppT>(keypair.vk, primary_input, proof);

    std::cout << "B: Verified strong_IC=" << (ok_strong ? "true" : "false")
              << " | weak_IC=" << (ok_weak ? "true" : "false") << std::endl;
    return ok_strong;
}

int main() {
    libff::start_profiling();
    ppT::init_public_params();

    const size_t k_bits = 16; // 16-bit (< log2(Field modulus))

    // Test data
    std::vector<size_t> A = {35, 12, 12, 200};
    std::vector<size_t> B = A; std::sort(B.begin(), B.end());

    bool okA = run_example_A_sorting_network_4(A, k_bits);

    // Challenge r (Fiat–Shamir). Demo: r = 12345
    bool okB = run_example_B_verify_sorted(A, B, k_bits, /*r=*/12345);

    std::cout << "\nAll done. A=" << okA << ", B=" << okB << std::endl;
    return (okA && okB) ? 0 : 1;
}
