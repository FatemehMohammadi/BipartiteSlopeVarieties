MACAULAY2 VERIFICATION

Run from this directory:

    M2 --script Verify.m2

Files
-----
Circuits.m2
    Generates the complete circuit families from the proved K_(4,t)
    classification, checks their edge counts, and finds the lexicographically
    largest complementary spanning-tree monomial by cycle-pruned search.
    For K_(4,6) it regenerates all 10,760 circuit/leading-tree pairs.

Transfer.m2
    Compresses their leading-tree patterns, removes redundant forbidden
    words, constructs the reachable prefix automaton and minimizes it.
    It checks 633 compressed words, 55 minimal patterns, 7,946 accepting
    prefix states, and 70 minimal states (69 accepting, one rejecting).
    It proves acyclicity after deleting loops and computes the order-15
    denominator bound. Exact polynomial cross multiplication verifies the
    reduced order-8 rational identity. It performs the Hilbert substitution,
    checks all eight printed numerator polynomials, and verifies the closed
    degree and final-corner formulas by exact generating-function identities.
    Independent native monomial-ideal hilbertSeries checks cover t=3,4,5,6.

AlgebraChecks.m2
    Checks the K_(3,t) determinantal ideals and full minimal resolutions for
    t=4,5,6 over QQ, ZZ/2, and ZZ/3, together with their Hilbert formulas.
    It also checks three fixed-neighbour scroll resolutions and the K_(3,4)
    sextic: 216 terms, vanishing on an exact rational drawing, and its cleared
    rooted degree-11 polynomial in 19 variables.

Verify.m2
    Runs all stages from scratch and stops with an assertion error if any
    claimed equality fails. A successful run prints the final PASS line.

K4TransferCertificate.m2
    A small, inspectable transition table written by Verify.m2. It is an
    output and is not needed as input to the verification. Regeneration
    overwrites it with the reconstructed table.

verification.log
    Successful output from the full native Macaulay2 run.

Conventions and proof scope
--------------------------
Edges are indexed by t*i+j, with i=0,1,2,3 and j=0,...,t-1. The variable
with larger index has higher lexicographic priority. Circuit and tree masks
are integers whose corresponding edge bits are one.

The all-t result is not inferred from finitely many numerical examples:
the paper proves that all circuit patterns occur already on K_(4,6), and
the finite transition graph gives an exact denominator bound. Polynomial
cross multiplication then certifies the rational identity for every word
length. Native Hilbert-engine checks are independent corroboration.

The K_(3,t), fixed-neighbour, Gorenstein, and physical-coordinate results
have written uniform proofs in the paper. 
