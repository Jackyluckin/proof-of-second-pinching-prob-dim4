# Exact Certificate Data

This file specifies the exact coefficient and witness representation for
the inequality W_(1/2) <= -1/10000. Appendix A of the paper gives the
mathematical reduction. `mathematica/Verification.nb` explains and
executes the calculation; `mathematica/Verification.pdf` is its static
export. All executable routines named below are in
`mathematica/Chern4Verifier.wl`.

Storage indices in JSON are zero based. A stored amplitude index a
corresponds to the paper's x_(a+1). Bernstein control indices i,j range
from 0 to 14. Wolfram list access adds one to each storage index.

## Files and fields

- `mathematica/data/endpoint.json` contains `degrees`, the 196
  `quartic_monomials`, their `polynomials`, and `denominator_L5`.
- `mathematica/data/certificate.json` contains the endpoint input hash,
  `null_denominator`, and the 24 leaves. Each leaf has a binary `path`,
  four `null_corners`, and a `witness_file` identifier.
- `mathematica/data/witnesses/leaf_0000.json` through
  `leaf_0023.json` contain the integer witness pools and control indices.
  The stored `witness_file` identifier retains its original `.npz`
  suffix. `verifyLeaf` replaces that suffix by `.json` when resolving
  the file in the supplied `witnesses/` directory.
- `mathematica/data_integrity.json` records the fixed computational-file
  identities checked by the verifier; `input_manifest.json` at the
  supplement root records the static distribution files and provenance.

Mathematical integers are represented by exact JSON integers or signed
decimal integer strings and are parsed by `readInteger`; machine-real
values are not accepted as integers. Polynomial degree indices are
exact integers. The historical `generation_seconds` field is metadata
and does not enter a polynomial, denominator or positivity test.

## Paper, implementation and data

| Paper object | Wolfram routines | Input or checked output |
| --- | --- | --- |
| Spectral and cubic charts, `eq:spectralchart`--`eq:normalizedchart` | `makeChart`, `checkSpectralGroup` | Traces, positive normalization, full-rank cubic basis and the 48 signed permutations |
| Endpoint polynomial, `eq:Pidentity` | `closedPolynomial`, `comparePolynomial` | All polynomial coefficients and the denominator channel in `endpoint.json` |
| Fourth-tensor contraction reconstruction, `eq:Grams` | `rawGram`, `checkGramFormulas`, `rawPolynomial` | Ordered metrics in 35 coordinates, the Gram identities and all coefficients of P |
| Bernstein expansions, `eq:Bernstein` | `integerTransforms`, `affineTransform`, `act` | 197 channels: 196 quartics and one denominator |
| Closed rectangular cover | `checkCover`, `rectangle` | The 24 binary leaf paths |
| Gram reconstruction, `eq:compressedgram`, `eq:Gramcertificate` | `bookkeeping`, `verifyLeaf` | All 442 weighted positions at every control, including zero-polynomial corrections |
| Integer positive definiteness, `eq:integercriterion` | `verifyLeaf` | Symmetry and strict row inequalities after the supplied congruence |
| Complete execution | `VerifyChern4`, `run_verification.wls` | Both reconstructions and both complete replays, with their current run identifier |

The public verification entry uses Wolfram alone. The original Python
implementation and NPZ files are retained in the development archive
as an auxiliary regression baseline. Their different intermediate
scaling is recorded below because it must not be confused with the
scaling used by the supplied Wolfram constructor.

## Closed rectangular cover

Starting from [0,1]^2 at depth zero, a path bisects the r interval at even
depth and the y interval at odd depth. A digit 0 retains the lower closed
half; a digit 1 retains the upper closed half. Read each word from left to
right. The 24 paths, in stored order, are:

```text
000       001       010       0110      01110     01111
10000     10001     100100    100101    10011     1010
1011      11000     11001     1101      111000    111001
11101000  11101001  11101010  11101011  111011    1111
```

Path number k in this order uses `leaf_k.json`, with k
written as four decimal digits starting at 0000. The corresponding `path`
field in `certificate.json` is the same word. Every non-leaf prefix has
both children, and no listed leaf has a listed descendant. Thus the closed
rectangles cover the full square, with disjoint interiors, including every
spectral boundary. 

## Ordered fields and arrays

`quartic_monomials` is the lexicographically sorted list of 196 nonzero
quartic types, each a sorted four-tuple from 0,...,11. Entry k in `polynomials`
is the list `[r_degree,y_degree,integer_coefficient_string]` for that type.
The complete reconstruction also verifies that all other 1169 quartic types
are zero. The stored denominator is exactly `(5625/32)*L^5`, equivalently
`180000*(1+r^2+r^2*y^2)^5`. There are 19020 nonzero bivariate coefficient
terms in P, counted independently of the denominator.

The 78 quadratic labels are `combinations_with_replacement(range(12),2)`.
For amplitudes x_1,...,x_12 in that order, the four-bit frame-sign
characters are `[14,13,11,7,1,1,2,2,4,4,8,8]`. Bit k-1 records reversal
of the kth frame vector, 1 <= k <= 4. The character of x_a*x_b is the
bitwise XOR of their two characters. This gives sorted XOR classes
`[0,3,5,6,9,10,12,15]`, block sizes `[16,9,9,9,9,9,9,8]`. A block retains
the original quadratic order. Upper-triangular entries use block, row,
column order, with row <= column, giving 442 entries. A diagonal entry has
weight 1, an off-diagonal entry weight 2. `c_gamma` is the sum of these
weights over a quartic label. Labels are obtained by sorting the four
amplitude indices; their order is the stored quartic order.

A leaf's four `null_corners` are in order (0,0),(1,0),(0,1),(1,1), each an
integer vector of length 442. Their common denominator is 12884901888.
For i,j=0,...,14 their integer interpolation numerator is

    nu = (14-i)(14-j)n00 + i(14-j)n10 + (14-i)j n01 + ij n11.

Let p_gamma and d>0 be the polynomial and denominator control coefficients
with the SAME positive integer scaling. The rational Gram entry is

    p_gamma/(c_gamma*d) + nu_entry/(196*null_denominator).

The integer numerator is

    Q_entry = p_gamma*(196*null_denominator/c_gamma) + d*nu_entry.

Its positive denominator is `196*null_denominator*d`. For each of the four
corner vectors and each quartic label gamma, the weighted sum of the
entries with that label is zero. These identities imply the full Gram
polynomial identity, labels `eq:compressedgram` and `eq:Gramcertificate`
in the paper. Positive definiteness is
checked at every control; there is no inference from corner positivity.

Each witness JSON file contains nested lists `pool0` through `pool7`,
with shape (number_of_witnesses, block_size, block_size), and lists
`index0` through `index7` of length 225. Control order is h=15*i+j;
each index selects a zero-based witness. Wolfram adds one when accessing
lists. The auxiliary Python data in the development archive use the
same arrays in NPZ form and convert them to `dtype=object` before
arbitrary-precision integer arithmetic. Those NPZ files and Python
programs are not part of this public distribution.

## Intermediate scalings

The final polynomial is the same in all reconstruction paths. However,
the auxiliary Python closed constructor uses F=L^3*N*B, whereas Wolfram's `ff` is
L^2*N*B. Both use a numerator for L*K_A. The raw Python constructor uses
covariant coordinates of L^3*N*B in its nine-dimensional matrix basis;
its metric inverse is part of the contractions. The raw Wolfram constructor
works directly with the 35-coordinate dual projection. Matching variable
names is not evidence that these intermediate arrays are equal. Only the
fully scaled output P is compared to the stored polynomial.

Midpoint arrays are scaled by (14!)^2 at the root and by 2^14 for each
bisection. Direct affine arrays are scaled by (14!)^2*q_r^14*q_y^14, with
positive q_r,q_y clearing local endpoint denominators. P and its denominator
share the scale. A minimum integer row margin therefore depends on the
chosen scale and is not a bound on the optimal value of W_(1/2).

## Coverage, integrity and failure

The 24 literal paths above form the complete binary prefix cover of
the closed spectral square. Each replay checks 5400 Gram identities,
43200 blocks and 421200 strict row inequalities. The two methods
check the same controls, each by its own Bernstein conversion.

File hashes establish byte identity, not polynomial equality or
positive definiteness. The verifier separately reconstructs P, checks
its full coefficient support, verifies the positive normalization
factors, and performs the complete Gram and row tests.

Missing files, an unexpected fixed input hash, malformed integer data,
invalid dimensions or indices, an incomplete cover, a nonzero
purported zero-polynomial correction, a coefficient mismatch, a
nonpositive denominator, an asymmetric block or a failed strict row
inequality causes failure. `EndpointCertified -> True` is produced
only after both reconstructions and every requested complete replay
finish. The publication entry uses the default Midpoint and Affine
methods together. The command-line wrapper returns a nonzero exit
status on failure. Runtime reports are written outside `data/`.
