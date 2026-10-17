import SecondPinching.FiniteEndpointData
import SecondPinching.ReleasedLiterals

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Matrix
namespace SecondPinching

/-- The integer multiplier n! q^n of the degree-14 affine Bernstein transform.
The arguments a and h are the integer lower endpoint and interval width after
clearing the two endpoint denominators by q. -/
def releasedAffineEntry (q : Nat) (a h : Int) (i k : Nat) : Int :=
  (q : Int) ^ (14-k) *
    ((List.range (min i k + 1)).map fun s =>
      (Nat.choose k s : Int) * a^(k-s) * h^s * (Nat.choose i s : Int) *
        (Nat.factorial s : Int) * (Nat.factorial (14-s) : Int)).sum

/-- Exact denominator clearing for either axis of a released rectangle. -/
def releasedAxisDenominator (leaf : Fin 24) (axis : Fin 2) : Nat :=
  let lo := certificateRectangles leaf (Fin.ofNat 4 (2*axis.val))
  let hi := certificateRectangles leaf (Fin.ofNat 4 (2*axis.val+1))
  Nat.lcm lo.den hi.den

def releasedAxisEntry (leaf : Fin 24) (axis : Fin 2) (i k : Nat) : Int :=
  let lo := certificateRectangles leaf (Fin.ofNat 4 (2*axis.val))
  let hi := certificateRectangles leaf (Fin.ofNat 4 (2*axis.val+1))
  let q := releasedAxisDenominator leaf axis
  releasedAffineEntry q (lo*(q:ℚ)).num ((hi-lo)*(q:ℚ)).num i k

/-- Common positive integer Bernstein clearing scale. This is sigma, not
the denominator polynomial's Bernstein coefficient. -/
def releasedBernsteinScale (leaf : Fin 24) : Int :=
  (Nat.factorial 14 : Int)^2 * (releasedAxisDenominator leaf 0 : Int)^14 *
    (releasedAxisDenominator leaf 1 : Int)^14

/-- Integer Bernstein coefficient of a literal bivariate polynomial. -/
def releasedScaledCoefficient (leaf : Fin 24) (ij : ControlIndex)
    (terms : Array ReleasedPowerTerm) : Int :=
  (terms.toList.map fun t => t.coefficient *
    releasedAxisEntry leaf 0 ij.1.val t.rDegree *
    releasedAxisEntry leaf 1 ij.2.val t.yDegree).sum

def releasedScaledNumerator (leaf : Fin 24) (ij : ControlIndex) (g : Nat) : Int :=
  releasedScaledCoefficient leaf ij (releasedPowerTerms.getD g #[])

def releasedScaledDenominator (leaf : Fin 24) (ij : ControlIndex) : Int :=
  releasedScaledCoefficient leaf ij releasedDenominatorTerms

/-- Upper-triangular storage slot of an ordered block entry. Symmetric
entries select the same original compressed integer. -/
def releasedGramSlot (b : Fin 8) (i j : Fin (certificateBlockSize b)) : Nat :=
  let r := min i.val j.val
  let c := max i.val j.val
  releasedBlockSlotOffset.getD b.val 0 +
    r*(2*certificateBlockSize b+1-r)/2 + (c-r)

/-- Bilinear interpolation numerator in the original corner order
(0,0),(1,0),(0,1),(1,1), at every Bernstein control. -/
def releasedNullNumerator (leaf : Fin 24) (ij : ControlIndex) (slot : Nat) : Int :=
  let n := fun k => ((releasedLeaf leaf).nullCorners.getD k #[]).getD slot 0
  let i : Int := ij.1.val
  let j : Int := ij.2.val
  (14-i)*(14-j)*n 0 + i*(14-j)*n 1 + (14-i)*j*n 2 + i*j*n 3

/-- The original compressed Gram reconstruction with positive denominator
clearing. Its canonical term and zero-polynomial correction are both retained. -/
def releasedGramNumerator (leaf : Fin 24) (ij : ControlIndex) (b : Fin 8) :
    Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) Int :=
  fun i j =>
    let slot := releasedGramSlot b i j
    let g := releasedSlotLabel.getD slot 0
    (compressedGramConstant / (releasedQuarticMultiplicity.getD g 0 : Int)) *
      releasedScaledNumerator leaf ij g +
      releasedScaledDenominator leaf ij * releasedNullNumerator leaf ij slot

/-- Original integer witness U, not U-transpose. The verifier and Lean both
test U Q U-transpose. Controls are indexed by 15*i+j; pools by row then column. -/
def releasedCongruenceWitness (leaf : Fin 24) (ij : ControlIndex) (b : Fin 8) :
    Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) Int :=
  fun i j =>
    let data := releasedLeaf leaf
    let k := (data.witnessIndices.getD b.val #[]).getD (15*ij.1.val+ij.2.val) 0
    (data.witnessPools.getD b.val #[]).getD
      ((k*certificateBlockSize b+i.val)*certificateBlockSize b+j.val) 0

noncomputable section

def releasedQuarticMonomial (g : Nat) : MvPolynomial (Fin 12) ℚ :=
  ((releasedQuarticLabels.getD g #[]).toList.map MvPolynomial.X).prod

/-- P in the ordered variables r,y,x_0,...,x_11, copied from all released
nonzero coefficients. The full finite equality also checks absent coefficients. -/
def releasedEndpointPolynomial : MvPolynomial (Fin 14) ℚ :=
  ((List.range releasedPowerTerms.size).map fun g =>
    ((releasedPowerTerms.getD g #[]).toList.map fun t =>
      MvPolynomial.C (t.coefficient : ℚ) * MvPolynomial.X 0 ^ t.rDegree *
        MvPolynomial.X 1 ^ t.yDegree *
        ((releasedQuarticLabels.getD g #[]).toList.map fun k =>
          MvPolynomial.X (Fin.natAdd 2 k)).prod).sum).sum

/-- The actual P-control, p_scaled/sigma. It is not P-control/D-control. -/
def releasedControlPolynomial (leaf : Fin 24) (ij : ControlIndex) :
    MvPolynomial (Fin 12) ℚ :=
  ((List.range releasedPowerTerms.size).map fun g =>
    MvPolynomial.C ((releasedScaledNumerator leaf ij g : ℚ) /
      (releasedBernsteinScale leaf : ℚ)) * releasedQuarticMonomial g).sum

/-- Fixed instance of the exact 11 October e2 release matching the manuscript.
No finite computation is asserted accepted by this definition. -/
def releasedEndpointData : FiniteEndpointData where
  polynomial := releasedEndpointPolynomial
  controls := releasedControlPolynomial
  gramNumerator := releasedGramNumerator
  congruenceWitness := releasedCongruenceWitness
  bernsteinIntegerScale := fun leaf _ => releasedBernsteinScale leaf

/-- Endpoint specialization to the immutable released data. Acceptance remains
an explicit finite computational premise, with no axiom replacing it. -/
theorem releasedEndpoint_bound (h : FiniteEndpointAccepted releasedEndpointData)
    (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ) :
    intrinsicPinchingW A τ (1/2) ≤ -(1/10000 : ℝ) :=
  finiteEndpointAccepted_endpoint releasedEndpointData h A τ had

end
end SecondPinching
