import SecondPinching.EndpointPolynomial
import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! A fixed-chart endpoint theorem with only finite certificate premises.
The unknown-function identities from CertificateEndpoint are discharged by
polynomial construction and complete finite coefficient comparisons. This
does not assert that the released arrays satisfy those comparisons. -/

/-- The affine interval coordinate (X_k-a)/(b-a), as a rational polynomial. -/
def certificateAffineCoordinate (k : Fin 14) (a b : ℚ) : MvPolynomial (Fin 14) ℚ :=
  MvPolynomial.C ((b-a)⁻¹) * (MvPolynomial.X k - MvPolynomial.C a)

/-- The degree-14 Bernstein weight of an actual released leaf, as a polynomial. -/
def certificateWeightPolynomial (leaf : Fin 24) (ij : ControlIndex) :
    MvPolynomial (Fin 14) ℚ :=
  let q := certificateRectangles leaf
  let s := certificateAffineCoordinate 0 (q 0) (q 1)
  let t := certificateAffineCoordinate 1 (q 2) (q 3)
  MvPolynomial.C (Nat.choose 14 ij.1.val : ℚ) * s^ij.1.val * (1-s)^(14-ij.1.val) *
    (MvPolynomial.C (Nat.choose 14 ij.2.val : ℚ) * t^ij.2.val * (1-t)^(14-ij.2.val))

/-- The complete Bernstein expansion with the twelve cubic variables embedded
after r and y. Every control index is included. -/
def certificateExpansionPolynomial (leaf : Fin 24)
    (C : ControlIndex → MvPolynomial (Fin 12) ℚ) : MvPolynomial (Fin 14) ℚ :=
  ∑ ij, certificateWeightPolynomial leaf ij * MvPolynomial.rename (Fin.natAdd 2) (C ij)

theorem certificateAffineCoordinate_eval (k : Fin 14) (a b : ℚ) (z : Fin 14 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) z (certificateAffineCoordinate k a b) =
      (z k-(a : ℝ))/((b : ℝ)-(a : ℝ)) := by
  simp [certificateAffineCoordinate, div_eq_mul_inv, mul_comm]

/-- The polynomial weight has exactly the rectangle weight used in the proof,
at every real point. Positivity is only needed later on the closed leaf. -/
theorem certificateWeightPolynomial_eval (leaf : Fin 24) (ij : ControlIndex)
    (r y : ℝ) (x : Fin 12 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x)
      (certificateWeightPolynomial leaf ij) = certificateLeafWeight leaf r y ij := by
  have hs := certificateAffineCoordinate_eval 0 (certificateRectangles leaf 0)
    (certificateRectangles leaf 1) (Fin.append ![r,y] x)
  have ht := certificateAffineCoordinate_eval 1 (certificateRectangles leaf 2)
    (certificateRectangles leaf 3) (Fin.append ![r,y] x)
  dsimp only [certificateWeightPolynomial]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one, MvPolynomial.eval₂_C,
    hs, ht, certificateLeafWeight, rectangleWeight, bernsteinWeight]
  norm_cast

theorem certificateExpansionPolynomial_eval (leaf : Fin 24)
    (C : ControlIndex → MvPolynomial (Fin 12) ℚ)
    (r y : ℝ) (x : Fin 12 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x)
      (certificateExpansionPolynomial leaf C) =
      ∑ ij, certificateLeafWeight leaf r y ij * MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (C ij) := by
  simp [certificateExpansionPolynomial, MvPolynomial.eval₂_sum,
    certificateWeightPolynomial_eval, MvPolynomial.eval₂_rename, Function.comp_def]

/-- A complete finite coefficient equality implies the Bernstein identity,
with no sampling and no hypothesis about generic parameter points. -/
theorem certificateExpansionCheck_sound (leaf : Fin 24)
    (P : MvPolynomial (Fin 14) ℚ) (C : ControlIndex → MvPolynomial (Fin 12) ℚ)
    (hcheck : exactCoefficientCheck 14 P (certificateExpansionPolynomial leaf C) = true)
    (r y : ℝ) (x : Fin 12 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x) P =
      ∑ ij, certificateLeafWeight leaf r y ij * MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (C ij) := by
  rw [(exactCoefficientCheck_iff 14 P _).mp hcheck]
  exact certificateExpansionPolynomial_eval leaf C r y x

/-- Finite checks alone imply the strict endpoint bound on the normalized
chart. These are all-support polynomial checks, positive integer scales and
all eight matrix checks at each of the 24*225 control indices. No functional
identity involving W or Bernstein weights remains an unproved premise. -/
theorem chart_endpoint_of_finite_certificate
    (P : MvPolynomial (Fin 14) ℚ)
    (C : Fin 24 → ControlIndex → MvPolynomial (Fin 12) ℚ)
    (Q V : Fin 24 → ControlIndex → (b : Fin 8) →
      Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) ℤ)
    (sigma : Fin 24 → ControlIndex → ℤ)
    (hP : exactCoefficientCheck 14 P endpointPolynomial = true)
    (hexp : ∀ leaf, exactCoefficientCheck 14 P
      (certificateExpansionPolynomial leaf (C leaf)) = true)
    (hs : ∀ leaf ij, 0 < sigma leaf ij)
    (hcoeff : ∀ leaf ij, exactCoefficientCheck 12 (C leaf ij)
      (integerBlockQuartic (Q leaf ij)
        ((compressedGramConstant : ℚ)*(sigma leaf ij : ℚ))) = true)
    (hblocks : ∀ leaf ij b, integerCertificateCheck (certificateBlockSize b)
      (Q leaf ij b) (V leaf ij b) = true)
    (r y : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))
      (normalizedChartCubic r y x) (1/2) < -1/10000 := by
  apply chart_endpoint_of_polynomial_identity P
  · intro r hr y _hy x hx
    exact checkedEndpointPolynomial_identity P hP r y hr.1 x hx
  · intro r hr y hy x hx
    exact certificate_polynomial_pos_of_finite_checks P C Q V sigma hs hcoeff hblocks
      (fun leaf r y _hmem x => certificateExpansionCheck_sound leaf P (C leaf)
        (hexp leaf) r y x) r y hr hy x hx
  all_goals assumption

/-- The paper's non-strict bound for every admissible cubic above a chart
spectrum, conditional only on the same finite data checks. This is not an
unconditional proof for arbitrary symmetric A: spectral transport and the
binding of released files to these finite inputs remain separate. -/
theorem admissible_chart_endpoint_of_finite_certificate
    (P : MvPolynomial (Fin 14) ℚ)
    (C : Fin 24 → ControlIndex → MvPolynomial (Fin 12) ℚ)
    (Q V : Fin 24 → ControlIndex → (b : Fin 8) →
      Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) ℤ)
    (sigma : Fin 24 → ControlIndex → ℤ)
    (hP : exactCoefficientCheck 14 P endpointPolynomial = true)
    (hexp : ∀ leaf, exactCoefficientCheck 14 P
      (certificateExpansionPolynomial leaf (C leaf)) = true)
    (hs : ∀ leaf ij, 0 < sigma leaf ij)
    (hcoeff : ∀ leaf ij, exactCoefficientCheck 12 (C leaf ij)
      (integerBlockQuartic (Q leaf ij)
        ((compressedGramConstant : ℚ)*(sigma leaf ij : ℚ))) = true)
    (hblocks : ∀ leaf ij b, integerCertificateCheck (certificateBlockSize b)
      (Q leaf ij b) (V leaf ij b) = true)
    (r y : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (tau : Cubic4) (ha : PaperAdmissible (normalizedChartMatrix r y) tau) :
    pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y)) tau (1/2) ≤
      -1/10000 := by
  exact chart_endpoint_for_all_admissible_cubics r y hr hy
    (fun x hx => chart_endpoint_of_finite_certificate P C Q V sigma hP hexp hs hcoeff
      hblocks r y hr hy x hx) tau ha

end
end SecondPinching
