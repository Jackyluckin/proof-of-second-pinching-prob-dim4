import SecondPinching.IntegerPositivity
import SecondPinching.BernsteinPositivity
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching

/-! A finite external-computation interface. No check on the released data is
asserted here. The results of finite rational coefficient comparisons and
integer matrix tests are explicit hypotheses. Their mathematical consequences
are proved by Lean. Identifying P with the paper's endpoint polynomial and
reconstructing every released Gram block remain separate obligations. -/

/-- Check the union of both supports: coefficients absent from either input
must still be compared to zero. This is a finite exact rational comparison. -/
def exactCoefficientCheck (n : ℕ) (P Q : MvPolynomial (Fin n) ℚ) : Bool :=
  decide (∀ m ∈ P.support ∪ Q.support, P.coeff m = Q.coeff m)

/-- The finite check is equivalent to the complete polynomial identity. -/
theorem exactCoefficientCheck_iff (n : ℕ) (P Q : MvPolynomial (Fin n) ℚ) :
    exactCoefficientCheck n P Q = true ↔ P = Q := by
  simp only [exactCoefficientCheck, decide_eq_true_eq]
  constructor
  · intro h
    ext m
    by_cases hm : m ∈ P.support ∪ Q.support
    · exact h m hm
    · have hp : P.coeff m = 0 := by
        by_contra hp
        exact hm (Finset.mem_union_left _ (MvPolynomial.mem_support_iff.mpr hp))
      have hq : Q.coeff m = 0 := by
        by_contra hq
        exact hm (Finset.mem_union_right _ (MvPolynomial.mem_support_iff.mpr hq))
      rw [hp, hq]
  · intro h m _
    rw [h]

/-- An accepted finite rational identity holds at every real point, including
all boundary points; no sampling or generic-point hypothesis occurs. -/
theorem exactCoefficientCheck_real_identity (n : ℕ) (P Q : MvPolynomial (Fin n) ℚ)
    (h : exactCoefficientCheck n P Q = true) (x : Fin n → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P = MvPolynomial.eval₂ (algebraMap ℚ ℝ) x Q := by
  rw [(exactCoefficientCheck_iff n P Q).mp h]

/-- The quadratic polynomial of an integer Gram matrix, with rational scaling. -/
noncomputable def integerGramPolynomial (s : ℕ) (Q : Matrix (Fin s) (Fin s) ℤ) (scale : ℚ) :
    MvPolynomial (Fin s) ℚ :=
  ∑ i, ∑ j, MvPolynomial.C ((Q i j : ℚ) / scale) * MvPolynomial.X i * MvPolynomial.X j

theorem integerGramPolynomial_eval (s : ℕ) (Q : Matrix (Fin s) (Fin s) ℤ)
    (scale : ℚ) (x : Fin s → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (integerGramPolynomial s Q scale) =
      (x ⬝ᵥ (integerMatrixToReal Q *ᵥ x)) / (scale : ℝ) := by
  simp [integerGramPolynomial, MvPolynomial.eval₂_sum, integerMatrixToReal,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_div, mul_div_assoc,
    div_mul_eq_mul_div, mul_assoc, mul_left_comm]

/-- External checks for an exact polynomial/Gram identity and an integer
congruence witness imply positivity. Both checks remain visible premises. -/
theorem positivity_from_external_finite_checks (s : ℕ) (hs : 1 ≤ s)
    (P : MvPolynomial (Fin s) ℚ) (Q V : Matrix (Fin s) (Fin s) ℤ)
    (scale : ℚ) (hscale : 0 < scale)
    (hcoeff : exactCoefficientCheck s P (integerGramPolynomial s Q scale) = true)
    (hmat : integerCertificateCheck s Q V = true)
    (x : Fin s → ℝ) (hx : x ≠ 0) :
    0 < MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P := by
  rw [exactCoefficientCheck_real_identity s P _ hcoeff x, integerGramPolynomial_eval]
  apply div_pos
  · simpa only [star_trivial] using
      (integerCertificateCheck_sound s hs Q V hmat).dotProduct_mulVec_pos hx
  · exact_mod_cast hscale

/-- z(x) in the fixed 78-coordinate identification proved in BernsteinPositivity. -/
noncomputable def certificateMonomialVector (x : Fin 12 → ℝ) : Fin 78 → ℝ :=
  fun i => quadraticMonomials x (quadraticIndexEquivFin.symm i)

theorem certificateMonomialVector_ne_zero (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    certificateMonomialVector x ≠ 0 := by
  intro hz
  apply quadraticMonomials_ne_zero hx
  funext q
  have h := congrFun hz (quadraticIndexEquivFin q)
  simpa [certificateMonomialVector] using h

/-- A Gram quartic in the twelve actual cubic-coordinate variables. The scale
is the positive denominator clearing factor, not a numerical tolerance. -/
noncomputable def integerQuarticGramPolynomial (Q : Matrix (Fin 78) (Fin 78) ℤ)
    (scale : ℚ) : MvPolynomial (Fin 12) ℚ :=
  ∑ i, ∑ j, MvPolynomial.C ((Q i j : ℚ) / scale) *
    (MvPolynomial.X (quadraticIndexEquivFin.symm i).val.1 *
      MvPolynomial.X (quadraticIndexEquivFin.symm i).val.2) *
    (MvPolynomial.X (quadraticIndexEquivFin.symm j).val.1 *
      MvPolynomial.X (quadraticIndexEquivFin.symm j).val.2)

theorem integerQuarticGramPolynomial_eval (Q : Matrix (Fin 78) (Fin 78) ℤ)
    (scale : ℚ) (x : Fin 12 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (integerQuarticGramPolynomial Q scale) =
      (certificateMonomialVector x ⬝ᵥ (integerMatrixToReal Q *ᵥ certificateMonomialVector x)) /
        (scale : ℝ) := by
  simp only [integerQuarticGramPolynomial, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    certificateMonomialVector, quadraticMonomials,
    integerMatrixToReal, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  norm_num
  ring


/-- The per-control quartic consequence needed by Lemma A.1. This does not
assert that any released control or block has passed its finite checks. -/
theorem quartic_positivity_from_external_finite_checks
    (P : MvPolynomial (Fin 12) ℚ) (Q V : Matrix (Fin 78) (Fin 78) ℤ)
    (scale : ℚ) (hscale : 0 < scale)
    (hcoeff : exactCoefficientCheck 12 P (integerQuarticGramPolynomial Q scale) = true)
    (hmat : integerCertificateCheck 78 Q V = true)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    0 < MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P := by
  rw [exactCoefficientCheck_real_identity 12 P _ hcoeff x, integerQuarticGramPolynomial_eval]
  apply div_pos
  · simpa only [star_trivial] using
      (integerCertificateCheck_sound 78 (by norm_num) Q V hmat).dotProduct_mulVec_pos
        (certificateMonomialVector_ne_zero x hx)
  · exact_mod_cast hscale

/-- A missing zero coefficient on the first side cannot pass. -/
theorem exactCoefficientCheck_rejects_extra_monomial :
    exactCoefficientCheck 1 0 (MvPolynomial.X 0) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have h := (exactCoefficientCheck_iff _ _ _).mp accepted
  have hc := congrArg (fun p : MvPolynomial (Fin 1) ℚ => p.coeff (Finsupp.single 0 1)) h
  norm_num at hc

/-- Support checking is symmetric; omission from either side is detected. -/
theorem exactCoefficientCheck_rejects_missing_monomial :
    exactCoefficientCheck 1 (MvPolynomial.X 0) 0 = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have h := (exactCoefficientCheck_iff _ _ _).mp accepted
  have hc := congrArg (fun p : MvPolynomial (Fin 1) ℚ => p.coeff (Finsupp.single 0 1)) h
  norm_num at hc

end SecondPinching
