import SecondPinching.FiniteCertificateInterface
import Mathlib.Algebra.Order.Star.Real

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching

/-! The reconstruction in Appendix A, equations compressedgram and Gramcertificate.
The entry and label sets are abstract finite sets, so the same argument applies
to the 442 stored upper-triangular slots and their 196 quartic labels. The
identification of those literal arrays is a separate finite representation check. -/

section Fibres
variable {E L R : Type*} [Fintype E] [DecidableEq L] [CommRing R]

/-- Weighted coefficient of one quartic label. In the release the weights are
one on diagonal slots and two on off-diagonal slots. -/
def gramFibreCoefficient (label : E → L) (weight : E → ℕ) (u : E → R) (g : L) : R :=
  ∑ e, if label e = g then (weight e : R) * u e else 0

/-- The multiplicity c_gamma, including ordered-index multiplicities. -/
def gramFibreMultiplicity (label : E → L) (weight : E → ℕ) (g : L) : ℕ :=
  ∑ e, if label e = g then weight e else 0

/-- Coefficient aggregation commutes with addition. -/
theorem gramFibreCoefficient_add (label : E → L) (weight : E → ℕ)
    (u v : E → R) (g : L) :
    gramFibreCoefficient label weight (fun e => u e + v e) g =
      gramFibreCoefficient label weight u g + gramFibreCoefficient label weight v g := by
  simp only [gramFibreCoefficient, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

/-- Coefficient aggregation commutes with scalar multiplication. -/
theorem gramFibreCoefficient_mul (label : E → L) (weight : E → ℕ)
    (a : R) (u : E → R) (g : L) :
    gramFibreCoefficient label weight (fun e => a * u e) g =
      a * gramFibreCoefficient label weight u g := by
  simp only [gramFibreCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

/-- Integer coefficient aggregation and rational inclusion agree exactly. -/
theorem gramFibreCoefficient_intCast (label : E → L) (weight : E → ℕ)
    (u : E → ℤ) (g : L) :
    gramFibreCoefficient label weight (fun e => (u e : ℚ)) g =
      ((gramFibreCoefficient label weight u g : ℤ) : ℚ) := by
  simp [gramFibreCoefficient]

/-- A coefficient which is constant on a label fibre factors out of that fibre. -/
theorem gramFibreCoefficient_label (label : E → L) (weight : E → ℕ)
    (p : L → R) (g : L) :
    gramFibreCoefficient label weight (fun e => p (label e)) g =
      (gramFibreMultiplicity label weight g : R) * p g := by
  simp only [gramFibreCoefficient, gramFibreMultiplicity, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : label e = g <;> simp [h]

end Fibres

section Reconstruction
variable {E L : Type*} [Fintype E] [Fintype L] [DecidableEq L]

/-- The fixed denominator n_* of the four stored null vectors. -/
def compressedNullDenominator : ℤ := 12884901888

/-- The positive constant 196 n_* used for denominator clearing. -/
def compressedGramConstant : ℤ := 196 * compressedNullDenominator

/-- Positivity does not depend on any leaf or control. -/
theorem compressedGramConstant_pos : 0 < compressedGramConstant := by
  norm_num [compressedGramConstant, compressedNullDenominator]

/-- The integer interpolation numerator at the actual degree-14 control (i,j).
The four corners are ordered (0,0),(1,0),(0,1),(1,1). -/
def compressedNullNumerator (n : Fin 4 → E → ℤ) (ij : ControlIndex) (e : E) : ℤ :=
  (14 - (ij.1.val : ℤ)) * (14 - (ij.2.val : ℤ)) * n 0 e +
  (ij.1.val : ℤ) * (14 - (ij.2.val : ℤ)) * n 1 e +
  (14 - (ij.1.val : ℤ)) * (ij.2.val : ℤ) * n 2 e +
  (ij.1.val : ℤ) * (ij.2.val : ℤ) * n 3 e

/-- The finite null-vector test includes every corner and every label. -/
def compressedNullCheck (label : E → L) (weight : E → ℕ) (n : Fin 4 → E → ℤ) : Bool :=
  decide (∀ k g, gramFibreCoefficient label weight (n k) g = 0)

/-- The finite predicate means precisely the four sets of zero-coefficient identities. -/
theorem compressedNullCheck_iff (label : E → L) (weight : E → ℕ) (n : Fin 4 → E → ℤ) :
    compressedNullCheck label weight n = true ↔
      ∀ k g, gramFibreCoefficient label weight (n k) g = 0 := by
  simp [compressedNullCheck]

/-- Four zero-polynomial corrections interpolate to a zero-polynomial correction
at every control. No positive-definiteness assumption at corners is involved. -/
theorem compressedNullNumerator_fibre_zero (label : E → L) (weight : E → ℕ)
    (n : Fin 4 → E → ℤ) (hn : compressedNullCheck label weight n = true)
    (ij : ControlIndex) (g : L) :
    gramFibreCoefficient label weight (compressedNullNumerator n ij) g = 0 := by
  have h := (compressedNullCheck_iff label weight n).mp hn
  unfold compressedNullNumerator
  rw [gramFibreCoefficient_add, gramFibreCoefficient_add, gramFibreCoefficient_add]
  simp only [gramFibreCoefficient_mul, h, mul_zero, add_zero]

/-- The canonical Gram term distributes each quartic coefficient over all its
weighted slots, with the common denominator control coefficient d. -/
def canonicalGramEntry (label : E → L) (weight : E → ℕ)
    (p : L → ℚ) (d : ℚ) (e : E) : ℚ :=
  p (label e) / ((gramFibreMultiplicity label weight (label e) : ℚ) * d)

omit [Fintype E] [Fintype L] [DecidableEq L] in
/-- Coefficient reconstruction for the canonical term; only the multiplicity
of the requested label and the common denominator must be nonzero. -/
theorem canonicalGramEntry_fibre [Fintype E] [Fintype L] [DecidableEq L] (label : E → L) (weight : E → ℕ)
    (p : L → ℚ) (d : ℚ) (hd : d ≠ 0) (g : L)
    (hc : gramFibreMultiplicity label weight g ≠ 0) :
    gramFibreCoefficient label weight (canonicalGramEntry label weight p d) g = p g / d := by
  unfold canonicalGramEntry
  rw [gramFibreCoefficient_label label weight
    (fun g => p g / ((gramFibreMultiplicity label weight g : ℚ) * d))]
  have hc' : (gramFibreMultiplicity label weight g : ℚ) ≠ 0 := by exact_mod_cast hc
  field_simp [hd, hc']

/-- The rational Gram entry in equation compressedgram. -/
def compressedGramEntry (label : E → L) (weight : E → ℕ)
    (p : L → ℚ) (d : ℚ) (n : Fin 4 → E → ℤ) (ij : ControlIndex) (e : E) : ℚ :=
  canonicalGramEntry label weight p d e +
    (compressedNullNumerator n ij e : ℚ) / (compressedGramConstant : ℚ)

/-- The reconstruction has exactly coefficient p_gamma/d at every control. -/
theorem compressedGramEntry_fibre (label : E → L) (weight : E → ℕ)
    (p : L → ℚ) (d : ℚ) (hd : d ≠ 0)
    (n : Fin 4 → E → ℤ) (hn : compressedNullCheck label weight n = true)
    (ij : ControlIndex) (g : L) (hc : gramFibreMultiplicity label weight g ≠ 0) :
    gramFibreCoefficient label weight (compressedGramEntry label weight p d n ij) g = p g / d := by
  unfold compressedGramEntry
  rw [gramFibreCoefficient_add, canonicalGramEntry_fibre label weight p d hd g hc]
  simp_rw [div_eq_mul_inv, mul_comm _ (compressedGramConstant : ℚ)⁻¹]
  rw [gramFibreCoefficient_mul, gramFibreCoefficient_intCast,
    compressedNullNumerator_fibre_zero label weight n hn ij g]
  simp

/-- Weighted polynomial of the stored slots. The supplied label monomials are
not required to be independent for the reconstruction identity. -/
noncomputable def gramSlotPolynomial (label : E → L) (weight : E → ℕ)
    (monomial : L → MvPolynomial (Fin 12) ℚ) (u : E → ℚ) : MvPolynomial (Fin 12) ℚ :=
  ∑ e, MvPolynomial.C ((weight e : ℚ) * u e) * monomial (label e)

/-- Regrouping the complete slot polynomial by label. -/
theorem gramSlotPolynomial_regroup (label : E → L) (weight : E → ℕ)
    (monomial : L → MvPolynomial (Fin 12) ℚ) (u : E → ℚ) :
    gramSlotPolynomial label weight monomial u =
      ∑ g, MvPolynomial.C (gramFibreCoefficient label weight u g) * monomial g := by
  classical
  simp only [gramFibreCoefficient, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold gramSlotPolynomial
  apply Finset.sum_congr rfl
  intro e _
  simp only [apply_ite, map_zero, ite_mul, zero_mul]
  simp

/-- The complete polynomial identity represented by the compressed entries.
This proves the mathematical reconstruction, not a successful data-file parse. -/
theorem compressedGram_polynomial (label : E → L) (weight : E → ℕ)
    (monomial : L → MvPolynomial (Fin 12) ℚ)
    (p : L → ℚ) (d : ℚ) (hd : d ≠ 0)
    (hc : ∀ g, gramFibreMultiplicity label weight g ≠ 0)
    (n : Fin 4 → E → ℤ) (hn : compressedNullCheck label weight n = true)
    (ij : ControlIndex) :
    gramSlotPolynomial label weight monomial (compressedGramEntry label weight p d n ij) =
      MvPolynomial.C (1 / d) * ∑ g, MvPolynomial.C (p g) * monomial g := by
  rw [gramSlotPolynomial_regroup]
  simp_rw [compressedGramEntry_fibre label weight p d hd n hn ij _ (hc _)]
  simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
  apply Finset.sum_congr rfl
  intro g _
  congr 2
  ring

/-- The integer entry Q in the release, with exact division of 196 n_* by c_gamma. -/
def compressedIntegerEntry (label : E → L) (weight : E → ℕ)
    (p : L → ℤ) (d : ℤ) (n : Fin 4 → E → ℤ) (ij : ControlIndex) (e : E) : ℤ :=
  (compressedGramConstant / (gramFibreMultiplicity label weight (label e) : ℤ)) * p (label e) +
    d * compressedNullNumerator n ij e

/-- The common clearing factor is positive whenever the scaled denominator is. -/
theorem compressedGram_clearing_pos (d : ℤ) (hd : 0 < d) :
    0 < compressedGramConstant * d := mul_pos compressedGramConstant_pos hd

omit [Fintype E] [Fintype L] [DecidableEq L] in
/-- Exact integer division gives the stated positive-denominator clearing
identity. Divisibility is a finite condition on the multiplicities. -/
theorem compressedIntegerEntry_eq [Fintype E] [Fintype L] [DecidableEq L] (label : E → L) (weight : E → ℕ)
    (p : L → ℤ) (d : ℤ) (hd : d ≠ 0)
    (n : Fin 4 → E → ℤ) (ij : ControlIndex) (e : E)
    (hc : gramFibreMultiplicity label weight (label e) ≠ 0)
    (hdiv : (gramFibreMultiplicity label weight (label e) : ℤ) ∣ compressedGramConstant) :
    (compressedIntegerEntry label weight p d n ij e : ℚ) =
      ((compressedGramConstant : ℚ) * (d : ℚ)) *
        compressedGramEntry label weight (fun g => (p g : ℚ)) (d : ℚ) n ij e := by
  have hc' : ((gramFibreMultiplicity label weight (label e) : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hc
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hk : (compressedGramConstant : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt compressedGramConstant_pos
  simp only [compressedIntegerEntry, Int.cast_add, Int.cast_mul, Int.cast_div hdiv hc',
    compressedGramEntry, canonicalGramEntry, Int.cast_natCast]
  field_simp

/-- The scale for Q representing P_ij is 196 n_* sigma. The extra d belongs
to the scale for G representing P_ij/d_ij, not to the scale for P_ij. -/
theorem compressedGram_scale_conversion (P G d sigma : ℚ)
    (hd : d ≠ 0) (hs : sigma ≠ 0) (h : P / (d / sigma) = G) :
    P = (((compressedGramConstant : ℚ) * d) * G) /
      ((compressedGramConstant : ℚ) * sigma) := by
  have hk : (compressedGramConstant : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt compressedGramConstant_pos
  rw [← h]
  field_simp


/-- Clearing a positive scalar denominator preserves positive definiteness
in both directions. This applies separately to each tested control matrix. -/
theorem posDef_positive_scale_iff {I : Type*} [Fintype I]
    (G : Matrix I I ℝ) (k : ℝ) (hk : 0 < k) :
    (k • G).PosDef ↔ G.PosDef := by
  constructor
  · intro h
    have hi := h.smul (inv_pos.mpr hk)
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hk), one_smul] using hi
  · intro h
    exact h.smul hk


end Reconstruction
end SecondPinching
