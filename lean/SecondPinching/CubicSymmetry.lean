import SecondPinching.Admissible

set_option autoImplicit false
open scoped BigOperators
namespace SecondPinching
noncomputable section

/-- Full symmetry implies the first adjacent transposition identity. -/
theorem cubicSymmetric_swap12 {τ : Cubic4} (hτ : CubicSymmetric τ)
    (i j k : Fin 4) : τ i j k = τ j i k := by
  simpa [Equiv.swap_apply_def] using (hτ (Equiv.swap 0 1) ![i,j,k]).symm

/-- Full symmetry implies the second adjacent transposition identity. -/
theorem cubicSymmetric_swap23 {τ : Cubic4} (hτ : CubicSymmetric τ)
    (i j k : Fin 4) : τ i j k = τ i k j := by
  simpa [Equiv.swap_apply_def] using (hτ (Equiv.swap 1 2) ![i,j,k]).symm

/-- The two adjacent swaps generate all permutations of three tensor slots. -/
theorem cubicSymmetric_iff_swaps (τ : Cubic4) :
    CubicSymmetric τ ↔
      (∀ i j k, τ i j k = τ j i k) ∧ (∀ i j k, τ i j k = τ i k j) := by
  constructor
  · intro h
    exact ⟨cubicSymmetric_swap12 h, cubicSymmetric_swap23 h⟩
  · rintro ⟨h12,h23⟩ σ v
    have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
    have h12' : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
    generalize hs0 : σ 0 = a at *
    generalize hs1 : σ 1 = b at *
    generalize hs2 : σ 2 = c at *
    fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num at *
    all_goals grind

/-- The ordered-index squared norm vanishes exactly for the zero tensor. -/
theorem cubicNormSq_eq_zero_iff (τ : Cubic4) : cubicNormSq τ = 0 ↔ τ = 0 := by
  constructor
  · intro h
    funext i j k
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
        sq_nonneg (τ i j k))))).mp h i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      Finset.sum_nonneg (fun k _ => sq_nonneg (τ i j k)))).mp hi j (Finset.mem_univ j)
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      sq_nonneg (τ i j k))).mp hj k (Finset.mem_univ k)
    change τ i j k = 0
    nlinarith [sq_nonneg (τ i j k)]
  · intro h
    simp [h,cubicNormSq]

/-- A nonzero cubic has strictly positive ordered-index squared norm. -/
theorem cubicNormSq_pos {τ : Cubic4} (hτ : τ ≠ 0) : 0 < cubicNormSq τ := by
  exact lt_of_le_of_ne (cubicNormSq_nonneg τ) (Ne.symm (mt (cubicNormSq_eq_zero_iff τ).mp hτ))

/-- A symmetric cubic in four dimensions is determined by its four
all-distinct components and its four repeated-index vectors. -/
theorem cubic_ext {τ υ : Cubic4} (hτ : CubicSymmetric τ) (hυ : CubicSymmetric υ)
    (hr : ∀ i k, τ i i k = υ i i k)
    (h0 : τ 1 2 3 = υ 1 2 3) (h1 : τ 0 2 3 = υ 0 2 3)
    (h2 : τ 0 1 3 = υ 0 1 3) (h3 : τ 0 1 2 = υ 0 1 2) : τ = υ := by
  have hτ12 := cubicSymmetric_swap12 hτ
  have hτ23 := cubicSymmetric_swap23 hτ
  have hυ12 := cubicSymmetric_swap12 hυ
  have hυ23 := cubicSymmetric_swap23 hυ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    grind

end
end SecondPinching
