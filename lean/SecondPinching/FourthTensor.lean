import SecondPinching.Admissible

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Ordered-index four-tensors and the ordinary trace, Section 3.
All symmetry statements quantify over every permutation of four slots. -/

abbrev Fourth4 := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

def FourthSymmetric (U : Fourth4) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → Fin 4),
    U (v (σ 0)) (v (σ 1)) (v (σ 2)) (v (σ 3)) = U (v 0) (v 1) (v 2) (v 3)

/-- The ordered-index inner products in Section 2. -/
def matrixInner (X Y : Matrix4) : ℝ := ∑ i, ∑ j, X i j * Y i j

def fourthInner (U V : Fourth4) : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, U i j k l * V i j k l

def fourthNormSq (U : Fourth4) : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, (U i j k l)^2

/-- The ordinary trace T_0 in Definition 3.1, also defined on arbitrary arrays. -/
def ordinaryTrace (U : Fourth4) : Matrix4 := fun k l => ∑ i, U i i k l

theorem fourthSymmetric_swap12 {U : Fourth4} (h : FourthSymmetric U)
    (i j k l : Fin 4) : U i j k l = U j i k l := by
  simpa [Equiv.swap_apply_def] using (h (Equiv.swap 0 1) ![i,j,k,l]).symm

theorem fourthSymmetric_swap23 {U : Fourth4} (h : FourthSymmetric U)
    (i j k l : Fin 4) : U i j k l = U i k j l := by
  simpa [Equiv.swap_apply_def] using (h (Equiv.swap 1 2) ![i,j,k,l]).symm

theorem fourthSymmetric_swap34 {U : Fourth4} (h : FourthSymmetric U)
    (i j k l : Fin 4) : U i j k l = U i j l k := by
  simpa [Equiv.swap_apply_def] using (h (Equiv.swap 2 3) ![i,j,k,l]).symm

/-- Three adjacent swaps are equivalent to full four-slot symmetry. -/
theorem fourthSymmetric_iff_swaps (U : Fourth4) : FourthSymmetric U ↔
    (∀ i j k l, U i j k l = U j i k l) ∧
    (∀ i j k l, U i j k l = U i k j l) ∧
    (∀ i j k l, U i j k l = U i j l k) := by
  constructor
  · intro h
    exact ⟨fourthSymmetric_swap12 h,fourthSymmetric_swap23 h,fourthSymmetric_swap34 h⟩
  · rintro ⟨h12,h23,h34⟩ σ v
    have h01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have h02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
    have h03 : σ 0 ≠ σ 3 := σ.injective.ne (by decide)
    have h12' : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
    have h13 : σ 1 ≠ σ 3 := σ.injective.ne (by decide)
    have h23' : σ 2 ≠ σ 3 := σ.injective.ne (by decide)
    generalize hs0 : σ 0 = a at *
    generalize hs1 : σ 1 = b at *
    generalize hs2 : σ 2 = c at *
    generalize hs3 : σ 3 = d at *
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> norm_num at *
    all_goals grind

theorem fourthSymmetric_sub {U V : Fourth4} (hU : FourthSymmetric U)
    (hV : FourthSymmetric V) : FourthSymmetric (U-V) := by
  intro σ v
  change U (v (σ 0)) (v (σ 1)) (v (σ 2)) (v (σ 3)) -
    V (v (σ 0)) (v (σ 1)) (v (σ 2)) (v (σ 3)) = _
  rw [hU σ v,hV σ v]
  rfl

/-- The matrix pairing agrees with the trace convention for symmetric matrices. -/
theorem matrixInner_eq_trace_mul (X Y : Matrix4) (hY : Y.IsSymm) :
    matrixInner X Y = Matrix.trace (X*Y) := by
  simp only [matrixInner,Matrix.trace,Matrix.diag,Matrix.mul_apply,hY.apply]

/-- Compatibility with the already formalised squared matrix norm. -/
theorem matrixInner_self (X : Matrix4) : matrixInner X X = matrixNormSq X := by
  simp only [matrixInner,matrixNormSq,pow_two]

/-- Positivity of the ordered four-tensor inner product. -/
theorem fourthInner_self_nonneg (U : Fourth4) : 0 ≤ fourthInner U U := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => mul_self_nonneg (U i j k l)))))

theorem fourthInner_comm (U V : Fourth4) : fourthInner U V = fourthInner V U := by
  simp only [fourthInner,mul_comm]

theorem fourthInner_self (U : Fourth4) : fourthInner U U = fourthNormSq U := by
  simp only [fourthInner,fourthNormSq,pow_two]

theorem fourthInner_sub_left (U V W : Fourth4) :
    fourthInner (U-V) W = fourthInner U W - fourthInner V W := by
  simp [fourthInner,sub_mul,Finset.sum_sub_distrib]

theorem fourthInner_sub_right (U V W : Fourth4) :
    fourthInner U (V-W) = fourthInner U V - fourthInner U W := by
  simp [fourthInner,mul_sub,Finset.sum_sub_distrib]

theorem fourthNormSq_eq_zero_iff (U : Fourth4) : fourthNormSq U = 0 ↔ U = 0 := by
  constructor
  · intro h
    funext i j k l
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (U i j k l)))))).mp h i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
      Finset.sum_nonneg (fun l _ => sq_nonneg (U i j k l))))).mp hi j (Finset.mem_univ j)
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      Finset.sum_nonneg (fun l _ => sq_nonneg (U i j k l)))).mp hj k (Finset.mem_univ k)
    have hl := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => sq_nonneg (U i j k l))).mp hk l (Finset.mem_univ l)
    change U i j k l = 0
    nlinarith [sq_nonneg (U i j k l)]
  · intro h
    simp [h,fourthNormSq]

theorem ordinaryTrace_symmetric {U : Fourth4} (hU : FourthSymmetric U) :
    (ordinaryTrace U).IsSymm := by
  ext k l
  simp only [Matrix.transpose_apply,ordinaryTrace]
  apply Finset.sum_congr rfl
  intro i _
  exact fourthSymmetric_swap34 hU i i l k

theorem ordinaryTrace_sub (U V : Fourth4) : ordinaryTrace (U-V) = ordinaryTrace U-ordinaryTrace V := by
  ext k l
  simp [ordinaryTrace,Finset.sum_sub_distrib]

end
end SecondPinching
