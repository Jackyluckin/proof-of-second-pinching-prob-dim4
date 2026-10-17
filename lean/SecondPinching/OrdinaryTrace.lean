import SecondPinching.FourthTensor

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The explicit adjoint and inverse formulas in Lemma 3.2.
The adjoint is proved using the ordered-index pairings, with uniqueness. -/

/-- Kronecker symmetry, used without choosing distinct indices. -/
theorem identityEntry_comm (i j : Fin 4) : (1 : Matrix4) i j = (1 : Matrix4) j i := by
  simp [Matrix.one_apply,eq_comm]

/-- The six-term component formula in the proof of Lemma 3.2. -/
def ordinaryTraceAdjoint (X : Matrix4) : Fourth4 := fun i j k l =>
  (1/6 : ℝ)*((1 : Matrix4) i j * X k l + (1 : Matrix4) i k * X j l +
    (1 : Matrix4) i l * X j k + (1 : Matrix4) j k * X i l +
    (1 : Matrix4) j l * X i k + (1 : Matrix4) k l * X i j)

/-- The proposed Gram operator in equation eq:T0Gram. -/
def ordinaryTraceGram (X : Matrix4) : Matrix4 :=
  (4/3 : ℝ) • X + (Matrix.trace X/6) • (1 : Matrix4)

/-- The inverse displayed in equation eq:P0. -/
def ordinaryTraceGramInverse (X : Matrix4) : Matrix4 :=
  (3/4 : ℝ) • X - (Matrix.trace X/16) • (1 : Matrix4)

theorem ordinaryTraceAdjoint_symmetric (X : Matrix4) (hX : X.IsSymm) :
    FourthSymmetric (ordinaryTraceAdjoint X) := by
  apply (fourthSymmetric_iff_swaps _).mpr
  refine ⟨?_,?_,?_⟩
  all_goals intro i j k l
  all_goals simp only [ordinaryTraceAdjoint,hX.apply,identityEntry_comm]
  all_goals ring

/-- The actual ordinary contraction of the proposed adjoint. -/
theorem ordinaryTrace_adjoint_gram (X : Matrix4) (hX : X.IsSymm) :
    ordinaryTrace (ordinaryTraceAdjoint X) = ordinaryTraceGram X := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [ordinaryTrace,ordinaryTraceAdjoint,ordinaryTraceGram,Matrix.trace,
      Matrix.one_apply,Fin.sum_univ_succ,hX.apply] <;> ring_nf
  all_goals nlinarith [hX.apply 0 2]

theorem ordinaryTraceGramInverse_symmetric (X : Matrix4) (hX : X.IsSymm) :
    (ordinaryTraceGramInverse X).IsSymm := by
  ext i j
  simp only [ordinaryTraceGramInverse,Matrix.transpose_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,hX.apply,identityEntry_comm]

theorem ordinaryTraceGram_inverse_left (X : Matrix4) :
    ordinaryTraceGram (ordinaryTraceGramInverse X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ordinaryTraceGram,ordinaryTraceGramInverse,Matrix.trace,
      Fin.sum_univ_succ] <;> ring

theorem ordinaryTraceGram_inverse_right (X : Matrix4) :
    ordinaryTraceGramInverse (ordinaryTraceGram X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ordinaryTraceGram,ordinaryTraceGramInverse,Matrix.trace,
      Fin.sum_univ_succ] <;> ring

/-- The defining adjoint identity, for every symmetric matrix and four-tensor. -/
theorem ordinaryTrace_adjoint_pairing (U : Fourth4) (hU : FourthSymmetric U)
    (X : Matrix4) (hX : X.IsSymm) :
    fourthInner U (ordinaryTraceAdjoint X) = matrixInner (ordinaryTrace U) X := by
  have h12 := fourthSymmetric_swap12 hU
  have h23 := fourthSymmetric_swap23 hU
  have h34 := fourthSymmetric_swap34 hU
  simp [fourthInner,ordinaryTraceAdjoint,matrixInner,ordinaryTrace,
    Matrix.one_apply,Fin.sum_univ_succ,h12,h23,h34,hX.apply]
  ring

/-- A universal-property formulation of T_0^*X in the paper's actual spaces. -/
def IsOrdinaryTraceAdjointAt (X : Matrix4) (T : Fourth4) : Prop :=
  FourthSymmetric T ∧ ∀ U : Fourth4, FourthSymmetric U →
    fourthInner U T = matrixInner (ordinaryTrace U) X

theorem ordinaryTraceAdjoint_spec (X : Matrix4) (hX : X.IsSymm) :
    IsOrdinaryTraceAdjointAt X (ordinaryTraceAdjoint X) := by
  exact ⟨ordinaryTraceAdjoint_symmetric X hX,fun U hU => ordinaryTrace_adjoint_pairing U hU X hX⟩

/-- Uniqueness proves that the component formula is the adjoint, rather than
merely naming an arbitrary tensor-valued expression "adjoint". -/
theorem ordinaryTraceAdjoint_unique (X : Matrix4) (hX : X.IsSymm)
    (T : Fourth4) (hT : IsOrdinaryTraceAdjointAt X T) : T = ordinaryTraceAdjoint X := by
  have hD := fourthSymmetric_sub hT.1 (ordinaryTraceAdjoint_symmetric X hX)
  have hzero : fourthNormSq (T-ordinaryTraceAdjoint X) = 0 := by
    rw [← fourthInner_self,fourthInner_sub_right,hT.2 _ hD,
      ordinaryTrace_adjoint_pairing _ hD X hX,sub_self]
  exact sub_eq_zero.mp ((fourthNormSq_eq_zero_iff _).mp hzero)

/-- Exactly one element of Sym^4 represents the adjoint functional at X. -/
theorem ordinaryTraceAdjoint_existsUnique (X : Matrix4) (hX : X.IsSymm) :
    ∃! T : Fourth4, IsOrdinaryTraceAdjointAt X T := by
  exact ⟨ordinaryTraceAdjoint X,ordinaryTraceAdjoint_spec X hX,
    fun T hT => ordinaryTraceAdjoint_unique X hX T hT⟩

end
end SecondPinching
