import SecondPinching.FourthSymmetrization

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Lemma 3.2's orthogonal projection, using the actual ordered pairings.
The projection is characterized, proved unique, and explicitly linear. -/

/-- The space H_4 of Definition 3.1, stated as a membership predicate. -/
def TraceFreeFourth (U : Fourth4) : Prop := FourthSymmetric U ∧ ordinaryTrace U = 0

/-- The defining range and orthogonality properties of P_0 U. -/
def IsTraceFreeProjectionAt (U V : Fourth4) : Prop :=
  TraceFreeFourth V ∧ ∀ W : Fourth4, TraceFreeFourth W → fourthInner (U-V) W = 0

/-- The formula in equation eq:P0. -/
def ordinaryTraceFreeProjection (U : Fourth4) : Fourth4 :=
  U - ordinaryTraceAdjoint (ordinaryTraceGramInverse (ordinaryTrace U))

/-- The explicit formula is genuinely a two-sided inverse on Sym^2. -/
theorem ordinaryTrace_inverse (X : Matrix4) (hX : X.IsSymm) :
    ordinaryTrace (ordinaryTraceAdjoint (ordinaryTraceGramInverse X)) = X ∧
    ordinaryTraceGramInverse (ordinaryTrace (ordinaryTraceAdjoint X)) = X := by
  constructor
  · rw [ordinaryTrace_adjoint_gram _ (ordinaryTraceGramInverse_symmetric X hX),
      ordinaryTraceGram_inverse_left]
  · rw [ordinaryTrace_adjoint_gram X hX,ordinaryTraceGram_inverse_right]

/-- The proposed projection lies in the specified trace-free symmetric space. -/
theorem ordinaryTraceFreeProjection_mem (U : Fourth4) (hU : FourthSymmetric U) :
    TraceFreeFourth (ordinaryTraceFreeProjection U) := by
  have hT := ordinaryTrace_symmetric hU
  constructor
  · exact fourthSymmetric_sub hU (ordinaryTraceAdjoint_symmetric _
      (ordinaryTraceGramInverse_symmetric _ hT))
  · rw [ordinaryTraceFreeProjection,ordinaryTrace_sub,(ordinaryTrace_inverse _ hT).1,sub_self]

/-- The removed component is orthogonal to every element of H_4. -/
theorem ordinaryTraceFreeProjection_orthogonal (U : Fourth4) (hU : FourthSymmetric U)
    (W : Fourth4) (hW : TraceFreeFourth W) :
    fourthInner (U-ordinaryTraceFreeProjection U) W = 0 := by
  have hX := ordinaryTraceGramInverse_symmetric _ (ordinaryTrace_symmetric hU)
  rw [ordinaryTraceFreeProjection,sub_sub_cancel,fourthInner_comm,
    ordinaryTrace_adjoint_pairing W hW.1 _ hX,hW.2]
  simp [matrixInner]

theorem ordinaryTraceFreeProjection_spec (U : Fourth4) (hU : FourthSymmetric U) :
    IsTraceFreeProjectionAt U (ordinaryTraceFreeProjection U) := by
  exact ⟨ordinaryTraceFreeProjection_mem U hU,fun W hW =>
    ordinaryTraceFreeProjection_orthogonal U hU W hW⟩

/-- The range and orthogonality conditions characterize the projection uniquely. -/
theorem ordinaryTraceFreeProjection_unique (U : Fourth4) (hU : FourthSymmetric U)
    (V : Fourth4) (hV : IsTraceFreeProjectionAt U V) :
    V = ordinaryTraceFreeProjection U := by
  have hp := ordinaryTraceFreeProjection_spec U hU
  have hD : TraceFreeFourth (V-ordinaryTraceFreeProjection U) := by
    refine ⟨fourthSymmetric_sub hV.1.1 hp.1.1,?_⟩
    rw [ordinaryTrace_sub,hV.1.2,hp.1.2,sub_self]
  have h1 := hp.2 _ hD
  have h2 := hV.2 _ hD
  have hzero : fourthNormSq (V-ordinaryTraceFreeProjection U) = 0 := by
    rw [← fourthInner_self,fourthInner_sub_left]
    simp only [fourthInner_sub_left] at h1 h2
    linarith
  exact sub_eq_zero.mp ((fourthNormSq_eq_zero_iff _).mp hzero)

theorem ordinaryTraceFreeProjection_existsUnique (U : Fourth4) (hU : FourthSymmetric U) :
    ∃! V : Fourth4, IsTraceFreeProjectionAt U V := by
  exact ⟨ordinaryTraceFreeProjection U,ordinaryTraceFreeProjection_spec U hU,
    fun V hV => ordinaryTraceFreeProjection_unique U hU V hV⟩

/-- The projection fixes every element of H_4. -/
theorem ordinaryTraceFreeProjection_eq_self (U : Fourth4) (hU : TraceFreeFourth U) :
    ordinaryTraceFreeProjection U = U := by
  apply (ordinaryTraceFreeProjection_unique U hU.1 U _).symm
  refine ⟨hU,?_⟩
  intro W _
  simp [fourthInner]

theorem ordinaryTraceFreeProjection_idempotent (U : Fourth4) (hU : FourthSymmetric U) :
    ordinaryTraceFreeProjection (ordinaryTraceFreeProjection U) = ordinaryTraceFreeProjection U :=
  ordinaryTraceFreeProjection_eq_self _ (ordinaryTraceFreeProjection_mem U hU)

/-- Self-adjointness follows from the proved orthogonality conditions. -/
theorem ordinaryTraceFreeProjection_self_adjoint (U V : Fourth4)
    (hU : FourthSymmetric U) (hV : FourthSymmetric V) :
    fourthInner (ordinaryTraceFreeProjection U) V =
      fourthInner U (ordinaryTraceFreeProjection V) := by
  have h1 := ordinaryTraceFreeProjection_orthogonal U hU _ (ordinaryTraceFreeProjection_mem V hV)
  have h2 := ordinaryTraceFreeProjection_orthogonal V hV _ (ordinaryTraceFreeProjection_mem U hU)
  simp only [fourthInner_sub_left] at h1 h2
  rw [fourthInner_comm V _,fourthInner_comm (ordinaryTraceFreeProjection V) _] at h2
  linarith

/-- The ordinary trace as a real linear map on the ambient tensor arrays. -/
def ordinaryTraceLinear : Fourth4 →ₗ[ℝ] Matrix4 where
  toFun := ordinaryTrace
  map_add' U V := by ext k l; simp [ordinaryTrace,Finset.sum_add_distrib]
  map_smul' c U := by ext k l; simp [ordinaryTrace,Finset.mul_sum]

/-- The explicit adjoint is real-linear; it restricts to Sym^2 -> Sym^4. -/
def ordinaryTraceAdjointLinear : Matrix4 →ₗ[ℝ] Fourth4 where
  toFun := ordinaryTraceAdjoint
  map_add' X Y := by
    funext i j k l
    simp only [ordinaryTraceAdjoint,Matrix.add_apply,Pi.add_apply]
    ring
  map_smul' c X := by
    funext i j k l
    simp only [ordinaryTraceAdjoint,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

/-- The displayed inverse is also a real linear map. -/
def ordinaryTraceGramInverseLinear : Matrix4 →ₗ[ℝ] Matrix4 where
  toFun := ordinaryTraceGramInverse
  map_add' X Y := by
    ext i j
    simp [ordinaryTraceGramInverse,Matrix.trace_add]
    ring
  map_smul' c X := by
    ext i j
    simp [ordinaryTraceGramInverse,Matrix.trace_smul,smul_smul]
    ring

/-- Equation eq:P0 as an identity of real linear maps on the ambient arrays. -/
def ordinaryTraceFreeProjectionLinear : Fourth4 →ₗ[ℝ] Fourth4 :=
  LinearMap.id - ordinaryTraceAdjointLinear.comp (ordinaryTraceGramInverseLinear.comp ordinaryTraceLinear)

theorem ordinaryTraceFreeProjectionLinear_apply (U : Fourth4) :
    ordinaryTraceFreeProjectionLinear U = ordinaryTraceFreeProjection U := rfl

/-- Lemma 3.2 in components and universal-property form.
Both inverse directions and the actual orthogonal-projection properties are
included, with exactly Sym^2 and Sym^4 as the respective domains. -/
theorem ordinary_trace_lemma (X : Matrix4) (hX : X.IsSymm)
    (U : Fourth4) (hU : FourthSymmetric U) :
    IsOrdinaryTraceAdjointAt X (ordinaryTraceAdjoint X) ∧
    ordinaryTraceAdjoint X = symmetrizeFourth (identityTensorProduct X) ∧
    ordinaryTrace (ordinaryTraceAdjoint X) = (4/3 : ℝ) • X + (Matrix.trace X/6) • (1 : Matrix4) ∧
    ordinaryTrace (ordinaryTraceAdjoint ((3/4 : ℝ) • X - (Matrix.trace X/16) • (1 : Matrix4))) = X ∧
    ordinaryTraceGramInverse (ordinaryTrace (ordinaryTraceAdjoint X)) = X ∧
    IsTraceFreeProjectionAt U
      (U-ordinaryTraceAdjoint (ordinaryTraceGramInverse (ordinaryTrace U))) := by
  exact ⟨ordinaryTraceAdjoint_spec X hX,ordinaryTraceAdjoint_eq_sym X hX,
    ordinaryTrace_adjoint_gram X hX,(ordinaryTrace_inverse X hX).1,
    (ordinaryTrace_inverse X hX).2,ordinaryTraceFreeProjection_spec U hU⟩

end
end SecondPinching
