import SecondPinching.Contractions

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Square completion for the actual two contractions. The projected norm is
not replaced by the coordinate expressions K_A, Z, H_tau in this module. -/

theorem fourthSymmetric_add {U V : Fourth4} (hU : FourthSymmetric U)
    (hV : FourthSymmetric V) : FourthSymmetric (U + V) := by
  intro σ x
  change U (x (σ 0)) (x (σ 1)) (x (σ 2)) (x (σ 3)) +
    V (x (σ 0)) (x (σ 1)) (x (σ 2)) (x (σ 3)) = _
  rw [hU σ x, hV σ x]
  rfl

theorem fourthInner_add_right (U V W : Fourth4) :
    fourthInner U (V + W) = fourthInner U V + fourthInner U W := by
  simp [fourthInner, mul_add, Finset.sum_add_distrib]

theorem fourthNormSq_sub (U V : Fourth4) :
    fourthNormSq (U - V) = fourthNormSq U - 2 * fourthInner U V + fourthNormSq V := by
  rw [← fourthInner_self, fourthInner_sub_left, fourthInner_sub_right,
    fourthInner_sub_right, fourthInner_self, fourthInner_self, fourthInner_comm V U]
  ring

/-- The trial tensor U=P_0(T_A^*Y+N_tau^*v), Section 3 and prop:meanconvex. -/
def jointTrialTensor (A Y : Matrix4) (τ : Cubic4) (v : Vector4) : Fourth4 :=
  ordinaryTraceFreeProjection (weightedTraceAdjoint A Y + cubicContractionAdjoint τ v)

theorem jointTrialTensor_mem (A Y : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (v : Vector4) :
    TraceFreeFourth (jointTrialTensor A Y τ v) :=
  ordinaryTraceFreeProjection_mem _ (fourthSymmetric_add
    (weightedTraceAdjoint_symmetric A Y hA hY) (cubicContractionAdjoint_symmetric τ hτ v))

/-- The actual pairing after trace removal; it uses all H_4 orthogonality. -/
theorem jointTrialTensor_pairing (A Y : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (v : Vector4)
    (V : Fourth4) (hV : TraceFreeFourth V) :
    fourthInner V (jointTrialTensor A Y τ v) =
      matrixInner (weightedTrace A V) Y + cubicContraction τ V ⬝ᵥ v := by
  have hp := ordinaryTraceFreeProjection_orthogonal
    (weightedTraceAdjoint A Y + cubicContractionAdjoint τ v)
    (fourthSymmetric_add (weightedTraceAdjoint_symmetric A Y hA hY)
      (cubicContractionAdjoint_symmetric τ hτ v)) V hV
  rw [fourthInner_comm, fourthInner_sub_right, fourthInner_add_right,
    weightedTrace_adjoint_pairing A Y hA hY V hV.1,
    cubicContraction_adjoint_pairing τ hτ v V hV.1] at hp
  change _ - fourthInner V (jointTrialTensor A Y τ v) = 0 at hp
  linarith

/-- The square-completion expression before evaluating its three Gram terms. -/
def jointSquareBound (A Y E : Matrix4) (τ : Cubic4) (v b₀ : Vector4) : ℝ :=
  2 * matrixInner E Y + 2 * (b₀ ⬝ᵥ v) - fourthNormSq (jointTrialTensor A Y τ v)

/-- Exact remainder identity underlying the joint estimate and prop:meanconvex.
The prescribed contractions are hypotheses, not definitions of V. -/
theorem joint_square_remainder (A Y E : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (v b₀ : Vector4)
    (V : Fourth4) (hV : TraceFreeFourth V)
    (hE : weightedTrace A V = E) (hb : cubicContraction τ V = b₀) :
    fourthNormSq V - jointSquareBound A Y E τ v b₀ =
      fourthNormSq (V - jointTrialTensor A Y τ v) := by
  rw [fourthNormSq_sub, jointTrialTensor_pairing A Y hA hY τ hτ v V hV, hE, hb]
  unfold jointSquareBound
  ring

/-- The displayed joint estimate at the opening of Section 3. -/
theorem joint_square_estimate (A Y E : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (v b₀ : Vector4)
    (V : Fourth4) (hV : TraceFreeFourth V)
    (hE : weightedTrace A V = E) (hb : cubicContraction τ V = b₀) :
    jointSquareBound A Y E τ v b₀ ≤ fourthNormSq V := by
  have he := joint_square_remainder A Y E hA hY τ hτ v b₀ V hV hE hb
  have hn := fourthInner_self_nonneg (V - jointTrialTensor A Y τ v)
  rw [fourthInner_self] at hn
  linarith

end
end SecondPinching
