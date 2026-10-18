import SecondPinching.HessianQuantities

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- The minimum-norm trace correction U_0 in Section 4. -/
def hessianTraceCorrection (μ : Vector4) (t : ℝ) : Fourth4 :=
  ordinaryTraceAdjoint ((-3*t/8) • Matrix.diagonal μ)

theorem scaledDiagonal_symmetric (μ : Vector4) (s : ℝ) :
    (s • Matrix.diagonal μ).IsSymm := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.transpose_apply, h, eq_comm]

theorem hessianTraceCorrection_symmetric (μ : Vector4) (t : ℝ) :
    FourthSymmetric (hessianTraceCorrection μ t) :=
  ordinaryTraceAdjoint_symmetric _ (scaledDiagonal_symmetric μ _)

/-- The inverse-Gram construction of U_0, rather than an unrelated trace lift. -/
theorem hessianTraceCorrection_inverse (μ : Vector4) (t : ℝ)
    (hμ : ∑ i, μ i = 0) :
    hessianTraceCorrection μ t =
      ordinaryTraceAdjoint (ordinaryTraceGramInverse ((-t/2) • Matrix.diagonal μ)) := by
  have hx : ordinaryTraceGramInverse ((-t/2) • Matrix.diagonal μ) =
      (-3*t/8) • Matrix.diagonal μ := by
    ext i j
    simp [ordinaryTraceGramInverse, Matrix.trace_smul, Matrix.trace_diagonal, hμ]
    ring
  rw [hx]
  rfl

/-- The displayed formula U_0 = -3t Sym(I tensor A)/8. -/
theorem hessianTraceCorrection_sym (μ : Vector4) (t : ℝ) :
    hessianTraceCorrection μ t =
      (-3*t/8) • symmetrizeFourth (identityTensorProduct (Matrix.diagonal μ)) := by
  rw [← ordinaryTraceAdjoint_eq_sym _ (Matrix.isSymm_diagonal μ)]
  exact ordinaryTraceAdjointLinear.map_smul _ _

theorem ordinaryTrace_hessianTraceCorrection (μ : Vector4) (t : ℝ)
    (hμ : ∑ i, μ i = 0) :
    ordinaryTrace (hessianTraceCorrection μ t) = (-t/2) • Matrix.diagonal μ := by
  rw [hessianTraceCorrection_inverse μ t hμ]
  exact (ordinaryTrace_inverse _ (scaledDiagonal_symmetric μ _)).1

theorem hessianTraceCorrection_norm (μ : Vector4) (t : ℝ)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1) :
    fourthNormSq (hessianTraceCorrection μ t) = (3/16 : ℝ) * t^2 := by
  rw [← fourthInner_self]
  change fourthInner (hessianTraceCorrection μ t)
    (ordinaryTraceAdjoint ((-3*t/8) • Matrix.diagonal μ)) = _
  rw [ordinaryTrace_adjoint_pairing _ (hessianTraceCorrection_symmetric μ t) _
    (scaledDiagonal_symmetric μ _), ordinaryTrace_hessianTraceCorrection μ t hμ]
  have raw : matrixInner ((-t/2) • Matrix.diagonal μ) ((-3*t/8) • Matrix.diagonal μ) =
      (3/16 : ℝ) * t^2 * (∑ i, (μ i)^2) := by
    simp [matrixInner, Matrix.diagonal_apply, Fin.sum_univ_succ]
    ring
  rw [raw, hn, mul_one]

theorem weightedTrace_hessianTraceCorrection (μ : Vector4) (t : ℝ)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1) :
    weightedTrace (Matrix.diagonal μ) (hessianTraceCorrection μ t) =
      (-t/16) • ((1 : Matrix4) + (4 : ℝ) • (Matrix.diagonal μ)^2) := by
  rw [hessianTraceCorrection, weightedTrace_ordinaryTraceAdjoint_diagonal μ _
    (scaledDiagonal_symmetric μ _), hμ]
  have hsum : (∑ i, μ i * (((-3*t/8) • Matrix.diagonal μ) i i)) = -3*t/8 := by
    calc
      _ = (-3*t/8) * (∑ i, (μ i)^2) := by
        simp [Fin.sum_univ_succ]
        ring
      _ = _ := by rw [hn, mul_one]
  rw [hsum]
  ext k l
  by_cases h : k = l <;>
    simp [Matrix.diagonal_pow, Matrix.one_apply, h]
  ring

/-- Both cubic trace constraints, and no condition d=0, give N_tau U_0 = 0. -/
theorem cubicContraction_hessianTraceCorrection (μ : Vector4) (τ : Cubic4)
    (hτ : CubicSymmetric τ) (ht : ∀ k, ∑ i, τ i i k = 0)
    (hw : ∀ k, ∑ i, μ i * τ i i k = 0) (t : ℝ) :
    cubicContraction τ (hessianTraceCorrection μ t) = 0 := by
  rw [hessianTraceCorrection, cubicContraction_ordinaryTraceAdjoint τ hτ _
    (scaledDiagonal_symmetric μ _)]
  funext l
  simp only [ht, zero_mul, Finset.sum_const_zero, zero_add]
  have he : (∑ i, ∑ j, τ i j l * (((-3*t/8) • Matrix.diagonal μ) i j)) =
      (-3*t/8) * (∑ i, μ i * τ i i l) := by
    simp [Matrix.diagonal_apply, Fin.sum_univ_succ]
    ring
  rw [he, hw l]
  simp

/-- The trace lift is perpendicular to the full kernel, using the actual adjoint identity. -/
theorem hessianTraceCorrection_orthogonal (μ : Vector4) (t : ℝ)
    (V : Fourth4) (hV : TraceFreeFourth V) :
    fourthInner (hessianTraceCorrection μ t) V = 0 := by
  rw [fourthInner_comm, hessianTraceCorrection,
    ordinaryTrace_adjoint_pairing V hV.1 _ (scaledDiagonal_symmetric μ _), hV.2]
  simp [matrixInner]

/-- The phrase minimum-norm is justified on the entire symmetric trace fibre. -/
theorem hessianTraceCorrection_minimum (μ : Vector4) (t : ℝ)
    (hμ : ∑ i, μ i = 0) (W : Fourth4) (hW : FourthSymmetric W)
    (htr : ordinaryTrace W = (-t/2) • Matrix.diagonal μ) :
    fourthNormSq (hessianTraceCorrection μ t) ≤ fourthNormSq W := by
  have hv : TraceFreeFourth (W - hessianTraceCorrection μ t) := by
    refine ⟨fourthSymmetric_sub hW (hessianTraceCorrection_symmetric μ t), ?_⟩
    rw [ordinaryTrace_sub, htr, ordinaryTrace_hessianTraceCorrection μ t hμ, sub_self]
  have ho := hessianTraceCorrection_orthogonal μ t _ hv
  rw [fourthInner_sub_right, fourthInner_self, fourthInner_comm] at ho
  have hn := fourthInner_self_nonneg (W - hessianTraceCorrection μ t)
  rw [fourthInner_self, fourthNormSq_sub] at hn
  linarith

end
end SecondPinching
