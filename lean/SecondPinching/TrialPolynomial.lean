import SecondPinching.HessianDecomposition
import SecondPinching.ScalarReduction

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- The adjoint Z* in eq:Zadjoint, using the ordered matrix pairing. -/
def mixedGramAdjoint (μ : Vector4) (τ : Cubic4) (v : Vector4) : Matrix4 :=
  fun i j => (1/8 : ℝ) * ∑ l, (4*μ l-μ i-μ j)*τ i j l*v l

theorem mixedGramAdjoint_pairing (μ : Vector4) (τ : Cubic4) (v : Vector4) (Y : Matrix4) :
    matrixInner (mixedGramAdjoint μ τ v) Y = v ⬝ᵥ mixedGramOperator μ τ Y := by
  simp [mixedGramAdjoint, matrixInner, mixedGramOperator, dotProduct, Fin.sum_univ_succ]
  ring

theorem mixedGramAdjoint_smul (μ : Vector4) (τ : Cubic4) (v : Vector4) (s : ℝ) :
    mixedGramAdjoint μ τ (s • v) = s • mixedGramAdjoint μ τ v := by
  ext i j
  simp [mixedGramAdjoint, Fin.sum_univ_succ]
  ring

/-- Both cubic traces are required for the trace-free codomain of Z*. -/
theorem mixedGramAdjoint_codomain (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (v : Vector4) :
    (mixedGramAdjoint μ τ v).IsSymm ∧ Matrix.trace (mixedGramAdjoint μ τ v) = 0 := by
  obtain ⟨hτ,_hμ,_hn,_hτn,ht,hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  constructor
  · ext i j
    simp only [Matrix.transpose_apply, mixedGramAdjoint, cubicSymmetric_swap12 hτ j i]
    congr 2
    funext l
    ring
  · have he : Matrix.trace (mixedGramAdjoint μ τ v) =
        (1/8 : ℝ) * ∑ l, (4*μ l*(∑ i, τ i i l)-2*(∑ i, μ i*τ i i l))*v l := by
      simp [mixedGramAdjoint, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
      ring
    simp [he, ht, hw]

theorem matrixInner_smul_left (s : ℝ) (X Y : Matrix4) :
    matrixInner (s • X) Y = s * matrixInner X Y := by
  simp [matrixInner, Finset.mul_sum, mul_assoc]

theorem matrixInner_smul_right (s : ℝ) (X Y : Matrix4) :
    matrixInner X (s • Y) = s * matrixInner X Y := by
  rw [matrixInner_comm, matrixInner_smul_left, matrixInner_comm Y X]

theorem matrixInner_sub_left (X Y Z : Matrix4) :
    matrixInner (X-Y) Z = matrixInner X Z - matrixInner Y Z := by
  simp [matrixInner, sub_mul, Finset.sum_sub_distrib]

theorem matrixInner_add_left (X Y Z : Matrix4) :
    matrixInner (X+Y) Z = matrixInner X Z + matrixInner Y Z := by
  simp [matrixInner, add_mul, Finset.sum_add_distrib]

theorem matrixGramOperator_smul (A Y : Matrix4) (s : ℝ) :
    matrixGramOperator A (s • Y) = s • matrixGramOperator A Y := by
  ext i j
  simp [matrixGramOperator, Matrix.mul_apply, Matrix.trace, Matrix.diag,
    Fin.sum_univ_succ]
  ring

/-- c in eq:abc, in the principal frame. -/
def cubicC (μ : Vector4) (τ : Cubic4) : ℝ := ∑ i, ∑ j, ∑ k, μ i*(τ i j k)^2

/-- v is fixed with (A,tau), independently of t. -/
def trialVector (μ : Vector4) (τ : Cubic4) : Vector4 :=
  (-7 : ℝ) • (Matrix.diagonal μ *ᵥ cubicD μ τ)

/-- B_t in eq:choice. -/
def trialBt (μ : Vector4) (τ : Cubic4) (t : ℝ) : Matrix4 :=
  hessianE (Matrix.diagonal μ) τ t - mixedGramAdjoint μ τ (trialVector μ τ)

/-- B means B_(1/2), not B_t. -/
def trialB (μ : Vector4) (τ : Cubic4) : Matrix4 := trialBt μ τ (1/2)

/-- Y_t in eq:choice. -/
def trialY (μ : Vector4) (τ : Cubic4) (t : ℝ) : Matrix4 := (8*t) • trialB μ τ

/-- L_4 in eq:L; zero average is a separate geometric assertion. -/
def correctionL4 (μ : Vector4) (τ : Cubic4) (t : ℝ) : ℝ :=
  t*(2*cubicA μ τ+cubicB μ τ-quarticMoment (Matrix.diagonal μ))

/-- L_3 in eq:L; d is retained. -/
def correctionL3 (μ : Vector4) (τ : Cubic4) (t : ℝ) : ℝ :=
  t*(-(cubicMoment (Matrix.diagonal μ))^2+
    2*cubicMoment (Matrix.diagonal μ)*cubicC μ τ+3*(cubicD μ τ ⬝ᵥ cubicD μ τ))

/-- J in eq:L. -/
def correctionJ (μ : Vector4) (τ : Cubic4) (t : ℝ) : ℝ :=
  t*(cubicA μ τ-2*cubicB μ τ)-phiNormSq (Matrix.diagonal μ)-t/4

/-- The concrete expression eq:Qt, with B fixed at t=1/2. -/
def trialQ (μ : Vector4) (τ : Cubic4) (t : ℝ) : ℝ :=
  16*t*matrixInner (trialBt μ τ t) (trialB μ τ)-
    64*t^2*matrixInner (trialB μ τ) (matrixGramOperator (Matrix.diagonal μ) (trialB μ τ))+
    2*(hessianB0 μ τ ⬝ᵥ trialVector μ τ)-
    trialVector μ τ ⬝ᵥ (vectorGramOperator τ *ᵥ trialVector μ τ)

/-- W_t is exactly eq:Wt, including all three correction terms. -/
def pinchingW (μ : Vector4) (τ : Cubic4) (t : ℝ) : ℝ :=
  3*t*(cubicA μ τ-2*cubicB μ τ)+t*(35*t-28)/16-
    (3/2 : ℝ)*phiNormSq (Matrix.diagonal μ)-trialQ μ τ t-
    (89/8 : ℝ)*correctionL4 μ τ t+16*correctionL3 μ τ t+
    (13/4 : ℝ)*correctionJ μ τ t

theorem trialBt_codomain (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    (trialBt μ τ t).IsSymm ∧ Matrix.trace (trialBt μ τ t) = 0 := by
  obtain ⟨he,het⟩ := hessianE_codomain_diagonal μ τ had t
  obtain ⟨hz,hzt⟩ := mixedGramAdjoint_codomain μ τ had (trialVector μ τ)
  exact ⟨he.sub hz, by simp [trialBt, Matrix.trace_sub, het, hzt]⟩

theorem trialB_codomain (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) :
    (trialB μ τ).IsSymm ∧ Matrix.trace (trialB μ τ) = 0 :=
  trialBt_codomain μ τ had (1/2)

theorem trialY_codomain (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    (trialY μ τ t).IsSymm ∧ Matrix.trace (trialY μ τ t) = 0 := by
  obtain ⟨hb,hbt⟩ := trialB_codomain μ τ had
  exact ⟨hb.smul _, by simp [trialY, Matrix.trace_smul, hbt]⟩

/-- Expanded B in eq:Zadjoint. No admissibility is needed for this identity. -/
theorem trialB_expanded (μ : Vector4) (τ : Cubic4) :
    trialB μ τ = (5/8 : ℝ) • (Matrix.diagonal μ)^2 -
      (cubicMoment (Matrix.diagonal μ)/2) • Matrix.diagonal μ -
      (1/32 : ℝ) • (1 : Matrix4) - (1/2 : ℝ) • cubicGramMatrix τ +
      (7 : ℝ) • mixedGramAdjoint μ τ (Matrix.diagonal μ *ᵥ cubicD μ τ) := by
  unfold trialB trialBt trialVector
  rw [mixedGramAdjoint_smul]
  ext i j
  simp [hessianE, normalizedPhi, hessianPsi]
  ring

/-- Q_t really is the joint contraction expression at the stated trial variables. -/
theorem trialQ_eq_joint (μ : Vector4) (τ : Cubic4) (t : ℝ) :
    trialQ μ τ t =
      2*matrixInner (hessianE (Matrix.diagonal μ) τ t) (trialY μ τ t)+
      2*(hessianB0 μ τ ⬝ᵥ trialVector μ τ)-
      matrixInner (trialY μ τ t) (matrixGramOperator (Matrix.diagonal μ) (trialY μ τ t))-
      2*(trialVector μ τ ⬝ᵥ mixedGramOperator μ τ (trialY μ τ t))-
      trialVector μ τ ⬝ᵥ (vectorGramOperator τ *ᵥ trialVector μ τ) := by
  rw [← mixedGramAdjoint_pairing]
  simp only [trialQ, trialY, trialBt, matrixInner_sub_left, matrixInner_smul_right,
    matrixGramOperator_smul, matrixInner_smul_left, mixedGramAdjoint_pairing]
  ring

/-- The affine dependence of B_t; B remains the value at one half. -/
theorem trialBt_affine (μ : Vector4) (τ : Cubic4) (t : ℝ) :
    trialBt μ τ t = trialBt μ τ 0 + t • hessianPsi (Matrix.diagonal μ) τ := by
  ext i j
  simp [trialBt, hessianE]
  ring

/-- The quadratic coefficient in the proof of prop:convex. -/
def wQuadraticCoeff (μ : Vector4) (τ : Cubic4) : ℝ :=
  35/16+64*matrixInner (trialB μ τ) (matrixGramOperator (Matrix.diagonal μ) (trialB μ τ))-
    16*matrixInner (hessianPsi (Matrix.diagonal μ) τ) (trialB μ τ)

/-- The linear coefficient, keeping the notation from eq:Wt. -/
def wLinearCoeff (μ : Vector4) (τ : Cubic4) : ℝ :=
  3*(cubicA μ τ-2*cubicB μ τ)-7/4-
    16*matrixInner (trialBt μ τ 0) (trialB μ τ)-
    (89/8 : ℝ)*(2*cubicA μ τ+cubicB μ τ-quarticMoment (Matrix.diagonal μ))+
    16*(-(cubicMoment (Matrix.diagonal μ))^2+
      2*cubicMoment (Matrix.diagonal μ)*cubicC μ τ+3*(cubicD μ τ ⬝ᵥ cubicD μ τ))+
    (13/4 : ℝ)*(cubicA μ τ-2*cubicB μ τ-1/4)

/-- The constant coefficient from prop:convex. -/
def wConstantCoeff (μ : Vector4) (τ : Cubic4) : ℝ :=
  -(19/4 : ℝ)*phiNormSq (Matrix.diagonal μ)-
    21*((Matrix.diagonal μ *ᵥ cubicD μ τ) ⬝ᵥ (Matrix.diagonal μ *ᵥ cubicD μ τ))+
    49*((Matrix.diagonal μ *ᵥ cubicD μ τ) ⬝ᵥ
      (vectorGramOperator τ *ᵥ (Matrix.diagonal μ *ᵥ cubicD μ τ)))

theorem trial_vector_terms (μ : Vector4) (τ : Cubic4) :
    2*(hessianB0 μ τ ⬝ᵥ trialVector μ τ)-
      trialVector μ τ ⬝ᵥ (vectorGramOperator τ *ᵥ trialVector μ τ) =
    21*((Matrix.diagonal μ *ᵥ cubicD μ τ) ⬝ᵥ (Matrix.diagonal μ *ᵥ cubicD μ τ))-
    49*((Matrix.diagonal μ *ᵥ cubicD μ τ) ⬝ᵥ
      (vectorGramOperator τ *ᵥ (Matrix.diagonal μ *ᵥ cubicD μ τ))) := by
  rw [hessianB0_eq_matrix]
  simp [trialVector, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

/-- Identification with the actual W, rather than an unrelated scalar quadratic. -/
theorem pinchingW_eq_quadratic (μ : Vector4) (τ : Cubic4) (t : ℝ) :
    pinchingW μ τ t = quadratic (wQuadraticCoeff μ τ) (wLinearCoeff μ τ)
      (wConstantCoeff μ τ) t := by
  have hq : trialQ μ τ t =
      16*t*(matrixInner (trialBt μ τ 0) (trialB μ τ)+
        t*matrixInner (hessianPsi (Matrix.diagonal μ) τ) (trialB μ τ))-
      64*t^2*matrixInner (trialB μ τ) (matrixGramOperator (Matrix.diagonal μ) (trialB μ τ))+
      (2*(hessianB0 μ τ ⬝ᵥ trialVector μ τ)-
        trialVector μ τ ⬝ᵥ (vectorGramOperator τ *ᵥ trialVector μ τ)) := by
    unfold trialQ
    rw [trialBt_affine μ τ t, matrixInner_add_left, matrixInner_smul_left]
    ring
  rw [pinchingW, hq, trial_vector_terms]
  unfold quadratic wQuadraticCoeff wLinearCoeff wConstantCoeff correctionL4 correctionL3 correctionJ
  ring

theorem pinchingW_zero (μ : Vector4) (τ : Cubic4) :
    pinchingW μ τ 0 = wConstantCoeff μ τ := by
  rw [pinchingW_eq_quadratic]
  simp [quadratic]

/-- The exact expanded polynomial eq:endpointexpanded. The identity p=u-m^2-1/4
is used; no positivity certificate is assumed or evaluated here. -/
theorem pinchingW_half_expanded (μ : Vector4) (τ : Cubic4)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1) :
    pinchingW μ τ (1/2) = 21/32+(13/16 : ℝ)*phiNormSq (Matrix.diagonal μ)-
      (39/16 : ℝ)*(cubicMoment (Matrix.diagonal μ))^2-8*cubicA μ τ-
      (189/16 : ℝ)*cubicB μ τ+16*cubicMoment (Matrix.diagonal μ)*cubicC μ τ+
      24*(cubicD μ τ ⬝ᵥ cubicD μ τ)-8*matrixNormSq (trialB μ τ)+
      16*matrixInner (trialB μ τ) (matrixGramOperator (Matrix.diagonal μ) (trialB μ τ))-
      21*((Matrix.diagonal μ *ᵥ cubicD μ τ) ⬝ᵥ (Matrix.diagonal μ *ᵥ cubicD μ τ))+
      49*((Matrix.diagonal μ *ᵥ cubicD μ τ) ⬝ᵥ
        (vectorGramOperator τ *ᵥ (Matrix.diagonal μ *ᵥ cubicD μ τ))) := by
  have hq : trialQ μ τ (1/2) =
      8*matrixNormSq (trialB μ τ)-
      16*matrixInner (trialB μ τ) (matrixGramOperator (Matrix.diagonal μ) (trialB μ τ))+
      (2*(hessianB0 μ τ ⬝ᵥ trialVector μ τ)-
        trialVector μ τ ⬝ᵥ (vectorGramOperator τ *ᵥ trialVector μ τ)) := by
    change 16*(1/2 : ℝ)*matrixInner (trialB μ τ) (trialB μ τ)-_+_-_ = _
    rw [matrixInner_self]
    ring
  rw [pinchingW, hq, trial_vector_terms]
  unfold correctionL4 correctionL3 correctionJ
  rw [phiNormSq_diagonal μ hμ hn]
  ring

end
end SecondPinching
