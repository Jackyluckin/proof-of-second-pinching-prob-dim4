import SecondPinching.IntrinsicRemainder
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Smoothness is in the finite-dimensional component topology. The scoped
elementwise norm only equips the parameter space; all tensor norm expressions
remain the ordered-index sums defined in the manuscript. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
@[fun_prop] theorem contDiff_matrix_product {A B : E → Matrix4}
    (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) : ContDiff ℝ n (fun x => A x * B x) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  change ContDiff ℝ n (fun x => ∑ k, A x i k * B x k j)
  fun_prop
@[fun_prop] theorem contDiff_matrix_power {A : E → Matrix4}
    (hA : ContDiff ℝ n A) (k : ℕ) : ContDiff ℝ n (fun x => A x ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (contDiff_const : ContDiff ℝ n (fun _ : E => (1 : Matrix4)))
  | succ k ih => simp only [pow_succ]; exact contDiff_matrix_product ih hA
@[fun_prop] theorem contDiff_matrix_trace {A : E → Matrix4}
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (fun x => Matrix.trace (A x)) := by
  unfold Matrix.trace Matrix.diag
  fun_prop
@[fun_prop] theorem contDiff_matrix_of {A : E → (Fin 4 → Fin 4 → ℝ)}
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (fun x => Matrix.of (A x)) := hA
@[fun_prop] theorem contDiff_matrix_transpose {A : E → Matrix4}
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (fun x => (A x)ᵀ) := by
  change ContDiff ℝ n (fun x i j => A x j i)
  fun_prop
@[fun_prop] theorem contDiff_matrix_mulVector {A : E → Matrix4} {v : E → Vector4}
    (hA : ContDiff ℝ n A) (hv : ContDiff ℝ n v) : ContDiff ℝ n (fun x => A x *ᵥ v x) := by
  unfold Matrix.mulVec dotProduct
  fun_prop
@[fun_prop] theorem contDiff_vector_dot {v w : E → Vector4}
    (hv : ContDiff ℝ n v) (hw : ContDiff ℝ n w) : ContDiff ℝ n (fun x => v x ⬝ᵥ w x) := by
  unfold dotProduct
  fun_prop

/-- All five scalar integrands are smooth functions of arbitrary component
arrays and t, before imposing admissibility. No eigenvector map is involved. -/
theorem contDiff_intrinsicIntegrands (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : Matrix4 × Cubic4 × ℝ × Fourth4 =>
      (intrinsicPinchingW x.1 x.2.1 x.2.2.1,
       intrinsicCorrectionL4 x.1 x.2.1 x.2.2.1,
       intrinsicCorrectionL3 x.1 x.2.1 x.2.2.1,
       intrinsicCorrectionJ x.1 x.2.1 x.2.2.1,
       intrinsicPinchingSquare x.1 x.2.1 x.2.2.1 x.2.2.2)) := by
  unfold intrinsicPinchingW intrinsicCorrectionJ phiNormSq matrixNormSq
    intrinsicCorrectionL3 intrinsicCubicC intrinsicCorrectionL4 quarticMoment
    intrinsicCubicB cubicInner cubicMatrixAction intrinsicCubicA
    intrinsicTrialQ matrixInner vectorGramOperator matrixGramOperator
    intrinsicHessianB0 intrinsicPinchingSquare fourthNormSq intrinsicPinchingTrialTensor
    intrinsicTrialY intrinsicTrialB intrinsicTrialBt hessianE
    normalizedPhi cubicMoment hessianPsi cubicGramMatrix
    intrinsicMixedGramAdjoint weightedTrace intrinsicTrialVector intrinsicCubicD
    cubicWeightedTrace jointTrialTensor cubicContractionAdjoint weightedTraceAdjoint
    ordinaryTraceFreeProjection ordinaryTrace ordinaryTraceGramInverse ordinaryTraceAdjoint
  fun_prop

/-- Continuity for component fields on any topological space. This is a
composition result and does not assert that a global frame exists. -/
theorem continuous_intrinsicIntegrands {Ω : Type*} [TopologicalSpace Ω]
    {A : Ω → Matrix4} {τ : Ω → Cubic4} {t : Ω → ℝ} {V : Ω → Fourth4}
    (hA : Continuous A) (hτ : Continuous τ) (ht : Continuous t) (hV : Continuous V) :
    Continuous (fun x =>
      (intrinsicPinchingW (A x) (τ x) (t x),
       intrinsicCorrectionL4 (A x) (τ x) (t x),
       intrinsicCorrectionL3 (A x) (τ x) (t x),
       intrinsicCorrectionJ (A x) (τ x) (t x),
       intrinsicPinchingSquare (A x) (τ x) (t x) (V x))) :=
  (contDiff_intrinsicIntegrands 0).continuous.comp (hA.prodMk (hτ.prodMk (ht.prodMk hV)))

/-- Ordinary continuity of W in the component topology. -/
theorem continuous_intrinsicPinchingW :
    Continuous (fun x : Matrix4 × Cubic4 × ℝ => intrinsicPinchingW x.1 x.2.1 x.2.2) := by
  exact (continuous_intrinsicIntegrands continuous_fst continuous_snd.fst
    continuous_snd.snd (continuous_const (y := (0 : Fourth4)))).fst

/-- Compactness and finite measure discharge integrability for continuous
component fields. This is an auxiliary analytic statement, not a global framing
hypothesis added to the geometric theorem. -/
theorem integrable_intrinsicIntegrands {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] (ν : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure ν]
    {A : Ω → Matrix4} {τ : Ω → Cubic4} {t : Ω → ℝ} {V : Ω → Fourth4}
    (hA : Continuous A) (hτ : Continuous τ) (ht : Continuous t) (hV : Continuous V) :
    MeasureTheory.Integrable (fun x => intrinsicPinchingW (A x) (τ x) (t x)) ν ∧
    MeasureTheory.Integrable (fun x => intrinsicCorrectionL4 (A x) (τ x) (t x)) ν ∧
    MeasureTheory.Integrable (fun x => intrinsicCorrectionL3 (A x) (τ x) (t x)) ν ∧
    MeasureTheory.Integrable (fun x => intrinsicCorrectionJ (A x) (τ x) (t x)) ν ∧
    MeasureTheory.Integrable (fun x => intrinsicPinchingSquare (A x) (τ x) (t x) (V x)) ν := by
  have h := continuous_intrinsicIntegrands hA hτ ht hV
  exact ⟨h.fst.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    h.snd.fst.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    h.snd.snd.fst.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    h.snd.snd.snd.fst.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    h.snd.snd.snd.snd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)⟩

end
end SecondPinching
