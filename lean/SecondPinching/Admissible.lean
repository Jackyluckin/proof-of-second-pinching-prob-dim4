import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit false

/-! # Definition 2.2 and its norm convention

All sums are over ordered indices, as in Section 2. No assumption about
distinct eigenvalues, a diagonal frame, or a constant cubic trace occurs.
-/

open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Cubic4 := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- Full symmetry under every permutation of the three slots. -/
def CubicSymmetric (τ : Cubic4) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → Fin 4),
    τ (v (σ 0)) (v (σ 1)) (v (σ 2)) = τ (v 0) (v 1) (v 2)

def matrixNormSq (A : Matrix4) : ℝ := ∑ i, ∑ j, (A i j)^2

def cubicNormSq (τ : Cubic4) : ℝ := ∑ i, ∑ j, ∑ k, (τ i j k)^2

theorem matrixNormSq_nonneg (A : Matrix4) : 0 ≤ matrixNormSq A := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))

theorem cubicNormSq_nonneg (τ : Cubic4) : 0 ≤ cubicNormSq τ := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun k _ => sq_nonneg (τ i j k))))

/-- A literal transcription of Definition 2.2, using the square root of
its specified ordered-index sum for the tensor norm. -/
def PaperAdmissible (A : Matrix4) (τ : Cubic4) : Prop :=
  A.IsSymm ∧ CubicSymmetric τ ∧ Matrix.trace A = 0 ∧
  Real.sqrt (matrixNormSq A) = 1 ∧ Real.sqrt (cubicNormSq τ) = 1 ∧
  (∀ k, ∑ i, τ i i k = 0) ∧
  (∀ k, ∑ i, ∑ j, A i j * τ i j k = 0)

/-- The squared-norm version used in subsequent formal algebra. -/
def Admissible (A : Matrix4) (τ : Cubic4) : Prop :=
  A.IsSymm ∧ CubicSymmetric τ ∧ Matrix.trace A = 0 ∧
  matrixNormSq A = 1 ∧ cubicNormSq τ = 1 ∧
  (∀ k, ∑ i, τ i i k = 0) ∧
  (∀ k, ∑ i, ∑ j, A i j * τ i j k = 0)

/-- Definition 2.2 is unchanged by using squared unit norms. This is a
kernel-checked equivalence, not a new admissibility assumption. -/
theorem admissible_iff_paper (A : Matrix4) (τ : Cubic4) :
    Admissible A τ ↔ PaperAdmissible A τ := by
  simp only [Admissible, PaperAdmissible, Real.sqrt_eq_one]

end
end SecondPinching
