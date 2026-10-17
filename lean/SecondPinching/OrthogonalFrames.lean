import SecondPinching.JointContractions
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Pointwise changes of orthonormal frame. The rows of Q are the new basis
vectors in the old coordinates. No orientation or eigenvalue condition is used.
All tensor slots transform by Q and all inner products use ordered indices. -/

/-- The full real orthogonal group, including determinant minus one. -/
def OrthogonalFrame (Q : Matrix4) : Prop := Qᵀ * Q = 1

/-- Components of a vector in the new frame. -/
def frameVector (Q : Matrix4) (v : Vector4) : Vector4 := Q *ᵥ v

/-- Components of a covariant two-tensor in the new orthonormal frame. -/
def frameMatrix (Q A : Matrix4) : Matrix4 :=
  fun i j => ∑ a, Q i a * ∑ b, Q j b * A a b

/-- The same frame change on each of the three tensor slots. -/
def frameCubic (Q : Matrix4) (τ : Cubic4) : Cubic4 :=
  fun i j k => ∑ a, Q i a * frameMatrix Q (τ a) j k

/-- The same frame change on each of the four tensor slots. -/
def frameFourth (Q : Matrix4) (U : Fourth4) : Fourth4 :=
  fun i j k l => ∑ a, Q i a * frameCubic Q (U a) j k l

/-- Auxiliary pairing with the manuscript's ordered-index convention. -/
def cubicInner (τ υ : Cubic4) : ℝ := ∑ i, ∑ j, ∑ k, τ i j k * υ i j k

theorem orthogonalFrame_mul_transpose (Q : Matrix4) (hQ : OrthogonalFrame Q) :
    Q * Qᵀ = 1 := by
  exact (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mp
    ((Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mpr hQ)

theorem orthogonalFrame_transpose (Q : Matrix4) (hQ : OrthogonalFrame Q) :
    OrthogonalFrame Qᵀ := by
  simpa only [OrthogonalFrame, Matrix.transpose_transpose] using orthogonalFrame_mul_transpose Q hQ

theorem frameVector_inner (Q : Matrix4) (hQ : OrthogonalFrame Q) (v w : Vector4) :
    frameVector Q v ⬝ᵥ frameVector Q w = v ⬝ᵥ w := by
  change Qᵀ * Q = 1 at hQ
  change (Q *ᵥ v) ⬝ᵥ (Q *ᵥ w) = _
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec, dotProduct_comm]

theorem frameVector_inverse (Q : Matrix4) (hQ : OrthogonalFrame Q) (v : Vector4) :
    frameVector Qᵀ (frameVector Q v) = v := by
  change Qᵀ * Q = 1 at hQ
  simp only [frameVector, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]

theorem frameMatrix_eq_conjugate (Q A : Matrix4) :
    frameMatrix Q A = Q * A * Qᵀ := by
  ext i j
  simp only [frameMatrix, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frameMatrix_inverse (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) :
    frameMatrix Qᵀ (frameMatrix Q A) = A := by
  simp only [frameMatrix_eq_conjugate, Matrix.transpose_transpose]
  calc
    Qᵀ * (Q * A * Qᵀ) * Q = (Qᵀ * Q) * A * (Qᵀ * Q) := by noncomm_ring
    _ = A := by rw [hQ, one_mul, mul_one]

theorem frameMatrix_symmetric (Q A : Matrix4) (hA : A.IsSymm) :
    (frameMatrix Q A).IsSymm := by
  rw [frameMatrix_eq_conjugate]
  change (Q * A * Qᵀ)ᵀ = Q * A * Qᵀ
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq, Matrix.mul_assoc]

theorem frameMatrix_inner (Q : Matrix4) (hQ : OrthogonalFrame Q) (A B : Matrix4) :
    matrixInner (frameMatrix Q A) (frameMatrix Q B) = matrixInner A B := by
  have hv := frameVector_inner Q hQ
  simp only [frameVector, Matrix.mulVec, dotProduct] at hv
  unfold matrixInner frameMatrix
  rw [Finset.sum_comm]
  simp_rw [hv]
  rw [Finset.sum_comm]
  simp_rw [hv]

theorem frameMatrix_normSq (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) :
    matrixNormSq (frameMatrix Q A) = matrixNormSq A := by
  simpa only [matrixInner_self] using frameMatrix_inner Q hQ A A

theorem frameMatrix_trace (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) :
    Matrix.trace (frameMatrix Q A) = Matrix.trace A := by
  rw [frameMatrix_eq_conjugate, Matrix.trace_mul_cycle, hQ, one_mul]

theorem frameMatrix_one (Q : Matrix4) (hQ : OrthogonalFrame Q) :
    frameMatrix Q 1 = 1 := by
  rw [frameMatrix_eq_conjugate, mul_one, orthogonalFrame_mul_transpose Q hQ]

theorem frameCubic_inner (Q : Matrix4) (hQ : OrthogonalFrame Q) (τ υ : Cubic4) :
    cubicInner (frameCubic Q τ) (frameCubic Q υ) = cubicInner τ υ := by
  have hv := frameVector_inner Q hQ
  simp only [frameVector, Matrix.mulVec, dotProduct] at hv
  unfold cubicInner frameCubic
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [hv]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => frameMatrix_inner Q hQ (τ a) (υ a))

theorem frameCubic_normSq (Q : Matrix4) (hQ : OrthogonalFrame Q) (τ : Cubic4) :
    cubicNormSq (frameCubic Q τ) = cubicNormSq τ := by
  simpa only [cubicInner, cubicNormSq, pow_two] using frameCubic_inner Q hQ τ τ

theorem frameFourth_inner (Q : Matrix4) (hQ : OrthogonalFrame Q) (U V : Fourth4) :
    fourthInner (frameFourth Q U) (frameFourth Q V) = fourthInner U V := by
  have hv := frameVector_inner Q hQ
  simp only [frameVector, Matrix.mulVec, dotProduct] at hv
  unfold fourthInner frameFourth
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]; arg 2; ext k; rw [Finset.sum_comm]
  simp_rw [hv]
  conv_lhs => arg 2; ext j; arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => frameCubic_inner Q hQ (U a) (V a))

theorem frameFourth_normSq (Q : Matrix4) (hQ : OrthogonalFrame Q) (U : Fourth4) :
    fourthNormSq (frameFourth Q U) = fourthNormSq U := by
  simpa only [fourthInner_self] using frameFourth_inner Q hQ U U

theorem frameCubic_symmetric (Q : Matrix4) (τ : Cubic4) (hτ : CubicSymmetric τ) :
    CubicSymmetric (frameCubic Q τ) := by
  apply (cubicSymmetric_iff_swaps _).mpr
  constructor
  · intro i j k
    change frameMatrix Q (fun a b => ∑ c, Q k c * τ a b c) i j =
      frameMatrix Q (fun a b => ∑ c, Q k c * τ a b c) j i
    apply (frameMatrix_symmetric Q _ _).apply
    apply Matrix.IsSymm.ext
    intro a b
    simp only [cubicSymmetric_swap12 hτ b a]
  · intro i j k
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    apply (frameMatrix_symmetric Q (τ a) _).apply
    apply Matrix.IsSymm.ext
    intro b c
    exact cubicSymmetric_swap23 hτ a c b

theorem frameFourth_symmetric (Q : Matrix4) (U : Fourth4) (hU : FourthSymmetric U) :
    FourthSymmetric (frameFourth Q U) := by
  have hs : ∀ a, CubicSymmetric (frameCubic Q (U a)) := by
    intro a
    apply frameCubic_symmetric
    apply (cubicSymmetric_iff_swaps _).mpr
    exact ⟨fun b c d => fourthSymmetric_swap23 hU a b c d,
      fun b c d => fourthSymmetric_swap34 hU a b c d⟩
  apply (fourthSymmetric_iff_swaps _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    change frameMatrix Q (fun a b => frameMatrix Q (U a b) k l) i j =
      frameMatrix Q (fun a b => frameMatrix Q (U a b) k l) j i
    apply (frameMatrix_symmetric Q _ _).apply
    apply Matrix.IsSymm.ext
    intro a b
    simp only [frameMatrix, fourthSymmetric_swap12 hU b a]
  · intro i j k l
    apply Finset.sum_congr rfl
    intro a _
    rw [cubicSymmetric_swap12 (hs a) j k l]
  · intro i j k l
    apply Finset.sum_congr rfl
    intro a _
    rw [cubicSymmetric_swap23 (hs a) j k l]

/-- Linear action on the ambient arrays, before imposing symmetry. -/
def frameMatrixLinear (Q : Matrix4) : Matrix4 →ₗ[ℝ] Matrix4 where
  toFun := frameMatrix Q
  map_add' A B := by ext i j; simp [frameMatrix, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext i j
    simp [frameMatrix, Finset.mul_sum, mul_left_comm]

def frameCubicLinear (Q : Matrix4) : Cubic4 →ₗ[ℝ] Cubic4 where
  toFun := frameCubic Q
  map_add' τ υ := by
    funext i j k
    simp [frameCubic, frameMatrix, mul_add, Finset.sum_add_distrib]
  map_smul' c τ := by
    funext i j k
    simp [frameCubic, frameMatrix, Finset.mul_sum, mul_left_comm]

def frameFourthLinear (Q : Matrix4) : Fourth4 →ₗ[ℝ] Fourth4 where
  toFun := frameFourth Q
  map_add' U V := by
    funext i j k l
    simp [frameFourth, frameCubic, frameMatrix, mul_add, Finset.sum_add_distrib]
  map_smul' c U := by
    funext i j k l
    simp [frameFourth, frameCubic, frameMatrix, Finset.mul_sum, mul_left_comm]

theorem frameCubic_slice (Q : Matrix4) (τ : Cubic4) (i : Fin 4) :
    frameCubic Q τ i = ∑ a, Q i a • frameMatrix Q (τ a) := by
  ext j k
  simp only [frameCubic, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem frameFourth_slice (Q : Matrix4) (U : Fourth4) (i : Fin 4) :
    frameFourth Q U i = ∑ a, Q i a • frameCubic Q (U a) := by
  funext j k l
  simp [frameFourth]

theorem frameCubic_inverse (Q : Matrix4) (hQ : OrthogonalFrame Q) (τ : Cubic4) :
    frameCubic Qᵀ (frameCubic Q τ) = τ := by
  have hm (i : Fin 4) : frameMatrix Qᵀ (frameCubic Q τ i) = ∑ a, Q i a • τ a := by
    rw [frameCubic_slice]
    change frameMatrixLinear Qᵀ (∑ a, Q i a • frameMatrix Q (τ a)) = _
    rw [map_sum]
    simp only [map_smul]
    change (∑ a, Q i a • frameMatrix Qᵀ (frameMatrix Q (τ a))) = _
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun X : Matrix4 => Q i a • X) (frameMatrix_inverse Q hQ (τ a))
  funext i j k
  change (∑ a, Qᵀ i a * frameMatrix Qᵀ (frameCubic Q τ a) j k) = τ i j k
  simp only [hm]
  exact congrFun (frameVector_inverse Q hQ (fun a => τ a j k)) i

theorem frameFourth_inverse (Q : Matrix4) (hQ : OrthogonalFrame Q) (U : Fourth4) :
    frameFourth Qᵀ (frameFourth Q U) = U := by
  have hc (i : Fin 4) : frameCubic Qᵀ (frameFourth Q U i) = ∑ a, Q i a • U a := by
    rw [frameFourth_slice]
    change frameCubicLinear Qᵀ (∑ a, Q i a • frameCubic Q (U a)) = _
    rw [map_sum]
    simp only [map_smul]
    change (∑ a, Q i a • frameCubic Qᵀ (frameCubic Q (U a))) = _
    simp_rw [frameCubic_inverse Q hQ]
  funext i j k l
  simp only [frameFourth, hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact congrFun (frameVector_inverse Q hQ (fun a => U a j k l)) i

end
end SecondPinching
