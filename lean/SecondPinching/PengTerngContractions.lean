import SecondPinching.CubicBochner
import SecondPinching.PengTerngExpressions

set_option autoImplicit false
set_option maxHeartbeats 4800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

theorem cubicInner_swap12_right (T U : Cubic4) (hT : CubicSymmetric T) :
    cubicInner T (fun i j k => U j i k) = cubicInner T U := by
  unfold cubicInner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  rw [cubicSymmetric_swap12 hT j i k]

theorem cubicInner_swap23_right (T U : Cubic4) (hT : CubicSymmetric T) :
    cubicInner T (fun i j k => U i k j) = cubicInner T U := by
  unfold cubicInner
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  rw [cubicSymmetric_swap23 hT i k j]

theorem cubicInner_slot1 (q : Matrix4) (T : Cubic4) (hT : CubicSymmetric T) :
    cubicInner T (fun i j k => ∑ r, q i r*T r j k) = Matrix.trace (q*cubicGramMatrix T) := by
  simp only [cubicInner,Matrix.trace,Matrix.diag,Matrix.mul_apply,cubicGramMatrix,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  rw [cubicSymmetric_swap12 hT i j k,cubicSymmetric_swap23 hT j i k,
    cubicSymmetric_swap12 hT r j k,cubicSymmetric_swap23 hT j r k]
  ring

theorem cubicInner_connectionAction (q : Matrix4) (T : Cubic4) (hT : CubicSymmetric T) :
    cubicInner T (cubicConnectionAction q T) = 3*Matrix.trace (q*cubicGramMatrix T) := by
  let U : Cubic4 := fun i j k => ∑ r, q i r*T r j k
  have hc : cubicConnectionAction q T = U+(fun i j k => U j i k)+(fun i j k => U k i j) := by
    funext i j k
    simp only [cubicConnectionAction,U,Pi.add_apply,Finset.sum_add_distrib]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl; intro r _
      rw [cubicSymmetric_swap12 hT i r k]
    · apply Finset.sum_congr rfl; intro r _
      rw [cubicSymmetric_swap23 hT i j r,cubicSymmetric_swap12 hT i r j]
  have h2 := cubicInner_swap12_right T U hT
  have h3 : cubicInner T (fun i j k => U k i j) = cubicInner T U := by
    calc
      _ = cubicInner T (fun i j k => U j i k) :=
        cubicInner_swap23_right T (fun i j k => U j i k) hT
      _ = _ := h2
  rw [hc,cubicInner_add_right,cubicInner_add_right,h2,h3,cubicInner_slot1 q T hT]
  ring

def cubicDoubleAction (h : Matrix4) (T : Cubic4) : Cubic4 := fun i j k =>
  ∑ r, ∑ a, (h i r*h j a*T r a k+h i r*h k a*T r j a+h j r*h k a*T i r a)

theorem cubicInner_doubleAction (h : Matrix4) (T : Cubic4) (hT : CubicSymmetric T) :
    cubicInner T (cubicDoubleAction h T) = 3*intrinsicCubicB h T := by
  let U := cubicMatrixAction h T
  have hc : cubicDoubleAction h T = (fun i j k => U k i j)+(fun i j k => U j i k)+U := by
    funext i j k
    simp only [cubicDoubleAction,U,cubicMatrixAction,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.of_apply,Pi.add_apply,Finset.sum_add_distrib,Finset.sum_mul]
    refine congrArg₂ (fun a b : ℝ => a+b) (congrArg₂ (fun a b : ℝ => a+b) ?_ ?_) ?_
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro a _
      rw [cubicSymmetric_swap23 hT a r k,cubicSymmetric_swap12 hT a k r]
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro a _
      rw [cubicSymmetric_swap12 hT a j r]
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro a _
      ring
  have h2 := cubicInner_swap12_right T U hT
  have h3 : cubicInner T (fun i j k => U k i j) = cubicInner T U := by
    calc
      _ = cubicInner T (fun i j k => U j i k) :=
        cubicInner_swap23_right T (fun i j k => U j i k) hT
      _ = _ := h2
  rw [hc,cubicInner_add_right,cubicInner_add_right,h2,h3]
  change _ = 3*cubicInner T U
  ring

def cubicTraceProduct (h : Matrix4) (w : Vector4) : Cubic4 := fun i j k =>
  h i j*w k+h i k*w j+h j k*w i

theorem cubicInner_traceProduct (h : Matrix4) (T : Cubic4) (w : Vector4) (hT : CubicSymmetric T) :
    cubicInner T (cubicTraceProduct h w) = 3*(cubicWeightedTrace h T ⬝ᵥ w) := by
  let U : Cubic4 := fun i j k => h i j*w k
  have hc : cubicTraceProduct h w = U+(fun i j k => U i k j)+(fun i j k => U j k i) := rfl
  have h2 := cubicInner_swap23_right T U hT
  have h3 : cubicInner T (fun i j k => U j k i) = cubicInner T U := by
    calc
      _ = cubicInner T (fun i j k => U i k j) :=
        cubicInner_swap12_right T (fun i j k => U i k j) hT
      _ = _ := h2
  rw [hc,cubicInner_add_right,cubicInner_add_right,h2,h3]
  have he : cubicInner T U = cubicWeightedTrace h T ⬝ᵥ w := by
    simp only [cubicInner,U,cubicWeightedTrace,dotProduct,Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [he]; ring

end
end SecondPinching
