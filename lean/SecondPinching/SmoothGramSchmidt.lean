import SecondPinching.ImmersionNormal
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Topology ContDiff
open InnerProductSpace
namespace SecondPinching
noncomputable section

/-- Smoothness of Gram-Schmidt on a family of linearly independent tangent
vectors. Independence guarantees every denominator stays nonzero. -/
theorem contDiffOn_gramSchmidt_four {U : Set Chart4} (v : Chart4 → Fin 4 → Ambient6)
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun x => v x i) U)
    (hli : ∀ x ∈ U, LinearIndependent ℝ (v x)) (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => gramSchmidt ℝ (v x) i) U := by
  apply wellFounded_lt.induction i
  intro k ih
  have he : (fun x => gramSchmidt ℝ (v x) k) = fun x => v x k -
      ∑ j ∈ Finset.Iio k, (inner ℝ (gramSchmidt ℝ (v x) j) (v x k) /
        ‖gramSchmidt ℝ (v x) j‖^2) • gramSchmidt ℝ (v x) j := by
    funext x
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton]
    rfl
  rw [he]
  apply (hv k).sub
  apply ContDiffOn.sum
  intro j hj
  have hs := ih j (Finset.mem_Iio.mp hj)
  have hn (x : Chart4) (hx : x ∈ U) : gramSchmidt ℝ (v x) j ≠ 0 :=
    gramSchmidt_ne_zero j (hli x hx)
  exact ((hs.inner ℝ (hv k)).div ((hs.norm ℝ hn).pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hn x hx)))).smul hs

theorem contDiffOn_gramSchmidtNormed_four {U : Set Chart4} (v : Chart4 → Fin 4 → Ambient6)
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun x => v x i) U)
    (hli : ∀ x ∈ U, LinearIndependent ℝ (v x)) (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => gramSchmidtNormed ℝ (v x) i) U := by
  have hs := contDiffOn_gramSchmidt_four v hv hli i
  have hn (x : Chart4) (hx : x ∈ U) : gramSchmidt ℝ (v x) i ≠ 0 :=
    gramSchmidt_ne_zero i (hli x hx)
  exact ((hs.norm ℝ hn).inv (fun x hx => norm_ne_zero_iff.mpr (hn x hx))).smul hs

end
end SecondPinching
