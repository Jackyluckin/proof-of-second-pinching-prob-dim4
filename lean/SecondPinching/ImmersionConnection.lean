import SecondPinching.ImmersionRegularity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem immersionSecondDerivative_eq (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j : Fin 4) :
    immersionSecondDerivative F.map x i j =
      fderiv ℝ (fderiv ℝ F.map) x (coordinateUnit j) (coordinateUnit i) := by
  have hf := (F.smooth_map x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  unfold immersionSecondDerivative immersionTangent
  rw [fderiv_clm_apply hd (differentiableAt_const (coordinateUnit i))]
  simp

/-- Equality of mixed partials is obtained from smoothness of the actual map. -/
theorem immersionSecondDerivative_symmetric (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j : Fin 4) :
    immersionSecondDerivative F.map x i j = immersionSecondDerivative F.map x j i := by
  have hf := (F.smooth_map x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)
  rw [immersionSecondDerivative_eq F x hx,immersionSecondDerivative_eq F x hx]
  exact (hf.isSymmSndFDerivAt (by simp)).eq _ _

theorem immersionSecondForm_symmetric (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) : (immersionSecondForm F.map F.normal x).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply,immersionSecondForm,
    immersionSecondDerivative_symmetric F x hx j i]

/-- Torsion vanishes for the connection constructed from the immersion. -/
theorem immersionChristoffel_symmetric (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (r i j : Fin 4) :
    immersionChristoffel F.map x r i j = immersionChristoffel F.map x r j i := by
  simp only [immersionChristoffel,immersionSecondDerivative_symmetric F x hx i j]

/-- Metric compatibility in coordinates, with derivative index k last.
Together with torsion-freeness this is the coordinate characterization of
the induced Levi-Civita connection. -/
theorem immersionChristoffel_metric (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j k : Fin 4) :
    fderiv ℝ (fun y => immersionMetric F.map y i j) x (coordinateUnit k) =
      (∑ r, immersionMetric F.map x j r * immersionChristoffel F.map x r i k) +
      (∑ r, immersionMetric F.map x i r * immersionChristoffel F.map x r j k) := by
  have hd (a : Fin 4) := ((contDiffOn_immersionTangent F.isOpen_domain F.smooth_map a) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx) |>.differentiableAt (by simp)
  rw [immersionChristoffel_projection F.map x (F.injective_derivative x hx) j i k,
    immersionChristoffel_projection F.map x (F.injective_derivative x hx) i j k]
  change fderiv ℝ (fun y => inner ℝ (immersionTangent F.map y i) (immersionTangent F.map y j)) x _ = _
  rw [fderiv_inner_apply ℝ (hd i) (hd j)]
  simp only [immersionSecondDerivative]
  rw [real_inner_comm (immersionTangent F.map x i)]
  ring

end
end SecondPinching
