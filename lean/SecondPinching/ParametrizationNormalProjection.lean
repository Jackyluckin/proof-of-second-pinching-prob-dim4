import SecondPinching.SphereParametrization
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section
attribute [local fun_prop] ContDiffOn.inner contDiff_inner

/-- Five ambient directions have a nonzero orthogonal complement in R6.
This pointwise choice supplies the initial vector for a local normal field. -/
theorem parametrization_exists_normal_vector (F : SphereParametrization) (x : Chart4) :
    ∃ w : Ambient6, w≠0 ∧ inner ℝ w (F.map x)=0 ∧
      ∀ v : Chart4, inner ℝ w (fderiv ℝ F.map x v)=0 := by
  let L := parametrizationRadialTangentMap F x
  have hd : Module.finrank ℝ L.range ≤ 5 := by
    simpa [Chart4,Module.finrank_prod] using L.finrank_range_le
  have ho : L.rangeᗮ ≠ ⊥ := by
    intro h
    have h6 : Module.finrank ℝ Ambient6=6 := by simp [Ambient6]
    have he : Module.finrank ℝ L.range=6 := by
      have he := L.range.finrank_add_finrank_orthogonal
      rw [h,h6,finrank_bot,add_zero] at he
      exact he
    omega
  obtain ⟨w,hw,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ho
  have hp := (Submodule.mem_orthogonal' L.range w).mp hw
  refine ⟨w,hne,?_,?_⟩
  · simpa [L,parametrizationRadialTangentMap] using hp _ (L.mem_range_self (1,0))
  · intro v
    simpa [L,parametrizationRadialTangentMap] using hp _ (L.mem_range_self (0,v))

def parametrizationProjectionCoefficients (F : SphereParametrization) (w : Ambient6)
    (x : Chart4) : Chart4 :=
  (immersionMetric F.map x)⁻¹ *ᵥ (fun i => inner ℝ (immersionTangent F.map x i) w)

/-- Remove the radial and tangent components of a fixed ambient vector. -/
def parametrizationNormalProjection (F : SphereParametrization) (w : Ambient6)
    (x : Chart4) : Ambient6 :=
  w - (inner ℝ (F.map x) w) • F.map x -
    fderiv ℝ F.map x (parametrizationProjectionCoefficients F w x)

theorem parametrization_projection_coefficients_identity (F : SphereParametrization)
    (w : Ambient6) (x : Chart4) (hx : x ∈ F.domain) (i : Fin 4) :
    (immersionMetric F.map x *ᵥ parametrizationProjectionCoefficients F w x) i =
      inner ℝ (immersionTangent F.map x i) w := by
  unfold parametrizationProjectionCoefficients
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx))),
    Matrix.one_mulVec]

theorem parametrizationNormalProjection_radial (F : SphereParametrization) (w : Ambient6)
    (x : Chart4) (hx : x ∈ F.domain) :
    inner ℝ (F.map x) (parametrizationNormalProjection F w x)=0 := by
  simp only [parametrizationNormalProjection,inner_sub_right,inner_smul_right,F.sphere x hx,
    parametrization_radial_tangent F x hx,mul_one,sub_self]

theorem parametrizationNormalProjection_tangent (F : SphereParametrization) (w : Ambient6)
    (x : Chart4) (hx : x ∈ F.domain) (i : Fin 4) :
    inner ℝ (immersionTangent F.map x i) (parametrizationNormalProjection F w x)=0 := by
  have hr : inner ℝ (immersionTangent F.map x i) (F.map x)=0 := by
    rw [real_inner_comm]
    exact parametrization_radial_tangent F x hx (coordinateUnit i)
  have ht : inner ℝ (immersionTangent F.map x i)
      (fderiv ℝ F.map x (parametrizationProjectionCoefficients F w x)) =
      inner ℝ (immersionTangent F.map x i) w := by
    rw [immersionTangent_expansion,inner_sum]
    simp only [inner_smul_right]
    have he := parametrization_projection_coefficients_identity F w x hx i
    simp only [Matrix.mulVec,dotProduct,immersionMetric,Matrix.gram_apply] at he
    convert he using 1
    apply Finset.sum_congr rfl; intro j _; ring
  simp only [parametrizationNormalProjection,inner_sub_right,inner_smul_right,hr,ht,
    mul_zero,sub_zero,sub_self]

theorem parametrizationNormalProjection_eq_self (F : SphereParametrization) (w : Ambient6)
    (x : Chart4) (hr : inner ℝ w (F.map x)=0)
    (ht : ∀ v : Chart4, inner ℝ w (fderiv ℝ F.map x v)=0) :
    parametrizationNormalProjection F w x=w := by
  have hr' : inner ℝ (F.map x) w=0 := by rwa [real_inner_comm]
  have ht' : (fun i => inner ℝ (immersionTangent F.map x i) w : Vector4)=0 := by
    funext i
    rw [real_inner_comm]
    exact ht (coordinateUnit i)
  simp only [parametrizationNormalProjection,parametrizationProjectionCoefficients,hr',ht',
    Matrix.mulVec_zero,map_zero,zero_smul,sub_zero]

theorem contDiffOn_parametrizationNormalProjection (F : SphereParametrization) (w : Ambient6) :
    ContDiffOn ℝ ∞ (parametrizationNormalProjection F w) F.domain := by
  have hf := F.smooth_map
  have hd := hf.fderiv_of_isOpen F.isOpen_domain (m:=∞) (by simp)
  have hi := contDiffOn_matrix4_inverse (contDiffOn_immersionMetric F.isOpen_domain hf)
    (fun x hx => immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx))
  have ht (i : Fin 4) := contDiffOn_immersionTangent F.isOpen_domain hf i
  have hc : ContDiffOn ℝ ∞ (parametrizationProjectionCoefficients F w) F.domain := by
    unfold parametrizationProjectionCoefficients Matrix.mulVec dotProduct
    fun_prop
  unfold parametrizationNormalProjection
  fun_prop

end
end SecondPinching
