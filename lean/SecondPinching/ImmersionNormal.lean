import SecondPinching.ImmersionFrameChange
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem chart4_coordinate_expansion (v : Chart4) :
    v = ∑ i, v i • coordinateUnit i := by
  ext j
  simp [coordinateUnit,Pi.single_apply]

theorem immersionTangent_expansion (f : Chart4 → Ambient6) (x v : Chart4) :
    fderiv ℝ f x v = ∑ i, v i • immersionTangent f x i := by
  conv_lhs => rw [chart4_coordinate_expansion v]
  simp only [map_sum,map_smul,immersionTangent]

/-- Differentiating the sphere equation makes the position vector orthogonal
to the actual tangent image. This is derived, not a field of the local data. -/
theorem immersion_radial_tangent (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (v : Chart4) :
    inner ℝ (F.map x) (fderiv ℝ F.map x v) = 0 := by
  have hf := ((F.smooth_map x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun y => inner ℝ (F.map y) (F.map y)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) (fun y hy => F.sphere y hy)
  have h := congrArg (fun L : Chart4 →L[ℝ] ℝ => L v) (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_inner_apply ℝ hf hf] at h
  simp only [fderiv_const_apply,zero_apply] at h
  have hc : inner ℝ (fderiv ℝ F.map x v) (F.map x) =
      inner ℝ (F.map x) (fderiv ℝ F.map x v) := real_inner_comm _ _
  rw [hc] at h
  linarith

theorem immersion_normal_tangent (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (v : Chart4) :
    inner ℝ (F.normal x) (fderiv ℝ F.map x v) = 0 := by
  rw [immersionTangent_expansion]
  simp [inner_sum,inner_smul_right,F.normal_tangent x hx]

/-- The two normal directions (sphere position and hypersurface normal),
together with the four-dimensional tangent image, fill the ambient R6. -/
def immersionAmbientMap (F : LocalSphereImmersion) (x : Chart4) :
    (ℝ × (ℝ × Chart4)) →ₗ[ℝ] Ambient6 where
  toFun c := c.1 • F.normal x + c.2.1 • F.map x + fderiv ℝ F.map x c.2.2
  map_add' a b := by simp [add_smul,add_assoc,add_left_comm,add_comm]
  map_smul' s c := by simp [smul_add,smul_smul]

theorem immersionAmbientMap_injective (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) : Function.Injective (immersionAmbientMap F x) := by
  have hz (c : ℝ × (ℝ × Chart4)) (hc : immersionAmbientMap F x c = 0) : c = 0 := by
    have ha := congrArg (fun w => inner ℝ (F.normal x) w) hc
    have hb := congrArg (fun w => inner ℝ (F.map x) w) hc
    simp only [immersionAmbientMap,LinearMap.coe_mk,AddHom.coe_mk,inner_add_right,
      inner_smul_right,F.normal_unit x hx,F.normal_radial x hx,
      immersion_normal_tangent F x hx,inner_zero_right,mul_one,mul_zero,add_zero] at ha
    have hn : inner ℝ (F.map x) (F.normal x) = 0 := by
      rw [real_inner_comm]; exact F.normal_radial x hx
    simp only [immersionAmbientMap,LinearMap.coe_mk,AddHom.coe_mk,inner_add_right,
      inner_smul_right,hn,F.sphere x hx,immersion_radial_tangent F x hx,
      inner_zero_right,mul_one,mul_zero,zero_add,add_zero] at hb
    have hv : c.2.2 = 0 := by
      apply F.injective_derivative x hx
      simpa [immersionAmbientMap,ha,hb] using hc
    exact Prod.ext ha (Prod.ext hb hv)
  intro c d h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub,h,sub_self]

theorem immersionAmbientMap_surjective (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) : Function.Surjective (immersionAmbientMap F x) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (immersionAmbientMap_injective F x hx)
  simp [Chart4,Ambient6,Module.finrank_prod]

/-- A vector orthogonal to the tangent image and the radial direction is a
multiple of the chosen hypersurface normal. No orientation is assumed. -/
theorem immersion_normal_line (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (w : Ambient6)
    (hr : inner ℝ w (F.map x) = 0)
    (ht : ∀ v, inner ℝ w (fderiv ℝ F.map x v) = 0) :
    w = (inner ℝ (F.normal x) w) • F.normal x := by
  obtain ⟨⟨a,b,v⟩,he⟩ := immersionAmbientMap_surjective F x hx w
  change a • F.normal x + b • F.map x + fderiv ℝ F.map x v = w at he
  have hb := congrArg (fun u => inner ℝ u (F.map x)) he
  simp only [inner_add_left,real_inner_smul_left,F.normal_radial x hx,
    F.sphere x hx,mul_zero,mul_one,zero_add] at hb
  have hrv : inner ℝ (fderiv ℝ F.map x v) (F.map x) = 0 := by
    rw [real_inner_comm]; exact immersion_radial_tangent F x hx v
  rw [hrv,add_zero,hr] at hb
  have hv := congrArg (fun u => inner ℝ u (fderiv ℝ F.map x v)) he
  simp only [inner_add_left,real_inner_smul_left,immersion_normal_tangent F x hx,
    immersion_radial_tangent F x hx,mul_zero,zero_add,ht] at hv
  have hz : fderiv ℝ F.map x v = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hv
  have hw : w = a • F.normal x := by simpa [hb,hz] using he.symm
  rw [hw]
  simp only [inner_smul_right,F.normal_unit x hx,mul_one]

theorem immersion_unit_normal_eq_or_neg (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (w : Ambient6)
    (hu : inner ℝ w w = 1) (hr : inner ℝ w (F.map x) = 0)
    (ht : ∀ v, inner ℝ w (fderiv ℝ F.map x v) = 0) :
    w = F.normal x ∨ w = -F.normal x := by
  have he := immersion_normal_line F x hx w hr ht
  let a := inner ℝ (F.normal x) w
  have ha : a^2 = 1 := by
    rw [he] at hu
    simpa only [a,inner_smul_right,real_inner_smul_left,F.normal_unit x hx,mul_one,pow_two] using hu
  rcases (sq_eq_one_iff).mp ha with h | h
  · left; simpa [a] using he.trans (by rw [show inner ℝ (F.normal x) w = 1 from h]; simp)
  · right; simpa [a] using he.trans (by rw [show inner ℝ (F.normal x) w = -1 from h]; simp)

/-- Continuity turns pointwise sign ambiguity into a single sign on a
neighborhood. No connected overlap or global orientability is required. -/
theorem immersion_unit_normal_germ (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (N : Chart4 → Ambient6) (hN : ContinuousAt N x)
    (hgeom : ∀ᶠ y in 𝓝 x, inner ℝ (N y) (N y) = 1 ∧
      inner ℝ (N y) (F.map y) = 0 ∧
      ∀ v, inner ℝ (N y) (fderiv ℝ F.map y v) = 0) :
    N =ᶠ[𝓝 x] F.normal ∨ N =ᶠ[𝓝 x] -F.normal := by
  have hcont : ContinuousAt (fun y => inner ℝ (F.normal y) (N y)) x :=
    (((F.smooth_normal x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).continuousAt).inner hN
  have hpt := hgeom.self_of_nhds
  rcases immersion_unit_normal_eq_or_neg F x hx (N x) hpt.1 hpt.2.1 hpt.2.2 with hp | hn
  · left
    have hpos : 0 < inner ℝ (F.normal x) (N x) := by rw [hp,F.normal_unit x hx]; norm_num
    filter_upwards [hgeom,F.isOpen_domain.mem_nhds hx,hcont.eventually (lt_mem_nhds hpos)] with y hy hyU hyp
    rcases immersion_unit_normal_eq_or_neg F y hyU (N y) hy.1 hy.2.1 hy.2.2 with he | he
    · exact he

    · rw [he,inner_neg_right,F.normal_unit y hyU] at hyp
      norm_num at hyp
  · right
    have hneg : inner ℝ (F.normal x) (N x) < 0 := by
      rw [hn,inner_neg_right,F.normal_unit x hx]; norm_num
    filter_upwards [hgeom,F.isOpen_domain.mem_nhds hx,hcont.eventually (gt_mem_nhds hneg)] with y hy hyU hyn
    rcases immersion_unit_normal_eq_or_neg F y hyU (N y) hy.1 hy.2.1 hy.2.2 with he | he
    · rw [he,F.normal_unit y hyU] at hyn
      norm_num at hyn
    · exact he

/-- The radial vector, normal and four tangent coordinate vectors determine
every ambient vector by their inner products. -/
theorem immersion_ambient_ext (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (w z : Ambient6)
    (hn : inner ℝ w (F.normal x) = inner ℝ z (F.normal x))
    (hr : inner ℝ w (F.map x) = inner ℝ z (F.map x))
    (ht : ∀ i, inner ℝ w (immersionTangent F.map x i) =
      inner ℝ z (immersionTangent F.map x i)) : w = z := by
  have hn0 : inner ℝ (w-z) (F.normal x) = 0 := by rw [inner_sub_left,hn,sub_self]
  have hr0 : inner ℝ (w-z) (F.map x) = 0 := by rw [inner_sub_left,hr,sub_self]
  have ht0 (v : Chart4) : inner ℝ (w-z) (fderiv ℝ F.map x v) = 0 := by
    rw [immersionTangent_expansion]
    simp only [inner_sum,inner_smul_right,inner_sub_left,ht,sub_self,mul_zero,Finset.sum_const_zero]
  have he := immersion_normal_line F x hx (w-z) hr0 ht0
  have hn1 : inner ℝ (F.normal x) (w-z) = 0 := by rw [real_inner_comm]; exact hn0
  rw [hn1,zero_smul] at he
  exact sub_eq_zero.mp he

end
end SecondPinching
