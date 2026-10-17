import SecondPinching.ImmersionNormal

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem immersionSecondDerivative_radial (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j : Fin 4) :
    inner ℝ (immersionSecondDerivative F.map x i j) (F.map x) =
      -immersionMetric F.map x i j := by
  have hf := ((F.smooth_map x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have ht := ((contDiffOn_immersionTangent F.isOpen_domain F.smooth_map i) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx) |>.differentiableAt (by simp)
  have he : (fun y => inner ℝ (immersionTangent F.map y i) (F.map y)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [F.isOpen_domain.mem_nhds hx] with y hy
    rw [real_inner_comm]
    exact immersion_radial_tangent F y hy (coordinateUnit i)
  have hd := congrArg (fun L : Chart4 →L[ℝ] ℝ => L (coordinateUnit j))
    (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_inner_apply ℝ ht hf] at hd
  simp only [fderiv_const_apply,zero_apply] at hd
  change immersionMetric F.map x i j +
    inner ℝ (immersionSecondDerivative F.map x i j) (F.map x) = 0 at hd
  linarith

/-- The ambient second derivative splits into the induced tangential
connection, the hypersurface normal part and the radial part of the unit sphere. -/
theorem immersion_gauss_formula (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j : Fin 4) :
    immersionSecondDerivative F.map x i j =
      (∑ r, immersionChristoffel F.map x r i j • immersionTangent F.map x r) +
      immersionSecondForm F.map F.normal x i j • F.normal x -
      immersionMetric F.map x i j • F.map x := by
  apply immersion_ambient_ext F x hx
  · have hn (r : Fin 4) : inner ℝ (immersionTangent F.map x r) (F.normal x) = 0 := by
      rw [real_inner_comm]; exact F.normal_tangent x hx r
    have hr : inner ℝ (F.map x) (F.normal x) = 0 := by
      rw [real_inner_comm]; exact F.normal_radial x hx
    simp only [inner_sub_left,inner_add_left,sum_inner,real_inner_smul_left,
      hn,hr,F.normal_unit x hx,mul_zero,Finset.sum_const_zero,mul_one,zero_add,sub_zero,
      immersionSecondForm]
  · have ht (r : Fin 4) : inner ℝ (immersionTangent F.map x r) (F.map x) = 0 := by
      rw [real_inner_comm]; exact immersion_radial_tangent F x hx (coordinateUnit r)
    simp only [inner_sub_left,inner_add_left,sum_inner,real_inner_smul_left,
      ht,F.normal_radial x hx,F.sphere x hx,mul_zero,Finset.sum_const_zero,mul_one,
      zero_add,zero_sub,immersionSecondDerivative_radial F x hx]
  · intro s
    have hr : inner ℝ (F.map x) (immersionTangent F.map x s) = 0 :=
      immersion_radial_tangent F x hx (coordinateUnit s)
    simp only [inner_sub_left,inner_add_left,sum_inner,real_inner_smul_left,
      F.normal_tangent x hx s,hr,mul_zero,add_zero,sub_zero]
    rw [← immersionChristoffel_projection F.map x (F.injective_derivative x hx) s i j]
    apply Finset.sum_congr rfl
    intro r _
    change inner ℝ (immersionTangent F.map x s) (immersionTangent F.map x r) * _ = _
    rw [real_inner_comm (immersionTangent F.map x s)]
    ring

theorem immersion_normal_derivative_normal (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (j : Fin 4) :
    inner ℝ (fderiv ℝ F.normal x (coordinateUnit j)) (F.normal x) = 0 := by
  have hN := ((F.smooth_normal x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun y => inner ℝ (F.normal y) (F.normal y)) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) (fun y hy => F.normal_unit y hy)
  have hd := congrArg (fun L : Chart4 →L[ℝ] ℝ => L (coordinateUnit j))
    (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_inner_apply ℝ hN hN] at hd
  simp only [fderiv_const_apply,zero_apply] at hd
  have hc : inner ℝ (F.normal x) (fderiv ℝ F.normal x (coordinateUnit j)) =
      inner ℝ (fderiv ℝ F.normal x (coordinateUnit j)) (F.normal x) := real_inner_comm _ _
  rw [hc] at hd
  linarith

theorem immersion_normal_derivative_radial (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (j : Fin 4) :
    inner ℝ (fderiv ℝ F.normal x (coordinateUnit j)) (F.map x) = 0 := by
  have hN := ((F.smooth_normal x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hf := ((F.smooth_map x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun y => inner ℝ (F.normal y) (F.map y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) (fun y hy => F.normal_radial y hy)
  have hd := congrArg (fun L : Chart4 →L[ℝ] ℝ => L (coordinateUnit j))
    (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_inner_apply ℝ hN hf] at hd
  change inner ℝ (F.normal x) (immersionTangent F.map x j) + _ = _ at hd
  simpa only [F.normal_tangent x hx j,zero_add,fderiv_const_apply,zero_apply] using hd

theorem immersion_normal_derivative_tangent (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j : Fin 4) :
    inner ℝ (fderiv ℝ F.normal x (coordinateUnit j)) (immersionTangent F.map x i) =
      -immersionSecondForm F.map F.normal x i j := by
  have hN := ((F.smooth_normal x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have ht := ((contDiffOn_immersionTangent F.isOpen_domain F.smooth_map i) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx) |>.differentiableAt (by simp)
  have he : (fun y => inner ℝ (F.normal y) (immersionTangent F.map y i)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℝ)) := Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
      (fun y hy => F.normal_tangent y hy i)
  have hd := congrArg (fun L : Chart4 →L[ℝ] ℝ => L (coordinateUnit j))
    (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_inner_apply ℝ hN ht] at hd
  simp only [fderiv_const_apply,zero_apply] at hd
  have hc : inner ℝ (F.normal x) (immersionSecondDerivative F.map x i j) =
      inner ℝ (immersionSecondDerivative F.map x i j) (F.normal x) := real_inner_comm _ _
  change inner ℝ (F.normal x) (immersionSecondDerivative F.map x i j) + _ = 0 at hd
  rw [hc] at hd
  change immersionSecondForm F.map F.normal x i j + _ = 0 at hd
  linarith

/-- The sign follows from differentiating <N,partial_i f>=0; the metric
inverse raises the tangent index. No curvature equation is assumed. -/
theorem immersion_weingarten_formula (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (j : Fin 4) :
    fderiv ℝ F.normal x (coordinateUnit j) =
      -∑ r, (∑ s, (immersionMetric F.map x)⁻¹ r s *
        immersionSecondForm F.map F.normal x s j) • immersionTangent F.map x r := by
  apply immersion_ambient_ext F x hx
  · have hn (r : Fin 4) : inner ℝ (immersionTangent F.map x r) (F.normal x) = 0 := by
      rw [real_inner_comm]; exact F.normal_tangent x hx r
    simp only [immersion_normal_derivative_normal F x hx,inner_neg_left,sum_inner,
      real_inner_smul_left,hn,mul_zero,Finset.sum_const_zero,neg_zero]
  · have ht (r : Fin 4) : inner ℝ (immersionTangent F.map x r) (F.map x) = 0 := by
      rw [real_inner_comm]; exact immersion_radial_tangent F x hx (coordinateUnit r)
    simp only [immersion_normal_derivative_radial F x hx,inner_neg_left,sum_inner,
      real_inner_smul_left,ht,mul_zero,Finset.sum_const_zero,neg_zero]
  · intro i
    rw [immersion_normal_derivative_tangent F x hx]
    simp only [inner_neg_left,sum_inner,real_inner_smul_left]
    congr 1
    let g := immersionMetric F.map x
    let b : Vector4 := fun s => immersionSecondForm F.map F.normal x s j
    have hsum : (∑ r, (∑ s, g⁻¹ r s * b s) *
        inner ℝ (immersionTangent F.map x r) (immersionTangent F.map x i)) =
        (g *ᵥ (g⁻¹ *ᵥ b)) i := by
      change _ = ∑ r, g i r * (g⁻¹ *ᵥ b) r
      apply Finset.sum_congr rfl
      intro r _
      change _ = inner ℝ (immersionTangent F.map x i) (immersionTangent F.map x r) * _
      rw [real_inner_comm (immersionTangent F.map x i)]
      exact mul_comm _ _
    change b i = ∑ r, (∑ s, g⁻¹ r s * b s) * _
    rw [hsum,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx))),
      Matrix.one_mulVec]

end
end SecondPinching
