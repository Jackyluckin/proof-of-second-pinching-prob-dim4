import SecondPinching.CoordinateRicci

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Tangential projection after differentiating the actual ambient Gauss
formula. The position and normal derivatives provide the two curvature terms. -/
theorem immersionThirdDerivative_tangent (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i k l s : Fin 4) :
    inner ℝ (immersionThirdDerivative F.map x i k l) (immersionTangent F.map x s) =
    ((matrixDerivative (fun y => coordinateConnectionMatrix (immersionChristoffel F.map) y k)
        x (coordinateUnit l) +
      coordinateConnectionMatrix (immersionChristoffel F.map) x k *
      coordinateConnectionMatrix (immersionChristoffel F.map) x l) * immersionMetric F.map x) i s -
      immersionSecondForm F.map F.normal x i k * immersionSecondForm F.map F.normal x s l -
      immersionMetric F.map x i k * immersionMetric F.map x l s := by
  have hΓ := ((contDiffOn_immersionChristoffel F x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hh := (((contDiffOn_immersionForms F).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hg := ((contDiffOn_immersionMetric F.isOpen_domain F.smooth_map x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hf := ((F.smooth_map x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hn := ((F.smooth_normal x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have ht (r : Fin 4) := ((contDiffOn_immersionTangent F.isOpen_domain F.smooth_map r x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hc (r : Fin 4) : DifferentiableAt ℝ (fun y => immersionChristoffel F.map y r i k) x := by fun_prop
  have hhi : DifferentiableAt ℝ (fun y => immersionSecondForm F.map F.normal y i k) x := by fun_prop
  have hgi : DifferentiableAt ℝ (fun y => immersionMetric F.map y i k) x := by fun_prop
  have he : (fun y => immersionSecondDerivative F.map y i k) =ᶠ[𝓝 x]
      (fun y => (∑ r, immersionChristoffel F.map y r i k • immersionTangent F.map y r) +
        immersionSecondForm F.map F.normal y i k • F.normal y - immersionMetric F.map y i k • F.map y) :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) (fun y hy => immersion_gauss_formula F y hy i k)
  have hsum : DifferentiableAt ℝ (fun y => ∑ r, immersionChristoffel F.map y r i k • immersionTangent F.map y r) x :=
    DifferentiableAt.fun_sum (fun r _ => (hc r).smul (ht r))
  unfold immersionThirdDerivative
  rw [he.fderiv_eq]
  erw [fderiv_fun_sub (hsum.add (hhi.smul hn)) (hgi.smul hf),
    fderiv_fun_add hsum (hhi.smul hn),
    fderiv_fun_sum (fun r _ => (hc r).smul (ht r)),
    fderiv_fun_smul hhi hn, fderiv_fun_smul hgi hf]
  simp only [sub_apply, add_apply, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, inner_sub_left, inner_add_left, sum_inner,
    real_inner_smul_left, F.normal_tangent x hx s,
    immersion_normal_derivative_tangent F x hx s l, mul_zero, add_zero]
  have hp (r : Fin 4) :
      inner ℝ (immersionSecondDerivative F.map x r l) (immersionTangent F.map x s) =
      ∑ a, immersionChristoffel F.map x a r l*immersionMetric F.map x a s := by
    rw [← immersionChristoffel_projection F.map x (F.injective_derivative x hx) s r l]
    apply Finset.sum_congr rfl; intro a _
    change inner ℝ (immersionTangent F.map x s) (immersionTangent F.map x a)*_ = _
    rw [real_inner_comm]
    change immersionMetric F.map x a s * _ = _
    ring
  have hpder (r : Fin 4) :
      fderiv ℝ ((fun y => immersionChristoffel F.map y r i k) •
        (fun y => immersionTangent F.map y r)) x (coordinateUnit l) =
      immersionChristoffel F.map x r i k • immersionSecondDerivative F.map x r l +
      fderiv ℝ (fun y => immersionChristoffel F.map y r i k) x (coordinateUnit l) • immersionTangent F.map x r := by
    change fderiv ℝ (fun y => immersionChristoffel F.map y r i k • immersionTangent F.map y r) x _ = _
    rw [fderiv_fun_smul (hc r) (ht r)]
    rfl
  simp only [hpder, inner_add_left, real_inner_smul_left]
  change (∑ r, (immersionChristoffel F.map x r i k *
      inner ℝ (immersionSecondDerivative F.map x r l) (immersionTangent F.map x s) +
      (fderiv ℝ (fun y => immersionChristoffel F.map y r i k) x (coordinateUnit l)) *
      immersionMetric F.map x r s)) + _ - _ = _
  have hr : inner ℝ (F.map x) (immersionTangent F.map x s) = 0 :=
    immersion_radial_tangent F x hx (coordinateUnit s)
  have htg : inner ℝ (fderiv ℝ F.map x (coordinateUnit l)) (immersionTangent F.map x s) =
      immersionMetric F.map x l s := rfl
  simp only [hr, htg, mul_zero]
  simp_rw [hp]
  have hcc := congrArg (fun M : Matrix4 => M i s)
    (Matrix.mul_assoc (coordinateConnectionMatrix (immersionChristoffel F.map) x k)
      (coordinateConnectionMatrix (immersionChristoffel F.map) x l) (immersionMetric F.map x))
  simp only [Matrix.mul_apply, coordinateConnectionMatrix] at hcc
  simp only [Matrix.add_apply, Matrix.mul_apply,
    coordinateConnectionMatrix, matrixDerivative, Finset.sum_add_distrib, add_mul, Finset.sum_mul]
  simp only [Finset.sum_mul] at hcc
  linarith

/-- The Gauss curvature equation for the induced connection in arbitrary
coordinates. The sign is chosen to match H_ijkl-H_ijlk in the manuscript. -/
theorem immersion_coordinateCurvature_gauss (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i s k l : Fin 4) :
    (coordinateCurvature (immersionChristoffel F.map) x k l * immersionMetric F.map x) i s =
      immersionMetric F.map x i l * immersionMetric F.map x k s -
      immersionMetric F.map x i k * immersionMetric F.map x l s +
      immersionSecondForm F.map F.normal x i l * immersionSecondForm F.map F.normal x s k -
      immersionSecondForm F.map F.normal x i k * immersionSecondForm F.map F.normal x s l := by
  have ha := immersionThirdDerivative_tangent F x hx i k l s
  have hb := immersionThirdDerivative_tangent F x hx i l k s
  rw [immersionThirdDerivative_swap23 F x hx i k l] at ha
  unfold coordinateCurvature
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.add_apply, Matrix.sub_apply] at ha hb ⊢
  linarith

end
end SecondPinching
