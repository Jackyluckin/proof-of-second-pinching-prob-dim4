import SecondPinching.ImmersionGaussWeingarten

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

def immersionThirdDerivative (f : Chart4 → Ambient6) (x : Chart4)
    (i j k : Fin 4) : Ambient6 :=
  fderiv ℝ (fun y => immersionSecondDerivative f y i j) x (coordinateUnit k)

theorem immersionThirdDerivative_swap12 (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j k : Fin 4) :
    immersionThirdDerivative F.map x i j k = immersionThirdDerivative F.map x j i k := by
  have he : (fun y => immersionSecondDerivative F.map y i j) =ᶠ[𝓝 x]
      (fun y => immersionSecondDerivative F.map y j i) :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
      (fun y hy => immersionSecondDerivative_symmetric F y hy i j)
  exact congrArg (fun L : Chart4 →L[ℝ] Ambient6 => L (coordinateUnit k))
    (he.fderiv_eq (𝕜 := ℝ))

theorem immersionThirdDerivative_swap23 (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j k : Fin 4) :
    immersionThirdDerivative F.map x i j k = immersionThirdDerivative F.map x i k j := by
  have ht := ((contDiffOn_immersionTangent F.isOpen_domain F.smooth_map i) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)
  have hd := (ht.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  unfold immersionThirdDerivative immersionSecondDerivative
  rw [fderiv_clm_apply hd (differentiableAt_const (coordinateUnit j)),
    fderiv_clm_apply hd (differentiableAt_const (coordinateUnit k))]
  simpa using (ht.isSymmSndFDerivAt (by simp)).eq (coordinateUnit k) (coordinateUnit j)

theorem immersion_secondDerivative_normalDerivative (F : LocalSphereImmersion)
    (x : Chart4) (hx : x ∈ F.domain) (i j k : Fin 4) :
    inner ℝ (immersionSecondDerivative F.map x i j)
      (fderiv ℝ F.normal x (coordinateUnit k)) =
      -∑ r, immersionChristoffel F.map x r i j * immersionSecondForm F.map F.normal x r k := by
  rw [immersion_gauss_formula F x hx]
  have hn : inner ℝ (F.normal x) (fderiv ℝ F.normal x (coordinateUnit k)) = 0 := by
    rw [real_inner_comm]; exact immersion_normal_derivative_normal F x hx k
  have hf : inner ℝ (F.map x) (fderiv ℝ F.normal x (coordinateUnit k)) = 0 := by
    rw [real_inner_comm]; exact immersion_normal_derivative_radial F x hx k
  have ht (r : Fin 4) : inner ℝ (immersionTangent F.map x r)
      (fderiv ℝ F.normal x (coordinateUnit k)) = -immersionSecondForm F.map F.normal x r k := by
    rw [real_inner_comm]; exact immersion_normal_derivative_tangent F x hx r k
  simp only [inner_sub_left,inner_add_left,sum_inner,real_inner_smul_left,hn,hf,ht,
    mul_zero,add_zero,sub_zero,mul_neg,Finset.sum_neg_distrib]

/-- Differentiate the actual second fundamental form. Gauss--Weingarten
turns the differentiated normal into the third connection correction. -/
theorem immersionThirdForm_formula (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j k : Fin 4) :
    immersionThirdForm F.map F.normal x i j k =
      inner ℝ (immersionThirdDerivative F.map x i j k) (F.normal x) -
      ∑ r, (immersionChristoffel F.map x r i j * immersionSecondForm F.map F.normal x r k +
        immersionChristoffel F.map x r i k * immersionSecondForm F.map F.normal x r j +
        immersionChristoffel F.map x r j k * immersionSecondForm F.map F.normal x i r) := by
  have h2 := ((contDiffOn_immersionSecondDerivative F.isOpen_domain F.smooth_map i j) x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx) |>.differentiableAt (by simp)
  have hN := ((F.smooth_normal x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hd : fderiv ℝ (fun y => immersionSecondForm F.map F.normal y i j) x (coordinateUnit k) =
      inner ℝ (immersionSecondDerivative F.map x i j) (fderiv ℝ F.normal x (coordinateUnit k)) +
      inner ℝ (immersionThirdDerivative F.map x i j k) (F.normal x) :=
    fderiv_inner_apply ℝ h2 hN _
  simp only [immersionThirdForm,coordinateCovariant2,hd,
    immersion_secondDerivative_normalDerivative F x hx,Finset.sum_add_distrib]
  ring

/-- Codazzi is obtained from the actual immersion derivatives, equality of
mixed partials and Gauss--Weingarten. It is not a field of the local data. -/
theorem immersionThirdForm_symmetric (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) : CubicSymmetric (immersionThirdForm F.map F.normal x) := by
  apply (cubicSymmetric_iff_swaps _).mpr
  constructor
  · intro i j k
    rw [immersionThirdForm_formula F x hx,immersionThirdForm_formula F x hx,
      immersionThirdDerivative_swap12 F x hx i j k]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [immersionChristoffel_symmetric F x hx r i j,
      (immersionSecondForm_symmetric F x hx).apply i r,
      (immersionSecondForm_symmetric F x hx).apply j r]
    ring
  · intro i j k
    rw [immersionThirdForm_formula F x hx,immersionThirdForm_formula F x hx,
      immersionThirdDerivative_swap23 F x hx i j k]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [immersionChristoffel_symmetric F x hx r j k]
    ring

/-- Covariant differentiation preserves the symmetry among the original
three slots. No symmetry involving the last derivative slot is asserted. -/
theorem coordinateCovariant3_firstThree
    (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (T : Chart4 → Cubic4)
    (x : Chart4) (hT : ∀ᶠ y in 𝓝 x, CubicSymmetric (T y)) :
    FirstThreeSymmetric (coordinateCovariant3 Γ T x) := by
  have hs := hT.self_of_nhds
  constructor
  · intro i j k l
    have he : (fun y => T y i j k) =ᶠ[𝓝 x] (fun y => T y j i k) :=
      hT.mono (fun y hy => cubicSymmetric_swap12 hy i j k)
    simp only [coordinateCovariant3,he.fderiv_eq (𝕜 := ℝ)]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [cubicSymmetric_swap12 hs r j k,cubicSymmetric_swap12 hs i r k,
      cubicSymmetric_swap12 hs i j r]
    ring
  · intro i j k l
    have he : (fun y => T y i j k) =ᶠ[𝓝 x] (fun y => T y i k j) :=
      hT.mono (fun y hy => cubicSymmetric_swap23 hy i j k)
    simp only [coordinateCovariant3,he.fderiv_eq (𝕜 := ℝ)]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [cubicSymmetric_swap23 hs r j k,cubicSymmetric_swap23 hs i r k,
      cubicSymmetric_swap23 hs i j r]
    ring

theorem immersionFourthForm_firstThree (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) : FirstThreeSymmetric (immersionFourthForm F.map F.normal x) := by
  apply coordinateCovariant3_firstThree
  filter_upwards [F.isOpen_domain.mem_nhds hx] with y hy
  exact immersionThirdForm_symmetric F y hy

theorem immersionFrameThird_symmetric (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) : CubicSymmetric (immersionFrameThird F e x) :=
  frameCubic_symmetric _ _ (immersionThirdForm_symmetric F x hx)

theorem immersionFrameFourth_firstThree (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) : FirstThreeSymmetric (immersionFrameFourth F e x) :=
  frameFourth_firstThree _ _ (immersionFourthForm_firstThree F x hx)

end
end SecondPinching
