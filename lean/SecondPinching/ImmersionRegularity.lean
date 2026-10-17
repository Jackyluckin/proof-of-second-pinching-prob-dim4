import SecondPinching.ImmersionCoordinates
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section
attribute [local fun_prop] ContDiffOn.inner contDiff_inner

theorem contDiffOn_matrix4_det {U : Set Chart4} {A : Chart4 → Matrix4}
    (hA : ContDiffOn ℝ ∞ A U) : ContDiffOn ℝ ∞ (fun x => (A x).det) U := by
  simp only [Matrix.det_apply']
  fun_prop

theorem contDiffOn_matrix4_inverse {U : Set Chart4} {A : Chart4 → Matrix4}
    (hA : ContDiffOn ℝ ∞ A U) (hd : ∀ x ∈ U, (A x).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => (A x)⁻¹) U := by
  have hi := (contDiffOn_matrix4_det hA).inv hd
  apply contDiffOn_pi.mpr; intro i
  apply contDiffOn_pi.mpr; intro j
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,Matrix.adjugate_apply]
  apply hi.mul
  apply contDiffOn_matrix4_det
  apply contDiffOn_pi.mpr; intro a
  apply contDiffOn_pi.mpr; intro b
  by_cases ha : a = j
  · subst a
    simpa using (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Chart4 => (Pi.single i (1 : ℝ) : Vector4) b) U)
  · simpa [Matrix.updateRow_apply,ha] using
      ((contDiffOn_pi.mp (contDiffOn_pi.mp hA a)) b)

theorem contDiffOn_immersionTangent {U : Set Chart4} (hU : IsOpen U)
    {f : Chart4 → Ambient6} (hf : ContDiffOn ℝ ∞ f U) (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => immersionTangent f x i) U := by
  have hd := hf.fderiv_of_isOpen hU (m := ∞) (by simp)
  unfold immersionTangent
  fun_prop

theorem contDiffOn_immersionSecondDerivative {U : Set Chart4} (hU : IsOpen U)
    {f : Chart4 → Ambient6} (hf : ContDiffOn ℝ ∞ f U) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => immersionSecondDerivative f x i j) U := by
  have hd := (contDiffOn_immersionTangent hU hf i).fderiv_of_isOpen hU (m := ∞) (by simp)
  unfold immersionSecondDerivative
  fun_prop

theorem contDiffOn_immersionMetric {U : Set Chart4} (hU : IsOpen U)
    {f : Chart4 → Ambient6} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (immersionMetric f) U := by
  apply contDiffOn_pi.mpr; intro i
  apply contDiffOn_pi.mpr; intro j
  exact (contDiffOn_immersionTangent hU hf i).inner ℝ (contDiffOn_immersionTangent hU hf j)

theorem contDiffOn_immersionChristoffel (F : LocalSphereImmersion) :
    ContDiffOn ℝ ∞ (immersionChristoffel F.map) F.domain := by
  have hg := contDiffOn_immersionMetric F.isOpen_domain F.smooth_map
  have hi := contDiffOn_matrix4_inverse hg
    (fun x hx => immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx))
  have h1 := contDiffOn_immersionTangent F.isOpen_domain F.smooth_map
  have h2 := contDiffOn_immersionSecondDerivative F.isOpen_domain F.smooth_map
  unfold immersionChristoffel
  fun_prop

theorem contDiffOn_coordinateCovariant2 {U : Set Chart4} (hU : IsOpen U)
    {Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ} {h : Chart4 → Matrix4}
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hh : ContDiffOn ℝ ∞ h U) :
    ContDiffOn ℝ ∞ (coordinateCovariant2 Γ h) U := by
  apply contDiffOn_pi.mpr; intro i
  apply contDiffOn_pi.mpr; intro j
  apply contDiffOn_pi.mpr; intro k
  have hd := ((contDiffOn_pi.mp (contDiffOn_pi.mp hh i)) j).fderiv_of_isOpen hU
    (m := ∞) (by simp)
  unfold coordinateCovariant2
  fun_prop

theorem contDiffOn_coordinateCovariant3 {U : Set Chart4} (hU : IsOpen U)
    {Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ} {T : Chart4 → Cubic4}
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (coordinateCovariant3 Γ T) U := by
  apply contDiffOn_pi.mpr; intro i
  apply contDiffOn_pi.mpr; intro j
  apply contDiffOn_pi.mpr; intro k
  apply contDiffOn_pi.mpr; intro l
  have hd := ((contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hT i) j)) k).fderiv_of_isOpen hU
    (m := ∞) (by simp)
  unfold coordinateCovariant3
  fun_prop

/-- Smoothness is proved from the actual smooth immersion and local normal.
No continuity assumption on an independently supplied h,T,H is needed. -/
theorem contDiffOn_immersionForms (F : LocalSphereImmersion) :
    ContDiffOn ℝ ∞ (immersionSecondForm F.map F.normal) F.domain ∧
    ContDiffOn ℝ ∞ (immersionThirdForm F.map F.normal) F.domain ∧
    ContDiffOn ℝ ∞ (immersionFourthForm F.map F.normal) F.domain := by
  have hh : ContDiffOn ℝ ∞ (immersionSecondForm F.map F.normal) F.domain := by
    apply contDiffOn_pi.mpr; intro i
    apply contDiffOn_pi.mpr; intro j
    exact (contDiffOn_immersionSecondDerivative F.isOpen_domain F.smooth_map i j).inner ℝ F.smooth_normal
  have hΓ := contDiffOn_immersionChristoffel F
  have ht := contDiffOn_coordinateCovariant2 F.isOpen_domain hΓ hh
  exact ⟨hh,ht,contDiffOn_coordinateCovariant3 F.isOpen_domain hΓ ht⟩

end
end SecondPinching
