import SecondPinching.ReducedHessian
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

abbrev Chart4 := Fin 4 → ℝ
abbrev Ambient6 := EuclideanSpace ℝ (Fin 6)

def coordinateUnit (i : Fin 4) : Chart4 := Pi.single i 1

/-- Actual derivatives of a local parametrization, with the derivative slot last. -/
def immersionTangent (f : Chart4 → Ambient6) (x : Chart4) (i : Fin 4) : Ambient6 :=
  fderiv ℝ f x (coordinateUnit i)

def immersionSecondDerivative (f : Chart4 → Ambient6) (x : Chart4) (i j : Fin 4) : Ambient6 :=
  fderiv ℝ (fun y => immersionTangent f y i) x (coordinateUnit j)

def immersionMetric (f : Chart4 → Ambient6) (x : Chart4) : Matrix4 :=
  Matrix.gram ℝ (immersionTangent f x)

/-- A local sphere parametrization with a chosen local unit normal. The
structure contains no curvature identity, no normalized tensor and no reduced
Hessian. Existence of such choices on a manifold atlas is a separate obligation. -/
structure LocalSphereImmersion where
  domain : Set Chart4
  isOpen_domain : IsOpen domain
  map : Chart4 → Ambient6
  normal : Chart4 → Ambient6
  smooth_map : ContDiffOn ℝ ∞ map domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  injective_derivative : ∀ x ∈ domain, Function.Injective (fderiv ℝ map x)
  sphere : ∀ x ∈ domain, inner ℝ (map x) (map x) = 1
  normal_unit : ∀ x ∈ domain, inner ℝ (normal x) (normal x) = 1
  normal_radial : ∀ x ∈ domain, inner ℝ (normal x) (map x) = 0
  normal_tangent : ∀ x ∈ domain, ∀ i, inner ℝ (normal x) (immersionTangent map x i) = 0

theorem immersionMetric_posDef (f : Chart4 → Ambient6) (x : Chart4)
    (hi : Function.Injective (fderiv ℝ f x)) : (immersionMetric f x).PosDef := by
  apply Matrix.posDef_gram_of_linearIndependent
  exact (Pi.linearIndependent_single_one (Fin 4) ℝ).map' (fderiv ℝ f x).toLinearMap
    (LinearMap.ker_eq_bot.mpr hi)

theorem immersionMetric_det_ne_zero (f : Chart4 → Ambient6) (x : Chart4)
    (hi : Function.Injective (fderiv ℝ f x)) : (immersionMetric f x).det ≠ 0 :=
  (immersionMetric_posDef f x hi).det_pos.ne'

/-- Coefficients of the tangential projection of the actual second derivative.
These are the Christoffel coefficients of the induced metric in coordinates. -/
def immersionChristoffel (f : Chart4 → Ambient6) (x : Chart4) (r i j : Fin 4) : ℝ :=
  ∑ s, (immersionMetric f x)⁻¹ r s *
    inner ℝ (immersionSecondDerivative f x i j) (immersionTangent f x s)

/-- This projection equation fixes the connection coefficients from f;
they are not an arbitrary connection supplied with the component arrays. -/
theorem immersionChristoffel_projection (f : Chart4 → Ambient6) (x : Chart4)
    (hi : Function.Injective (fderiv ℝ f x)) (s i j : Fin 4) :
    ∑ r, immersionMetric f x s r * immersionChristoffel f x r i j =
      inner ℝ (immersionSecondDerivative f x i j) (immersionTangent f x s) := by
  let b : Vector4 := fun r => inner ℝ (immersionSecondDerivative f x i j) (immersionTangent f x r)
  change ((immersionMetric f x) *ᵥ ((immersionMetric f x)⁻¹ *ᵥ b)) s = b s
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (immersionMetric_det_ne_zero f x hi)),
    Matrix.one_mulVec]

/-- Sign convention h_ij=<partial_j partial_i f,N>, agreeing with the
manuscript's Gauss equation. The radial second fundamental form of the unit
sphere has zero pairing with its tangent normal N. -/
def immersionSecondForm (f N : Chart4 → Ambient6) (x : Chart4) : Matrix4 :=
  fun i j => inner ℝ (immersionSecondDerivative f x i j) (N x)

/-- Covariant differentiation of a covariant two-tensor in the induced
coordinate connection. The derivative index is the final slot. -/
def coordinateCovariant2 (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : Chart4 → Matrix4) (x : Chart4) : Cubic4 := fun i j k =>
  fderiv ℝ (fun y => h y i j) x (coordinateUnit k) -
    ∑ r, (Γ x r i k * h x r j + Γ x r j k * h x i r)

/-- The third subtraction is essential: the derivative slot of nabla h is
itself covariant when forming nabla^2 h. -/
def coordinateCovariant3 (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T : Chart4 → Cubic4) (x : Chart4) : Fourth4 := fun i j k l =>
  fderiv ℝ (fun y => T y i j k) x (coordinateUnit l) -
    ∑ r, (Γ x r i l * T x r j k + Γ x r j l * T x i r k +
      Γ x r k l * T x i j r)

def immersionThirdForm (f N : Chart4 → Ambient6) : Chart4 → Cubic4 :=
  coordinateCovariant2 (immersionChristoffel f) (immersionSecondForm f N)

def immersionFourthForm (f N : Chart4 → Ambient6) : Chart4 → Fourth4 :=
  coordinateCovariant3 (immersionChristoffel f) (immersionThirdForm f N)

theorem coordinateCovariant2_neg (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : Chart4 → Matrix4) : coordinateCovariant2 Γ (-h) = -coordinateCovariant2 Γ h := by
  funext x i j k
  simp only [coordinateCovariant2,Pi.neg_apply,Matrix.neg_apply]
  have hd : fderiv ℝ (fun y => -h y i j) x = -fderiv ℝ (fun y => h y i j) x := fderiv_neg
  rw [hd]
  simp only [neg_apply,mul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

theorem coordinateCovariant3_neg (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T : Chart4 → Cubic4) : coordinateCovariant3 Γ (-T) = -coordinateCovariant3 Γ T := by
  funext x i j k l
  simp only [coordinateCovariant3,Pi.neg_apply]
  have hd : fderiv ℝ (fun y => -T y i j k) x = -fderiv ℝ (fun y => T y i j k) x := fderiv_neg
  rw [hd]
  simp only [neg_apply,mul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

/-- Normal reversal is derived for the actual derivatives, before normalization. -/
theorem immersion_forms_normal_reversal (f N : Chart4 → Ambient6) :
    immersionSecondForm f (-N) = -immersionSecondForm f N ∧
    immersionThirdForm f (-N) = -immersionThirdForm f N ∧
    immersionFourthForm f (-N) = -immersionFourthForm f N := by
  have h : immersionSecondForm f (-N) = -immersionSecondForm f N := by
    funext x i j; simp [immersionSecondForm]
  have hT : immersionThirdForm f (-N) = -immersionThirdForm f N := by
    unfold immersionThirdForm
    rw [h,coordinateCovariant2_neg]
  exact ⟨h,hT,by unfold immersionFourthForm; rw [hT,coordinateCovariant3_neg]⟩

theorem coordinateCovariant2_congr_germ (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h g : Chart4 → Matrix4) (x : Chart4) (he : h =ᶠ[𝓝 x] g) :
    coordinateCovariant2 Γ h =ᶠ[𝓝 x] coordinateCovariant2 Γ g := by
  filter_upwards [he.eventuallyEq_nhds] with y hy
  funext i j k
  have he' : (fun z => h z i j) =ᶠ[𝓝 y] (fun z => g z i j) :=
    hy.mono (fun z hz => congrFun (congrFun hz i) j)
  have hd := he'.fderiv_eq (𝕜 := ℝ)
  simp only [coordinateCovariant2,hd,hy.self_of_nhds]

theorem coordinateCovariant3_congr_germ (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T U : Chart4 → Cubic4) (x : Chart4) (he : T =ᶠ[𝓝 x] U) :
    coordinateCovariant3 Γ T =ᶠ[𝓝 x] coordinateCovariant3 Γ U := by
  filter_upwards [he.eventuallyEq_nhds] with y hy
  funext i j k l
  have he' : (fun z => T z i j k) =ᶠ[𝓝 y] (fun z => U z i j k) :=
    hy.mono (fun z hz => congrFun (congrFun (congrFun hz i) j) k)
  have hd := he'.fderiv_eq (𝕜 := ℝ)
  simp only [coordinateCovariant3,hd,hy.self_of_nhds]

/-- Only equality on a neighborhood is needed. No global choice of the normal
is built into the coordinate derivatives or their overlap comparison. -/
theorem immersion_forms_congr_normal_germ (f N N' : Chart4 → Ambient6)
    (x : Chart4) (he : N =ᶠ[𝓝 x] N') :
    immersionSecondForm f N =ᶠ[𝓝 x] immersionSecondForm f N' ∧
    immersionThirdForm f N =ᶠ[𝓝 x] immersionThirdForm f N' ∧
    immersionFourthForm f N =ᶠ[𝓝 x] immersionFourthForm f N' := by
  have hh : immersionSecondForm f N =ᶠ[𝓝 x] immersionSecondForm f N' := by
    filter_upwards [he] with y hy
    funext i j
    simp only [immersionSecondForm,hy]
  have ht := coordinateCovariant2_congr_germ (immersionChristoffel f) _ _ x hh
  exact ⟨hh,ht,coordinateCovariant3_congr_germ (immersionChristoffel f) _ _ x ht⟩

end
end SecondPinching
