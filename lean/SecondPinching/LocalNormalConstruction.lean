import SecondPinching.ParametrizationNormalProjection
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section
attribute [local fun_prop] ContDiffOn.inner contDiff_inner

def localNormalDomain (F : SphereParametrization) (w : Ambient6) : Set Chart4 :=
  F.domain ∩ {x | parametrizationNormalProjection F w x ≠ 0}

def constructedLocalNormal (F : SphereParametrization) (w : Ambient6) (x : Chart4) : Ambient6 :=
  (Real.sqrt (inner ℝ (parametrizationNormalProjection F w x)
    (parametrizationNormalProjection F w x)))⁻¹ • parametrizationNormalProjection F w x

theorem isOpen_localNormalDomain (F : SphereParametrization) (w : Ambient6) :
    IsOpen (localNormalDomain F w) :=
  (contDiffOn_parametrizationNormalProjection F w).continuousOn.isOpen_inter_preimage
    F.isOpen_domain isOpen_compl_singleton

theorem contDiffOn_constructedLocalNormal (F : SphereParametrization) (w : Ambient6) :
    ContDiffOn ℝ ∞ (constructedLocalNormal F w) (localNormalDomain F w) := by
  have hp := (contDiffOn_parametrizationNormalProjection F w).mono
    (show localNormalDomain F w ⊆ F.domain from fun _ hx => hx.1)
  have hi : ContDiffOn ℝ ∞ (fun x => inner ℝ (parametrizationNormalProjection F w x)
      (parametrizationNormalProjection F w x)) (localNormalDomain F w) := hp.inner ℝ hp
  have hn (x : Chart4) (hx : x ∈ localNormalDomain F w) :
      inner ℝ (parametrizationNormalProjection F w x) (parametrizationNormalProjection F w x) ≠ 0 :=
    fun h => hx.2 ((inner_self_eq_zero (𝕜:=ℝ)).mp h)
  have hs := hi.sqrt hn
  exact (hs.inv (fun x hx => Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne
    (real_inner_self_nonneg) (Ne.symm (hn x hx))))).smul hp

theorem constructedLocalNormal_unit (F : SphereParametrization) (w : Ambient6)
    (x : Chart4) (hx : x ∈ localNormalDomain F w) :
    inner ℝ (constructedLocalNormal F w x) (constructedLocalNormal F w x)=1 := by
  let z := parametrizationNormalProjection F w x
  have hi : 0 < inner ℝ z z := lt_of_le_of_ne (real_inner_self_nonneg)
    (Ne.symm (fun h => hx.2 ((inner_self_eq_zero (𝕜:=ℝ)).mp h)))
  have hn : Real.sqrt (inner ℝ z z)≠0 := Real.sqrt_ne_zero'.mpr hi
  have hs := Real.sq_sqrt hi.le
  change inner ℝ ((Real.sqrt (inner ℝ z z))⁻¹ • z) ((Real.sqrt (inner ℝ z z))⁻¹ • z)=1
  rw [real_inner_smul_left,inner_smul_right]
  calc
    _ = (Real.sqrt (inner ℝ z z))⁻¹ * ((Real.sqrt (inner ℝ z z))⁻¹ *
      (Real.sqrt (inner ℝ z z))^2) := by rw [hs]
    _ = 1 := by field_simp

theorem constructedLocalNormal_radial (F : SphereParametrization) (w : Ambient6)
    (x : Chart4) (hx : x ∈ localNormalDomain F w) :
    inner ℝ (constructedLocalNormal F w x) (F.map x)=0 := by
  have hr : inner ℝ (parametrizationNormalProjection F w x) (F.map x)=0 :=
    (real_inner_comm _ _).trans (parametrizationNormalProjection_radial F w x hx.1)
  simp only [constructedLocalNormal,real_inner_smul_left,hr,mul_zero]

theorem constructedLocalNormal_tangent (F : SphereParametrization) (w : Ambient6)
    (x : Chart4) (hx : x ∈ localNormalDomain F w) (i : Fin 4) :
    inner ℝ (constructedLocalNormal F w x) (immersionTangent F.map x i)=0 := by
  have ht : inner ℝ (parametrizationNormalProjection F w x) (immersionTangent F.map x i)=0 :=
    (real_inner_comm _ _).trans (parametrizationNormalProjection_tangent F w x hx.1 i)
  simp only [constructedLocalNormal,real_inner_smul_left,ht,mul_zero]

/-- The actual local data required by the previously proved differential
identities. Its normal is constructed, not supplied as a new geometric axiom. -/
def parametrizationWithLocalNormal (F : SphereParametrization) (w : Ambient6) : LocalSphereImmersion where
  domain := localNormalDomain F w
  isOpen_domain := isOpen_localNormalDomain F w
  map := F.map
  normal := constructedLocalNormal F w
  smooth_map := F.smooth_map.mono (fun _ hx => hx.1)
  smooth_normal := contDiffOn_constructedLocalNormal F w
  injective_derivative := fun x hx => F.injective_derivative x hx.1
  sphere := fun x hx => F.sphere x hx.1
  normal_unit := constructedLocalNormal_unit F w
  normal_radial := constructedLocalNormal_radial F w
  normal_tangent := constructedLocalNormal_tangent F w

theorem exists_parametrizationWithLocalNormal (F : SphereParametrization) (x : Chart4)
    (hx : x ∈ F.domain) :
    ∃ w : Ambient6, x ∈ (parametrizationWithLocalNormal F w).domain ∧
      (parametrizationWithLocalNormal F w).map=F.map := by
  obtain ⟨w,hn,hr,ht⟩ := parametrization_exists_normal_vector F x
  refine ⟨w,⟨hx,?_⟩,rfl⟩
  change parametrizationNormalProjection F w x ≠ 0
  rw [parametrizationNormalProjection_eq_self F w x hr ht]
  exact hn

end
end SecondPinching
