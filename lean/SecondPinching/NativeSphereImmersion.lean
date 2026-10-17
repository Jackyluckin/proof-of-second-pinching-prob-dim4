import SecondPinching.GlobalSphereImmersion
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Manifold ContDiff Topology
namespace SecondPinching
noncomputable section
universe u

abbrev Sphere5 := Metric.sphere (0 : Ambient6) 1

variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

/-- The manuscript's smooth immersion into the native five-sphere manifold.
The immersion property is local differential injectivity, not injectivity of
the map itself. -/
structure SphereImmersion (M : Type u) [TopologicalSpace M] [ChartedSpace Chart4 M] where
  map : M → Sphere5
  smooth : ContMDiff 𝓘(ℝ,Chart4) (𝓡 5) ∞ map
  immersion : ∀ x, IsDiffImmersionAt 𝓘(ℝ,Chart4) (𝓡 5) map x

theorem sphere_inclusion_mfderiv_injective (x : Sphere5) :
    Function.Injective (mfderiv (𝓡 5) 𝓘(ℝ,Ambient6) (Subtype.val : Sphere5 → Ambient6) x) := by
  let _ : Fact (Module.finrank ℝ Ambient6=5+1) := ⟨by simp [Ambient6]⟩
  convert! injective_mvfderiv_subtypeVal_sphere (n:=5) x

theorem sphere_inclusion_smooth : ContMDiff (𝓡 5) 𝓘(ℝ,Ambient6) ∞ (Subtype.val : Sphere5 → Ambient6) := by
  let _ : Fact (Module.finrank ℝ Ambient6=5+1) := ⟨by simp [Ambient6]⟩
  exact contMDiff_coe_sphere (n:=5)

def sphereImmersionToAmbient (F : SphereImmersion M) : GlobalSphereImmersion M where
  map := fun x => (F.map x : Ambient6)
  smooth := sphere_inclusion_smooth.comp F.smooth
  injective_derivative := by
    intro x
    have hc := mfderiv_comp x (sphere_inclusion_smooth.mdifferentiableAt (by simp))
      (F.smooth.mdifferentiableAt (by simp))
    change Function.Injective (mfderiv 𝓘(ℝ,Chart4) 𝓘(ℝ,Ambient6)
      ((Subtype.val : Sphere5 → Ambient6) ∘ F.map) x)
    rw [hc]
    exact (sphere_inclusion_mfderiv_injective (F.map x)).comp (F.immersion x).mfderiv_injective
  sphere := by
    intro x
    have hn : ‖(F.map x : Ambient6)‖=1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using (F.map x).property
    rw [real_inner_self_eq_norm_sq,hn]
    norm_num

omit [IsManifold 𝓘(ℝ,Chart4) ∞ M] in
theorem ambientImmersion_mem_sphere (F : GlobalSphereImmersion M) (x : M) : F.map x ∈ Metric.sphere (0 : Ambient6) 1 := by
  rw [Metric.mem_sphere,dist_zero_right]
  have hs := F.sphere x
  rw [real_inner_self_eq_norm_sq] at hs
  nlinarith [norm_nonneg (F.map x)]

def ambientImmersionSphereMap (F : GlobalSphereImmersion M) : M → Sphere5 :=
  Set.codRestrict F.map _ (ambientImmersion_mem_sphere F)

theorem ambientImmersionSphereMap_smooth (F : GlobalSphereImmersion M) :
    ContMDiff 𝓘(ℝ,Chart4) (𝓡 5) ∞ (ambientImmersionSphereMap F) := by
  let _ : Fact (Module.finrank ℝ Ambient6=5+1) := ⟨by simp [Ambient6]⟩
  exact F.smooth.codRestrict_sphere (n:=5) (ambientImmersion_mem_sphere F)

theorem ambientImmersionSphereMap_isImmersionAt (F : GlobalSphereImmersion M) (x : M) :
    IsDiffImmersionAt 𝓘(ℝ,Chart4) (𝓡 5) (ambientImmersionSphereMap F) x := by
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  have hc := mfderiv_comp x (sphere_inclusion_smooth.mdifferentiableAt (by simp))
    ((ambientImmersionSphereMap_smooth F).mdifferentiableAt (by simp))
  have he : mfderiv 𝓘(ℝ,Chart4) 𝓘(ℝ,Ambient6) F.map x =
      (mfderiv (𝓡 5) 𝓘(ℝ,Ambient6) (Subtype.val : Sphere5 → Ambient6) (ambientImmersionSphereMap F x)).comp
        (mfderiv 𝓘(ℝ,Chart4) (𝓡 5) (ambientImmersionSphereMap F) x) := hc
  have hi := F.injective_derivative x
  rw [he] at hi
  exact Function.Injective.of_comp
    (f := mfderiv (𝓡 5) 𝓘(ℝ,Ambient6) (Subtype.val : Sphere5 → Ambient6) (ambientImmersionSphereMap F x))
    (g := mfderiv 𝓘(ℝ,Chart4) (𝓡 5) (ambientImmersionSphereMap F) x) hi

def ambientImmersionToSphere (F : GlobalSphereImmersion M) : SphereImmersion M where
  map := ambientImmersionSphereMap F
  smooth := ambientImmersionSphereMap_smooth F
  immersion := ambientImmersionSphereMap_isImmersionAt F

omit [IsManifold 𝓘(ℝ,Chart4) ∞ M] in
theorem globalSphereImmersion_ext_map (F G : GlobalSphereImmersion M) (h : F.map=G.map) : F=G := by
  cases F
  cases G
  cases h
  rfl

omit [IsManifold 𝓘(ℝ,Chart4) ∞ M] in
theorem sphereImmersion_ext_map (F G : SphereImmersion M) (h : F.map=G.map) : F=G := by
  cases F
  cases G
  cases h
  rfl

theorem sphere_to_ambient_to_sphere (F : SphereImmersion M) :
    ambientImmersionToSphere (sphereImmersionToAmbient F)=F := by
  apply sphereImmersion_ext_map
  funext x
  apply Subtype.ext
  rfl

theorem ambient_to_sphere_to_ambient (F : GlobalSphereImmersion M) :
    sphereImmersionToAmbient (ambientImmersionToSphere F)=F := by
  apply globalSphereImmersion_ext_map
  rfl

end
end SecondPinching
