import SecondPinching.LocalNormalConstruction
import SecondPinching.ImmersionCoordinateBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

def globalLocalNormalSeed (F : GlobalSphereImmersion M) (p : M) : Ambient6 :=
  Classical.choose (parametrization_exists_normal_vector (globalSphereParametrization F p) (chartAt Chart4 p p))

def globalImmersionLocal (F : GlobalSphereImmersion M) (p : M) : LocalSphereImmersion :=
  parametrizationWithLocalNormal (globalSphereParametrization F p) (globalLocalNormalSeed F p)

theorem globalImmersionLocal_map (F : GlobalSphereImmersion M) (p : M) :
    (globalImmersionLocal F p).map=globalImmersionCoordinateMap F p := rfl

theorem globalImmersionLocal_center (F : GlobalSphereImmersion M) (p : M) :
    chartAt Chart4 p p ∈ (globalImmersionLocal F p).domain := by
  have hs := Classical.choose_spec
    (parametrization_exists_normal_vector (globalSphereParametrization F p) (chartAt Chart4 p p))
  change chartAt Chart4 p p ∈ (globalSphereParametrization F p).domain ∧
    parametrizationNormalProjection (globalSphereParametrization F p) (globalLocalNormalSeed F p)
      (chartAt Chart4 p p) ≠ 0
  refine ⟨mem_chart_target Chart4 p,?_⟩
  have he : parametrizationNormalProjection (globalSphereParametrization F p) (globalLocalNormalSeed F p)
      (chartAt Chart4 p p)=globalLocalNormalSeed F p :=
    parametrizationNormalProjection_eq_self _ _ _ hs.2.1 hs.2.2
  exact he.trans_ne hs.1

theorem globalImmersionLocal_domain_subset (F : GlobalSphereImmersion M) (p : M) :
    (globalImmersionLocal F p).domain ⊆ (chartAt Chart4 p).target := fun _ hx => hx.1

def globalImmersionLocalSource (F : GlobalSphereImmersion M) (p : M) : Set M :=
  (chartAt Chart4 p).source ∩ (chartAt Chart4 p) ⁻¹' (globalImmersionLocal F p).domain

theorem isOpen_globalImmersionLocalSource (F : GlobalSphereImmersion M) (p : M) :
    IsOpen (globalImmersionLocalSource F p) :=
  (chartAt Chart4 p).continuousOn.isOpen_inter_preimage (chartAt Chart4 p).open_source
    (globalImmersionLocal F p).isOpen_domain

theorem globalImmersionLocalSource_center (F : GlobalSphereImmersion M) (p : M) :
    p ∈ globalImmersionLocalSource F p :=
  ⟨mem_chart_source Chart4 p,globalImmersionLocal_center F p⟩

theorem globalImmersionLocalSource_cover (F : GlobalSphereImmersion M) (x : M) :
    ∃ p, x ∈ globalImmersionLocalSource F p := ⟨x,globalImmersionLocalSource_center F x⟩

theorem globalImmersionLocalSource_chart_continuous (F : GlobalSphereImmersion M) (p : M) :
    ContinuousOn (chartAt Chart4 p) (globalImmersionLocalSource F p) :=
  (chartAt Chart4 p).continuousOn.mono (fun _ hx => hx.1)

def globalChartTransition (p q : M) : OpenPartialHomeomorph Chart4 Chart4 :=
  (chartAt Chart4 q).symm.trans (chartAt Chart4 p)

theorem contDiffOn_globalChartTransition (p q : M) :
    ContDiffOn ℝ ∞ (globalChartTransition p q) (globalChartTransition p q).source := by
  apply ContMDiffOn.contDiffOn
  exact (contMDiffOn_chart (I:=𝓘(ℝ,Chart4)) (x:=p)).comp
    ((contMDiffOn_chart_symm (I:=𝓘(ℝ,Chart4)) (x:=q)).mono (fun _ hx => hx.1))
    (fun _ hx => hx.2)

theorem globalChartTransition_injective_derivative (p q : M) (x : Chart4)
    (hx : x ∈ (globalChartTransition p q).source) :
    Function.Injective (fderiv ℝ (globalChartTransition p q) x) := by
  have hd := ((mdifferentiable_chart (I:=𝓘(ℝ,Chart4)) q).symm.trans
    (mdifferentiable_chart (I:=𝓘(ℝ,Chart4)) p)).mfderiv_injective hx
  rw [← mfderiv_eq_fderiv]
  exact hd

/-- Actual chart transition, restricted so its image lies in the local
immersion domain chosen at p. -/
def globalImmersionReparametrization (F : GlobalSphereImmersion M) (p q : M) :
    ImmersionReparametrization (globalImmersionLocal F p) where
  domain := (globalChartTransition p q).source ∩
    (globalChartTransition p q) ⁻¹' (globalImmersionLocal F p).domain
  isOpen_domain := (globalChartTransition p q).continuousOn.isOpen_inter_preimage
    (globalChartTransition p q).open_source (globalImmersionLocal F p).isOpen_domain
  map := globalChartTransition p q
  smooth_map := (contDiffOn_globalChartTransition p q).mono (fun _ hx => hx.1)
  mapsTo := fun _ hx => hx.2
  injective_derivative := fun x hx => globalChartTransition_injective_derivative p q x hx.1

theorem globalImmersionReparametrization_point (F : GlobalSphereImmersion M) (p q x : M)
    (hp : x ∈ globalImmersionLocalSource F p) (hq : x ∈ globalImmersionLocalSource F q) :
    chartAt Chart4 q x ∈ (globalImmersionReparametrization F p q).domain ∧
      (globalImmersionReparametrization F p q).map (chartAt Chart4 q x)=chartAt Chart4 p x := by
  have hi : (chartAt Chart4 q).symm (chartAt Chart4 q x)=x := (chartAt Chart4 q).left_inv hq.1
  change (chartAt Chart4 q x ∈ (globalChartTransition p q).source ∧
      (globalChartTransition p q) (chartAt Chart4 q x) ∈ (globalImmersionLocal F p).domain) ∧ _
  have ht : (globalChartTransition p q) (chartAt Chart4 q x)=chartAt Chart4 p x := by
    change (chartAt Chart4 p) ((chartAt Chart4 q).symm ((chartAt Chart4 q) x))=_
    rw [hi]
  refine ⟨⟨?_,?_⟩,ht⟩
  · change chartAt Chart4 q x ∈ (chartAt Chart4 q).target ∧
      (chartAt Chart4 q).symm (chartAt Chart4 q x) ∈ (chartAt Chart4 p).source
    exact ⟨(chartAt Chart4 q).map_source hq.1,by simpa only [hi] using hp.1⟩
  · rw [ht]
    exact hp.2

theorem globalImmersionReparametrization_germ (F : GlobalSphereImmersion M) (p q : M)
    (x : Chart4) (hx : x ∈ (globalImmersionReparametrization F p q).domain) :
    (globalImmersionLocal F q).map =ᶠ[𝓝 x]
      (globalImmersionLocal F p).map ∘ (globalImmersionReparametrization F p q).map := by
  apply Filter.eventuallyEq_of_mem ((globalImmersionReparametrization F p q).isOpen_domain.mem_nhds hx)
  intro y hy
  change F.map ((chartAt Chart4 q).symm y)=
    F.map ((chartAt Chart4 p).symm ((chartAt Chart4 p) ((chartAt Chart4 q).symm y)))
  have hi : (chartAt Chart4 p).symm ((chartAt Chart4 p) ((chartAt Chart4 q).symm y)) =
      (chartAt Chart4 q).symm y := (chartAt Chart4 p).left_inv hy.1.2
  exact (congrArg F.map hi).symm

/-- Coordinate compatibility is obtained from the given manifold charts and
the one global immersion map, with no tensor or connection transition premise. -/
theorem globalImmersionLocal_coordinate_overlaps (F : GlobalSphereImmersion M) :
    ImmersionCoordinateOverlaps (globalImmersionLocal F) (fun p => chartAt Chart4 p)
      (globalImmersionLocalSource F) := by
  intro p q x hp hq
  obtain ⟨hx,he⟩ := globalImmersionReparametrization_point F p q x hp hq
  exact ⟨globalImmersionReparametrization F p q,hx,he,
    globalImmersionReparametrization_germ F p q _ hx⟩

end
end SecondPinching
