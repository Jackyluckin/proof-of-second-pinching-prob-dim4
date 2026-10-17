import SecondPinching.ScalarCutoffCalculus

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped BigOperators Topology ContDiff
namespace SecondPinching
noncomputable section

theorem immersionCoordinateDivergence_smul (F : LocalSphereImmersion)
    (χ : Chart4 → ℝ) (Y : Chart4 → Vector4) (x : Chart4)
    (hχ : DifferentiableAt ℝ χ x) (hY : DifferentiableAt ℝ Y x) :
    immersionCoordinateDivergence F (fun y => χ y • Y y) x =
      χ x * immersionCoordinateDivergence F Y x + fderiv ℝ χ x (Y x) := by
  have hy (i : Fin 4) := differentiableAt_pi.mp hY i
  have he (i : Fin 4) :
      (∑ j, immersionChristoffel F.map x i j i * (χ x * Y x j)) =
        χ x * ∑ j, immersionChristoffel F.map x i j i * Y x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  unfold immersionCoordinateDivergence
  simp only [Pi.smul_apply,smul_eq_mul,fderiv_fun_mul hχ (hy _),add_apply,smul_apply]
  rw [scalar_fderiv_coordinate_expansion χ x (Y x),Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [he i]
  ring

theorem contDiffOn_immersionCoordinateDivergence (F : LocalSphereImmersion)
    (Y : Chart4 → Vector4) (hY : ContDiffOn ℝ ∞ Y F.domain) :
    ContDiffOn ℝ ∞ (immersionCoordinateDivergence F Y) F.domain := by
  have hΓ := contDiffOn_immersionChristoffel F
  have hd (i : Fin 4) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => Y y i) x (coordinateUnit i)) F.domain :=
    ((contDiffOn_pi.mp hY i).fderiv_of_isOpen F.isOpen_domain (m:=∞) (by simp)).clm_apply contDiffOn_const
  unfold immersionCoordinateDivergence
  fun_prop

def coordinateCutoffVectorDensity (F : LocalSphereImmersion) (χ : Chart4 → ℝ)
    (Y : Chart4 → Vector4) (x : Chart4) : Vector4 := χ x • (immersionVolumeDensity F x • Y x)

theorem contDiff_coordinateCutoffVectorDensity (F : LocalSphereImmersion) (χ : Chart4 → ℝ)
    (Y : Chart4 → Vector4) (hχ : ContDiff ℝ ∞ χ) (hY : ContDiffOn ℝ ∞ Y F.domain)
    (hs : tsupport χ ⊆ F.domain) : ContDiff ℝ ∞ (coordinateCutoffVectorDensity F χ Y) :=
  contDiff_cutoff_smul F.domain F.isOpen_domain χ _ hχ
    ((contDiffOn_immersionVolumeDensity F).smul hY) hs

theorem hasCompactSupport_coordinateCutoffVectorDensity (F : LocalSphereImmersion)
    (χ : Chart4 → ℝ) (Y : Chart4 → Vector4) (hc : HasCompactSupport χ) :
    HasCompactSupport (coordinateCutoffVectorDensity F χ Y) :=
  hasCompactSupport_cutoff_smul χ _ hc

theorem coordinateDivergence_cutoff_density (F : LocalSphereImmersion)
    (χ : Chart4 → ℝ) (Y : Chart4 → Vector4)
    (hχ : ContDiff ℝ ∞ χ) (hY : ContDiffOn ℝ ∞ Y F.domain) (hs : tsupport χ ⊆ F.domain)
    (x : Chart4) :
    coordinateDivergence (coordinateCutoffVectorDensity F χ Y) x =
      χ x * (immersionVolumeDensity F x * immersionCoordinateDivergence F Y x) +
        immersionVolumeDensity F x * fderiv ℝ χ x (Y x) := by
  by_cases hx : x ∈ F.domain
  · have hc := (hχ.differentiable (by simp)) x
    have hy := ((hY x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
    have he : coordinateCutoffVectorDensity F χ Y =
        (fun y => immersionVolumeDensity F y • (χ y • Y y)) := by
      funext y
      simp only [coordinateCutoffVectorDensity,smul_smul]
      rw [mul_comm]
    rw [he]
    have hd := immersionCoordinateDivergence_density F (fun y => χ y • Y y) x hx (hc.smul hy)
    rw [immersionCoordinateDivergence_smul F χ Y x hc hy] at hd
    exact hd.trans (by ring)
  · have hn : x ∉ tsupport χ := fun h => hx (hs h)
    have he : coordinateCutoffVectorDensity F χ Y =ᶠ[𝓝 x] fun _ => (0 : Vector4) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).mono
        (fun y hy => by simp only [coordinateCutoffVectorDensity,hy,Pi.zero_apply,zero_smul])
    have hz : coordinateDivergence (coordinateCutoffVectorDensity F χ Y) x=0 := by
      apply Finset.sum_eq_zero; intro i _
      have hei : (fun y => coordinateCutoffVectorDensity F χ Y y i) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        he.mono (fun y hy => congrFun hy i)
      rw [hei.fderiv_eq]
      simp
    rw [hz,image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn]
    simp

/-- Both summands are integrable before the local divergence theorem is
split into its two integrals. -/
theorem coordinate_cutoff_integrals (F : LocalSphereImmersion) (χ : Chart4 → ℝ)
    (Y : Chart4 → Vector4) (hχ : ContDiff ℝ ∞ χ) (hY : ContDiffOn ℝ ∞ Y F.domain)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ F.domain) :
    Integrable (fun x => χ x * (immersionVolumeDensity F x * immersionCoordinateDivergence F Y x)) ∧
    Integrable (fun x => immersionVolumeDensity F x * fderiv ℝ χ x (Y x)) ∧
      (∫ x : Chart4, χ x * (immersionVolumeDensity F x * immersionCoordinateDivergence F Y x)) +
        (∫ x : Chart4, immersionVolumeDensity F x * fderiv ℝ χ x (Y x))=0 := by
  have hv := (contDiffOn_immersionVolumeDensity F).mul (contDiffOn_immersionCoordinateDivergence F Y hY)
  have ha : Integrable (fun x => χ x * (immersionVolumeDensity F x * immersionCoordinateDivergence F Y x)) :=
    (contDiff_cutoff_smul F.domain F.isOpen_domain χ _ hχ hv hs).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_cutoff_smul χ _ hc)
  have hz := contDiff_coordinateCutoffVectorDensity F χ Y hχ hY hs
  have hzc := hasCompactSupport_coordinateCutoffVectorDensity F χ Y hc
  have hd : Integrable (coordinateDivergence (coordinateCutoffVectorDensity F χ Y)) :=
    (continuous_coordinateDivergence _ hz).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateDivergence _ hzc)
  have he := coordinateDivergence_cutoff_density F χ Y hχ hY hs
  have hb : Integrable (fun x => immersionVolumeDensity F x * fderiv ℝ χ x (Y x)) := by
    convert hd.sub ha using 1
    funext x
    change immersionVolumeDensity F x * fderiv ℝ χ x (Y x) =
      coordinateDivergence (coordinateCutoffVectorDensity F χ Y) x -
        χ x * (immersionVolumeDensity F x * immersionCoordinateDivergence F Y x)
    rw [he x]
    ring
  refine ⟨ha,hb,?_⟩
  rw [← integral_add ha hb]
  have hf : (fun x => χ x * (immersionVolumeDensity F x * immersionCoordinateDivergence F Y x) +
      immersionVolumeDensity F x * fderiv ℝ χ x (Y x)) =
      coordinateDivergence (coordinateCutoffVectorDensity F χ Y) := funext (fun x => (he x).symm)
  rw [hf]
  exact integral_coordinateDivergence_eq_zero _ hz hzc

end
end SecondPinching
