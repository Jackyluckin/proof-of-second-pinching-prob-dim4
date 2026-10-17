import SecondPinching.LocalDivergenceIntegration

set_option autoImplicit false
open scoped Topology ContDiff
namespace SecondPinching
noncomputable section

/-- A smooth cutoff supported in an open set makes a locally smooth field
globally smooth. Outside the cutoff support the product is locally zero. -/
theorem contDiff_cutoff_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set Chart4) (hU : IsOpen U) (χ : Chart4 → ℝ) (v : Chart4 → E)
    (hχ : ContDiff ℝ ∞ χ) (hv : ContDiffOn ℝ ∞ v U) (hs : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun x => χ x • v x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul ((hv x (hs hx)).contDiffAt (hU.mem_nhds (hs hx)))
  · have he : (fun x => χ x • v x) =ᶠ[𝓝 x] fun _ => (0 : E) :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).mono
        (fun y hy => by simp only [hy,Pi.zero_apply,zero_smul])
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem hasCompactSupport_cutoff_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : Chart4 → ℝ) (v : Chart4 → E) (hc : HasCompactSupport χ) :
    HasCompactSupport (fun x => χ x • v x) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  exact hx (by
    change χ x • v x=0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul])

end
end SecondPinching
