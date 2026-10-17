import SecondPinching.CoordinateDivergence
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped BigOperators Topology ContDiff
namespace SecondPinching
noncomputable section

theorem coordinateDivergence_eq_zero_off_tsupport (Y : Chart4 → Vector4)
    (x : Chart4) (hx : x ∉ tsupport Y) : coordinateDivergence Y x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hn : x ∉ tsupport (fun y => Y y i) := by
    exact fun h => hx ((tsupport_comp_subset (g := fun v : Vector4 => v i) rfl Y) h)
  rw [fderiv_of_notMem_tsupport ℝ hn]
  rfl

theorem continuous_coordinateDivergence (Y : Chart4 → Vector4)
    (hY : ContDiff ℝ ∞ Y) : Continuous (coordinateDivergence Y) := by
  unfold coordinateDivergence
  apply continuous_finsetSum
  intro i _
  exact ((contDiff_pi.mp hY i).continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_coordinateDivergence (Y : Chart4 → Vector4)
    (hc : HasCompactSupport Y) : HasCompactSupport (coordinateDivergence Y) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  exact hx (coordinateDivergence_eq_zero_off_tsupport Y x hn)

/-- Compact support permits a box strictly outside the support. Its flux
vanishes on every face, and the Euclidean divergence theorem gives zero. -/
theorem integral_coordinateDivergence_eq_zero (Y : Chart4 → Vector4)
    (hY : ContDiff ℝ ∞ Y) (hc : HasCompactSupport Y) :
    (∫ x : Chart4, coordinateDivergence Y x) = 0 := by
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_ball (0 : Chart4)).mp hc.isCompact.isBounded
  let R : ℝ := |r|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hb (x : Chart4) (hx : x ∈ tsupport Y) : ‖x‖ < R := by
    have hn : ‖x‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hr hx
    exact hn.trans (by dsimp [R]; linarith [le_abs_self r])
  have hz (x : Chart4) (i : Fin 4) (hi : R ≤ |x i|) : Y x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hn : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact (not_lt_of_ge (hi.trans hn)) (hb x hx)
  have hbox : tsupport Y ⊆ Icc (fun _ : Fin 4 => -R) (fun _ => R) := by
    intro x hx
    constructor <;> intro i
    · have hn : |x i| < R := lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i) (hb x hx)
      exact (abs_lt.mp hn).1.le
    · have hn : |x i| < R := lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i) (hb x hx)
      exact (abs_lt.mp hn).2.le
  have hi : Integrable (coordinateDivergence Y) := (continuous_coordinateDivergence Y hY).integrable_of_hasCompactSupport
    (hasCompactSupport_coordinateDivergence Y hc)
  have he := integral_divergence_of_hasFDerivAt_off_countable'
    (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R) (fun _ => by linarith)
    (fun i x => Y x i) (fun i => fderiv ℝ (fun x => Y x i)) ∅ countable_empty
    (fun i => (contDiff_pi.mp hY i).continuous.continuousOn)
    (fun x _ i => ((contDiff_pi.mp hY i).differentiable (by simp) x).hasFDerivAt)
    hi.integrableOn
  change (∫ x in Icc (fun _ : Fin 4 => -R) (fun _ => R), coordinateDivergence Y x) = _ at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => coordinateDivergence_eq_zero_off_tsupport Y x (fun hy => hx (hbox hy)))] at he
  rw [he]
  apply Finset.sum_eq_zero
  intro i _
  have hp (z : Fin 3 → ℝ) : Y (i.insertNth R z) = 0 := by
    apply hz _ i
    simp only [Fin.insertNth_apply_same,abs_of_pos hR,le_refl]
  have hm (z : Fin 3 → ℝ) : Y (i.insertNth (-R) z) = 0 := by
    apply hz _ i
    simp only [Fin.insertNth_apply_same,abs_neg,abs_of_pos hR,le_refl]
  simp only [hp,hm,Pi.zero_apply,integral_zero,sub_self]

end
end SecondPinching
