import SecondPinching.Admissible

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The explicit spectral and repeated-index charts of Appendix A.
This file does not yet prove reduction of an arbitrary spectrum by the
signed-permutation group. Every chart assertion retains its stated domain. -/

/-- Equation (A.1), before normalising the eigenvalues. -/
def spectralVector (r y : ℝ) : Fin 4 → ℝ :=
  ![1+r+r*y, 1-r-r*y, -1+r-r*y, -1-r+r*y]

/-- The positive squared norm L in equation (A.1). -/
def spectralScale (r y : ℝ) : ℝ := 4*(1+r^2+r^2*y^2)

theorem spectralVector_trace (r y : ℝ) : ∑ i, spectralVector r y i = 0 := by
  simp [spectralVector, Fin.sum_univ_succ]
  ring

theorem spectralVector_normSq (r y : ℝ) :
    ∑ i, (spectralVector r y i)^2 = spectralScale r y := by
  simp [spectralVector, spectralScale, Fin.sum_univ_succ]
  ring

theorem spectralScale_pos (r y : ℝ) : 0 < spectralScale r y := by
  unfold spectralScale
  positivity

/-- Matrix C(r,y) of equation (A.2); both columns are retained. -/
def cubicBasis (r y : ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![-1+r*y, -r+r*y; 1+r, 0; 0, 1+r; -r-r*y, -1-r*y]

/-- One repeated-index fibre, with its two actual trace constraints. -/
def CubicFibre (r y : ℝ) (z : Fin 4 → ℝ) : Prop :=
  (∑ i, z i = 0) ∧ ∑ i, spectralVector r y i * z i = 0

theorem cubicBasis_fibre (r y : ℝ) (v : Fin 2 → ℝ) :
    CubicFibre r y (cubicBasis r y *ᵥ v) := by
  constructor <;> simp [cubicBasis, spectralVector, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ] <;> ring

theorem cubicBasis_injective {r y : ℝ} (hr : 0 ≤ r) :
    Function.Injective (fun v : Fin 2 → ℝ => cubicBasis r y *ᵥ v) := by
  intro v w h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [cubicBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h1 h2
  have hn : 1+r ≠ 0 := ne_of_gt (by linarith)
  funext i
  fin_cases i
  · exact h1.resolve_right hn
  · exact h2.resolve_right hn

/-- The explicit inverse uses rows 2 and 3, whose entries are 1+r. -/
theorem cubicBasis_reconstruct {r y : ℝ} (hr : 0 ≤ r)
    (z : Fin 4 → ℝ) (hz : CubicFibre r y z) :
    cubicBasis r y *ᵥ ![z 1/(1+r), z 2/(1+r)] = z := by
  obtain ⟨ht,hw⟩ := hz
  simp [spectralVector, Fin.sum_univ_succ] at ht hw
  have hn : 1+r ≠ 0 := ne_of_gt (by linarith)
  funext i
  fin_cases i <;> simp [cubicBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · field_simp
    linear_combination (-1/2 : ℝ)*hw + ((-1-r+r*y)/2)*ht
  · field_simp
  · field_simp
  · field_simp
    linear_combination (1/2 : ℝ)*hw - ((1+r+r*y)/2)*ht

/-- Appendix A's basis claim, including the entire closed parameter square.
Existence and uniqueness are both proved; neither is assumed. -/
theorem cubicFibre_iff_existsUnique (r y : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (_hy : y ∈ Set.Icc (0 : ℝ) 1)
    (z : Fin 4 → ℝ) :
    CubicFibre r y z ↔ ∃! v : Fin 2 → ℝ, cubicBasis r y *ᵥ v = z := by
  constructor
  · intro hz
    refine ⟨![z 1/(1+r),z 2/(1+r)], cubicBasis_reconstruct hr.1 z hz, ?_⟩
    intro v hv
    exact cubicBasis_injective hr.1 (hv.trans (cubicBasis_reconstruct hr.1 z hz).symm)
  · rintro ⟨v,hv,_⟩
    rw [← hv]
    exact cubicBasis_fibre r y v

end
end SecondPinching
