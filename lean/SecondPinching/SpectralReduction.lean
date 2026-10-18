import SecondPinching.NormalizedChart
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The spectral part of Appendix A. Sorting four eigenvalues and, if needed,
negating them in reverse order gives the same closed chamber as the signed
three-coordinate argument in the paper. Repeated and zero entries are allowed.
No diagonalization of a general matrix is asserted in this module. -/

/-- Reindexing the four eigenvalues, with a common real factor. -/
def signedSpectrum (s : ℝ) (e : Equiv.Perm (Fin 4)) (μ : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => s * μ (e i)

theorem signedSpectrum_trace (s : ℝ) (e : Equiv.Perm (Fin 4)) (μ : Fin 4 → ℝ) :
    (∑ i, signedSpectrum s e μ i) = s * ∑ i, μ i := by
  simp only [signedSpectrum, ← Finset.mul_sum, Equiv.sum_comp]

theorem signedSpectrum_normSq (s : ℝ) (e : Equiv.Perm (Fin 4)) (μ : Fin 4 → ℝ) :
    (∑ i, signedSpectrum s e μ i ^ 2) = s^2 * ∑ i, μ i^2 := by
  simp only [signedSpectrum, mul_pow, ← Finset.mul_sum]
  rw [Equiv.sum_comp e (fun i => μ i^2)]

/-- Every spectrum has a signed permutation in the chamber used below.
This order statement does not require either spectral normalization. -/
theorem spectral_chamber_representative (μ : Fin 4 → ℝ) :
    ∃ (s : ℝ) (e : Equiv.Perm (Fin 4)), (s = 1 ∨ s = -1) ∧
      let ν := signedSpectrum s e μ
      ν 1 ≤ ν 0 ∧ ν 2 ≤ ν 1 ∧ ν 3 ≤ ν 2 ∧ 0 ≤ ν 0 + ν 3 := by
  let e := Tuple.sort (fun i => -μ i)
  have ho (i j : Fin 4) (hij : i ≤ j) : μ (e j) ≤ μ (e i) := by
    have h := Tuple.monotone_sort (fun i => -μ i) hij
    simpa [Function.comp_def, e] using h
  by_cases h : 0 ≤ μ (e 0) + μ (e 3)
  · refine ⟨1, e, Or.inl rfl, ?_⟩
    simpa [signedSpectrum] using
      And.intro (ho 0 1 (by decide))
        ⟨ho 1 2 (by decide), ho 2 3 (by decide), h⟩
  · refine ⟨-1, Fin.revPerm.trans e, Or.inr rfl, ?_⟩
    have h01 := ho 0 1 (by decide)
    have h12 := ho 1 2 (by decide)
    have h23 := ho 2 3 (by decide)
    simp only [signedSpectrum, Equiv.trans_apply, Fin.revPerm_apply,
      show (0 : Fin 4).rev = 3 from rfl, show (1 : Fin 4).rev = 2 from rfl,
      show (2 : Fin 4).rev = 1 from rfl, show (3 : Fin 4).rev = 0 from rfl]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith

/-- The ordered chamber is parametrized by the closed square. The b=0
branch explicitly chooses r=y=0; no division by a vanishing coordinate occurs. -/
theorem ordered_spectrum_chart (μ : Fin 4 → ℝ)
    (ht : ∑ i, μ i = 0) (hn : ∑ i, μ i^2 = 1)
    (h01 : μ 1 ≤ μ 0) (h12 : μ 2 ≤ μ 1) (h23 : μ 3 ≤ μ 2)
    (hc : 0 ≤ μ 0 + μ 3) :
    ∃ r y : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1 ∧
      μ = fun i => spectralVector r y i / Real.sqrt (spectralScale r y) := by
  have ht' := ht
  have hn' := hn
  simp [Fin.sum_univ_succ] at ht' hn'
  let a := μ 0 + μ 1
  let b := μ 0 + μ 2
  let c := μ 0 + μ 3
  have hba : b ≤ a := by dsimp [a, b]; linarith
  have hcb : c ≤ b := by dsimp [b, c]; linarith
  have hc0 : 0 ≤ c := hc
  have hb0 : 0 ≤ b := le_trans hc0 hcb
  have ha : 0 < a := by
    by_contra h
    have ha0 : a ≤ 0 := le_of_not_gt h
    have hz0 : μ 0 = 0 := by dsimp [a, b, c] at *; linarith
    have hz1 : μ 1 = 0 := by dsimp [a, b, c] at *; linarith
    have hz2 : μ 2 = 0 := by dsimp [a, b, c] at *; linarith
    have hz3 : μ 3 = 0 := by dsimp [a, b, c] at *; linarith
    simp [hz0, hz1, hz2, hz3] at hn'
  have ha0 : a ≠ 0 := ne_of_gt ha
  let r := b / a
  let y := if b = 0 then 0 else c / b
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hb0 ha.le, (div_le_one ha).mpr hba⟩
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [y]
    split_ifs with hb
    · norm_num
    · exact ⟨div_nonneg hc0 hb0, (div_le_one (lt_of_le_of_ne hb0 (Ne.symm hb))).mpr hcb⟩
  have har : a*r = b := by dsimp [r]; field_simp
  have hry : r*y = c/a := by
    dsimp [r, y]
    split_ifs with hb
    · have hc' : c = 0 := by linarith
      simp [hb, hc']
    · field_simp
  have hary : a*(r*y) = c := by rw [hry]; field_simp
  have he (i : Fin 4) : a * spectralVector r y i = 2 * μ i := by
    fin_cases i <;> simp only [spectralVector]
    all_goals dsimp [a, b, c] at har hary ⊢; linarith [ht']
  have hnorm : a^2 * spectralScale r y = 4 := by
    rw [← spectralVector_normSq]
    calc
      a^2 * (∑ i, spectralVector r y i ^ 2) =
          ∑ i, (a*spectralVector r y i)^2 := by simp [mul_pow, Finset.mul_sum]
      _ = ∑ i, (2*μ i)^2 := by simp only [he]
      _ = 4 := by simp only [mul_pow, ← Finset.mul_sum, hn]; norm_num
  have hs : 0 < Real.sqrt (spectralScale r y) := Real.sqrt_pos.mpr (spectralScale_pos r y)
  have hsq := Real.sq_sqrt (spectralScale_pos r y).le
  have has : a * Real.sqrt (spectralScale r y) = 2 := by
    have h : (a * Real.sqrt (spectralScale r y))^2 = 4 := by
      rw [mul_pow, hsq, hnorm]
    nlinarith [mul_pos ha hs]
  refine ⟨r, y, hr, hy, ?_⟩
  funext i
  apply (eq_div_iff (ne_of_gt hs)).mpr
  apply (mul_left_cancel₀ ha0)
  calc
    a * (μ i * Real.sqrt (spectralScale r y)) =
        (a * Real.sqrt (spectralScale r y)) * μ i := by ring
    _ = 2 * μ i := by rw [has]
    _ = a * spectralVector r y i := (he i).symm

/-- Coverage of every trace-free unit spectrum by eq:spectralchart, up to
a coordinate permutation and a global sign. All closed boundaries are included. -/
theorem tracefree_unit_spectrum_chart (μ : Fin 4 → ℝ)
    (ht : ∑ i, μ i = 0) (hn : ∑ i, μ i^2 = 1) :
    ∃ (s : ℝ) (e : Equiv.Perm (Fin 4)) (r y : ℝ),
      (s = 1 ∨ s = -1) ∧ r ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1 ∧
      signedSpectrum s e μ =
        fun i => spectralVector r y i / Real.sqrt (spectralScale r y) := by
  obtain ⟨s,e,hs,h01,h12,h23,hc⟩ := spectral_chamber_representative μ
  have hs2 : s^2 = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have ht' : ∑ i, signedSpectrum s e μ i = 0 := by rw [signedSpectrum_trace,ht,mul_zero]
  have hn' : ∑ i, signedSpectrum s e μ i^2 = 1 := by rw [signedSpectrum_normSq,hs2,hn,mul_one]
  obtain ⟨r,y,hr,hy,h⟩ := ordered_spectrum_chart (signedSpectrum s e μ) ht' hn' h01 h12 h23 hc
  exact ⟨s,e,r,y,hs,hr,hy,h⟩

end
end SecondPinching
