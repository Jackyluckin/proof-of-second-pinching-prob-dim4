import SecondPinching.SpectralChart
import SecondPinching.CubicSymmetry

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The twelve-coordinate parametrisation in Appendix A.
Lean indices start at zero; amplitudes 0,1,2,3 are respectively T₂₃₄,
T₁₃₄,T₁₂₄,T₁₂₃, and amplitudes 4+2k,5+2k belong to the k-th fibre. -/

/-- The two amplitudes in equation (A.3), with zero-based indices. -/
def repeatedCoordinates (x : Fin 12 → ℝ) (k : Fin 4) : Fin 2 → ℝ :=
  ![x ⟨4+2*k.val, by omega⟩,x ⟨5+2*k.val, by omega⟩]

/-- The actual cubic T(r,y,x) of Appendix A, extended by full symmetry.
For three distinct indices, 6-i-j-k is the missing index in {0,1,2,3}. -/
def chartCubic (r y : ℝ) (x : Fin 12 → ℝ) : Cubic4 := fun i j k =>
  if i = j then (cubicBasis r y *ᵥ repeatedCoordinates x k) i
  else if i = k then (cubicBasis r y *ᵥ repeatedCoordinates x j) i
  else if j = k then (cubicBasis r y *ᵥ repeatedCoordinates x i) j
  else x (Fin.ofNat 12 (6-(i.val+j.val+k.val)))

/-- Both adjacent swaps hold, hence full tensor symmetry holds. -/
theorem chartCubic_symmetric (r y : ℝ) (x : Fin 12 → ℝ) :
    CubicSymmetric (chartCubic r y x) := by
  apply (cubicSymmetric_iff_swaps _).mpr
  constructor <;> intro i j k <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [chartCubic]

/-- The repeated components are exactly the prescribed four C-matrix fibres. -/
theorem chartCubic_repeated (r y : ℝ) (x : Fin 12 → ℝ) (i k : Fin 4) :
    chartCubic r y x i i k = (cubicBasis r y *ᵥ repeatedCoordinates x k) i := by
  simp [chartCubic]

/-- The four all-distinct components, in precisely the paper's order. -/
theorem chartCubic_distinct (r y : ℝ) (x : Fin 12 → ℝ) :
    chartCubic r y x 1 2 3 = x 0 ∧ chartCubic r y x 0 2 3 = x 1 ∧
    chartCubic r y x 0 1 3 = x 2 ∧ chartCubic r y x 0 1 2 = x 3 := by
  norm_num [chartCubic]
  rfl

/-- The unnormalised constrained cubic space; no unit norm is imposed here. -/
def ChartConstrained (r y : ℝ) (τ : Cubic4) : Prop :=
  CubicSymmetric τ ∧ ∀ k, CubicFibre r y (fun i => τ i i k)

theorem chartCubic_constrained (r y : ℝ) (x : Fin 12 → ℝ) :
    ChartConstrained r y (chartCubic r y x) := by
  refine ⟨chartCubic_symmetric r y x, ?_⟩
  intro k
  simpa only [chartCubic_repeated] using cubicBasis_fibre r y (repeatedCoordinates x k)

/-- The explicit inverse coordinates. In each fibre we read rows 2 and 3. -/
def cubicCoordinates (r : ℝ) (τ : Cubic4) : Fin 12 → ℝ :=
  ![τ 1 2 3, τ 0 2 3, τ 0 1 3, τ 0 1 2,
    τ 1 1 0/(1+r), τ 2 2 0/(1+r),
    τ 1 1 1/(1+r), τ 2 2 1/(1+r),
    τ 1 1 2/(1+r), τ 2 2 2/(1+r),
    τ 1 1 3/(1+r), τ 2 2 3/(1+r)]

theorem repeatedCoordinates_inverse (r : ℝ) (τ : Cubic4) (k : Fin 4) :
    repeatedCoordinates (cubicCoordinates r τ) k = ![τ 1 1 k/(1+r),τ 2 2 k/(1+r)] := by
  fin_cases k <;> rfl

/-- Every constrained symmetric cubic is reconstructed from these 12 coordinates. -/
theorem chartCubic_reconstruct {r y : ℝ} (hr : 0 ≤ r)
    (τ : Cubic4) (hτ : ChartConstrained r y τ) :
    chartCubic r y (cubicCoordinates r τ) = τ := by
  apply cubic_ext (chartCubic_symmetric _ _ _) hτ.1
  · intro i k
    rw [chartCubic_repeated,repeatedCoordinates_inverse]
    exact congrFun (cubicBasis_reconstruct hr _ (hτ.2 k)) i
  all_goals simp [chartCubic, cubicCoordinates]
  rfl

/-- Conversely, recovering the coordinates of a chart tensor returns the input. -/
theorem cubicCoordinates_chart {r y : ℝ} (hr : 0 ≤ r) (x : Fin 12 → ℝ) :
    cubicCoordinates r (chartCubic r y x) = x := by
  have hn : 1+r ≠ 0 := ne_of_gt (by linarith)
  funext i
  fin_cases i <;>
    simp [cubicCoordinates, chartCubic, repeatedCoordinates, cubicBasis,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,hn]
  rfl

/-- The full parametrisation claim in Appendix A. The quantifier over τ
ranges over every real cubic tensor, including spectra on the boundary. -/
theorem chartConstrained_iff_existsUnique (r y : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (_hy : y ∈ Set.Icc (0 : ℝ) 1) (τ : Cubic4) :
    ChartConstrained r y τ ↔ ∃! x : Fin 12 → ℝ, chartCubic r y x = τ := by
  constructor
  · intro hτ
    refine ⟨cubicCoordinates r τ,chartCubic_reconstruct hr.1 τ hτ,?_⟩
    intro x hx
    rw [← hx,cubicCoordinates_chart hr.1]
  · rintro ⟨x,hx,_⟩
    rw [← hx]
    exact chartCubic_constrained r y x

/-- N(r,y,x) of the paper is the specified ordered-index squared norm. -/
def chartNormSq (r y : ℝ) (x : Fin 12 → ℝ) : ℝ := cubicNormSq (chartCubic r y x)

/-- Positivity of N for every nonzero amplitude vector, without deleting boundaries. -/
theorem chartNormSq_pos {r y : ℝ} (hr : 0 ≤ r)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) : 0 < chartNormSq r y x := by
  apply cubicNormSq_pos
  intro hzero
  apply hx
  have h := cubicCoordinates_chart (y := y) hr x
  rw [hzero] at h
  have hz : cubicCoordinates r (0 : Cubic4) = 0 := by
    funext i
    fin_cases i <;> simp [cubicCoordinates]
  simpa only [hz] using h.symm

end
end SecondPinching
