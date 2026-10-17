import SecondPinching.CubicChart

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Equation `eq:normalizedchart`, and coverage of every unit cubic over a
fixed chart spectrum. This does not assume or prove coverage of arbitrary
symmetric matrices by changes of orthonormal frame. -/

/-- The matrix A(r,y) in the paper. -/
def normalizedChartMatrix (r y : ℝ) : Matrix4 :=
  Matrix.diagonal (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))

/-- The cubic τ(r,y,x) in the paper, with its actual positive normalising factor. -/
def normalizedChartCubic (r y : ℝ) (x : Fin 12 → ℝ) : Cubic4 :=
  fun i j k => chartCubic r y x i j k / Real.sqrt (chartNormSq r y x)

theorem matrixNormSq_diagonal (μ : Fin 4 → ℝ) :
    matrixNormSq (Matrix.diagonal μ) = ∑ i, (μ i)^2 := by
  simp [matrixNormSq, Matrix.diagonal_apply]

theorem normalizedChartMatrix_symmetric (r y : ℝ) :
    (normalizedChartMatrix r y).IsSymm := by
  exact Matrix.isSymm_diagonal _

theorem normalizedChartMatrix_trace (r y : ℝ) :
    Matrix.trace (normalizedChartMatrix r y) = 0 := by
  simp only [normalizedChartMatrix, Matrix.trace_diagonal]
  rw [← Finset.sum_div,spectralVector_trace,zero_div]

theorem normalizedChartMatrix_normSq (r y : ℝ) :
    matrixNormSq (normalizedChartMatrix r y) = 1 := by
  simp only [normalizedChartMatrix, matrixNormSq_diagonal,div_pow]
  rw [← Finset.sum_div,spectralVector_normSq,Real.sq_sqrt (spectralScale_pos r y).le]
  exact div_self (ne_of_gt (spectralScale_pos r y))

theorem chartCubic_zero (r y : ℝ) : chartCubic r y 0 = 0 := by
  funext i j k
  simp [chartCubic,repeatedCoordinates,Matrix.mulVec,dotProduct]

theorem normalizedChartCubic_symmetric (r y : ℝ) (x : Fin 12 → ℝ) :
    CubicSymmetric (normalizedChartCubic r y x) := by
  intro σ v
  unfold normalizedChartCubic
  rw [chartCubic_symmetric r y x σ v]

theorem normalizedChartCubic_normSq {r y : ℝ} (hr : 0 ≤ r)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    cubicNormSq (normalizedChartCubic r y x) = 1 := by
  have hn := chartNormSq_pos (y := y) hr x hx
  simp only [cubicNormSq,normalizedChartCubic,div_pow]
  simp_rw [← Finset.sum_div]
  change chartNormSq r y x / (Real.sqrt (chartNormSq r y x))^2 = 1
  rw [Real.sq_sqrt hn.le,div_self (ne_of_gt hn)]

theorem normalizedChartCubic_trace (r y : ℝ) (x : Fin 12 → ℝ) (k : Fin 4) :
    ∑ i, normalizedChartCubic r y x i i k = 0 := by
  simp only [normalizedChartCubic]
  rw [← Finset.sum_div,((chartCubic_constrained r y x).2 k).1,zero_div]

/-- The diagonal A-trace is exactly the ell-trace divided by sqrt(L). -/
theorem normalizedChartMatrix_weightedTrace (r y : ℝ) (τ : Cubic4) (k : Fin 4) :
    (∑ i, ∑ j, normalizedChartMatrix r y i j * τ i j k) =
      (∑ i, spectralVector r y i * τ i i k) / Real.sqrt (spectralScale r y) := by
  simp only [normalizedChartMatrix,Matrix.diagonal_apply]
  simp
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem normalizedChartCubic_weightedTrace (r y : ℝ) (x : Fin 12 → ℝ) (k : Fin 4) :
    ∑ i, ∑ j, normalizedChartMatrix r y i j * normalizedChartCubic r y x i j k = 0 := by
  rw [normalizedChartMatrix_weightedTrace]
  simp only [normalizedChartCubic,← mul_div_assoc]
  rw [← Finset.sum_div,((chartCubic_constrained r y x).2 k).2]
  simp

/-- The normalized formulas really satisfy every condition of Definition 2.2. -/
theorem normalizedChart_admissible (r y : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (_hy : y ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    Admissible (normalizedChartMatrix r y) (normalizedChartCubic r y x) := by
  exact ⟨normalizedChartMatrix_symmetric r y, normalizedChartCubic_symmetric r y x,
    normalizedChartMatrix_trace r y, normalizedChartMatrix_normSq r y,
    normalizedChartCubic_normSq hr.1 x hx,normalizedChartCubic_trace r y x,
    normalizedChartCubic_weightedTrace r y x⟩

/-- The same conclusion in the literal norm convention of the paper. -/
theorem normalizedChart_paperAdmissible (r y : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    PaperAdmissible (normalizedChartMatrix r y) (normalizedChartCubic r y x) :=
  (admissible_iff_paper _ _).mp (normalizedChart_admissible r y hr hy x hx)

/-- Unit cubics with this normalized spectrum satisfy the unnormalized fibre traces. -/
theorem admissible_chart_constrained (r y : ℝ) (τ : Cubic4)
    (hτ : Admissible (normalizedChartMatrix r y) τ) : ChartConstrained r y τ := by
  refine ⟨hτ.2.1,?_⟩
  intro k
  refine ⟨hτ.2.2.2.2.2.1 k,?_⟩
  have hw := hτ.2.2.2.2.2.2 k
  rw [normalizedChartMatrix_weightedTrace] at hw
  have hn : Real.sqrt (spectralScale r y) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (spectralScale_pos r y))
  exact (div_eq_zero_iff.mp hw).resolve_right hn

/-- Exact coverage of all admissible cubics over each chart spectrum.
The normalized parametrisation is surjective, not injective: scaling x
by a positive scalar leaves the normalized tensor unchanged. -/
theorem paperAdmissible_chart_iff (r y : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) (τ : Cubic4) :
    PaperAdmissible (normalizedChartMatrix r y) τ ↔
      ∃ x : Fin 12 → ℝ, x ≠ 0 ∧ normalizedChartCubic r y x = τ := by
  constructor
  · intro hp
    have ha := (admissible_iff_paper _ _).mpr hp
    have hn : cubicNormSq τ = 1 := ha.2.2.2.2.1
    have hc := chartCubic_reconstruct hr.1 τ (admissible_chart_constrained r y τ ha)
    have hx : cubicCoordinates r τ ≠ 0 := by
      intro hz
      rw [hz,chartCubic_zero] at hc
      have hn' := hn
      rw [← hc] at hn'
      norm_num [cubicNormSq] at hn'
    refine ⟨cubicCoordinates r τ,hx,?_⟩
    funext i j k
    simp [normalizedChartCubic,chartNormSq,hc,hn]
  · rintro ⟨x,hx,hτ⟩
    rw [← hτ]
    exact normalizedChart_paperAdmissible r y hr hy x hx

end
end SecondPinching
