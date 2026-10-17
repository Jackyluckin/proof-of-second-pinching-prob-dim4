import SecondPinching.EndpointSymmetry
import SecondPinching.CertificatePolynomialChecks
import SecondPinching.WConvexity

set_option autoImplicit false
open scoped BigOperators Matrix
open MeasureTheory
namespace SecondPinching
noncomputable section

/-! The finite certificate implication for every diagonal admissible pair.
The stored release arrays have not been supplied as instances of the finite
checks. General orthogonal frame changes and geometric realization of the
integral inputs are not premises hidden by these statements. -/

/-- Full twelve-coordinate coverage for every diagonal admissible pair,
up to the explicitly specified signed permutation. -/
theorem paperAdmissible_diagonal_chart (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) :
    ∃ (s : ℝ) (e : Equiv.Perm (Fin 4)) (r y : ℝ) (x : Fin 12 → ℝ),
      (s = 1 ∨ s = -1) ∧ r ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1 ∧ x ≠ 0 ∧
      signedSpectrum s e μ =
        (fun i => spectralVector r y i / Real.sqrt (spectralScale r y)) ∧
      permuteCubic e τ = normalizedChartCubic r y x := by
  obtain ⟨_,ht,hn,_,_,_⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  obtain ⟨s,e,r,y,hs,hr,hy,he⟩ := tracefree_unit_spectrum_chart μ ht hn
  have hs2 : s^2 = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have ha := paperAdmissible_signed_permutation s hs2 e μ τ had
  rw [he] at ha
  obtain ⟨x,hx,hτ⟩ := (paperAdmissible_chart_iff r y hr hy (permuteCubic e τ)).mp ha
  exact ⟨s,e,r,y,x,hs,hr,hy,hx,he,hτ.symm⟩

/-- A chart endpoint bound suffices for every diagonal admissible pair.
This intermediate transport statement makes its functional premise explicit. -/
theorem diagonal_endpoint_of_chart_bound
    (hchart : ∀ (r y : ℝ), r ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (τ : Cubic4), PaperAdmissible (normalizedChartMatrix r y) τ →
        pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))
          τ (1/2) ≤ -(1/10000 : ℝ))
    (μ : Vector4) (τ : Cubic4) (had : PaperAdmissible (Matrix.diagonal μ) τ) :
    pinchingW μ τ (1/2) ≤ -(1/10000 : ℝ) := by
  obtain ⟨_,ht,hn,_,_,_⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  obtain ⟨s,e,r,y,hs,hr,hy,he⟩ := tracefree_unit_spectrum_chart μ ht hn
  have hs2 : s^2 = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have ha := paperAdmissible_signed_permutation s hs2 e μ τ had
  have hw := pinchingW_half_signed_permutation s hs2 e μ τ ht hn
  rw [he] at ha hw
  rw [← hw]
  exact hchart r y hr hy (permuteCubic e τ) ha

section FiniteInputs
variable
    (P : MvPolynomial (Fin 14) ℚ)
    (C : Fin 24 → ControlIndex → MvPolynomial (Fin 12) ℚ)
    (Q V : Fin 24 → ControlIndex → (b : Fin 8) →
      Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) ℤ)
    (sigma : Fin 24 → ControlIndex → ℤ)
    (hP : exactCoefficientCheck 14 P endpointPolynomial = true)
    (hexp : ∀ leaf, exactCoefficientCheck 14 P
      (certificateExpansionPolynomial leaf (C leaf)) = true)
    (hs : ∀ leaf ij, 0 < sigma leaf ij)
    (hcoeff : ∀ leaf ij, exactCoefficientCheck 12 (C leaf ij)
      (integerBlockQuartic (Q leaf ij)
        ((compressedGramConstant : ℚ)*(sigma leaf ij : ℚ))) = true)
    (hblocks : ∀ leaf ij b, integerCertificateCheck (certificateBlockSize b)
      (Q leaf ij b) (V leaf ij b) = true)

include P C Q V sigma hP hexp hs hcoeff hblocks

/-- The paper's endpoint constant for arbitrary diagonal admissible pairs,
conditional only on the complete finite coefficient and integer block checks.
No infinite polynomial identity or chart bound is an additional premise. -/
theorem diagonal_endpoint_of_finite_certificate
    (μ : Vector4) (τ : Cubic4) (had : PaperAdmissible (Matrix.diagonal μ) τ) :
    pinchingW μ τ (1/2) ≤ -(1/10000 : ℝ) := by
  apply diagonal_endpoint_of_chart_bound _ μ τ had
  intro r y hr hy tau ha
  simpa only [neg_div] using admissible_chart_endpoint_of_finite_certificate P C Q V sigma
    hP hexp hs hcoeff hblocks r y hr hy tau ha

/-- The interval exclusion after replacing the endpoint premise by the finite
checks. The probability measure, admissible scalar fields, integrability and
nonnegative integral are still explicit geometric inputs, not derived here. -/
theorem pinching_interval_exclusion_of_finite_certificate
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Ω → Vector4) (τ : Ω → Cubic4)
    (had : ∀ x, PaperAdmissible (Matrix.diagonal (μ x)) (τ x))
    (S : ℝ) (hS : 4 < S)
    (hInt : Integrable (fun x => pinchingW (μ x) (τ x) (pinchingParameter S)) ν)
    (hmean : 0 ≤ ∫ x, pinchingW (μ x) (τ x) (pinchingParameter S) ∂ν) : 8 < S := by
  exact pinching_interval_exclusion_of_W_inputs ν μ τ had
    (fun x => diagonal_endpoint_of_finite_certificate P C Q V sigma
      hP hexp hs hcoeff hblocks (μ x) (τ x) (had x)) S hS hInt hmean

end FiniteInputs
end
end SecondPinching
