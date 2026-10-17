import SecondPinching.IntrinsicRemainder

set_option autoImplicit false
open scoped BigOperators Matrix
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- The averaged identity of prop:meanconvex, in any frame, from the explicit
conclusions of prop:reduction and lem:mean. These inputs have not here been
proved to arise from an immersion. No principal-frame field is chosen. -/
theorem intrinsicPinchingW_integral_identity {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (A : Ω → Matrix4) (τ : Ω → Cubic4) (V : Ω → Fourth4) (t : ℝ)
    (had : ∀ x, PaperAdmissible (A x) (τ x))
    (hV : ∀ x, TraceFreeFourth (V x))
    (hE : ∀ x, weightedTrace (A x) (V x) = hessianE (A x) (τ x) t)
    (hb : ∀ x, cubicContraction (τ x) (V x) = intrinsicHessianB0 (A x) (τ x))
    (hn : ∀ x, fourthNormSq (V x) = 3*t*(intrinsicCubicA (A x) (τ x)-2*intrinsicCubicB (A x) (τ x))+
      t*(35*t-28)/16-(3/2 : ℝ)*phiNormSq (A x))
    (hF : Integrable (fun x => intrinsicPinchingSquare (A x) (τ x) t (V x)) ν)
    (h4 : Integrable (fun x => intrinsicCorrectionL4 (A x) (τ x) t) ν)
    (h3 : Integrable (fun x => intrinsicCorrectionL3 (A x) (τ x) t) ν)
    (hJ : Integrable (fun x => intrinsicCorrectionJ (A x) (τ x) t) ν)
    (hz4 : ∫ x, intrinsicCorrectionL4 (A x) (τ x) t ∂ν = 0)
    (hz3 : ∫ x, intrinsicCorrectionL3 (A x) (τ x) t ∂ν = 0)
    (hzJ : ∫ x, intrinsicCorrectionJ (A x) (τ x) t ∂ν = 0) :
    Integrable (fun x => intrinsicPinchingW (A x) (τ x) t) ν ∧
    (∫ x, intrinsicPinchingW (A x) (τ x) t ∂ν) =
      (∫ x, intrinsicPinchingSquare (A x) (τ x) t (V x) ∂ν) ∧
    0 ≤ ∫ x, intrinsicPinchingW (A x) (τ x) t ∂ν := by
  have he : (fun x => intrinsicPinchingW (A x) (τ x) t) =
      fun x => intrinsicPinchingSquare (A x) (τ x) t (V x)-
        (89/8 : ℝ)*intrinsicCorrectionL4 (A x) (τ x) t+
        16*intrinsicCorrectionL3 (A x) (τ x) t+(13/4 : ℝ)*intrinsicCorrectionJ (A x) (τ x) t := by
    funext x
    exact intrinsicPinchingW_pointwise_remainder (A x) (τ x) (had x) t (V x)
      (hV x) (hE x) (hb x) (hn x)
  have hint : Integrable (fun x => intrinsicPinchingW (A x) (τ x) t) ν := by
    rw [he]
    exact ((hF.sub (h4.const_mul (89/8 : ℝ))).add (h3.const_mul (16 : ℝ))).add
      (hJ.const_mul (13/4 : ℝ))
  have havg : (∫ x, intrinsicPinchingW (A x) (τ x) t ∂ν) =
      ∫ x, intrinsicPinchingSquare (A x) (τ x) t (V x) ∂ν := by
    rw [he]
    exact integral_zero_corrections ν _ _ _ _ hF h4 h3 hJ hz4 hz3 hzJ
  exact ⟨hint,havg,by rw [havg]; exact integral_nonneg fun x =>
    intrinsicPinchingSquare_nonneg _ _ _ _⟩

/-- The same interpolation bound, for a single arbitrary admissible pair.
Diagonalization is used only at this point; no measurable choice is needed. -/
theorem intrinsicPinchingW_interpolation_of_endpoint (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (hhalf : intrinsicPinchingW A τ (1/2) ≤ -(1/10000 : ℝ))
    (t : ℝ) (ht : 0 ≤ t) (htop : t ≤ 1/2) : intrinsicPinchingW A τ t ≤ -t/5000 := by
  obtain ⟨O,μ,hO,hdiag,ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  rw [intrinsicPinchingW_in_principal_frame A τ had O hO μ hdiag] at hhalf ⊢
  exact pinchingW_interpolation_of_endpoint μ (frameCubic O τ) ha hhalf t ht htop

/-- Conditional scalar exclusion, including S=8, for arbitrary-frame fields. -/
theorem intrinsic_interval_exclusion_of_W_inputs {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A : Ω → Matrix4) (τ : Ω → Cubic4)
    (had : ∀ x, PaperAdmissible (A x) (τ x))
    (hhalf : ∀ x, intrinsicPinchingW (A x) (τ x) (1/2) ≤ -(1/10000 : ℝ))
    (S : ℝ) (hS : 4 < S)
    (hInt : Integrable (fun x => intrinsicPinchingW (A x) (τ x) (pinchingParameter S)) ν)
    (hmean : 0 ≤ ∫ x, intrinsicPinchingW (A x) (τ x) (pinchingParameter S) ∂ν) : 8 < S := by
  by_contra h8
  have htop := pinchingParameter_le_half hS (le_of_not_gt h8)
  have ht := pinchingParameter_pos hS
  have hbound : (∫ x, intrinsicPinchingW (A x) (τ x) (pinchingParameter S) ∂ν) ≤
      ∫ _ : Ω, -(pinchingParameter S)/5000 ∂ν :=
    integral_mono hInt (integrable_const _) (fun x =>
      intrinsicPinchingW_interpolation_of_endpoint (A x) (τ x) (had x) (hhalf x) _ ht.le htop)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hbound
  linarith

section FiniteInputs
variable
    (P : MvPolynomial (Fin 14) ℚ)
    (C : Fin 24 → ControlIndex → MvPolynomial (Fin 12) ℚ)
    (Q G : Fin 24 → ControlIndex → (b : Fin 8) →
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
      (Q leaf ij b) (G leaf ij b) = true)

include P C Q G sigma hP hexp hs hcoeff hblocks

/-- The endpoint premise is discharged by the five complete finite-check
families, without accepting any specific released array instance. -/
theorem intrinsic_interval_exclusion_of_finite_certificate
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : Ω → Matrix4) (τ : Ω → Cubic4)
    (had : ∀ x, PaperAdmissible (A x) (τ x)) (S : ℝ) (hS : 4 < S)
    (hInt : Integrable (fun x => intrinsicPinchingW (A x) (τ x) (pinchingParameter S)) ν)
    (hmean : 0 ≤ ∫ x, intrinsicPinchingW (A x) (τ x) (pinchingParameter S) ∂ν) : 8 < S := by
  exact intrinsic_interval_exclusion_of_W_inputs ν A τ had
    (fun x => intrinsic_endpoint_of_finite_certificate P C Q G sigma hP hexp hs hcoeff hblocks
      (A x) (τ x) (had x)) S hS hInt hmean

/-- The nonnegative average is now derived from the component Hessian
identities and three zero integrals. Those geometric identities and integrability
remain explicit premises. This theorem is not thm:main for an immersion. -/
theorem intrinsic_interval_exclusion_of_hessian_inputs
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : Ω → Matrix4) (τ : Ω → Cubic4) (V : Ω → Fourth4) (S : ℝ) (hS : 4 < S)
    (had : ∀ x, PaperAdmissible (A x) (τ x))
    (hV : ∀ x, TraceFreeFourth (V x))
    (hE : ∀ x, weightedTrace (A x) (V x) = hessianE (A x) (τ x) (pinchingParameter S))
    (hb : ∀ x, cubicContraction (τ x) (V x) = intrinsicHessianB0 (A x) (τ x))
    (hn : ∀ x, fourthNormSq (V x) =
      3*pinchingParameter S*(intrinsicCubicA (A x) (τ x)-2*intrinsicCubicB (A x) (τ x))+
      pinchingParameter S*(35*pinchingParameter S-28)/16-(3/2 : ℝ)*phiNormSq (A x))
    (hF : Integrable (fun x => intrinsicPinchingSquare (A x) (τ x) (pinchingParameter S) (V x)) ν)
    (h4 : Integrable (fun x => intrinsicCorrectionL4 (A x) (τ x) (pinchingParameter S)) ν)
    (h3 : Integrable (fun x => intrinsicCorrectionL3 (A x) (τ x) (pinchingParameter S)) ν)
    (hJ : Integrable (fun x => intrinsicCorrectionJ (A x) (τ x) (pinchingParameter S)) ν)
    (hz4 : ∫ x, intrinsicCorrectionL4 (A x) (τ x) (pinchingParameter S) ∂ν = 0)
    (hz3 : ∫ x, intrinsicCorrectionL3 (A x) (τ x) (pinchingParameter S) ∂ν = 0)
    (hzJ : ∫ x, intrinsicCorrectionJ (A x) (τ x) (pinchingParameter S) ∂ν = 0) : 8 < S := by
  obtain ⟨hi,_he,hm⟩ := intrinsicPinchingW_integral_identity ν A τ V (pinchingParameter S)
    had hV hE hb hn hF h4 h3 hJ hz4 hz3 hzJ
  exact intrinsic_interval_exclusion_of_finite_certificate P C Q G sigma hP hexp hs hcoeff hblocks
    ν A τ had S hS hi hm

end FiniteInputs
end
end SecondPinching
