import SecondPinching.LocalIntegrands
import SecondPinching.IntrinsicIntegral

set_option autoImplicit false
open scoped Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory
namespace SecondPinching
noncomputable section

theorem pinchingScalars_square_nonneg {Ω ι : Type*} (F : PinchingScalarFields Ω)
    (U : ι → Set Ω) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4) (t : ℝ)
    (hr : pinchingScalarsRepresent F U A τ V t) : ∀ x, 0 ≤ F.square x := by
  intro x
  obtain ⟨i,hi⟩ := hcover x
  rw [(hr i x hi).2.2.2.2]
  exact intrinsicPinchingSquare_nonneg _ _ _ _

/-- The exact pointwise identity descends from the local reduced-Hessian
equations. The three correction fields remain present pointwise. -/
theorem pinchingScalars_remainder_of_local_hessian {Ω ι : Type*}
    (F : PinchingScalarFields Ω) (U : ι → Set Ω) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4) (t : ℝ)
    (hr : pinchingScalarsRepresent F U A τ V t)
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (hV : ∀ i x, x ∈ U i → TraceFreeFourth (V i x))
    (hE : ∀ i x, x ∈ U i → weightedTrace (A i x) (V i x) = hessianE (A i x) (τ i x) t)
    (hb : ∀ i x, x ∈ U i → cubicContraction (τ i x) (V i x) = intrinsicHessianB0 (A i x) (τ i x))
    (hn : ∀ i x, x ∈ U i → fourthNormSq (V i x) =
      3*t*(intrinsicCubicA (A i x) (τ i x)-2*intrinsicCubicB (A i x) (τ i x))+
      t*(35*t-28)/16-(3/2 : ℝ)*phiNormSq (A i x)) :
    ∀ x, F.W x = F.square x-(89/8 : ℝ)*F.L4 x+16*F.L3 x+(13/4 : ℝ)*F.J x := by
  intro x
  obtain ⟨i,hi⟩ := hcover x
  obtain ⟨hW,h4,h3,hJ,hs⟩ := hr i x hi
  rw [hW,h4,h3,hJ,hs]
  exact intrinsicPinchingW_pointwise_remainder (A i x) (τ i x) (had i x hi) t (V i x)
    (hV i x hi) (hE i x hi) (hb i x hi) (hn i x hi)

/-- Integration of the global scalar identity. Zero averages are explicit
integral assumptions, not pointwise equations for L4, L3 or J. -/
theorem pinchingScalars_integral_identity {Ω : Type*} [MeasurableSpace Ω]
    (F : PinchingScalarFields Ω) (ν : Measure Ω) (hInt : pinchingScalarsIntegrable F ν)
    (he : ∀ x, F.W x = F.square x-(89/8 : ℝ)*F.L4 x+16*F.L3 x+(13/4 : ℝ)*F.J x)
    (hpos : ∀ x, 0 ≤ F.square x)
    (hz4 : ∫ x, F.L4 x ∂ν = 0) (hz3 : ∫ x, F.L3 x ∂ν = 0) (hzJ : ∫ x, F.J x ∂ν = 0) :
    (∫ x, F.W x ∂ν) = (∫ x, F.square x ∂ν) ∧ 0 ≤ ∫ x, F.W x ∂ν := by
  have havg : (∫ x, F.W x ∂ν) = ∫ x, F.square x ∂ν := by
    calc
      _ = ∫ x, F.square x-(89/8 : ℝ)*F.L4 x+16*F.L3 x+(13/4 : ℝ)*F.J x ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall he)
      _ = _ := integral_zero_corrections ν F.square F.L4 F.L3 F.J
        hInt.2.2.2.2 hInt.2.1 hInt.2.2.1 hInt.2.2.2.1 hz4 hz3 hzJ
  exact ⟨havg,by rw [havg]; exact integral_nonneg hpos⟩

/-- Prop:meanconvex from represented local data, conditional on precisely
the reduced-Hessian inputs and the three global zero integrals. -/
theorem pinchingScalars_integral_of_local_hessian {Ω ι : Type*} [MeasurableSpace Ω]
    (F : PinchingScalarFields Ω) (ν : Measure Ω) (hInt : pinchingScalarsIntegrable F ν)
    (U : ι → Set Ω) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4) (t : ℝ)
    (hr : pinchingScalarsRepresent F U A τ V t)
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (hV : ∀ i x, x ∈ U i → TraceFreeFourth (V i x))
    (hE : ∀ i x, x ∈ U i → weightedTrace (A i x) (V i x) = hessianE (A i x) (τ i x) t)
    (hb : ∀ i x, x ∈ U i → cubicContraction (τ i x) (V i x) = intrinsicHessianB0 (A i x) (τ i x))
    (hn : ∀ i x, x ∈ U i → fourthNormSq (V i x) =
      3*t*(intrinsicCubicA (A i x) (τ i x)-2*intrinsicCubicB (A i x) (τ i x))+
      t*(35*t-28)/16-(3/2 : ℝ)*phiNormSq (A i x))
    (hz4 : ∫ x, F.L4 x ∂ν = 0) (hz3 : ∫ x, F.L3 x ∂ν = 0) (hzJ : ∫ x, F.J x ∂ν = 0) :
    (∫ x, F.W x ∂ν) = (∫ x, F.square x ∂ν) ∧ 0 ≤ ∫ x, F.W x ∂ν :=
  pinchingScalars_integral_identity F ν hInt
    (pinchingScalars_remainder_of_local_hessian F U hcover A τ V t hr had hV hE hb hn)
    (pinchingScalars_square_nonneg F U hcover A τ V t hr) hz4 hz3 hzJ

/-- Construct the five global integrands from local frames, establish their
integrability, and attach the averaged identity to those very fields. The
remaining three zero integrals appear as premises of the final implication;
they are not assumed in order to construct the fields. -/
theorem localPinchingScalars_mean_identity {Ω ι : Type*} [TopologicalSpace Ω]
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (U : ι → Set Ω) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4) (t : ℝ)
    (hA : ∀ i, ContinuousOn (A i) (U i)) (hτ : ∀ i, ContinuousOn (τ i) (U i))
    (hVc : ∀ i, ContinuousOn (V i) (U i))
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (htrans : ∀ i j x, x ∈ U i → x ∈ U j → ∃ O : Matrix4, OrthogonalFrame O ∧
      ((A j x = frameMatrix O (A i x) ∧ τ j x = frameCubic O (τ i x) ∧
          V j x = frameFourth O (V i x)) ∨
       (A j x = -frameMatrix O (A i x) ∧ τ j x = -frameCubic O (τ i x) ∧
          V j x = -frameFourth O (V i x))))
    (hV : ∀ i x, x ∈ U i → TraceFreeFourth (V i x))
    (hE : ∀ i x, x ∈ U i → weightedTrace (A i x) (V i x) = hessianE (A i x) (τ i x) t)
    (hb : ∀ i x, x ∈ U i → cubicContraction (τ i x) (V i x) = intrinsicHessianB0 (A i x) (τ i x))
    (hn : ∀ i x, x ∈ U i → fourthNormSq (V i x) =
      3*t*(intrinsicCubicA (A i x) (τ i x)-2*intrinsicCubicB (A i x) (τ i x))+
      t*(35*t-28)/16-(3/2 : ℝ)*phiNormSq (A i x)) :
    ∃! F : PinchingScalarFields Ω, pinchingScalarsContinuous F ∧
      pinchingScalarsIntegrable F ν ∧ pinchingScalarsRepresent F U A τ V t ∧
      (∀ x, F.W x = F.square x-(89/8 : ℝ)*F.L4 x+16*F.L3 x+(13/4 : ℝ)*F.J x) ∧
      (∀ x, 0 ≤ F.square x) ∧
      ((∫ x, F.L4 x ∂ν = 0) → (∫ x, F.L3 x ∂ν = 0) → (∫ x, F.J x ∂ν = 0) →
        (∫ x, F.W x ∂ν) = (∫ x, F.square x ∂ν) ∧ 0 ≤ ∫ x, F.W x ∂ν) := by
  obtain ⟨F,hF,hu⟩ := pinchingScalars_glue_integrable ν U hU hcover A τ V t hA hτ hVc had htrans
  have he := pinchingScalars_remainder_of_local_hessian F U hcover A τ V t hF.2.2 had hV hE hb hn
  have hp := pinchingScalars_square_nonneg F U hcover A τ V t hF.2.2
  refine ⟨F,⟨hF.1,hF.2.1,hF.2.2,he,hp,?_⟩,?_⟩
  · exact fun hz4 hz3 hzJ => pinchingScalars_integral_identity F ν hF.2.1 he hp hz4 hz3 hzJ
  · intro G hG
    exact hu G ⟨hG.1,hG.2.1,hG.2.2.1⟩

/-- The interpolation inequality for the glued W uses one local chart at
each point only in the proof. It requires no measurable frame selection. -/
theorem pinchingScalars_local_interpolation {Ω ι : Type*} (F : PinchingScalarFields Ω)
    (U : ι → Set Ω) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4) (t : ℝ)
    (hr : pinchingScalarsRepresent F U A τ V t)
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (hhalf : ∀ i x, x ∈ U i → intrinsicPinchingW (A i x) (τ i x) (1/2) ≤ -(1/10000 : ℝ))
    (ht : 0 ≤ t) (htop : t ≤ 1/2) : ∀ x, F.W x ≤ -t/5000 := by
  intro x
  obtain ⟨i,hi⟩ := hcover x
  rw [(hr i x hi).1]
  exact intrinsicPinchingW_interpolation_of_endpoint (A i x) (τ i x) (had i x hi)
    (hhalf i x hi) t ht htop

theorem local_interval_exclusion_of_W_inputs {Ω ι : Type*} [MeasurableSpace Ω]
    (F : PinchingScalarFields Ω) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (U : ι → Set Ω) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4)
    (S : ℝ) (hS : 4 < S) (hr : pinchingScalarsRepresent F U A τ V (pinchingParameter S))
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (hhalf : ∀ i x, x ∈ U i → intrinsicPinchingW (A i x) (τ i x) (1/2) ≤ -(1/10000 : ℝ))
    (hInt : Integrable F.W ν) (hmean : 0 ≤ ∫ x, F.W x ∂ν) : 8 < S := by
  by_contra h8
  have ht := pinchingParameter_pos hS
  have htop := pinchingParameter_le_half hS (le_of_not_gt h8)
  have hbound := integral_mono hInt (integrable_const (-(pinchingParameter S)/5000))
    (pinchingScalars_local_interpolation F U hcover A τ V _ hr had hhalf ht.le htop)
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

/-- The same complete finite premises discharge the endpoint on every local
chart. The global W is already a scalar, not a chosen global component field. -/
theorem local_interval_exclusion_of_finite_certificate {Ω ι : Type*} [MeasurableSpace Ω]
    (F : PinchingScalarFields Ω) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (U : ι → Set Ω) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4)
    (S : ℝ) (hS : 4 < S) (hr : pinchingScalarsRepresent F U A τ V (pinchingParameter S))
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (hInt : Integrable F.W ν) (hmean : 0 ≤ ∫ x, F.W x ∂ν) : 8 < S := by
  exact local_interval_exclusion_of_W_inputs F ν U hcover A τ V S hS hr had
    (fun i x hi => intrinsic_endpoint_of_finite_certificate P C Q G sigma hP hexp hs hcoeff hblocks
      (A i x) (τ i x) (had i x hi)) hInt hmean

/-- For continuous represented fields on a compact space, all integrability
and nonnegative-mean premises are derived. Actual local geometric equations,
three zero integrals and the five complete finite families remain explicit. -/
theorem local_interval_exclusion_of_hessian_inputs {Ω ι : Type*} [TopologicalSpace Ω]
    [CompactSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (F : PinchingScalarFields Ω) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hc : pinchingScalarsContinuous F)
    (U : ι → Set Ω) (hcover : ∀ x, ∃ i, x ∈ U i)
    (A : ι → Ω → Matrix4) (τ : ι → Ω → Cubic4) (V : ι → Ω → Fourth4)
    (S : ℝ) (hS : 4 < S) (hr : pinchingScalarsRepresent F U A τ V (pinchingParameter S))
    (had : ∀ i x, x ∈ U i → PaperAdmissible (A i x) (τ i x))
    (hV : ∀ i x, x ∈ U i → TraceFreeFourth (V i x))
    (hE : ∀ i x, x ∈ U i → weightedTrace (A i x) (V i x) =
      hessianE (A i x) (τ i x) (pinchingParameter S))
    (hb : ∀ i x, x ∈ U i → cubicContraction (τ i x) (V i x) = intrinsicHessianB0 (A i x) (τ i x))
    (hn : ∀ i x, x ∈ U i → fourthNormSq (V i x) =
      3*pinchingParameter S*(intrinsicCubicA (A i x) (τ i x)-2*intrinsicCubicB (A i x) (τ i x))+
      pinchingParameter S*(35*pinchingParameter S-28)/16-(3/2 : ℝ)*phiNormSq (A i x))
    (hz4 : ∫ x, F.L4 x ∂ν = 0) (hz3 : ∫ x, F.L3 x ∂ν = 0) (hzJ : ∫ x, F.J x ∂ν = 0) : 8 < S := by
  have hInt := pinchingScalars_integrable_of_continuous F ν hc
  have hm := pinchingScalars_integral_of_local_hessian F ν hInt U hcover A τ V
    (pinchingParameter S) hr had hV hE hb hn hz4 hz3 hzJ
  exact local_interval_exclusion_of_finite_certificate P C Q G sigma hP hexp hs hcoeff hblocks
    F ν U hcover A τ V S hS hr had hInt.1 hm.2

end FiniteInputs
end
end SecondPinching
