import SecondPinching.TrialPolynomial

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators Matrix
open MeasureTheory
namespace SecondPinching
noncomputable section

/-- U_t in the proof of prop:meanconvex, at the actual trial variables. -/
def pinchingTrialTensor (μ : Vector4) (τ : Cubic4) (t : ℝ) : Fourth4 :=
  jointTrialTensor (Matrix.diagonal μ) (trialY μ τ t) τ (trialVector μ τ)

/-- The integrand on the right of the averaged identity. -/
def pinchingSquare (μ : Vector4) (τ : Cubic4) (t : ℝ) (D : Fourth4) : ℝ :=
  fourthNormSq (hessianRemainder μ t D-pinchingTrialTensor μ τ t)

theorem pinchingSquare_nonneg (μ : Vector4) (τ : Cubic4) (t : ℝ) (D : Fourth4) :
    0 ≤ pinchingSquare μ τ t D := by
  have h := fourthInner_self_nonneg (hessianRemainder μ t D-pinchingTrialTensor μ τ t)
  rwa [fourthInner_self] at h

/-- The pointwise identity includes the three correction terms. The geometric
origins of the Hessian and its differentiated identities remain explicit inputs. -/
theorem pinchingW_pointwise_remainder (μ : Vector4) (τ : Cubic4) (t : ℝ) (D : Fourth4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ ((1-t)/4) D)
    (htr : ordinaryTrace D = 0)
    (hweighted : weightedTrace (Matrix.diagonal μ) D = (-t) • cubicGramMatrix τ)
    (hcubic : cubicContraction τ D = 0)
    (hPT : fourthNormSq D = 3*t*(cubicA μ τ-2*cubicB μ τ)+t*(11*t-7)/4) :
    pinchingW μ τ t = pinchingSquare μ τ t D-
      (89/8 : ℝ)*correctionL4 μ τ t+16*correctionL3 μ τ t+
      (13/4 : ℝ)*correctionJ μ τ t := by
  obtain ⟨hy,hyt⟩ := trialY_codomain μ τ had t
  have hr := hessian_joint_remainder μ τ t D had hD hRicci htr hweighted hcubic hPT
    (trialY μ τ t) hy hyt (trialVector μ τ)
  rw [← trialQ_eq_joint] at hr
  change _ - trialQ μ τ t = pinchingSquare μ τ t D at hr
  unfold pinchingW
  rw [hr]

/-- Integration of the paper's specified linear combination. Integrability
and vanishing integrals are separate hypotheses, never pointwise vanishing. -/
theorem integral_zero_corrections {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (F L4 L3 J : Ω → ℝ) (hF : Integrable F ν) (h4 : Integrable L4 ν)
    (h3 : Integrable L3 ν) (hJ : Integrable J ν)
    (hz4 : ∫ x, L4 x ∂ν = 0) (hz3 : ∫ x, L3 x ∂ν = 0) (hzJ : ∫ x, J x ∂ν = 0) :
    (∫ x, F x-(89/8 : ℝ)*L4 x+16*L3 x+(13/4 : ℝ)*J x ∂ν) = ∫ x, F x ∂ν := by
  have h0 := integral_sub hF (h4.const_mul (89/8 : ℝ))
  have h1 := integral_add (hF.sub (h4.const_mul (89/8 : ℝ))) (h3.const_mul (16 : ℝ))
  have h2 := integral_add ((hF.sub (h4.const_mul (89/8 : ℝ))).add (h3.const_mul (16 : ℝ)))
    (hJ.const_mul (13/4 : ℝ))
  simp only [Pi.add_apply, Pi.sub_apply] at h0 h1 h2
  rw [h2, h1, h0]
  simp [integral_const_mul, hz4, hz3, hzJ]

/-- The exact averaged norm identity in prop:meanconvex, conditional on the
listed geometric component identities and the three zero integrals. The measure
may in particular be normalized Riemannian volume. No immersion theorem is asserted. -/
theorem pinchingW_integral_identity {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (μ : Ω → Vector4) (τ : Ω → Cubic4) (D : Ω → Fourth4) (t : ℝ)
    (had : ∀ x, PaperAdmissible (Matrix.diagonal (μ x)) (τ x))
    (hD : ∀ x, FirstThreeSymmetric (D x))
    (hRicci : ∀ x, HasRicciCommutator (μ x) ((1-t)/4) (D x))
    (htr : ∀ x, ordinaryTrace (D x) = 0)
    (hweighted : ∀ x, weightedTrace (Matrix.diagonal (μ x)) (D x) = (-t) • cubicGramMatrix (τ x))
    (hcubic : ∀ x, cubicContraction (τ x) (D x) = 0)
    (hPT : ∀ x, fourthNormSq (D x) = 3*t*(cubicA (μ x) (τ x)-2*cubicB (μ x) (τ x))+t*(11*t-7)/4)
    (hF : Integrable (fun x => pinchingSquare (μ x) (τ x) t (D x)) ν)
    (h4 : Integrable (fun x => correctionL4 (μ x) (τ x) t) ν)
    (h3 : Integrable (fun x => correctionL3 (μ x) (τ x) t) ν)
    (hJ : Integrable (fun x => correctionJ (μ x) (τ x) t) ν)
    (hz4 : ∫ x, correctionL4 (μ x) (τ x) t ∂ν = 0)
    (hz3 : ∫ x, correctionL3 (μ x) (τ x) t ∂ν = 0)
    (hzJ : ∫ x, correctionJ (μ x) (τ x) t ∂ν = 0) :
    Integrable (fun x => pinchingW (μ x) (τ x) t) ν ∧
    (∫ x, pinchingW (μ x) (τ x) t ∂ν) = (∫ x, pinchingSquare (μ x) (τ x) t (D x) ∂ν) ∧
    0 ≤ ∫ x, pinchingW (μ x) (τ x) t ∂ν := by
  have he : (fun x => pinchingW (μ x) (τ x) t) =
      fun x => pinchingSquare (μ x) (τ x) t (D x)-
        (89/8 : ℝ)*correctionL4 (μ x) (τ x) t+16*correctionL3 (μ x) (τ x) t+
        (13/4 : ℝ)*correctionJ (μ x) (τ x) t := by
    funext x
    exact pinchingW_pointwise_remainder (μ x) (τ x) t (D x) (had x) (hD x)
      (hRicci x) (htr x) (hweighted x) (hcubic x) (hPT x)
  have hint : Integrable (fun x => pinchingW (μ x) (τ x) t) ν := by
    rw [he]
    exact ((hF.sub (h4.const_mul (89/8 : ℝ))).add (h3.const_mul (16 : ℝ))).add (hJ.const_mul (13/4 : ℝ))
  have havg : (∫ x, pinchingW (μ x) (τ x) t ∂ν) =
      ∫ x, pinchingSquare (μ x) (τ x) t (D x) ∂ν := by
    rw [he]
    exact integral_zero_corrections ν _ _ _ _ hF h4 h3 hJ hz4 hz3 hzJ
  exact ⟨hint,havg,by rw [havg]; exact integral_nonneg fun x => pinchingSquare_nonneg _ _ _ _⟩

end
end SecondPinching
