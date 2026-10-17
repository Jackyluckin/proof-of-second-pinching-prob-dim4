import SecondPinching.CertificateBlocks
import SecondPinching.CompressedGram
import SecondPinching.CertificateCover
import SecondPinching.NormalizedChart
import SecondPinching.TrialPolynomial

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Endpoint transfer with every unproved identification left explicit.
This file does NOT assert the released polynomial identity or the all-control
finite tests. It proves their consequence for the actual normalized chart and W. -/

/-- The denominator D=5625 L^5/32 in eq:Pidentity. -/
def endpointDenominator (r y : ℝ) : ℝ := (5625 / 32 : ℝ) * spectralScale r y ^ 5

/-- The two displayed forms of D agree. -/
theorem endpointDenominator_expanded (r y : ℝ) :
    endpointDenominator r y = 180000 * (1 + r^2 + r^2*y^2)^5 := by
  unfold endpointDenominator spectralScale
  ring

/-- The denominator is positive without excluding any parameter boundary. -/
theorem endpointDenominator_pos (r y : ℝ) : 0 < endpointDenominator r y := by
  unfold endpointDenominator
  exact mul_pos (by norm_num) (pow_pos (spectralScale_pos r y) 5)

/-- The complete multiplier D N^2 is positive at every nonzero cubic coordinate. -/
theorem endpointNormalization_pos (r y : ℝ) (hr : 0 ≤ r)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    0 < endpointDenominator r y * chartNormSq r y x ^ 2 := by
  exact mul_pos (endpointDenominator_pos r y) (pow_pos (chartNormSq_pos hr x hx) 2)

/-- The Bernstein weight on an actual released leaf, including its boundaries. -/
def certificateLeafWeight (leaf : Fin 24) (r y : ℝ) (ij : ControlIndex) : ℝ :=
  rectangleWeight (certificateRectangles leaf 0) (certificateRectangles leaf 1)
    (certificateRectangles leaf 2) (certificateRectangles leaf 3) r y ij

/-- Actual-leaf weights are nonnegative on the closed leaf. -/
theorem certificateLeafWeight_nonneg (leaf : Fin 24) (r y : ℝ)
    (h : inClosedCertificateRectangle (certificateRectangles leaf) r y) (ij : ControlIndex) :
    0 ≤ certificateLeafWeight leaf r y ij := by
  obtain ⟨_,hr,_,_,hy,_⟩ := certificateRectangles_bounds leaf
  exact rectangleWeight_nonneg (by exact_mod_cast hr) (by exact_mod_cast hy)
    ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩ ij

/-- Actual-leaf weights sum to one on the closed leaf. -/
theorem certificateLeafWeight_sum (leaf : Fin 24) (r y : ℝ)
    (h : inClosedCertificateRectangle (certificateRectangles leaf) r y) :
    ∑ ij, certificateLeafWeight leaf r y ij = 1 := by
  obtain ⟨_,hr,_,_,hy,_⟩ := certificateRectangles_bounds leaf
  exact rectangleWeight_sum (by exact_mod_cast hr) (by exact_mod_cast hy)
    ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩

/-- The clearing scale for P_ij is positive for every positive common integer
scale sigma. This is distinct from the scale 196 n_* d for G_ij. -/
theorem compressedPolynomialScale_pos (sigma : ℤ) (hs : 0 < sigma) :
    0 < (compressedGramConstant : ℚ) * (sigma : ℚ) := by
  exact mul_pos (by exact_mod_cast compressedGramConstant_pos) (by exact_mod_cast hs)

/-- All 24*225 control quartics and all eight blocks at each control are
required. The complete coefficient checks include coefficients required to vanish.
The Bernstein expansion is still a displayed identification hypothesis. -/
theorem certificate_polynomial_pos_of_finite_checks
    (P : MvPolynomial (Fin 14) ℚ)
    (C : Fin 24 → ControlIndex → MvPolynomial (Fin 12) ℚ)
    (Q V : Fin 24 → ControlIndex → (b : Fin 8) →
      Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) ℤ)
    (sigma : Fin 24 → ControlIndex → ℤ)
    (hs : ∀ leaf ij, 0 < sigma leaf ij)
    (hcoeff : ∀ leaf ij, exactCoefficientCheck 12 (C leaf ij)
      (integerBlockQuartic (Q leaf ij)
        ((compressedGramConstant : ℚ) * (sigma leaf ij : ℚ))) = true)
    (hblocks : ∀ leaf ij b, integerCertificateCheck (certificateBlockSize b)
      (Q leaf ij b) (V leaf ij b) = true)
    (hexp : ∀ leaf r y, inClosedCertificateRectangle (certificateRectangles leaf) r y →
      ∀ x : Fin 12 → ℝ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x) P =
        ∑ ij, certificateLeafWeight leaf r y ij *
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (C leaf ij))
    (r y : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    0 < MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x) P := by
  obtain ⟨leaf,hmem⟩ := certificateRectangles_cover r y hr hy
  rw [hexp leaf r y hmem x]
  apply weighted_sum_pos
  · exact certificateLeafWeight_nonneg leaf r y hmem
  · exact certificateLeafWeight_sum leaf r y hmem
  · intro ij
    exact block_quartic_positivity_from_external_finite_checks (C leaf ij)
      (Q leaf ij) (V leaf ij) _ (compressedPolynomialScale_pos _ (hs leaf ij))
      (hcoeff leaf ij) (hblocks leaf ij) x hx

/-- Positivity of the exact endpoint polynomial yields the original endpoint
bound for the ACTUAL W, conditional on eq:Pidentity. No replacement functional
or certificate axiom is introduced. The intermediate bound is strict. -/
theorem chart_endpoint_of_polynomial_identity
    (P : MvPolynomial (Fin 14) ℚ)
    (hidentity : ∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ∀ x : Fin 12 → ℝ, x ≠ 0 →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x) P =
        endpointDenominator r y * chartNormSq r y x ^ 2 *
        (-pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))
          (normalizedChartCubic r y x) (1/2) - 1/10000))
    (hpositive : ∀ r ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ∀ x : Fin 12 → ℝ, x ≠ 0 →
      0 < MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x) P)
    (r y : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))
      (normalizedChartCubic r y x) (1/2) < -1/10000 := by
  have hp := hpositive r hr y hy x hx
  rw [hidentity r hr y hy x hx] at hp
  have hfac := endpointNormalization_pos r y hr.1 x hx
  have hterm := (mul_pos_iff_of_pos_left hfac).mp hp
  linarith

/-- The same endpoint inequality for every admissible cubic over a fixed chart
spectrum. Normalized-chart surjectivity is used, not assumed. This still does
not supply arbitrary-spectrum orthogonal transport or eq:Pidentity. -/
theorem chart_endpoint_for_all_admissible_cubics
    (r y : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hchart : ∀ x : Fin 12 → ℝ, x ≠ 0 →
      pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))
        (normalizedChartCubic r y x) (1/2) < -1/10000)
    (tau : Cubic4) (ha : PaperAdmissible (normalizedChartMatrix r y) tau) :
    pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y)) tau (1/2) ≤
      -1/10000 := by
  obtain ⟨x,hx,heq⟩ := (paperAdmissible_chart_iff r y hr hy tau).mp ha
  rw [← heq]
  exact (hchart x hx).le

end
end SecondPinching
