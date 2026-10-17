import SecondPinching.EndpointNumerator
import SecondPinching.CertificateEndpoint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The polynomial in eq:Pidentity is constructed, rather than supplied as an
unknown function satisfying that identity. Equality to the stored coefficient
array remains a complete finite coefficient check, stated as a premise. -/

section Algebra
variable {R : Type*} [CommRing R]

/-- The spectral chart as a polynomial formula over a commutative ring. -/
def endpointChartSpectrum (r y : R) : Fin 4 → R :=
  ![1+r+r*y, 1-r-r*y, -1+r-r*y, -1-r+r*y]

/-- L as a polynomial formula. -/
def endpointChartScale (r y : R) : R := 4*(1+r^2+r^2*y^2)

/-- The two-column basis from eq:cubicchart, over a commutative ring. -/
def endpointChartBasis (r y : R) : Matrix (Fin 4) (Fin 2) R :=
  !![-1+r*y, -r+r*y; 1+r, 0; 0, 1+r; -r-r*y, -1-r*y]

/-- The actual twelve-coordinate cubic formula, with its ordered entries. -/
def endpointChartTensor (r y : R) (x : Fin 12 → R) : Fin 4 → Fin 4 → Fin 4 → R :=
  let fibre := fun k : Fin 4 =>
    endpointChartBasis r y *ᵥ ![x ⟨4+2*k.val, by omega⟩,x ⟨5+2*k.val, by omega⟩]
  fun i j k => if i = j then fibre k i
    else if i = k then fibre j i
    else if j = k then fibre i j
    else x (Fin.ofNat 12 (6-(i.val+j.val+k.val)))

variable [Algebra ℚ R]

/-- A polynomial expression whose real evaluation is P(r,y,x). -/
def endpointChartExpression (r y : R) (x : Fin 12 → R) : R :=
  algebraMap ℚ R (5625/32) * endpointRawNumerator
    (endpointChartScale r y) (endpointRawNorm (endpointChartTensor r y x))
    (endpointChartSpectrum r y) (endpointChartTensor r y x)

variable {S : Type*} [CommRing S] [Algebra ℚ S]

theorem endpointRawNumerator_map (f : R →ₐ[ℚ] S) (L N : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    f (endpointRawNumerator L N ell T) = endpointRawNumerator (f L) (f N)
      (fun i => f (ell i)) (fun i j k => f (T i j k)) := by
  simp [endpointRawNumerator, endpointRawB, endpointRawK, endpointRawMoment,
    endpointRawInner, endpointRawR, endpointRawD, endpointRawAd, endpointRawA,
    endpointRawBContraction, endpointRawC, map_sum, map_ofNat, apply_ite]

theorem endpointChartTensor_map (f : R →ₐ[ℚ] S) (r y : R) (x : Fin 12 → R) :
    (fun i j k => f (endpointChartTensor r y x i j k)) =
      endpointChartTensor (f r) (f y) (fun k => f (x k)) := by
  have hf (a b : Fin 4) :
      f ((endpointChartBasis r y *ᵥ ![x ⟨4+2*a.val, by omega⟩,
        x ⟨5+2*a.val, by omega⟩]) b) =
      (endpointChartBasis (f r) (f y) *ᵥ ![f (x ⟨4+2*a.val, by omega⟩),
        f (x ⟨5+2*a.val, by omega⟩)]) b := by
    fin_cases b <;> simp [endpointChartBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  funext i j k
  dsimp only [endpointChartTensor]
  split_ifs <;> simp only [hf]

theorem endpointChartExpression_map (f : R →ₐ[ℚ] S) (r y : R) (x : Fin 12 → R) :
    f (endpointChartExpression r y x) =
      endpointChartExpression (f r) (f y) (fun k => f (x k)) := by
  have hl : f (endpointChartScale r y) = endpointChartScale (f r) (f y) := by
    simp [endpointChartScale, map_ofNat]
  have he : (fun i => f (endpointChartSpectrum r y i)) =
      endpointChartSpectrum (f r) (f y) := by
    funext i
    fin_cases i <;> simp [endpointChartSpectrum]
  have hn : f (endpointRawNorm (endpointChartTensor r y x)) =
      endpointRawNorm (endpointChartTensor (f r) (f y) (fun k => f (x k))) := by
    rw [← endpointChartTensor_map f r y x]
    simp [endpointRawNorm, map_sum]
  simp only [endpointChartExpression, map_mul, AlgHom.commutes,
    endpointRawNumerator_map, hl, he, hn, endpointChartTensor_map]

end Algebra

/-- The generic chart formulas are exactly the existing real chart. -/
theorem endpointChart_real (r y : ℝ) (x : Fin 12 → ℝ) :
    endpointChartSpectrum r y = spectralVector r y ∧
    endpointChartScale r y = spectralScale r y ∧
    endpointChartTensor r y x = chartCubic r y x := by
  exact ⟨rfl,rfl,rfl⟩

/-- Clearing the positive normalising square roots gives eq:Pidentity for the
constructed expression. No finite coefficient or positivity check is assumed.
The proof even applies to every r>=0 and every real y. -/
theorem endpointChartExpression_identity (r y : ℝ) (hr : 0 ≤ r)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    endpointChartExpression r y x = endpointDenominator r y * chartNormSq r y x^2 *
      (-pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))
        (normalizedChartCubic r y x) (1/2)-1/10000) := by
  let s := Real.sqrt (spectralScale r y)
  let u := Real.sqrt (chartNormSq r y x)
  let μ : Vector4 := fun i => spectralVector r y i / s
  let τ := normalizedChartCubic r y x
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (spectralScale_pos r y))
  have hu : u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (chartNormSq_pos hr x hx))
  have hs2 : s^2 = spectralScale r y := Real.sq_sqrt (spectralScale_pos r y).le
  have hu2 : u^2 = chartNormSq r y x := Real.sq_sqrt (chartNormSq_pos hr x hx).le
  have hμ : ∑ i, μ i = 0 := by
    simpa [normalizedChartMatrix, Matrix.trace_diagonal, μ, s] using
      normalizedChartMatrix_trace r y
  have hn : ∑ i, μ i^2 = 1 := by
    simpa [normalizedChartMatrix, matrixNormSq_diagonal, μ, s] using
      normalizedChartMatrix_normSq r y
  have he : (fun i => s*μ i) = spectralVector r y := by
    funext i
    dsimp [μ]
    field_simp
  have ht : (fun i j k => u*τ i j k) = chartCubic r y x := by
    funext i j k
    change u*(chartCubic r y x i j k/u) = chartCubic r y x i j k
    field_simp
  have hid := endpointRawNumerator_scale s u (1 : ℝ) 1 μ τ
  rw [mul_one, mul_one, hs2, hu2, he, ht, endpointRawNumerator_unit μ τ hμ hn] at hid
  have hp : s^10*u^4 = spectralScale r y^5 * chartNormSq r y x^2 := by
    calc
      s^10*u^4 = (s^2)^5*(u^2)^2 := by ring
      _ = _ := by rw [hs2,hu2]
  rw [hp] at hid
  change algebraMap ℚ ℝ (5625/32)*endpointRawNumerator (spectralScale r y)
    (chartNormSq r y x) (spectralVector r y) (chartCubic r y x) = _
  have hrat : algebraMap ℚ ℝ (5625/32) = (5625/32 : ℝ) := by norm_num
  rw [hrat]
  rw [hid]
  dsimp [endpointDenominator, μ, τ, s]
  ring

/-- The unexpanded rational polynomial in the fourteen ordered variables
(r,y,x_1,...,x_12). No coefficient table is imported by this definition. -/
def endpointPolynomial : MvPolynomial (Fin 14) ℚ :=
  endpointChartExpression (MvPolynomial.X 0) (MvPolynomial.X 1)
    (fun i : Fin 12 => MvPolynomial.X (Fin.natAdd 2 i))

/-- Polynomial evaluation agrees with the constructed chart expression at every
real point, including x=0. -/
theorem endpointPolynomial_eval (r y : ℝ) (x : Fin 12 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x) endpointPolynomial =
      endpointChartExpression r y x := by
  change MvPolynomial.aeval (Fin.append ![r,y] x) endpointPolynomial = _
  unfold endpointPolynomial
  rw [endpointChartExpression_map]
  simp only [MvPolynomial.aeval_X, Fin.append_right]
  rfl

/-- The actual identity eq:Pidentity, proved without assuming an identity
between an unknown polynomial and W. The integer-content and degree bounds of
the released coefficient table are separate, unasserted finite claims. -/
theorem endpointPolynomial_identity (r y : ℝ) (hr : 0 ≤ r)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x) endpointPolynomial =
      endpointDenominator r y * chartNormSq r y x^2 *
      (-pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))
        (normalizedChartCubic r y x) (1/2)-1/10000) := by
  rw [endpointPolynomial_eval]
  exact endpointChartExpression_identity r y hr x hx

/-- A complete finite coefficient check transfers the proved identity to any
supplied rational coefficient polynomial. The check is a visible premise. -/
theorem checkedEndpointPolynomial_identity (P : MvPolynomial (Fin 14) ℚ)
    (hcheck : exactCoefficientCheck 14 P endpointPolynomial = true)
    (r y : ℝ) (hr : 0 ≤ r) (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Fin.append ![r,y] x) P =
      endpointDenominator r y * chartNormSq r y x^2 *
      (-pinchingW (fun i => spectralVector r y i / Real.sqrt (spectralScale r y))
        (normalizedChartCubic r y x) (1/2)-1/10000) := by
  rw [(exactCoefficientCheck_iff 14 P endpointPolynomial).mp hcheck]
  exact endpointPolynomial_identity r y hr x hx

end
end SecondPinching
