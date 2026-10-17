import SecondPinching.TrialPolynomial

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! An unexpanded polynomial numerator for eq:Pidentity. All contractions use
ordered indices. The generic formulas below use only rational constants,
addition and multiplication, so they also make sense in a polynomial ring.
No coefficient array or external computation is assumed in this file. -/

section Algebra
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Unnormalised spectral power sum. -/
def endpointRawMoment (ell : Fin 4 → R) (k : ℕ) : R := ∑ i, ell i ^ k

/-- The ordered squared norm of the unnormalised cubic. -/
def endpointRawNorm (T : Fin 4 → Fin 4 → Fin 4 → R) : R :=
  ∑ i, ∑ j, ∑ k, T i j k ^ 2

/-- Unnormalised cubic Gram matrix. -/
def endpointRawR (T : Fin 4 → Fin 4 → Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun k l => ∑ i, ∑ j, T i j k * T i j l

/-- Unnormalised vector d; no vanishing condition is imposed. -/
def endpointRawD (ell : Fin 4 → R) (T : Fin 4 → Fin 4 → Fin 4 → R) : Fin 4 → R :=
  fun k => ∑ i, ell i ^ 2 * T i i k

/-- Unnormalised contraction a. -/
def endpointRawA (ell : Fin 4 → R) (T : Fin 4 → Fin 4 → Fin 4 → R) : R :=
  ∑ i, ∑ j, ∑ k, ell i ^ 2 * T i j k ^ 2

/-- Unnormalised contraction b. -/
def endpointRawBContraction (ell : Fin 4 → R) (T : Fin 4 → Fin 4 → Fin 4 → R) : R :=
  ∑ i, ∑ j, ∑ k, ell i * ell j * T i j k ^ 2

/-- Unnormalised contraction c. -/
def endpointRawC (ell : Fin 4 → R) (T : Fin 4 → Fin 4 → Fin 4 → R) : R :=
  ∑ i, ∑ j, ∑ k, ell i * T i j k ^ 2

/-- The vector with components ell_i d_i before normalisation. -/
def endpointRawAd (ell : Fin 4 → R) (T : Fin 4 → Fin 4 → Fin 4 → R) : Fin 4 → R :=
  fun i => ell i * endpointRawD ell T i

/-- Ordered matrix pairing, over a rational algebra. -/
def endpointRawInner (X Y : Matrix (Fin 4) (Fin 4) R) : R := ∑ i, ∑ j, X i j * Y i j

/-- F=L^2 N B. This is a numerator, not the Python supplement's L^3 N B. -/
def endpointRawB (L N : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun i j =>
    (if i = j then algebraMap ℚ R (5/8) * L * N * ell i ^ 2 -
      algebraMap ℚ R (1/2) * endpointRawMoment ell 3 * N * ell i -
      algebraMap ℚ R (1/32) * L^2 * N else 0) -
    algebraMap ℚ R (1/2) * L^2 * endpointRawR T i j +
    algebraMap ℚ R (7/8) *
      ∑ k, (4*ell k-ell i-ell j)*T i j k*endpointRawAd ell T k

/-- The numerator L K_A Y when A=diag(ell/sqrt(L)). -/
def endpointRawK (L : R) (ell : Fin 4 → R)
    (Y : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  fun i j => (algebraMap ℚ R (1/6)*L+
      algebraMap ℚ R (1/4)*(ell i^2+ell j^2)-
      algebraMap ℚ R (1/6)*ell i*ell j)*Y i j +
    if i = j then algebraMap ℚ R (7/36)*ell i*(∑ a, ell a*Y a a)-
      algebraMap ℚ R (1/12)*(∑ a, ell a^2*Y a a) else 0

/-- The polynomial numerator L^5 N^2(-W_(1/2)-1/10000), before the
constant factor 5625/32. The identity with W is proved below. -/
def endpointRawNumerator (L N : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) : R :=
  let F := endpointRawB L N ell T
  let d := endpointRawD ell T
  let e := endpointRawAd ell T
  let m := endpointRawMoment ell 3
  let p := endpointRawMoment ell 4 * L - m^2 - algebraMap ℚ R (1/4)*L^3
  8*L*endpointRawInner F F - 16*endpointRawInner F (endpointRawK L ell F) -
    algebraMap ℚ R (21/32+1/10000)*L^5*N^2 -
    algebraMap ℚ R (13/16)*p*L^2*N^2 + algebraMap ℚ R (39/16)*m^2*L^2*N^2 +
    8*endpointRawA ell T*L^4*N + algebraMap ℚ R (189/16)*endpointRawBContraction ell T*L^4*N -
    16*m*endpointRawC ell T*L^3*N - 24*(∑ i, d i^2)*L^3*N +
    algebraMap ℚ R (35/4)*(∑ i, e i^2)*L^2*N -
    algebraMap ℚ R (441/16)*(∑ i, ∑ j, e i*endpointRawR T i j*e j)*L^2

theorem endpointRawMoment_scale (s : R) (ell : Fin 4 → R) (k : ℕ) :
    endpointRawMoment (fun i => s*ell i) k = s^k*endpointRawMoment ell k := by
  simp [endpointRawMoment, mul_pow, Finset.mul_sum]

theorem endpointRawNorm_scale (s : R) (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawNorm (fun i j k => s*T i j k) = s^2*endpointRawNorm T := by
  simp [endpointRawNorm, mul_pow, Finset.mul_sum]

theorem endpointRawR_scale (s : R) (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawR (fun i j k => s*T i j k) =
      fun i j => s^2*endpointRawR T i j := by
  ext i j
  simp only [endpointRawR, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

theorem endpointRawD_scale (s u : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawD (fun i => s*ell i) (fun i j k => u*T i j k) =
      fun k => s^2*u*endpointRawD ell T k := by
  funext k
  simp only [endpointRawD, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  ring

theorem endpointRawA_scale (s u : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawA (fun i => s*ell i) (fun i j k => u*T i j k) =
      s^2*u^2*endpointRawA ell T := by
  simp only [endpointRawA, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem endpointRawBContraction_scale (s u : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawBContraction (fun i => s*ell i) (fun i j k => u*T i j k) =
      s^2*u^2*endpointRawBContraction ell T := by
  simp only [endpointRawBContraction, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem endpointRawC_scale (s u : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawC (fun i => s*ell i) (fun i j k => u*T i j k) =
      s*u^2*endpointRawC ell T := by
  simp only [endpointRawC, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

theorem endpointRawAd_scale (s u : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawAd (fun i => s*ell i) (fun i j k => u*T i j k) =
      fun k => s^3*u*endpointRawAd ell T k := by
  funext k
  simp only [endpointRawAd, endpointRawD_scale]
  ring

theorem endpointRawInner_scale (s u : R) (X Y : Matrix (Fin 4) (Fin 4) R) :
    endpointRawInner (fun i j => s*X i j) (fun i j => u*Y i j) =
      s*u*endpointRawInner X Y := by
  simp only [endpointRawInner, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem endpointRawB_scale (s u L N : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawB (s^2*L) (u^2*N) (fun i => s*ell i) (fun i j k => u*T i j k) =
      fun i j => s^4*u^2*endpointRawB L N ell T i j := by
  ext i j
  simp only [endpointRawB, endpointRawMoment_scale, endpointRawR_scale, endpointRawAd_scale]
  have he : (∑ k, (4*(s*ell k)-s*ell i-s*ell j)*(u*T i j k)*
      (s^3*u*endpointRawAd ell T k)) =
      s^4*u^2*(∑ k, (4*ell k-ell i-ell j)*T i j k*endpointRawAd ell T k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    ring
  rw [he]
  by_cases h : i = j <;> simp only [h, ite_true, ite_false] <;> ring

theorem endpointRawK_scale (s q L : R) (ell : Fin 4 → R)
    (Y : Matrix (Fin 4) (Fin 4) R) :
    endpointRawK (s^2*L) (fun i => s*ell i) (fun i j => q*Y i j) =
      fun i j => s^2*q*endpointRawK L ell Y i j := by
  ext i j
  simp only [endpointRawK]
  have h1 : (∑ a, s*ell a*(q*Y a a)) = s*q*(∑ a, ell a*Y a a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    ring
  have h2 : (∑ a, (s*ell a)^2*(q*Y a a)) = s^2*q*(∑ a, ell a^2*Y a a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    ring
  rw [h1,h2]
  by_cases h : i = j <;> simp only [h, ite_true, ite_false] <;> ring

theorem endpointRawNumerator_scale (s u L N : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawNumerator (s^2*L) (u^2*N) (fun i => s*ell i) (fun i j k => u*T i j k) =
      s^10*u^4*endpointRawNumerator L N ell T := by
  simp only [endpointRawNumerator, endpointRawB_scale, endpointRawK_scale,
    endpointRawInner_scale, endpointRawMoment_scale, endpointRawA_scale,
    endpointRawBContraction_scale, endpointRawC_scale, endpointRawD_scale,
    endpointRawAd_scale, endpointRawR_scale]
  simp only [Fin.sum_univ_succ]
  ring

end Algebra

/-- At unit normalising scales the raw B is exactly the paper's trial B. -/
theorem endpointRawB_unit (μ : Vector4) (τ : Cubic4) :
    endpointRawB 1 1 μ τ = trialB μ τ := by
  rw [trialB_expanded]
  ext i j
  simp [endpointRawB, endpointRawMoment, endpointRawR, endpointRawAd, endpointRawD,
    cubicD, cubicMoment_diagonal, cubicGramMatrix, mixedGramAdjoint,
    Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  split_ifs <;> ring

/-- At L=1 the raw K is the actual ordered-metric Gram operator. -/
theorem endpointRawK_unit (μ : Vector4) (Y : Matrix4) :
    endpointRawK 1 μ Y = matrixGramOperator (Matrix.diagonal μ) Y := by
  ext i j
  simp [endpointRawK, matrixGramOperator, Matrix.diagonal_pow,
    Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.diagonal_apply,
    Matrix.one_apply, Fin.sum_univ_succ]
  split_ifs <;> ring

/-- The cleared expression agrees with the actual endpoint functional at unit
scales. Only the two stated spectral constraints are needed here. -/
theorem endpointRawNumerator_unit (μ : Vector4) (τ : Cubic4)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, μ i^2 = 1) :
    endpointRawNumerator 1 1 μ τ = -pinchingW μ τ (1/2)-1/10000 := by
  rw [pinchingW_half_expanded μ τ hμ hn, phiNormSq_diagonal μ hμ hn]
  simp only [endpointRawNumerator, endpointRawB_unit, endpointRawK_unit]
  simp [endpointRawMoment, endpointRawA, endpointRawBContraction, endpointRawC,
    endpointRawD, endpointRawAd, endpointRawR, endpointRawInner,
    cubicMoment_diagonal, quarticMoment_diagonal, cubicA, cubicB, cubicC, cubicD,
    matrixNormSq, matrixInner, vectorGramOperator, cubicGramMatrix,
    Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Matrix.one_apply,
    Fin.sum_univ_succ]
  ring

end
end SecondPinching
