import SecondPinching.EndpointNumerator
import SecondPinching.SpectralReduction

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Permutation and sign invariance of the actual endpoint functional.
The raw numerator is used only through its proved identity with W_(1/2).
All sums remain ordered; neither cubic trace is silently strengthened. -/

/-- Simultaneous reindexing in all three tensor slots. -/
def permuteCubic {R : Type*} (e : Equiv.Perm (Fin 4))
    (T : Fin 4 → Fin 4 → Fin 4 → R) : Fin 4 → Fin 4 → Fin 4 → R :=
  fun i j k => T (e i) (e j) (e k)

section Algebra
variable {R : Type*} [CommRing R]

theorem endpointRawMoment_permute (e : Equiv.Perm (Fin 4)) (ell : Fin 4 → R) (k : ℕ) :
    endpointRawMoment (fun i => ell (e i)) k = endpointRawMoment ell k := by
  exact Equiv.sum_comp e (fun i => ell i ^ k)

theorem endpointRawNorm_permute (e : Equiv.Perm (Fin 4))
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawNorm (permuteCubic e T) = endpointRawNorm T := by
  unfold endpointRawNorm
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  exact Equiv.sum_comp e (fun k => T (e i) (e j) k^2)

theorem endpointRawR_permute (e : Equiv.Perm (Fin 4))
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawR (permuteCubic e T) = fun i j => endpointRawR T (e i) (e j) := by
  funext i j
  unfold endpointRawR
  refine Fintype.sum_equiv e _ _ (fun k => ?_)
  exact Equiv.sum_comp e (fun l => T (e k) l (e i)*T (e k) l (e j))

theorem endpointRawD_permute (e : Equiv.Perm (Fin 4)) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawD (fun i => ell (e i)) (permuteCubic e T) =
      fun i => endpointRawD ell T (e i) := by
  funext i
  exact Equiv.sum_comp e (fun j => ell j^2 * T j j (e i))

theorem endpointRawA_permute (e : Equiv.Perm (Fin 4)) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawA (fun i => ell (e i)) (permuteCubic e T) = endpointRawA ell T := by
  unfold endpointRawA
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  exact Equiv.sum_comp e (fun k => ell (e i)^2*T (e i) (e j) k^2)

theorem endpointRawBContraction_permute (e : Equiv.Perm (Fin 4)) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawBContraction (fun i => ell (e i)) (permuteCubic e T) =
      endpointRawBContraction ell T := by
  unfold endpointRawBContraction
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  exact Equiv.sum_comp e (fun k => ell (e i)*ell (e j)*T (e i) (e j) k^2)

theorem endpointRawC_permute (e : Equiv.Perm (Fin 4)) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawC (fun i => ell (e i)) (permuteCubic e T) = endpointRawC ell T := by
  unfold endpointRawC
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  exact Equiv.sum_comp e (fun k => ell (e i)*T (e i) (e j) k^2)

theorem endpointRawAd_permute (e : Equiv.Perm (Fin 4)) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawAd (fun i => ell (e i)) (permuteCubic e T) =
      fun i => endpointRawAd ell T (e i) := by
  funext i
  dsimp only [endpointRawAd]
  rw [endpointRawD_permute]

theorem endpointRawInner_permute (e : Equiv.Perm (Fin 4))
    (X Y : Matrix (Fin 4) (Fin 4) R) :
    endpointRawInner (fun i j => X (e i) (e j)) (fun i j => Y (e i) (e j)) =
      endpointRawInner X Y := by
  unfold endpointRawInner
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  exact Equiv.sum_comp e (fun j => X (e i) j*Y (e i) j)

variable [Algebra ℚ R]

theorem endpointRawB_permute (e : Equiv.Perm (Fin 4)) (L N : R) (ell : Fin 4 → R)
    (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawB L N (fun i => ell (e i)) (permuteCubic e T) =
      fun i j => endpointRawB L N ell T (e i) (e j) := by
  funext i j
  simp only [endpointRawB, endpointRawMoment_permute, endpointRawR_permute,
    endpointRawAd_permute, permuteCubic, e.injective.eq_iff]
  rw [Equiv.sum_comp e (fun k =>
    (4*ell k-ell (e i)-ell (e j))*T (e i) (e j) k*endpointRawAd ell T k)]

theorem endpointRawK_permute (e : Equiv.Perm (Fin 4)) (L : R) (ell : Fin 4 → R)
    (Y : Matrix (Fin 4) (Fin 4) R) :
    endpointRawK L (fun i => ell (e i)) (fun i j => Y (e i) (e j)) =
      fun i j => endpointRawK L ell Y (e i) (e j) := by
  funext i j
  simp only [endpointRawK, e.injective.eq_iff]
  rw [Equiv.sum_comp e (fun k => ell k*Y k k),
    Equiv.sum_comp e (fun k => ell k^2*Y k k)]

/-- Coordinate permutations preserve the full cleared expression, including
the contractions containing d and Ad. No spectral constraints are needed. -/
theorem endpointRawNumerator_permute (e : Equiv.Perm (Fin 4)) (L N : R)
    (ell : Fin 4 → R) (T : Fin 4 → Fin 4 → Fin 4 → R) :
    endpointRawNumerator L N (fun i => ell (e i)) (permuteCubic e T) =
      endpointRawNumerator L N ell T := by
  simp only [endpointRawNumerator, endpointRawB_permute, endpointRawK_permute,
    endpointRawMoment_permute, endpointRawD_permute, endpointRawAd_permute,
    endpointRawA_permute, endpointRawBContraction_permute, endpointRawC_permute,
    endpointRawR_permute, endpointRawInner_permute]
  have hquad : (∑ i, ∑ j, endpointRawAd ell T (e i)*endpointRawR T (e i) (e j)*
      endpointRawAd ell T (e j)) =
      ∑ i, ∑ j, endpointRawAd ell T i*endpointRawR T i j*endpointRawAd ell T j := by
    refine Fintype.sum_equiv e _ _ (fun i => ?_)
    exact Equiv.sum_comp e (fun j => endpointRawAd ell T (e i)*endpointRawR T (e i) j*endpointRawAd ell T j)
  rw [Equiv.sum_comp e (fun i => endpointRawD ell T i^2),
    Equiv.sum_comp e (fun i => endpointRawAd ell T i^2), hquad]

end Algebra

/-- The cubic slot symmetry is preserved without any norm or trace assumptions. -/
theorem cubicSymmetric_permute (e : Equiv.Perm (Fin 4)) (τ : Cubic4)
    (hτ : CubicSymmetric τ) : CubicSymmetric (permuteCubic e τ) := by
  intro σ v
  exact hτ σ (fun i => e (v i))

/-- The actual admissibility conditions survive a signed permutation of the
spectrum and the corresponding permutation of all cubic slots. -/
theorem paperAdmissible_signed_permutation (s : ℝ) (hs : s^2 = 1)
    (e : Equiv.Perm (Fin 4)) (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) :
    PaperAdmissible (Matrix.diagonal (signedSpectrum s e μ)) (permuteCubic e τ) := by
  apply (admissible_iff_paper _ _).mp
  apply (admissible_diagonal_iff _ _).mpr
  obtain ⟨hτ,ht,hn,hτn,htr,hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  refine ⟨cubicSymmetric_permute e τ hτ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [signedSpectrum_trace, ht, mul_zero]
  · rw [signedSpectrum_normSq, hs, hn, mul_one]
  · change endpointRawNorm (permuteCubic e τ) = 1
    rw [endpointRawNorm_permute]
    exact hτn
  · intro k
    change (∑ i, τ (e i) (e i) (e k)) = 0
    rw [Equiv.sum_comp e (fun i => τ i i (e k)), htr]
  · intro k
    simp only [signedSpectrum, permuteCubic, mul_assoc, ← Finset.mul_sum]
    rw [Equiv.sum_comp e (fun i => μ i*τ i i (e k)), hw, mul_zero]

/-- Sign changes of the spectrum and of the cubic are separately harmless
for W_(1/2). Only the two spectral constraints are used in this algebraic identity. -/
theorem pinchingW_half_signs (s u : ℝ) (hs : s^2 = 1) (hu : u^2 = 1)
    (μ : Vector4) (τ : Cubic4) (ht : ∑ i, μ i = 0) (hn : ∑ i, μ i^2 = 1) :
    pinchingW (fun i => s*μ i) (fun i j k => u*τ i j k) (1/2) =
      pinchingW μ τ (1/2) := by
  have ht' : ∑ i, s*μ i = 0 := by rw [← Finset.mul_sum, ht, mul_zero]
  have hn' : ∑ i, (s*μ i)^2 = 1 := by
    simp only [mul_pow, ← Finset.mul_sum, hs, hn, mul_one]
  have h := endpointRawNumerator_scale s u (1 : ℝ) 1 μ τ
  have hs10 : s^10 = 1 := by
    calc
      s^10 = (s^2)^5 := by ring
      _ = 1 := by rw [hs]; norm_num
  have hu4 : u^4 = 1 := by
    calc
      u^4 = (u^2)^2 := by ring
      _ = 1 := by rw [hu]; norm_num
  rw [hs,hu,mul_one,endpointRawNumerator_unit _ _ ht' hn',
    endpointRawNumerator_unit μ τ ht hn,hs10,hu4,one_mul,one_mul] at h
  linarith

/-- Simultaneous coordinate permutations preserve the actual endpoint W. -/
theorem pinchingW_half_permute (e : Equiv.Perm (Fin 4)) (μ : Vector4) (τ : Cubic4)
    (ht : ∑ i, μ i = 0) (hn : ∑ i, μ i^2 = 1) :
    pinchingW (fun i => μ (e i)) (permuteCubic e τ) (1/2) = pinchingW μ τ (1/2) := by
  have ht' : ∑ i, μ (e i) = 0 := by rw [Equiv.sum_comp e,ht]
  have hn' : ∑ i, μ (e i)^2 = 1 := by rw [Equiv.sum_comp e (fun i => μ i^2),hn]
  have h := endpointRawNumerator_permute e (1 : ℝ) 1 μ τ
  rw [endpointRawNumerator_unit _ _ ht' hn',endpointRawNumerator_unit μ τ ht hn] at h
  linarith

/-- Combined invariance in the form needed by the closed spectral chart. -/
theorem pinchingW_half_signed_permutation (s : ℝ) (hs : s^2 = 1)
    (e : Equiv.Perm (Fin 4)) (μ : Vector4) (τ : Cubic4)
    (ht : ∑ i, μ i = 0) (hn : ∑ i, μ i^2 = 1) :
    pinchingW (signedSpectrum s e μ) (permuteCubic e τ) (1/2) = pinchingW μ τ (1/2) := by
  have ht' : ∑ i, μ (e i) = 0 := by rw [Equiv.sum_comp e,ht]
  have hn' : ∑ i, μ (e i)^2 = 1 := by rw [Equiv.sum_comp e (fun i => μ i^2),hn]
  have h := pinchingW_half_signs s 1 hs (by norm_num)
    (fun i => μ (e i)) (permuteCubic e τ) ht' hn'
  simp only [one_mul] at h
  exact h.trans (pinchingW_half_permute e μ τ ht hn)

end
end SecondPinching
