import SecondPinching.TrialPolynomial

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- Coordinates of the orthogonal projection of e_k to {1,mu} perpendicular. -/
def projectedCoordinate (μ : Vector4) (k : Fin 4) : Vector4 :=
  fun i => (1 : Matrix4) i k - 1/4 - μ k*μ i

/-- The projection norm formula in the proof of lem:bounds. -/
theorem projectedCoordinate_norm (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (hn : ∑ i, (μ i)^2 = 1) (k : Fin 4) :
    (∑ i, (projectedCoordinate μ k i)^2) = 3/4-(μ k)^2 := by
  have he : (∑ i, (projectedCoordinate μ k i)^2) =
      3/4-2*(μ k)^2+(μ k)^2*(∑ i, (μ i)^2)+(μ k/2)*(∑ i, μ i) := by
    fin_cases k <;> simp [projectedCoordinate, Matrix.one_apply, Fin.sum_univ_succ] <;> ring
  rw [he, hμ, hn]
  ring

/-- The curvature-coordinate bound eq:phiorth, including equality cases. -/
theorem principal_coordinate_sq_le (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (hn : ∑ i, (μ i)^2 = 1) (k : Fin 4) : (μ k)^2 ≤ 3/4 := by
  have hp : 0 ≤ ∑ i, (projectedCoordinate μ k i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [projectedCoordinate_norm μ hμ hn k] at hp
  linarith

theorem projectedCoordinate_pairing (μ z : Vector4) (k : Fin 4)
    (hz : ∑ i, z i = 0) (hmz : ∑ i, μ i*z i = 0) :
    (∑ i, projectedCoordinate μ k i*z i) = z k := by
  have he : (∑ i, projectedCoordinate μ k i*z i) =
      z k-(∑ i, z i)/4-μ k*(∑ i, μ i*z i) := by
    fin_cases k <;> simp [projectedCoordinate, Matrix.one_apply, Fin.sum_univ_succ] <;> ring
  rw [he, hz, hmz]
  ring

/-- The quantitative consequence of the two orthogonality constraints. -/
theorem repeated_component_bound (μ z : Vector4) (k : Fin 4)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1)
    (hz : ∑ i, z i = 0) (hmz : ∑ i, μ i*z i = 0) :
    (z k)^2 ≤ (3/4-(μ k)^2)*(∑ i, (z i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (projectedCoordinate μ k) z
  rwa [projectedCoordinate_norm μ hμ hn k, projectedCoordinate_pairing μ z k hz hmz] at h

/-- The squared norm of the ordered repeated-index group {i,i,k}. -/
def repeatedWeight (τ : Cubic4) (k : Fin 4) : ℝ :=
  3*(∑ i, (τ i i k)^2)-2*(τ k k k)^2

theorem repeatedWeight_lower (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (k : Fin 4) :
    (3/2+2*(μ k)^2)*(∑ i, (τ i i k)^2) ≤ repeatedWeight τ k := by
  obtain ⟨_hτ,hμ,hn,_hτn,ht,hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  have h := repeated_component_bound μ (fun i => τ i i k) k hμ hn (ht k) (hw k)
  unfold repeatedWeight
  linarith

/-- Exact ordered support accounting; the complement consists of the 24
all-distinct ordered components. No principal curvature is divided out. -/
theorem repeatedWeight_sum_identity (τ : Cubic4) (hτ : CubicSymmetric τ) :
    cubicNormSq τ - (∑ k, repeatedWeight τ k) =
      6*((τ 0 1 2)^2+(τ 0 1 3)^2+(τ 0 2 3)^2+(τ 1 2 3)^2) := by
  simp [cubicNormSq, repeatedWeight, Fin.sum_univ_succ,
    cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ]
  try simp only [cubicSymmetric_swap12 hτ 0 1,
    cubicSymmetric_swap12 hτ 0 2,
    cubicSymmetric_swap12 hτ 0 3,
    cubicSymmetric_swap12 hτ 1 2,
    cubicSymmetric_swap12 hτ 1 3,
    cubicSymmetric_swap12 hτ 2 3,
    cubicSymmetric_swap23 hτ 0 0 1,
    cubicSymmetric_swap23 hτ 0 0 2,
    cubicSymmetric_swap23 hτ 0 0 3,
    cubicSymmetric_swap23 hτ 0 1 2,
    cubicSymmetric_swap23 hτ 0 1 3,
    cubicSymmetric_swap23 hτ 0 2 3,
    cubicSymmetric_swap23 hτ 1 0 1,
    cubicSymmetric_swap23 hτ 1 0 2,
    cubicSymmetric_swap23 hτ 1 0 3,
    cubicSymmetric_swap23 hτ 1 1 2,
    cubicSymmetric_swap23 hτ 1 1 3,
    cubicSymmetric_swap23 hτ 1 2 3,
    cubicSymmetric_swap23 hτ 2 0 1,
    cubicSymmetric_swap23 hτ 2 0 2,
    cubicSymmetric_swap23 hτ 2 0 3,
    cubicSymmetric_swap23 hτ 2 1 2,
    cubicSymmetric_swap23 hτ 2 1 3,
    cubicSymmetric_swap23 hτ 2 2 3,
    cubicSymmetric_swap23 hτ 3 0 1,
    cubicSymmetric_swap23 hτ 3 0 2,
    cubicSymmetric_swap23 hτ 3 0 3,
    cubicSymmetric_swap23 hτ 3 1 2,
    cubicSymmetric_swap23 hτ 3 1 3,
    cubicSymmetric_swap23 hτ 3 2 3]
  ring

theorem repeatedWeight_sum_le (τ : Cubic4) (hτ : CubicSymmetric τ)
    (hτn : cubicNormSq τ = 1) : (∑ k, repeatedWeight τ k) ≤ 1 := by
  have he := repeatedWeight_sum_identity τ hτ
  rw [hτn] at he
  nlinarith [sq_nonneg (τ 0 1 2), sq_nonneg (τ 0 1 3),
    sq_nonneg (τ 0 2 3), sq_nonneg (τ 1 2 3)]

/-- d_k is the pairing with Phi, not with an unconstrained replacement. -/
theorem cubicD_eq_phi_pairing (μ : Vector4) (τ : Cubic4)
    (ht : ∀ k, ∑ i, τ i i k = 0) (hw : ∀ k, ∑ i, μ i*τ i i k = 0) (k : Fin 4) :
    cubicD μ τ k = ∑ i, normalizedPhi (Matrix.diagonal μ) i i * τ i i k := by
  have he : (∑ i, normalizedPhi (Matrix.diagonal μ) i i * τ i i k) =
      cubicD μ τ k-cubicMoment (Matrix.diagonal μ)*(∑ i, μ i*τ i i k)-
      (∑ i, τ i i k)/4 := by
    rw [normalizedPhi_diagonal]
    simp [cubicD, Matrix.diagonal_apply, Fin.sum_univ_succ]
    ring
  rw [he, ht, hw]
  ring

theorem phiNormSq_eq_diagonal_sum (μ : Vector4) :
    phiNormSq (Matrix.diagonal μ) = ∑ i, (normalizedPhi (Matrix.diagonal μ) i i)^2 := by
  unfold phiNormSq
  rw [normalizedPhi_diagonal]
  simp [matrixNormSq, Matrix.diagonal_apply]

/-- Cauchy--Schwarz in the four diagonal coordinates. -/
theorem cubicD_component_sq_bound (μ : Vector4) (τ : Cubic4)
    (ht : ∀ k, ∑ i, τ i i k = 0) (hw : ∀ k, ∑ i, μ i*τ i i k = 0) (k : Fin 4) :
    (cubicD μ τ k)^2 ≤ phiNormSq (Matrix.diagonal μ)*(∑ i, (τ i i k)^2) := by
  rw [cubicD_eq_phi_pairing μ τ ht hw k, phiNormSq_eq_diagonal_sum]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

/-- A denominator-free form of the component estimate in lem:bounds. -/
theorem weighted_cubicD_component_bound (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (k : Fin 4) :
    (μ k)^2*(cubicD μ τ k)^2 ≤ phiNormSq (Matrix.diagonal μ)*repeatedWeight τ k/4 := by
  obtain ⟨_hτ,hμ,hn,_hτn,ht,hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  have htlow := repeatedWeight_lower μ τ had k
  have hm := principal_coordinate_sq_le μ hμ hn k
  have hd := cubicD_component_sq_bound μ τ ht hw k
  have hz : 0 ≤ ∑ i, (τ i i k)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hp := phiNormSq_nonneg (Matrix.diagonal μ)
  have htheta : 4*(μ k)^2*(∑ i, (τ i i k)^2) ≤ repeatedWeight τ k := by
    nlinarith [mul_nonneg (show 0 ≤ 3/2-2*(μ k)^2 by linarith) hz]
  have h1 := mul_le_mul_of_nonneg_left hd (sq_nonneg (μ k))
  have h2 := mul_le_mul_of_nonneg_left htheta hp
  nlinarith

/-- The full bound |Ad|^2 <= p/4 from lem:bounds in the principal frame.
This includes p=0, zero or repeated eigenvalues, and nonzero d. -/
theorem cubicD_weighted_norm_bound (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) :
    (Matrix.diagonal μ *ᵥ cubicD μ τ) ⬝ᵥ (Matrix.diagonal μ *ᵥ cubicD μ τ) ≤
      phiNormSq (Matrix.diagonal μ)/4 := by
  obtain ⟨hτ,_hμ,_hn,hτn,_ht,_hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) =>
    weighted_cubicD_component_bound μ τ had k
  have hsupport := repeatedWeight_sum_le τ hτ hτn
  have hp := phiNormSq_nonneg (Matrix.diagonal μ)
  have hr : (∑ k, phiNormSq (Matrix.diagonal μ)*repeatedWeight τ k/4) =
      phiNormSq (Matrix.diagonal μ)*(∑ k, repeatedWeight τ k)/4 := by
    simp [Finset.sum_div, Finset.mul_sum]
  rw [hr] at hsum
  have he : (Matrix.diagonal μ *ᵥ cubicD μ τ) ⬝ᵥ (Matrix.diagonal μ *ᵥ cubicD μ τ) =
      ∑ k, (μ k)^2*(cubicD μ τ k)^2 := by
    simp [dotProduct, Matrix.mulVec, Matrix.diagonal_apply, Fin.sum_univ_succ]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hsupport hp]

end
end SecondPinching
