import SecondPinching.HessianQuantities

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- The symmetry of the first three slots available for the normalized Hessian. -/
def FirstThreeSymmetric (D : Fourth4) : Prop :=
  (∀ i j k l, D i j k l = D j i k l) ∧
  (∀ i j k l, D i j k l = D i k j l)

/-- The two adjacent swaps mean full symmetry of the first three slots. -/
theorem firstThreeSymmetric_iff (D : Fourth4) :
    FirstThreeSymmetric D ↔ ∀ l, CubicSymmetric (fun i j k => D i j k l) := by
  constructor
  · intro h l
    exact (cubicSymmetric_iff_swaps _).mpr ⟨fun i j k => h.1 i j k l,
      fun i j k => h.2 i j k l⟩
  · intro h
    exact ⟨fun i j k l => cubicSymmetric_swap12 (h l) i j k,
      fun i j k l => cubicSymmetric_swap23 (h l) i j k⟩

/-- The component C_iijj, before kappa is replaced by (1-t)/4. -/
def curvaturePair (μ : Vector4) (κ : ℝ) (i j : Fin 4) : ℝ :=
  (1/2 : ℝ) * (μ i - μ j) * (κ + μ i * μ j)

/-- The six signed components in Section 4, including zero on every other multiset. -/
def curvatureCorrection (μ : Vector4) (κ : ℝ) : Fourth4 := fun i j k l =>
  (1 : Matrix4) i j * (1 : Matrix4) k l * curvaturePair μ κ i k +
  (1 : Matrix4) i k * (1 : Matrix4) j l * curvaturePair μ κ i j +
  (1 : Matrix4) j k * (1 : Matrix4) i l * curvaturePair μ κ j i

theorem curvaturePair_self (μ : Vector4) (κ : ℝ) (i : Fin 4) :
    curvaturePair μ κ i i = 0 := by simp [curvaturePair]

theorem curvaturePair_swap (μ : Vector4) (κ : ℝ) (i j : Fin 4) :
    curvaturePair μ κ j i = -curvaturePair μ κ i j := by
  unfold curvaturePair
  ring

theorem curvatureCorrection_firstThree (μ : Vector4) (κ : ℝ) :
    FirstThreeSymmetric (curvatureCorrection μ κ) := by
  constructor <;> intro i j k l
  all_goals fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [curvatureCorrection, curvaturePair, Matrix.one_apply]

/-- All six ordered-index components for a pair of distinct indices. -/
theorem curvatureCorrection_six_components (μ : Vector4) (κ : ℝ)
    (i j : Fin 4) (hij : i ≠ j) :
    curvatureCorrection μ κ i i j j = curvaturePair μ κ i j ∧
    curvatureCorrection μ κ i j i j = curvaturePair μ κ i j ∧
    curvatureCorrection μ κ j i i j = curvaturePair μ κ i j ∧
    curvatureCorrection μ κ j j i i = -curvaturePair μ κ i j ∧
    curvatureCorrection μ κ j i j i = -curvaturePair μ κ i j ∧
    curvatureCorrection μ κ i j j i = -curvaturePair μ κ i j := by
  have hc := curvaturePair_swap μ κ i j
  simp [curvatureCorrection, Matrix.one_apply, hij, Ne.symm hij, hc]

/-- The component formula has no support beyond the three two-pair patterns. -/
theorem curvatureCorrection_off_support (μ : Vector4) (κ : ℝ)
    (i j k l : Fin 4) (h1 : ¬ (i = j ∧ k = l))
    (h2 : ¬ (i = k ∧ j = l)) (h3 : ¬ (j = k ∧ i = l)) :
    curvatureCorrection μ κ i j k l = 0 := by
  simp only [curvatureCorrection, Matrix.one_apply]
  split_ifs <;> simp_all

/-- The four-term symmetrization formula with only the first-three-slot symmetry. -/
theorem symmetrizeFourth_firstThree (D : Fourth4) (hD : FirstThreeSymmetric D) :
    symmetrizeFourth D = fun i j k l =>
      (D i j k l + D i j l k + D i k l j + D j k l i) / 4 := by
  funext i j k l
  unfold symmetrizeFourth
  rw [← fourthSlotPermutations_sum]
  simp only [Fin.sum_univ_succ]
  unfold fourthSlotPermutations
  dsimp
  simp only [hD.1, hD.2]
  ring

/-- The curvature defect has zero full symmetrization. -/
theorem curvatureCorrection_symmetrize (μ : Vector4) (κ : ℝ) :
    symmetrizeFourth (curvatureCorrection μ κ) = 0 := by
  rw [symmetrizeFourth_firstThree _ (curvatureCorrection_firstThree μ κ)]
  funext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [curvatureCorrection, curvaturePair, Matrix.one_apply] <;> ring

/-- Orthogonality to every fully symmetric tensor, in the ordered-index inner product. -/
theorem curvatureCorrection_orthogonal (μ : Vector4) (κ : ℝ)
    (W : Fourth4) (hW : FourthSymmetric W) :
    fourthInner (curvatureCorrection μ κ) W = 0 := by
  simp [fourthInner, curvatureCorrection, curvaturePair, Matrix.one_apply,
    Fin.sum_univ_succ, fourthSymmetric_swap12 hW, fourthSymmetric_swap23 hW,
    fourthSymmetric_swap34 hW]
  ring

/-- The multiplicity factor 3/4 comes from all six ordered components per unordered pair. -/
theorem curvatureCorrection_norm_raw (μ : Vector4) (κ : ℝ) :
    fourthNormSq (curvatureCorrection μ κ) =
      (3/4 : ℝ) * ∑ i, ∑ j, (μ i - μ j)^2 * (κ + μ i * μ j)^2 := by
  simp [fourthNormSq, curvatureCorrection, curvaturePair, Matrix.one_apply, Fin.sum_univ_succ]
  ring

/-- The finite sum is expanded before either spectral normalization is applied. -/
theorem curvature_sum_expansion (μ : Vector4) (κ : ℝ) :
    (∑ i, ∑ j, (μ i - μ j)^2 * (κ + μ i * μ j)^2) =
      8 * κ^2 * (∑ i, (μ i)^2) - 2 * κ^2 * (∑ i, μ i)^2 +
      4 * κ * (∑ i, (μ i)^3) * (∑ i, μ i) - 4 * κ * (∑ i, (μ i)^2)^2 +
      2 * (∑ i, (μ i)^4) * (∑ i, (μ i)^2) - 2 * (∑ i, (μ i)^3)^2 := by
  simp [Fin.sum_univ_succ]
  ring

/-- The correction norm from Section 4, including t=0 and repeated or zero eigenvalues. -/
theorem curvatureCorrection_norm (μ : Vector4) (t : ℝ)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1) :
    fourthNormSq (curvatureCorrection μ ((1-t)/4)) =
      (3/2 : ℝ) * phiNormSq (Matrix.diagonal μ) + (3/8 : ℝ) * t^2 := by
  rw [curvatureCorrection_norm_raw, curvature_sum_expansion, hμ, hn,
    phiNormSq_diagonal μ hμ hn, cubicMoment_diagonal, quarticMoment_diagonal]
  ring

/-- Ordinary trace before spectral normalization. -/
theorem ordinaryTrace_curvatureCorrection_raw (μ : Vector4) (κ : ℝ) :
    ordinaryTrace (curvatureCorrection μ κ) = Matrix.diagonal (fun k =>
      (κ * (∑ i, μ i) - 4 * κ * μ k + μ k * (∑ i, (μ i)^2) -
        (μ k)^2 * (∑ i, μ i)) / 2) := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [ordinaryTrace, curvatureCorrection, curvaturePair, Matrix.diagonal_apply,
      Matrix.one_apply, Fin.sum_univ_succ] <;> ring

/-- Weighted trace before spectral normalization. -/
theorem weightedTrace_curvatureCorrection_raw (μ : Vector4) (κ : ℝ) :
    weightedTrace (Matrix.diagonal μ) (curvatureCorrection μ κ) =
      Matrix.diagonal (fun k => (κ * (∑ i, (μ i)^2) - κ * μ k * (∑ i, μ i) +
        μ k * (∑ i, (μ i)^3) - (μ k)^2 * (∑ i, (μ i)^2)) / 2) := by
  rw [weightedTrace_diagonal]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [curvatureCorrection, curvaturePair, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;> ring

theorem ordinaryTrace_curvatureCorrection (μ : Vector4) (t : ℝ)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1) :
    ordinaryTrace (curvatureCorrection μ ((1-t)/4)) = (t/2) • Matrix.diagonal μ := by
  rw [ordinaryTrace_curvatureCorrection_raw, hμ, hn]
  ext k l
  by_cases h : k = l <;> simp [Matrix.diagonal_apply, h] <;> ring

theorem weightedTrace_curvatureCorrection (μ : Vector4) (κ : ℝ)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1) :
    weightedTrace (Matrix.diagonal μ) (curvatureCorrection μ κ) =
      (1/2 : ℝ) • (κ • (1 : Matrix4) + cubicMoment (Matrix.diagonal μ) •
        Matrix.diagonal μ - (Matrix.diagonal μ)^2) := by
  rw [weightedTrace_curvatureCorrection_raw, hμ, hn, cubicMoment_diagonal]
  ext k l
  by_cases h : k = l <;>
    simp [Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.one_apply, h] <;> ring

/-- The last-slot Ricci commutator carried by the correction, with the paper's sign. -/
theorem curvatureCorrection_commutator (μ : Vector4) (κ : ℝ) (i j k l : Fin 4) :
    curvatureCorrection μ κ i j k l - curvatureCorrection μ κ i j l k =
      (μ i - μ j) * (κ + μ i * μ j) *
        ((1 : Matrix4) i k * (1 : Matrix4) j l -
         (1 : Matrix4) i l * (1 : Matrix4) j k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [curvatureCorrection, curvaturePair, Matrix.one_apply] <;> ring

/-- The raw cubic contraction keeps both trace sums visible. -/
theorem cubicContraction_curvatureCorrection_raw (μ : Vector4) (κ : ℝ)
    (τ : Cubic4) (hτ : CubicSymmetric τ) :
    cubicContraction τ (curvatureCorrection μ κ) = fun l =>
      (3/2 : ℝ) * ∑ i, (μ i - μ l) * (κ + μ i * μ l) * τ i i l := by
  funext l
  fin_cases l <;>
    simp [cubicContraction, curvatureCorrection, curvaturePair, Matrix.one_apply,
      Fin.sum_univ_succ, cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ] <;>
    (try simp only [cubicSymmetric_swap12 hτ 0 1,
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
      cubicSymmetric_swap23 hτ 3 2 3]) <;> ring

/-- Equation eq:Cthird: N_tau C = 3 A d / 2, generally nonzero. -/
theorem cubicContraction_curvatureCorrection (μ : Vector4) (κ : ℝ)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (ht : ∀ k, ∑ i, τ i i k = 0)
    (hw : ∀ k, ∑ i, μ i * τ i i k = 0) :
    cubicContraction τ (curvatureCorrection μ κ) =
      fun l => (3/2 : ℝ) * μ l * cubicD μ τ l := by
  rw [cubicContraction_curvatureCorrection_raw μ κ τ hτ]
  funext l
  have he : (∑ i, (μ i - μ l) * (κ + μ i * μ l) * τ i i l) =
      κ * (∑ i, μ i * τ i i l) - κ * μ l * (∑ i, τ i i l) +
      μ l * cubicD μ τ l - (μ l)^2 * (∑ i, μ i * τ i i l) := by
    simp [cubicD, Fin.sum_univ_succ]
    ring
  rw [he, ht l, hw l]
  ring

end
end SecondPinching
