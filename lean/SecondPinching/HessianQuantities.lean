import SecondPinching.JointEstimate

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-- The cubic trace m, eq:moments; no constancy is assumed. -/
def cubicMoment (A : Matrix4) : ℝ := Matrix.trace (A^3)

/-- The fourth trace u, eq:moments. -/
def quarticMoment (A : Matrix4) : ℝ := Matrix.trace (A^4)

/-- The matrix Phi, eq:phi, defined before imposing admissibility. -/
def normalizedPhi (A : Matrix4) : Matrix4 :=
  A^2 - cubicMoment A • A - (1/4 : ℝ) • (1 : Matrix4)

/-- The paper's p is the actual squared ordered-index norm of Phi. -/
def phiNormSq (A : Matrix4) : ℝ := matrixNormSq (normalizedPhi A)

/-- The contraction a in eq:abc, in a principal frame. -/
def cubicA (μ : Vector4) (τ : Cubic4) : ℝ :=
  ∑ i, ∑ j, ∑ k, (μ i)^2 * (τ i j k)^2

/-- The contraction b in eq:abc, in a principal frame. -/
def cubicB (μ : Vector4) (τ : Cubic4) : ℝ :=
  ∑ i, ∑ j, ∑ k, μ i * μ j * (τ i j k)^2

/-- The vector d, eq:d. Its vanishing is never required. -/
def cubicD (μ : Vector4) (τ : Cubic4) : Vector4 :=
  fun k => ∑ i, (μ i)^2 * τ i i k

/-- Psi in eq:Edefinitions; R is the previously defined cubic Gram matrix. -/
def hessianPsi (A : Matrix4) (τ : Cubic4) : Matrix4 :=
  (1/4 : ℝ) • A^2 + (3/16 : ℝ) • (1 : Matrix4) - cubicGramMatrix τ

/-- E_t in eq:Edefinitions, for every real t. -/
def hessianE (A : Matrix4) (τ : Cubic4) (t : ℝ) : Matrix4 :=
  (1/2 : ℝ) • normalizedPhi A + t • hessianPsi A τ

/-- b_0 = -3 A d / 2 in the paper's principal frame. -/
def hessianB0 (μ : Vector4) (τ : Cubic4) : Vector4 :=
  fun l => -(3/2 : ℝ) * μ l * cubicD μ τ l

theorem cubicMoment_diagonal (μ : Vector4) :
    cubicMoment (Matrix.diagonal μ) = ∑ i, (μ i)^3 := by
  simp [cubicMoment, Matrix.diagonal_pow, Matrix.trace, Matrix.diag]

theorem quarticMoment_diagonal (μ : Vector4) :
    quarticMoment (Matrix.diagonal μ) = ∑ i, (μ i)^4 := by
  simp [quarticMoment, Matrix.diagonal_pow, Matrix.trace, Matrix.diag]

theorem phiNormSq_nonneg (A : Matrix4) : 0 ≤ phiNormSq A :=
  matrixNormSq_nonneg _

theorem normalizedPhi_diagonal (μ : Vector4) :
    normalizedPhi (Matrix.diagonal μ) = Matrix.diagonal (fun i =>
      (μ i)^2 - cubicMoment (Matrix.diagonal μ) * μ i - 1/4) := by
  ext i j
  by_cases h : i = j <;>
    simp [normalizedPhi, Matrix.diagonal_pow, h]

theorem normalizedPhi_symmetric_diagonal (μ : Vector4) :
    (normalizedPhi (Matrix.diagonal μ)).IsSymm := by
  rw [normalizedPhi_diagonal]
  exact Matrix.isSymm_diagonal _

/-- The first orthogonality identity in eq:phiorth. -/
theorem trace_normalizedPhi_diagonal (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (hn : ∑ i, (μ i)^2 = 1) : Matrix.trace (normalizedPhi (Matrix.diagonal μ)) = 0 := by
  rw [normalizedPhi_diagonal, Matrix.trace_diagonal]
  have he : (∑ i, ((μ i)^2 - cubicMoment (Matrix.diagonal μ) * μ i - 1/4)) =
      (∑ i, (μ i)^2) - cubicMoment (Matrix.diagonal μ) * (∑ i, μ i) - 1 := by
    simp [Fin.sum_univ_succ]
    ring
  rw [he, hμ, hn]
  ring

/-- The second orthogonality identity in eq:phiorth, with the actual matrix trace. -/
theorem trace_mul_normalizedPhi_diagonal (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (hn : ∑ i, (μ i)^2 = 1) :
    Matrix.trace (Matrix.diagonal μ * normalizedPhi (Matrix.diagonal μ)) = 0 := by
  have he : Matrix.trace (Matrix.diagonal μ * normalizedPhi (Matrix.diagonal μ)) =
      (∑ i, (μ i)^3) - cubicMoment (Matrix.diagonal μ) * (∑ i, (μ i)^2) -
        (∑ i, μ i)/4 := by
    rw [normalizedPhi_diagonal]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ]
    ring
  rw [he, hμ, hn, cubicMoment_diagonal]
  ring

theorem cubicGramMatrix_symmetric (τ : Cubic4) : (cubicGramMatrix τ).IsSymm := by
  ext k l
  simp [Matrix.transpose_apply, cubicGramMatrix, mul_comm]

theorem trace_cubicGramMatrix (τ : Cubic4) : Matrix.trace (cubicGramMatrix τ) = cubicNormSq τ := by
  simp [Matrix.trace, Matrix.diag, cubicGramMatrix, cubicNormSq, Fin.sum_univ_succ]
  ring

theorem hessianB0_eq_matrix (μ : Vector4) (τ : Cubic4) :
    hessianB0 μ τ = -(3/2 : ℝ) • (Matrix.diagonal μ *ᵥ cubicD μ τ) := by
  funext l
  simp [hessianB0, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  ring

/-- E_t belongs to the stated codomain Sym^2_0 for every admissible pair and real t. -/
theorem hessianE_codomain_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    (hessianE (Matrix.diagonal μ) τ t).IsSymm ∧
      Matrix.trace (hessianE (Matrix.diagonal μ) τ t) = 0 := by
  obtain ⟨_hτ,hμ,hn,hτn,_ht,_hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  constructor
  · ext i j
    simp only [hessianE, hessianPsi, Matrix.transpose_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      (normalizedPhi_symmetric_diagonal μ).apply, (cubicGramMatrix_symmetric τ).apply,
      identityEntry_comm, Matrix.diagonal_pow]
    by_cases h : i = j <;> simp [h, eq_comm]
  · simp only [hessianE, hessianPsi, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
      trace_normalizedPhi_diagonal μ hμ hn, trace_cubicGramMatrix, hτn,
      Matrix.diagonal_pow, Matrix.trace_diagonal]
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
    right
    simp [Fin.sum_univ_succ] at hn
    linarith

/-- The norm formula in eq:phi, using only trace zero and unit norm. -/
theorem phiNormSq_diagonal (μ : Vector4) (hμ : ∑ i, μ i = 0)
    (hn : ∑ i, (μ i)^2 = 1) :
    phiNormSq (Matrix.diagonal μ) =
      quarticMoment (Matrix.diagonal μ) - (cubicMoment (Matrix.diagonal μ))^2 - 1/4 := by
  have raw : phiNormSq (Matrix.diagonal μ) =
      (∑ i, (μ i)^4) - 2 * (∑ i, (μ i)^3)^2 +
      (∑ i, (μ i)^3)^2 * (∑ i, (μ i)^2) - (∑ i, (μ i)^2)/2 +
      (∑ i, (μ i)^3) * (∑ i, μ i)/2 + 1/4 := by
    simp [phiNormSq, matrixNormSq, normalizedPhi, cubicMoment_diagonal,
      Matrix.diagonal_pow, Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_succ]
    ring
  rw [raw, hμ, hn, cubicMoment_diagonal, quarticMoment_diagonal]
  ring

end
end SecondPinching
