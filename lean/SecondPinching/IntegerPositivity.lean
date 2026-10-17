import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Appendix A.2: the integer congruence test

`integer_positivity_test` is the paper lemma. The preceding real-matrix
lemmas prove the criterion without assuming the congruence matrix invertible.
-/

open scoped BigOperators Matrix

namespace SecondPinching

/-- Auxiliary: positive strict row diagonal dominance of a real symmetric
matrix implies positive definiteness. -/
theorem posDef_of_strict_diagonal_dominance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hdiag : ∀ i, ∑ j ∈ Finset.univ.erase i, |M i j| < M i i) :
    M.PosDef := by
  rw [hM.posDef_iff_eigenvalues_pos]
  intro i
  have heig : Module.End.HasEigenvalue (Matrix.toLin' M) (hM.eigenvalues i) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    simpa only [Matrix.spectrum_toLin'] using hM.eigenvalues_mem_spectrum_real i
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball heig
  have hball : |M k k - hM.eigenvalues i| ≤
      ∑ j ∈ Finset.univ.erase k, |M k j| := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hk
  have hle := le_abs_self (M k k - hM.eigenvalues i)
  have hstrict := hdiag k
  linarith

/-- Auxiliary: the real version of Appendix A.2. Invertibility of `V`
is deduced from the tested inequality, rather than assumed. -/
theorem real_congruence_positivity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q V : Matrix ι ι ℝ) (hQ : Q.IsHermitian)
    (hdiag : ∀ i, ∑ j ∈ Finset.univ.erase i, |(V * Q * V.transpose) i j| <
      (V * Q * V.transpose) i i) : Q.PosDef := by
  have hM : (V * Q * V.transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose V hQ
  have hpos := posDef_of_strict_diagonal_dominance _ hM hdiag
  have hdet : (V * Q * V.transpose).det ≠ 0 :=
    ne_of_gt hpos.det_pos
  have hVdet : V.det ≠ 0 := by
    simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hdet).1).1
  have hV : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr (isUnit_iff_ne_zero.mpr hVdet)
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff hV).mp
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hpos

/-- Entrywise inclusion of an integer matrix into real matrices. -/
def integerMatrixToReal {ι : Type*} (Q : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  fun i j => (Q i j : ℝ)

/-- Auxiliary: integer congruence commutes with the inclusion into the reals. -/
theorem integerMatrixToReal_congruence
    {ι : Type*} [Fintype ι] (Q V : Matrix ι ι ℤ) :
    integerMatrixToReal (V * Q * V.transpose) =
      integerMatrixToReal V * integerMatrixToReal Q * (integerMatrixToReal V).transpose := by
  ext i j
  simp [integerMatrixToReal, Matrix.mul_apply, Matrix.transpose_apply]

/-- Paper Lemma A.2, with exactly its integer matrices and row inequalities.
Positive definiteness is asserted over the reals. -/
theorem integer_positivity_test
    (s : ℕ) (_hs : 1 ≤ s) (Q V : Matrix (Fin s) (Fin s) ℤ)
    (hQ : Q.IsSymm)
    (hdiag : ∀ i, ∑ j ∈ Finset.univ.erase i, |(V * Q * V.transpose) i j| <
      (V * Q * V.transpose) i i) :
    (integerMatrixToReal Q).PosDef := by
  have hQR : (integerMatrixToReal Q).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa [integerMatrixToReal] using congrArg (fun a : ℤ => (a : ℝ)) (hQ.apply i j)
  apply real_congruence_positivity (integerMatrixToReal Q) (integerMatrixToReal V) hQR
  intro i
  rw [← integerMatrixToReal_congruence]
  dsimp only [integerMatrixToReal]
  exact_mod_cast hdiag i


/-- Executable exact test for one integer congruence block. Both symmetry
and every row inequality are included in the Boolean result. -/
def integerCertificateCheck (s : ℕ) (Q V : Matrix (Fin s) (Fin s) ℤ) : Bool :=
  decide (Q.IsSymm ∧ ∀ i, ∑ j ∈ Finset.univ.erase i, |(V * Q * V.transpose) i j| <
    (V * Q * V.transpose) i i)

/-- The Boolean test states precisely the hypotheses of Lemma A.2. -/
theorem integerCertificateCheck_iff (s : ℕ) (Q V : Matrix (Fin s) (Fin s) ℤ) :
    integerCertificateCheck s Q V = true ↔
      Q.IsSymm ∧ ∀ i, ∑ j ∈ Finset.univ.erase i, |(V * Q * V.transpose) i j| <
        (V * Q * V.transpose) i i := by
  simp only [integerCertificateCheck, decide_eq_true_eq]

/-- Soundness of the exact Boolean checker. The conclusion is a real
positive-definiteness proof, not a successful external program exit code. -/
theorem integerCertificateCheck_sound (s : ℕ) (hs : 1 ≤ s)
    (Q V : Matrix (Fin s) (Fin s) ℤ)
    (h : integerCertificateCheck s Q V = true) :
    (integerMatrixToReal Q).PosDef := by
  obtain ⟨hQ, hdiag⟩ := (integerCertificateCheck_iff s Q V).mp h
  exact integer_positivity_test s hs Q V hQ hdiag

end SecondPinching
