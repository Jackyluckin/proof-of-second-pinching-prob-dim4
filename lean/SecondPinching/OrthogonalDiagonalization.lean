import SecondPinching.FrameProjection
import SecondPinching.DiagonalEndpoint

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Pointwise spectral reduction of the manuscript's arbitrary admissible pair.
No global frame, regular eigenvalue multiplicity, or distinctness is assumed. -/

/-- The real spectral theorem, in the same row convention as frameCubic. -/
theorem symmetric_orthogonal_diagonalization (A : Matrix4) (hA : A.IsSymm) :
    ∃ (Q : Matrix4) (μ : Vector4), OrthogonalFrame Q ∧ frameMatrix Q A = Matrix.diagonal μ := by
  let hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  let O : Matrix4 := hH.eigenvectorUnitary
  refine ⟨Oᵀ,hH.eigenvalues,?_,?_⟩
  · change O * Oᵀ = 1
    simpa only [O, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hH.eigenvectorUnitary
  · have hs := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa only [frameMatrix_eq_conjugate, Matrix.transpose_transpose,
      Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp] using hs

/-- Admissibility is transported with the same orthogonal matrix as A. -/
theorem paperAdmissible_orthogonal_diagonalization (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) :
    ∃ (Q : Matrix4) (μ : Vector4), OrthogonalFrame Q ∧
      frameMatrix Q A = Matrix.diagonal μ ∧ PaperAdmissible (Matrix.diagonal μ) (frameCubic Q τ) := by
  obtain ⟨Q,μ,hQ,hdiag⟩ := symmetric_orthogonal_diagonalization A had.1
  refine ⟨Q,μ,hQ,hdiag,?_⟩
  rw [← hdiag]
  exact (paperAdmissible_frame_iff Q hQ A τ).mpr had

/-- Any principal frame satisfies the exact hypotheses of the diagonal Lean interface. -/
theorem paperAdmissible_in_principal_frame (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (μ : Vector4) (hdiag : frameMatrix Q A = Matrix.diagonal μ) :
    Admissible (Matrix.diagonal μ) (frameCubic Q τ) := by
  apply (admissible_iff_paper _ _).mpr
  rw [← hdiag]
  exact (paperAdmissible_frame_iff Q hQ A τ).mpr had

/-- Complete chart coverage after the pointwise orthogonal reduction. The signed
permutation is recorded separately; no smooth choice of any frame is asserted. -/
theorem paperAdmissible_orthogonal_chart (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) :
    ∃ (O : Matrix4) (μ : Vector4) (s : ℝ) (e : Equiv.Perm (Fin 4))
      (r y : ℝ) (x : Fin 12 → ℝ),
      OrthogonalFrame O ∧ frameMatrix O A = Matrix.diagonal μ ∧
      (s = 1 ∨ s = -1) ∧ r ∈ Set.Icc (0 : ℝ) 1 ∧ y ∈ Set.Icc (0 : ℝ) 1 ∧ x ≠ 0 ∧
      signedSpectrum s e μ =
        (fun i => spectralVector r y i / Real.sqrt (spectralScale r y)) ∧
      permuteCubic e (frameCubic O τ) = normalizedChartCubic r y x := by
  obtain ⟨O,μ,hO,hdiag,ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  obtain ⟨s,e,r,y,x,hs,hr,hy,hx,hμ,hτ⟩ := paperAdmissible_diagonal_chart μ (frameCubic O τ) ha
  exact ⟨O,μ,s,e,r,y,x,hO,hdiag,hs,hr,hy,hx,hμ,hτ⟩

/-- The prescribed contractions and ordered norm are the same data in a
principal frame. The geometric origin of V remains an explicit separate issue. -/
theorem contractions_in_principal_frame (A E : Matrix4) (τ : Cubic4) (b₀ : Vector4)
    (V : Fourth4) (hV : TraceFreeFourth V) (hE : weightedTrace A V = E)
    (hb : cubicContraction τ V = b₀) (O : Matrix4) (hO : OrthogonalFrame O)
    (μ : Vector4) (hdiag : frameMatrix O A = Matrix.diagonal μ) :
    TraceFreeFourth (frameFourth O V) ∧
      weightedTrace (Matrix.diagonal μ) (frameFourth O V) = frameMatrix O E ∧
      cubicContraction (frameCubic O τ) (frameFourth O V) = frameVector O b₀ ∧
      fourthNormSq (frameFourth O V) = fourthNormSq V := by
  refine ⟨frameFourth_traceFree O hO V hV,?_,?_,frameFourth_normSq O hO V⟩
  · rw [← hdiag,frameFourth_weightedTrace O hO,hE]
  · rw [frameFourth_cubicContraction O hO,hb]

section FiniteInputs
variable
    (P : MvPolynomial (Fin 14) ℚ)
    (C : Fin 24 → ControlIndex → MvPolynomial (Fin 12) ℚ)
    (Q V : Fin 24 → ControlIndex → (b : Fin 8) →
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
      (Q leaf ij b) (V leaf ij b) = true)

include P C Q V sigma hP hexp hs hcoeff hblocks

/-- The exact endpoint bound in every orthogonal principal frame of an
arbitrary manuscript-admissible pair, from the unchanged finite check families.
This does not assert a new intrinsic definition of W or accept concrete arrays. -/
theorem orthogonal_endpoint_of_finite_certificate
    (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ)
    (O : Matrix4) (hO : OrthogonalFrame O) (μ : Vector4)
    (hdiag : frameMatrix O A = Matrix.diagonal μ) :
    pinchingW μ (frameCubic O τ) (1/2) ≤ -(1/10000 : ℝ) := by
  apply diagonal_endpoint_of_finite_certificate P C Q V sigma hP hexp hs hcoeff hblocks
  exact (admissible_iff_paper _ _).mp
    (paperAdmissible_in_principal_frame A τ had O hO μ hdiag)

end FiniteInputs
end
end SecondPinching
