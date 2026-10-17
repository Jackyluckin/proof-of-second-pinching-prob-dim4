import SecondPinching.IntrinsicTrial

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The complete W_t, including all three corrections, expressed without
choosing eigenvectors. Agreement with every principal frame is proved for all
real t. These are pointwise algebraic statements, not geometric mean identities. -/

def intrinsicCorrectionL4 (A : Matrix4) (τ : Cubic4) (t : ℝ) : ℝ :=
  t*(2*intrinsicCubicA A τ+intrinsicCubicB A τ-quarticMoment A)

def intrinsicCorrectionL3 (A : Matrix4) (τ : Cubic4) (t : ℝ) : ℝ :=
  t*(-(cubicMoment A)^2+2*cubicMoment A*intrinsicCubicC A τ+
    3*(intrinsicCubicD A τ ⬝ᵥ intrinsicCubicD A τ))

def intrinsicCorrectionJ (A : Matrix4) (τ : Cubic4) (t : ℝ) : ℝ :=
  t*(intrinsicCubicA A τ-2*intrinsicCubicB A τ)-phiNormSq A-t/4

/-- Exactly eq:Wt, with Q from eq:Qt and the fixed matrix B=B_(1/2). -/
def intrinsicPinchingW (A : Matrix4) (τ : Cubic4) (t : ℝ) : ℝ :=
  3*t*(intrinsicCubicA A τ-2*intrinsicCubicB A τ)+t*(35*t-28)/16-
    (3/2 : ℝ)*phiNormSq A-intrinsicTrialQ A τ t-
    (89/8 : ℝ)*intrinsicCorrectionL4 A τ t+16*intrinsicCorrectionL3 A τ t+
    (13/4 : ℝ)*intrinsicCorrectionJ A τ t

theorem frame_intrinsicCorrectionL4 (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicCorrectionL4 (frameMatrix O A) (frameCubic O τ) t = intrinsicCorrectionL4 A τ t := by
  simp only [intrinsicCorrectionL4, frame_intrinsicCubicA O hO, frame_intrinsicCubicB O hO,
    frame_quarticMoment O hO]

theorem frame_intrinsicCorrectionL3 (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicCorrectionL3 (frameMatrix O A) (frameCubic O τ) t = intrinsicCorrectionL3 A τ t := by
  simp only [intrinsicCorrectionL3, frame_cubicMoment O hO, frame_intrinsicCubicC O hO,
    frame_intrinsicCubicD O hO, frameVector_inner O hO]

theorem frame_intrinsicCorrectionJ (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (t : ℝ) :
    intrinsicCorrectionJ (frameMatrix O A) (frameCubic O τ) t = intrinsicCorrectionJ A τ t := by
  simp only [intrinsicCorrectionJ, frame_intrinsicCubicA O hO, frame_intrinsicCubicB O hO,
    frame_phiNormSq O hO]

/-- Invariance of the full scalar under the entire orthogonal group. The
ambient identity needs only cubic symmetry; paper admissibility implies it. -/
theorem frame_intrinsicPinchingW (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (hτ : CubicSymmetric τ) (t : ℝ) :
    intrinsicPinchingW (frameMatrix O A) (frameCubic O τ) t = intrinsicPinchingW A τ t := by
  simp only [intrinsicPinchingW, frame_intrinsicCubicA O hO, frame_intrinsicCubicB O hO,
    frame_phiNormSq O hO, frame_intrinsicTrialQ O hO A τ hτ,
    frame_intrinsicCorrectionL4 O hO, frame_intrinsicCorrectionL3 O hO,
    frame_intrinsicCorrectionJ O hO]

theorem intrinsicCorrectionL4_diagonal (μ : Vector4) (τ : Cubic4) (hτ : CubicSymmetric τ) (t : ℝ) :
    intrinsicCorrectionL4 (Matrix.diagonal μ) τ t = correctionL4 μ τ t := by
  simp only [intrinsicCorrectionL4, intrinsicCubicA_diagonal μ τ hτ,
    intrinsicCubicB_diagonal μ τ hτ, correctionL4]

theorem intrinsicCorrectionL3_diagonal (μ : Vector4) (τ : Cubic4) (hτ : CubicSymmetric τ) (t : ℝ) :
    intrinsicCorrectionL3 (Matrix.diagonal μ) τ t = correctionL3 μ τ t := by
  simp only [intrinsicCorrectionL3, intrinsicCubicC_diagonal μ τ hτ,
    intrinsicCubicD_diagonal, correctionL3]

theorem intrinsicCorrectionJ_diagonal (μ : Vector4) (τ : Cubic4) (hτ : CubicSymmetric τ) (t : ℝ) :
    intrinsicCorrectionJ (Matrix.diagonal μ) τ t = correctionJ μ τ t := by
  simp only [intrinsicCorrectionJ, intrinsicCubicA_diagonal μ τ hτ,
    intrinsicCubicB_diagonal μ τ hτ, correctionJ]

/-- Equality with the existing principal-frame definition, on exactly the
manuscript admissible domain and for every real parameter. -/
theorem intrinsicPinchingW_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (t : ℝ) :
    intrinsicPinchingW (Matrix.diagonal μ) τ t = pinchingW μ τ t := by
  simp only [intrinsicPinchingW, intrinsicCubicA_diagonal μ τ had.2.1,
    intrinsicCubicB_diagonal μ τ had.2.1, intrinsicTrialQ_diagonal μ τ had,
    intrinsicCorrectionL4_diagonal μ τ had.2.1, intrinsicCorrectionL3_diagonal μ τ had.2.1,
    intrinsicCorrectionJ_diagonal μ τ had.2.1, pinchingW]

/-- Every orthogonal principal frame computes this same scalar. No choice or
regularity of an eigenframe field enters either side of this pointwise identity. -/
theorem intrinsicPinchingW_in_principal_frame (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (O : Matrix4) (hO : OrthogonalFrame O)
    (μ : Vector4) (hdiag : frameMatrix O A = Matrix.diagonal μ) (t : ℝ) :
    intrinsicPinchingW A τ t = pinchingW μ (frameCubic O τ) t := by
  have ha := (admissible_iff_paper _ _).mp (paperAdmissible_in_principal_frame A τ had O hO μ hdiag)
  rw [← intrinsicPinchingW_diagonal μ (frameCubic O τ) ha t, ← hdiag,
    frame_intrinsicPinchingW O hO A τ had.2.1]

/-- Repeated and zero eigenvalues require no separate choice rule: two
arbitrary orthogonal diagonalizers give identical W_t values. -/
theorem pinchingW_principal_frame_independence (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (O₁ O₂ : Matrix4)
    (hO₁ : OrthogonalFrame O₁) (hO₂ : OrthogonalFrame O₂) (μ₁ μ₂ : Vector4)
    (h₁ : frameMatrix O₁ A = Matrix.diagonal μ₁)
    (h₂ : frameMatrix O₂ A = Matrix.diagonal μ₂) (t : ℝ) :
    pinchingW μ₁ (frameCubic O₁ τ) t = pinchingW μ₂ (frameCubic O₂ τ) t := by
  rw [← intrinsicPinchingW_in_principal_frame A τ had O₁ hO₁ μ₁ h₁,
    ← intrinsicPinchingW_in_principal_frame A τ had O₂ hO₂ μ₂ h₂]

/-- The same function of t, with A,tau and therefore B fixed. -/
theorem intrinsicPinchingW_function_in_principal_frame (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (O : Matrix4) (hO : OrthogonalFrame O)
    (μ : Vector4) (hdiag : frameMatrix O A = Matrix.diagonal μ) :
    intrinsicPinchingW A τ = pinchingW μ (frameCubic O τ) := by
  funext t
  exact intrinsicPinchingW_in_principal_frame A τ had O hO μ hdiag t

theorem intrinsicPinchingW_zero_bound (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ) :
    intrinsicPinchingW A τ 0 ≤ -(75/32 : ℝ)*phiNormSq A ∧ -(75/32 : ℝ)*phiNormSq A ≤ 0 := by
  obtain ⟨O,μ,hO,hdiag,ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  have hb := pinchingW_zero_bound μ (frameCubic O τ) ha
  rw [← intrinsicPinchingW_in_principal_frame A τ had O hO μ hdiag, ← hdiag,
    frame_phiNormSq O hO] at hb
  exact hb

theorem intrinsicPinchingW_second_derivative_bound (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) (t : ℝ) :
    (1/3 : ℝ) ≤ deriv (deriv (intrinsicPinchingW A τ)) t := by
  obtain ⟨O,μ,hO,hdiag,ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  rw [intrinsicPinchingW_function_in_principal_frame A τ had O hO μ hdiag]
  exact pinchingW_second_derivative_bound μ (frameCubic O τ) ha t

theorem intrinsicPinchingW_convex (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ) :
    ConvexOn ℝ Set.univ (intrinsicPinchingW A τ) := by
  obtain ⟨O,μ,hO,hdiag,ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  rw [intrinsicPinchingW_function_in_principal_frame A τ had O hO μ hdiag]
  exact pinchingW_convex μ (frameCubic O τ) ha

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

/-- The endpoint for the single intrinsic scalar, under all five unchanged
finite-check families. This does not accept a concrete released data instance. -/
theorem intrinsic_endpoint_of_finite_certificate (A : Matrix4) (τ : Cubic4)
    (had : PaperAdmissible A τ) : intrinsicPinchingW A τ (1/2) ≤ -(1/10000 : ℝ) := by
  obtain ⟨O,μ,hO,hdiag,_ha⟩ := paperAdmissible_orthogonal_diagonalization A τ had
  rw [intrinsicPinchingW_in_principal_frame A τ had O hO μ hdiag]
  exact orthogonal_endpoint_of_finite_certificate P C Q V sigma hP hexp hs hcoeff hblocks
    A τ had O hO μ hdiag

end FiniteInputs
end
end SecondPinching
