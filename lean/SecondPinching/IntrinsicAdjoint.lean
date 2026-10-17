import SecondPinching.IntrinsicJoint

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The adjoint of Z as an actual contraction composition. Its principal-frame
formula is established by uniqueness in Sym^2_0 with the ordered pairing. -/

/-- Z* = T_A P_0 N_tau*, whose range is symmetric and trace free. -/
def intrinsicMixedGramAdjoint (A : Matrix4) (τ : Cubic4) (v : Vector4) : Matrix4 :=
  weightedTrace A (ordinaryTraceFreeProjection (cubicContractionAdjoint τ v))

theorem intrinsicMixedGramAdjoint_codomain (A : Matrix4) (τ : Cubic4)
    (hτ : CubicSymmetric τ) (v : Vector4) :
    (intrinsicMixedGramAdjoint A τ v).IsSymm ∧
      Matrix.trace (intrinsicMixedGramAdjoint A τ v) = 0 :=
  weightedTrace_traceFree _ _ (ordinaryTraceFreeProjection_mem _
    (cubicContractionAdjoint_symmetric τ hτ v))

/-- Adjointness is proved against every symmetric test matrix. Its restriction
to Sym^2_0 is the adjoint used in eq:Zadjoint. -/
theorem intrinsicMixedGramAdjoint_pairing (A : Matrix4) (hA : A.IsSymm)
    (τ : Cubic4) (hτ : CubicSymmetric τ) (v : Vector4)
    (Y : Matrix4) (hY : Y.IsSymm) :
    matrixInner (intrinsicMixedGramAdjoint A τ v) Y = v ⬝ᵥ intrinsicMixedGram A τ Y := by
  unfold intrinsicMixedGramAdjoint intrinsicMixedGram
  rw [← weightedTrace_adjoint_pairing A Y hA hY _
    (ordinaryTraceFreeProjection_mem _ (cubicContractionAdjoint_symmetric τ hτ v)).1,
    ordinaryTraceFreeProjection_self_adjoint _ _ (cubicContractionAdjoint_symmetric τ hτ v)
      (weightedTraceAdjoint_symmetric A Y hA hY), fourthInner_comm,
    cubicContraction_adjoint_pairing τ hτ v _
      (ordinaryTraceFreeProjection_mem _ (weightedTraceAdjoint_symmetric A Y hA hY)).1,
    dotProduct_comm]

theorem matrixNormSq_eq_zero_iff (X : Matrix4) : matrixNormSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    ext i j
    have hi : ∑ j, (X i j)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => sq_nonneg (X i j)))).mp h i (Finset.mem_univ i)
    have hij : (X i j)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (X i j))).mp hi j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hij
  · rintro rfl
    simp [matrixNormSq]

/-- The coordinate adjoint in the manuscript agrees as a matrix, not just
modulo a trace term. Both matrices are in Sym^2_0. -/
theorem intrinsicMixedGramAdjoint_diagonal (μ : Vector4) (τ : Cubic4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ) (v : Vector4) :
    intrinsicMixedGramAdjoint (Matrix.diagonal μ) τ v = mixedGramAdjoint μ τ v := by
  let D := intrinsicMixedGramAdjoint (Matrix.diagonal μ) τ v - mixedGramAdjoint μ τ v
  obtain ⟨hX,hXt⟩ := intrinsicMixedGramAdjoint_codomain (Matrix.diagonal μ) τ had.2.1 v
  obtain ⟨hY,hYt⟩ := mixedGramAdjoint_codomain μ τ had v
  have hD : D.IsSymm := hX.sub hY
  have hDt : Matrix.trace D = 0 := by simp [D, Matrix.trace_sub, hXt, hYt]
  have hz : matrixNormSq D = 0 := by
    rw [← matrixInner_self]
    change matrixInner (intrinsicMixedGramAdjoint (Matrix.diagonal μ) τ v - mixedGramAdjoint μ τ v) D = 0
    rw [matrixInner_sub_left, intrinsicMixedGramAdjoint_pairing _ had.1 τ had.2.1 v D hD,
      intrinsicMixedGram_diagonal μ τ had D hD hDt, mixedGramAdjoint_pairing, sub_self]
  exact sub_eq_zero.mp ((matrixNormSq_eq_zero_iff D).mp hz)

theorem frame_intrinsicMixedGramAdjoint (O : Matrix4) (hO : OrthogonalFrame O)
    (A : Matrix4) (τ : Cubic4) (hτ : CubicSymmetric τ) (v : Vector4) :
    intrinsicMixedGramAdjoint (frameMatrix O A) (frameCubic O τ) (frameVector O v) =
      frameMatrix O (intrinsicMixedGramAdjoint A τ v) := by
  unfold intrinsicMixedGramAdjoint
  rw [← frameFourth_cubicContractionAdjoint O hO τ hτ v,
    ← frameFourth_projection O hO _ (cubicContractionAdjoint_symmetric τ hτ v),
    frameFourth_weightedTrace O hO]

end
end SecondPinching
