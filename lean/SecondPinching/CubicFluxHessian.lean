import SecondPinching.TracePowerContractions

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

theorem matrixInner_diagonal_left (μ : Vector4) (A : Matrix4) :
    matrixInner (Matrix.diagonal μ) A = ∑ i, μ i*A i i := by
  simp [matrixInner,Matrix.diagonal_apply]

/-- The paired Ricci identity is used only after all covariant differentiations. -/
theorem hessian_ricci_pair (μ : Vector4) (H : Fourth4) (hH : FirstThreeSymmetric H)
    (hR : HasRicciCommutator μ 1 H) (i k : Fin 4) :
    H i i k k-H k k i i = (μ i-μ k)*(1+μ i*μ k) := by
  by_cases hik : i=k
  · subst k; ring
  · have he := hR i k i k
    rw [hH.2 i k i k,hH.1 i k k i,hH.2 k i k i] at he
    simpa [Matrix.one_apply,hik,Ne.symm hik] using he

theorem ricci_pair_spectral_sum (μ : Vector4) :
    (∑ i, ∑ k, (μ i)^2*μ k*((μ i-μ k)*(1+μ i*μ k))) =
      (∑ i, (μ i)^3)*(∑ i, μ i)-(∑ i, (μ i)^2)^2+
        (∑ i, (μ i)^4)*(∑ i, (μ i)^2)-(∑ i, (μ i)^3)^2 := by
  simp only [Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton]
  ring

/-- The Hessian term in div(h D), in a pointwise principal frame. -/
theorem cubic_flux_hessian_diagonal (μ : Vector4) (T : Cubic4) (H : Fourth4)
    (htr : ∑ i, μ i = 0)
    (hH : FirstThreeSymmetric H) (hR : HasRicciCommutator μ 1 H)
    (hw : weightedTrace (Matrix.diagonal μ) H = -cubicGramMatrix T) :
    matrixInner (Matrix.diagonal μ) (weightedTrace ((Matrix.diagonal μ)^2) H) =
      -intrinsicCubicA (Matrix.diagonal μ) T+
      matrixNormSq (Matrix.diagonal μ)*quarticMoment (Matrix.diagonal μ)-
      (cubicMoment (Matrix.diagonal μ))^2-(matrixNormSq (Matrix.diagonal μ))^2 := by
  have hp (i k : Fin 4) : H i i k k = H k k i i+(μ i-μ k)*(1+μ i*μ k) := by
    linarith [hessian_ricci_pair μ H hH hR i k]
  have hwi (i : Fin 4) : (∑ k, μ k*H k k i i) = -cubicGramMatrix T i i := by
    have he := congrFun (congrFun hw i) i
    rw [weightedTrace_diagonal] at he
    exact he
  have hn : (∑ i, (μ i)^2*cubicGramMatrix T i i) = intrinsicCubicA (Matrix.diagonal μ) T := by
    simp [intrinsicCubicA,Matrix.diagonal_pow,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Matrix.diagonal_apply]
  have he : matrixInner (Matrix.diagonal μ) (weightedTrace ((Matrix.diagonal μ)^2) H) =
      ∑ i, ∑ k, (μ i)^2*μ k*H i i k k := by
    rw [matrixInner_diagonal_left,Matrix.diagonal_pow,weightedTrace_diagonal]
    change (∑ k, μ k*(∑ i, (μ i)^2*H i i k k)) = _
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  have hs : (∑ i, ∑ k, (μ i)^2*μ k*H i i k k) =
      -(∑ i, (μ i)^2*cubicGramMatrix T i i)+
      ∑ i, ∑ k, (μ i)^2*μ k*((μ i-μ k)*(1+μ i*μ k)) := by
    calc
      _ = ∑ i, ∑ k, ((μ i)^2*(μ k*H k k i i)+
          (μ i)^2*μ k*((μ i-μ k)*(1+μ i*μ k))) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro k _
        rw [hp i k]; ring
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        congr 1
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.mul_sum,hwi,mul_neg]
  rw [hs,hn,ricci_pair_spectral_sum,htr,cubicMoment_diagonal,quarticMoment_diagonal,
    matrixNormSq_diagonal]
  ring

/-- The contracted Hessian scalar is invariant under the same orthogonal
frame change on h and every Hessian slot. -/
theorem frame_cubic_flux_hessian (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) (H : Fourth4) :
    matrixInner (frameMatrix Q A) (weightedTrace ((frameMatrix Q A)^2) (frameFourth Q H)) =
      matrixInner A (weightedTrace (A^2) H) := by
  rw [← frameMatrix_pow Q hQ,frameFourth_weightedTrace Q hQ,frameMatrix_inner Q hQ]

/-- Transport the given raw Ricci equality before choosing eigenvectors. -/
theorem frame_hessian_ricci (Q : Matrix4) (hQ : OrthogonalFrame Q) (A : Matrix4) (H : Fourth4)
    (hR : ∀ i j k l, H i j k l-H i j l k = ricciPolynomial 1 A (A*A) i j k l)
    (i j k l : Fin 4) :
    frameFourth Q H i j k l-frameFourth Q H i j l k =
      ricciPolynomial 1 (frameMatrix Q A) (frameMatrix Q A*frameMatrix Q A) i j k l := by
  have he : H-(fun a b c d => H a b d c) = ricciPolynomial 1 A (A*A) := by
    funext a b c d; exact hR a b c d
  have hf := congrArg (frameFourthLinear Q) he
  rw [map_sub] at hf
  change frameFourth Q H-frameFourth Q (fun a b c d => H a b d c) =
    frameFourth Q (ricciPolynomial 1 A (A*A)) at hf
  rw [frameFourth_swap34 Q H,frameFourth_ricciPolynomial,frameMatrix_one Q hQ,
    frameMatrix_mul Q hQ] at hf
  exact congrFun (congrFun (congrFun (congrFun hf i) j) k) l

/-- The full, unnormalized Hessian contraction used in the J divergence.
Trace constraints and Ricci are explicit algebraic premises here; actual
geometric sources are substituted in the immersion theorem. -/
theorem cubic_flux_hessian (A : Matrix4) (T : Cubic4) (H : Fourth4)
    (hA : A.IsSymm) (htr : Matrix.trace A=0)
    (hH : FirstThreeSymmetric H)
    (hR : ∀ i j k l, H i j k l-H i j l k = ricciPolynomial 1 A (A*A) i j k l)
    (hw : weightedTrace A H = -cubicGramMatrix T) :
    matrixInner A (weightedTrace (A^2) H) = -intrinsicCubicA A T+
      matrixNormSq A*quarticMoment A-(cubicMoment A)^2-(matrixNormSq A)^2 := by
  obtain ⟨Q,μ,hQ,hdiag⟩ := symmetric_orthogonal_diagonalization A hA
  have hzero : ∑ i, μ i=0 := by
    rw [← Matrix.trace_diagonal,← hdiag,frameMatrix_trace Q hQ,htr]
  have hw' : weightedTrace (Matrix.diagonal μ) (frameFourth Q H) = -cubicGramMatrix (frameCubic Q T) := by
    rw [← hdiag,frameFourth_weightedTrace Q hQ,hw,frame_cubicGramMatrix Q hQ]
    exact (frameMatrixLinear Q).map_neg _
  have hr' : HasRicciCommutator μ 1 (frameFourth Q H) := by
    intro i j k l
    rw [frame_hessian_ricci Q hQ A H hR,hdiag]
    simpa only [one_smul] using ricciPolynomial_diagonal μ 1 i j k l
  have he := cubic_flux_hessian_diagonal μ (frameCubic Q T) (frameFourth Q H)
    hzero (frameFourth_firstThree Q H hH) hr' hw'
  rw [← hdiag,frame_cubic_flux_hessian Q hQ,frame_intrinsicCubicA Q hQ,
    frameMatrix_normSq Q hQ,frame_quarticMoment Q hQ,frame_cubicMoment Q hQ] at he
  exact he

end
end SecondPinching
