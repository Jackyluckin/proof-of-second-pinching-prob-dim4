import SecondPinching.ImmersionHessianContractions

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
namespace SecondPinching
noncomputable section

theorem weightedTrace_smul_both (a b : ℝ) (h : Matrix4) (H : Fourth4) :
    weightedTrace (a • h) (b • H) = (a*b) • weightedTrace h H := by
  ext k l
  simp only [weightedTrace, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

theorem cubicContraction_smul_both (a b : ℝ) (T : Cubic4) (H : Fourth4) :
    cubicContraction (a • T) (b • H) = (a*b) • cubicContraction T H := by
  funext l
  simp only [cubicContraction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _; ring

theorem cubicGramMatrix_smul (a : ℝ) (T : Cubic4) :
    cubicGramMatrix (a • T) = a^2 • cubicGramMatrix T := by
  ext k l
  simp only [cubicGramMatrix, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- Exact normalization of the three raw contractions. Positivity S>4 is
used only to justify the square roots and the coefficient -t. -/
theorem hessianContractions_normalize (S : ℝ) (hS : 4 < S) (h : Matrix4) (T : Cubic4) (H : Fourth4)
    (htrace : ordinaryTrace H = 0)
    (hweighted : weightedTrace h H = -cubicGramMatrix T)
    (hcubic : cubicContraction T H = 0) :
    ordinaryTrace (normalizeFourth S H) = 0 ∧
    weightedTrace (normalizeSecond S h) (normalizeFourth S H) =
      (-pinchingParameter S) • cubicGramMatrix (normalizeThird S T) ∧
    cubicContraction (normalizeThird S T) (normalizeFourth S H) = 0 := by
  obtain ⟨ha,hb,hc,ha2,hb2⟩ := normalization_denominators hS
  have hs : S ≠ 0 := ne_of_gt (by linarith)
  have hd : S-4 ≠ 0 := ne_of_gt (by linarith)
  have hcoef : -((Real.sqrt S)⁻¹ * (S*Real.sqrt S)⁻¹) =
      -pinchingParameter S * ((Real.sqrt (S*(S-4)))⁻¹)^2 := by
    unfold pinchingParameter
    rw [inv_pow, hb2]
    field_simp [ha.ne', hs, hd]
    nlinarith [ha2]
  refine ⟨?_, ?_, ?_⟩
  · change ordinaryTraceLinear ((S*Real.sqrt S)⁻¹ • H) = 0
    rw [map_smul]
    change (S*Real.sqrt S)⁻¹ • ordinaryTrace H = 0
    rw [htrace, smul_zero]
  · unfold normalizeSecond normalizeFourth normalizeThird
    rw [weightedTrace_smul_both, hweighted, smul_neg, cubicGramMatrix_smul,
      smul_smul, ← neg_smul, hcoef]
  · unfold normalizeThird normalizeFourth
    rw [cubicContraction_smul_both, hcubic, smul_zero]

/-- eq:rawtraces for the actual normalized Hessian. Local Simons is explicit;
no raw or normalized Hessian contraction is an input. -/
theorem immersionNormalized_hessian_contractions (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hS : 4 < S)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (hSimons : ∀ y ∈ F.domain, cubicNormSq (immersionFrameThird F e y) = S*(S-4))
    (x : Chart4) (hx : x ∈ F.domain) :
    ordinaryTrace (immersionNormalizedD F e S x) = 0 ∧
    weightedTrace (immersionNormalizedA F e S x) (immersionNormalizedD F e S x) =
      (-pinchingParameter S) • cubicGramMatrix (immersionNormalizedTau F e S x) ∧
    cubicContraction (immersionNormalizedTau F e S x) (immersionNormalizedD F e S x) = 0 := by
  apply hessianContractions_normalize S hS
  · exact immersionFrameFourth_trace_of_minimality F e hminimal x hx
  · exact immersionFrameFourth_weighted_of_constant_norm F e S hSnorm x hx
  · exact immersionFrameFourth_cubic_of_constant_norm_germ F e (S*(S-4)) x hx
      (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) hSimons)

end
end SecondPinching
