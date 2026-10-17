import SecondPinching.RicciFrameAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- The rough Laplacian contracts the two derivative slots, not the first two. -/
def roughTrace (H : Fourth4) : Matrix4 := fun i j => ∑ k, H i j k k

theorem ricciPolynomial_rough_sum (h : Matrix4) (hh : h.IsSymm)
    (htr : Matrix.trace h = 0) (i j : Fin 4) :
    (∑ k, ricciPolynomial 1 h (h*h) i k j k) = (4-matrixNormSq h)*h i j := by
  have hn : Matrix.trace (h*h) = matrixNormSq h := by
    rw [← matrixInner_eq_trace_mul h h hh, matrixInner_self]
  have hc := congrArg (fun M : Matrix4 => M i j) (Matrix.mul_assoc h h h)
  change (∑ k, (h*h) i k*h k j) = ∑ k, h i k*(h*h) k j at hc
  simp only [ricciPolynomial, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : (∑ k, (1 : Matrix4) i k*h k j) = h i j := by simp [Matrix.one_apply]
  have h2 : (∑ k, h i k*(1 : Matrix4) k j) = h i j := by simp [Matrix.one_apply]
  have h3 : (∑ k : Fin 4, h i j*(1 : Matrix4) k k) = 4*h i j := by simp
  rw [h1,h2,h3,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum]
  change h i j-(1 : Matrix4) i j*Matrix.trace h+4*h i j-h i j+
    (∑ k, h i k*(h*h) k j)-h i j*Matrix.trace (h*h)+(h*h) i j*Matrix.trace h-
    (∑ k, (h*h) i k*h k j) = _
  rw [htr,hn,hc]
  ring

/-- Contracting Ricci interchange after Codazzi gives the tensor Simons
identity. The ordinary trace is the differentiated minimality equation. -/
theorem roughTrace_of_ricci (h : Matrix4) (H : Fourth4) (hh : h.IsSymm)
    (htr : Matrix.trace h = 0) (hH : FirstThreeSymmetric H)
    (htrace : ordinaryTrace H = 0)
    (hRicci : ∀ i j k l, H i j k l-H i j l k = ricciPolynomial 1 h (h*h) i j k l) :
    roughTrace H = (4-matrixNormSq h) • h := by
  ext i j
  have he (k : Fin 4) : H i j k k = H k k i j+ricciPolynomial 1 h (h*h) i k j k := by
    have hr := hRicci i k j k
    rw [hH.1 i k k j,hH.2 k i k j] at hr
    rw [hH.2 i j k k]
    linarith
  simp only [roughTrace,he,Finset.sum_add_distrib,Matrix.smul_apply,smul_eq_mul]
  change ordinaryTrace H i j+(∑ k, ricciPolynomial 1 h (h*h) i k j k) = _
  rw [htrace,Matrix.zero_apply,zero_add,ricciPolynomial_rough_sum h hh htr]

theorem trace_weightedTrace_eq_roughPairing (h : Matrix4) (H : Fourth4) :
    Matrix.trace (weightedTrace h H) = matrixInner h (roughTrace H) := by
  simp only [Matrix.trace,Matrix.diag,weightedTrace,matrixInner,roughTrace,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]

theorem simons_norm_of_constant_norm_contraction (h : Matrix4) (T : Cubic4) (H : Fourth4)
    (hweighted : weightedTrace h H = -cubicGramMatrix T)
    (hSimons : roughTrace H = (4-matrixNormSq h) • h) :
    cubicNormSq T = matrixNormSq h*(matrixNormSq h-4) := by
  have he := congrArg Matrix.trace hweighted
  rw [trace_weightedTrace_eq_roughPairing,Matrix.trace_neg,trace_cubicGramMatrix,hSimons,
    matrixInner_smul_right,matrixInner_self] at he
  linarith

end
end SecondPinching
