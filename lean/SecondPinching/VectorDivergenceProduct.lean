import SecondPinching.ImmersionScalarCalculus

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem fderiv_mulVec_component (A : Chart4 → Matrix4) (X : Chart4 → Vector4)
    (x v : Chart4) (hA : DifferentiableAt ℝ A x) (hX : DifferentiableAt ℝ X x) (i : Fin 4) :
    fderiv ℝ (fun y => (A y*ᵥX y) i) x v =
      (matrixDerivative A x v*ᵥX x) i+∑ r, A x i r*fderiv ℝ (fun y => X y r) x v := by
  have ha (r : Fin 4) := differentiableAt_pi.mp (differentiableAt_pi.mp hA i) r
  have hx (r : Fin 4) := differentiableAt_pi.mp hX r
  simp only [Matrix.mulVec,dotProduct]
  erw [fderiv_fun_sum (u := Finset.univ) (fun r _ => (ha r).mul (hx r))]
  simp only [sum_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro r _
  erw [fderiv_fun_mul (ha r) (hx r)]
  simp only [add_apply,smul_apply,smul_eq_mul,matrixDerivative]
  ring

theorem mulVec_connection_cancellation (O A U : Matrix4) (v z : Vector4) (hO : Oᵀ = -O) :
    (O*A+A*Oᵀ+U)*ᵥv+A*ᵥ(O*ᵥv+z) = O*ᵥ(A*ᵥv)+U*ᵥv+A*ᵥz := by
  rw [hO]
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.add_apply,Matrix.neg_apply,
    Pi.add_apply,Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton]
  ring

/-- Divergence of A X from the actual moving connection and the two
covariant residuals U and Z. All connection terms cancel before taking the trace. -/
theorem immersionVectorDivergence_mulVec (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (A : Chart4 → Matrix4) (X : Chart4 → Vector4) (x : Chart4) (hx : x ∈ F.domain)
    (hA : DifferentiableAt ℝ A x) (hX : DifferentiableAt ℝ X x)
    (U : Fin 4 → Matrix4) (Z : Matrix4)
    (hdA : ∀ k, matrixDerivative A x (e.coefficients x k) =
      immersionFrameConnection F e x k*A x+A x*(immersionFrameConnection F e x k)ᵀ+U k)
    (hdX : ∀ i k, fderiv ℝ (fun y => X y i) x (e.coefficients x k) =
      (immersionFrameConnection F e x k*ᵥX x) i+Z i k) :
    immersionVectorDivergence F e (fun y => A y*ᵥX y) x =
      (∑ k, (U k*ᵥX x) k)+(∑ k, ∑ r, A x k r*Z r k) := by
  have hd (i k : Fin 4) : fderiv ℝ (fun y => (A y*ᵥX y) i) x (e.coefficients x k) =
      (immersionFrameConnection F e x k*ᵥ(A x*ᵥX x)) i+
        (U k*ᵥX x) i+(A x*ᵥ(fun r => Z r k)) i := by
    rw [fderiv_mulVec_component A X x (e.coefficients x k) hA hX i,hdA k]
    have he : (∑ r, A x i r*fderiv ℝ (fun y => X y r) x (e.coefficients x k)) =
        (A x*ᵥ(immersionFrameConnection F e x k*ᵥX x+(fun r => Z r k))) i := by
      simp only [hdX,Matrix.mulVec,dotProduct,Pi.add_apply]
    rw [he]
    exact congrFun (mulVec_connection_cancellation _ _ _ _ _ (immersionFrameConnection_skew F e x hx k)) i
  unfold immersionVectorDivergence
  simp only [hd]
  change (∑ k, ((∑ r, immersionFrameConnection F e x k k r*(A x*ᵥX x) r)+
    (U k*ᵥX x) k+(∑ r, A x k r*Z r k)-(∑ r, immersionFrameConnection F e x k k r*(A x*ᵥX x) r))) = _
  have he (a b c : ℝ) : a+b+c-a=b+c := by ring
  simp only [he,Finset.sum_add_distrib]

end
end SecondPinching
