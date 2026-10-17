import SecondPinching.PengTerngExpressions

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem ricciVariation_eq (h U : Matrix4) :
    ricciVariation h U = ricciPolynomial 1 U (h*h)+ricciPolynomial 0 h (U*h+h*U) := by
  funext i j k l
  simp only [ricciVariation,ricciPolynomial,Matrix.zero_apply,zero_mul,mul_zero,
    Pi.add_apply]
  ring

theorem ricciVariation_add (h U V : Matrix4) :
    ricciVariation h (U+V) = ricciVariation h U+ricciVariation h V := by
  funext i j k l
  simp only [ricciVariation,Matrix.add_apply,Matrix.add_mul,Matrix.mul_add,Pi.add_apply]
  ring

/-- The connection acts on every factor of each covariant tensor product. -/
theorem fourthConnectionAction_ricciPolynomial (O g h q : Matrix4) :
    fourthConnectionAction O (ricciPolynomial g h q) =
      ricciPolynomial g (O*h+h*Oᵀ) q+
      ricciPolynomial (O*g+g*Oᵀ) h (O*q+q*Oᵀ) := by
  funext i j k l
  simp only [fourthConnectionAction,cubicConnectionAction,ricciPolynomial,Matrix.add_apply,
    Matrix.mul_apply,Matrix.transpose_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton]
  ring

theorem fourthConnectionAction_ricci (O h : Matrix4) (hO : Oᵀ = -O) :
    fourthConnectionAction O (ricciPolynomial 1 h (h*h)) = ricciVariation h (O*h+h*Oᵀ) := by
  rw [fourthConnectionAction_ricciPolynomial,ricciVariation_eq]
  have hg : O*1+1*Oᵀ = 0 := by rw [mul_one,one_mul,hO,add_neg_cancel]
  have hq : O*(h*h)+(h*h)*Oᵀ = (O*h+h*Oᵀ)*h+h*(O*h+h*Oᵀ) := by
    rw [hO]; noncomm_ring
  rw [hg,hq]

theorem fourthDerivative_ricciPolynomial (g h q : Chart4 → Matrix4) (x v : Chart4)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (hq : DifferentiableAt ℝ q x) :
    fourthDerivative (fun y => ricciPolynomial (g y) (h y) (q y)) x v =
      ricciPolynomial (g x) (matrixDerivative h x v) (q x)+
      ricciPolynomial (matrixDerivative g x v) (h x) (matrixDerivative q x v) := by
  have ha (i j : Fin 4) : DifferentiableAt ℝ (fun y => g y i j) x := by fun_prop
  have hb (i j : Fin 4) : DifferentiableAt ℝ (fun y => h y i j) x := by fun_prop
  have hc (i j : Fin 4) : DifferentiableAt ℝ (fun y => q y i j) x := by fun_prop
  funext i j k l
  simp only [fourthDerivative,ricciPolynomial,matrixDerivative,Pi.add_apply]
  simp (disch := fun_prop) only [fderiv_fun_sub,fderiv_fun_add,fderiv_fun_mul]
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul]
  ring

theorem fourthDerivative_ricci (h : Chart4 → Matrix4) (x v : Chart4)
    (hh : DifferentiableAt ℝ h x) :
    fourthDerivative (fun y => ricciPolynomial 1 (h y) (h y*h y)) x v =
      ricciVariation (h x) (matrixDerivative h x v) := by
  have hq : DifferentiableAt ℝ (fun y => h y*h y) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    simp only [Matrix.mul_apply]; fun_prop
  rw [fourthDerivative_ricciPolynomial _ _ _ x v (differentiableAt_const _) hh hq,
    matrixDerivative_mul _ _ x v hh hh,ricciVariation_eq]
  have hz : matrixDerivative (fun _ : Chart4 => (1 : Matrix4)) x v = 0 := by
    ext i j; simp [matrixDerivative]
  rw [hz]

theorem fourthConnectionAction_swap34 (O : Matrix4) (H : Fourth4) :
    fourthConnectionAction O (fun i j k l => H i j l k) =
      fun i j k l => fourthConnectionAction O H i j l k := by
  funext i j k l
  simp only [fourthConnectionAction,cubicConnectionAction,Pi.add_apply,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib]
  ring

theorem fourthConnectionAction_sub (O : Matrix4) (H K : Fourth4) :
    fourthConnectionAction O (H-K) = fourthConnectionAction O H-fourthConnectionAction O K := by
  funext i j k l
  simp only [fourthConnectionAction,cubicConnectionAction,Pi.add_apply,Pi.sub_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_sub,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  ring

/-- Differentiate the actual Ricci identity covariantly, before choosing a principal frame. -/
theorem immersionFrameFifth_ricci_differentiated (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (i j k l m : Fin 4) :
    immersionFrameFifth F e x i j k l m-immersionFrameFifth F e x i j l k m =
      ricciVariation (immersionFrameSecond F e x)
        (fun a b => immersionFrameThird F e x a b m) i j k l := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hH := (((contDiffOn_immersionFrameForms F e).2.2 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have h1 : DifferentiableAt ℝ (fun y => immersionFrameFourth F e y i j k l) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hH i) j) k) l
  have h2 : DifferentiableAt ℝ (fun y => immersionFrameFourth F e y i j l k) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hH i) j) l) k
  have hg : (fun y => immersionFrameFourth F e y i j k l-immersionFrameFourth F e y i j l k) =ᶠ[𝓝 x]
      fun y => ricciPolynomial 1 (immersionFrameSecond F e y)
        (immersionFrameSecond F e y*immersionFrameSecond F e y) i j k l :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
      (fun y hy => immersionFrameFourth_ricci F e y hy i j k l)
  have hd := congrArg (fun L : Chart4 →L[ℝ] ℝ => L (e.coefficients x m)) hg.fderiv_eq
  rw [fderiv_fun_sub h1 h2] at hd
  change fourthDerivative (immersionFrameFourth F e) x (e.coefficients x m) i j k l-
      fourthDerivative (immersionFrameFourth F e) x (e.coefficients x m) i j l k =
      fourthDerivative (fun y => ricciPolynomial 1 (immersionFrameSecond F e y)
        (immersionFrameSecond F e y*immersionFrameSecond F e y)) x (e.coefficients x m) i j k l at hd
  rw [immersionFrameFourth_frame_derivative F e x hx m,fourthDerivative_ricci _ _ _ hh,
    immersionFrameSecond_frame_derivative F e x hx m,ricciVariation_add,
    ← fourthConnectionAction_ricci _ _ (immersionFrameConnection_skew F e x hx m)] at hd
  have hr : immersionFrameFourth F e x-(fun a b c d => immersionFrameFourth F e x a b d c) =
      ricciPolynomial 1 (immersionFrameSecond F e x)
        (immersionFrameSecond F e x*immersionFrameSecond F e x) := by
    funext a b c d; exact immersionFrameFourth_ricci F e x hx a b c d
  have ha := congrArg (fourthConnectionAction (immersionFrameConnection F e x m)) hr
  rw [fourthConnectionAction_sub,
    fourthConnectionAction_swap34 (immersionFrameConnection F e x m) (immersionFrameFourth F e x)] at ha
  have hav := congrFun (congrFun (congrFun (congrFun ha i) j) k) l
  simp only [Pi.sub_apply] at hav
  simp only [Pi.add_apply] at hd
  change immersionFrameFifth F e x i j k l m-immersionFrameFifth F e x i j l k m =
    ricciVariation (immersionFrameSecond F e x)
      (Matrix.of (fun a b => immersionFrameThird F e x a b m)) i j k l
  linarith

end
end SecondPinching
