import SecondPinching.MovingFrameFourth

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 3600000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

def roughTraceFifth (K : Fifth4) : Cubic4 := fun i j k => ∑ l, K i j k l l

theorem cubicInner_add_right (T U V : Cubic4) :
    cubicInner T (U+V) = cubicInner T U+cubicInner T V := by
  simp only [cubicInner,Pi.add_apply,mul_add,Finset.sum_add_distrib]

theorem cubicInner_add_left (T U V : Cubic4) :
    cubicInner (T+U) V = cubicInner T V+cubicInner U V := by
  simp only [cubicInner,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem cubicInner_sum_smul (T : Cubic4) (c : Fin 4 → ℝ) (U : Fin 4 → Cubic4) :
    cubicInner T (∑ r, c r • U r) = ∑ r, c r*cubicInner T (U r) := by
  simp only [cubicInner,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _; ring

theorem skew_cubicConnection_pairing (O : Matrix4) (T U : Cubic4)
    (hO : Oᵀ = -O) (hT : CubicSymmetric T) (hU : CubicSymmetric U) :
    cubicInner (cubicConnectionAction O T) U+cubicInner T (cubicConnectionAction O U) = 0 := by
  have hadd : CubicSymmetric (T+U) := by
    apply (cubicSymmetric_iff_swaps _).mpr
    constructor
    · intro i j k; simp only [Pi.add_apply,cubicSymmetric_swap12 hT i j k,cubicSymmetric_swap12 hU i j k]
    · intro i j k; simp only [Pi.add_apply,cubicSymmetric_swap23 hT i j k,cubicSymmetric_swap23 hU i j k]
  have ha := skew_cubicConnectionAction_inner O (T+U) hO hadd
  have he : cubicConnectionAction O (T+U) = cubicConnectionAction O T+cubicConnectionAction O U :=
    (cubicActionLinear O).map_add T U
  rw [he,cubicInner_add_left,cubicInner_add_right,cubicInner_add_right,
    skew_cubicConnectionAction_inner O T hO hT,skew_cubicConnectionAction_inner O U hO hU] at ha
  have hc : cubicInner U (cubicConnectionAction O T) = cubicInner (cubicConnectionAction O T) U := by
    simp only [cubicInner,mul_comm]
  rw [hc] at ha
  linarith

theorem fourthConnectionAction_last_cubic (O : Matrix4) (H : Fourth4) (l : Fin 4) :
    (fun i j k => fourthConnectionAction O H i j k l : Cubic4) =
      cubicConnectionAction O (fun i j k => H i j k l)+∑ r, O l r • (fun i j k => H i j k r) := by
  funext i j k
  simp only [fourthConnectionAction,cubicConnectionAction,Pi.add_apply,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib]
  ring

theorem fderiv_cubicInner (T U : Chart4 → Cubic4) (x v : Chart4)
    (hT : DifferentiableAt ℝ T x) (hU : DifferentiableAt ℝ U x) :
    fderiv ℝ (fun y => cubicInner (T y) (U y)) x v =
      cubicInner (cubicDerivative T x v) (U x)+cubicInner (T x) (cubicDerivative U x v) := by
  have ht (i : Fin 4) : DifferentiableAt ℝ (fun y => Matrix.of (T y i)) x := by
    change DifferentiableAt ℝ (fun y j k => T y i j k) x; fun_prop
  have hu (i : Fin 4) : DifferentiableAt ℝ (fun y => Matrix.of (U y i)) x := by
    change DifferentiableAt ℝ (fun y j k => U y i j k) x; fun_prop
  have hi (i : Fin 4) : DifferentiableAt ℝ (fun y => matrixInner (T y i) (U y i)) x := by
    unfold matrixInner; fun_prop
  change fderiv ℝ (fun y => ∑ i, matrixInner (T y i) (U y i)) x v = _
  erw [fderiv_fun_sum (u := Finset.univ) (fun i _ => hi i)]
  simp only [sum_apply]
  have he (i : Fin 4) := fderiv_matrixInner (fun y => Matrix.of (T y i)) (fun y => Matrix.of (U y i)) x v (ht i) (hu i)
  change (∑ i, fderiv ℝ (fun y => matrixInner (T y i) (U y i)) x v) =
    (∑ i, matrixInner (matrixDerivative (fun y => Matrix.of (T y i)) x v) (U x i))+
    ∑ i, matrixInner (T x i) (matrixDerivative (fun y => Matrix.of (U y i)) x v)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact he i

/-- Product rule for the contraction T_ijk H_ijkl. The free covector slot
contributes the displayed connection term. -/
theorem immersion_cubicContraction_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (l m : Fin 4) :
    fderiv ℝ (fun y => cubicContraction (immersionFrameThird F e y) (immersionFrameFourth F e y) l)
      x (e.coefficients x m) =
      cubicInner (fun i j k => immersionFrameFourth F e x i j k m)
        (fun i j k => immersionFrameFourth F e x i j k l)+
      cubicInner (immersionFrameThird F e x) (fun i j k => immersionFrameFifth F e x i j k l m)+
      ∑ r, immersionFrameConnection F e x m l r*
        cubicContraction (immersionFrameThird F e x) (immersionFrameFourth F e x) r := by
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hH := (((contDiffOn_immersionFrameForms F e).2.2 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hu : DifferentiableAt ℝ (fun y i j k => immersionFrameFourth F e y i j k l) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    apply differentiableAt_pi.mpr; intro k
    exact differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hH i) j) k) l
  have hs : CubicSymmetric (fun i j k => immersionFrameFourth F e x i j k l) := by
    apply (cubicSymmetric_iff_swaps _).mpr
    have h := immersionFrameFourth_firstThree F e x hx
    exact ⟨fun i j k => h.1 i j k l,fun i j k => h.2 i j k l⟩
  have hd : cubicDerivative (fun y i j k => immersionFrameFourth F e y i j k l) x (e.coefficients x m) =
      (fun i j k => fourthConnectionAction (immersionFrameConnection F e x m)
        (immersionFrameFourth F e x) i j k l)+(fun i j k => immersionFrameFifth F e x i j k l m) := by
    funext i j k
    exact congrFun (congrFun (congrFun (congrFun
      (immersionFrameFourth_frame_derivative F e x hx m) i) j) k) l
  change fderiv ℝ (fun y => cubicInner (immersionFrameThird F e y)
    (fun i j k => immersionFrameFourth F e y i j k l)) x _ = _
  rw [fderiv_cubicInner _ _ _ _ ht hu,immersionFrameThird_frame_derivative F e x hx m,hd,
    fourthConnectionAction_last_cubic,cubicInner_add_left,cubicInner_add_right,cubicInner_add_right,
    cubicInner_sum_smul]
  have hc := skew_cubicConnection_pairing _ _ _ (immersionFrameConnection_skew F e x hx m)
    (immersionFrameThird_symmetric F e x hx) hs
  change _ = _+_+∑ r, immersionFrameConnection F e x m l r*
    cubicInner (immersionFrameThird F e x) (fun i j k => immersionFrameFourth F e x i j k r)
  linarith

/-- Metric product rule for the actual scalar Laplacian of |nabla h|^2. -/
theorem immersionScalarLaplacian_cubic_norm (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) :
    (1/2 : ℝ)*immersionScalarLaplacian F e (fun y => cubicNormSq (immersionFrameThird F e y)) x =
      fourthNormSq (immersionFrameFourth F e x)+
      cubicInner (immersionFrameThird F e x) (roughTraceFifth (immersionFrameFifth F e x)) := by
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hH := (((contDiffOn_immersionFrameForms F e).2.2 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hd (l : Fin 4) : fderiv ℝ (fun y =>
      fderiv ℝ (fun z => cubicNormSq (immersionFrameThird F e z)) y (e.coefficients y l)) x (e.coefficients x l) =
      2*(cubicInner (fun i j k => immersionFrameFourth F e x i j k l)
          (fun i j k => immersionFrameFourth F e x i j k l)+
        cubicInner (immersionFrameThird F e x) (fun i j k => immersionFrameFifth F e x i j k l l)+
        ∑ r, immersionFrameConnection F e x l l r*
          cubicContraction (immersionFrameThird F e x) (immersionFrameFourth F e x) r) := by
    have he : (fun y => fderiv ℝ (fun z => cubicNormSq (immersionFrameThird F e z)) y (e.coefficients y l)) =ᶠ[𝓝 x]
        fun y => 2*cubicContraction (immersionFrameThird F e y) (immersionFrameFourth F e y) l :=
      Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
        (fun y hy => immersionFrameThird_norm_derivative F e y hy l)
    have hw : DifferentiableAt ℝ (fun y => cubicContraction (immersionFrameThird F e y)
        (immersionFrameFourth F e y) l) x := by
      unfold cubicContraction
      apply DifferentiableAt.fun_sum; intro i _
      apply DifferentiableAt.fun_sum; intro j _
      apply DifferentiableAt.fun_sum; intro k _
      exact (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp ht i) j) k).mul
        (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hH i) j) k) l)
    rw [he.fderiv_eq]
    erw [fderiv_fun_mul (differentiableAt_const (2 : ℝ)) hw]
    simp only [add_apply,smul_apply,smul_eq_mul,fderiv_const_apply,zero_apply,mul_zero,add_zero]
    rw [immersion_cubicContraction_derivative F e x hx l l]
  unfold immersionScalarLaplacian
  simp only [hd,immersionFrameThird_norm_derivative F e x hx]
  have hc (l : Fin 4) : (∑ r, immersionFrameConnection F e x l l r*
      (2*cubicContraction (immersionFrameThird F e x) (immersionFrameFourth F e x) r)) =
      2*(∑ r, immersionFrameConnection F e x l l r*
        cubicContraction (immersionFrameThird F e x) (immersionFrameFourth F e x) r) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring
  simp only [hc]
  have hs (a b c : ℝ) : 2*(a+b+c)-2*c = 2*(a+b) := by ring
  simp only [hs,← Finset.mul_sum,Finset.sum_add_distrib]
  have hn : (∑ l, cubicInner (fun i j k => immersionFrameFourth F e x i j k l)
      (fun i j k => immersionFrameFourth F e x i j k l)) = fourthNormSq (immersionFrameFourth F e x) := by
    simp only [cubicInner,fourthNormSq,pow_two]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
  have hp : (∑ l, cubicInner (immersionFrameThird F e x)
      (fun i j k => immersionFrameFifth F e x i j k l l)) =
      cubicInner (immersionFrameThird F e x) (roughTraceFifth (immersionFrameFifth F e x)) := by
    simp only [cubicInner,roughTraceFifth,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
  rw [hn,hp]
  ring

end
end SecondPinching
