import SecondPinching.HessianContractionDifferentiation

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem immersionFrameThird_slice_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k l : Fin 4) :
    matrixDerivative (fun y => Matrix.of (fun i j => immersionFrameThird F e y i j k))
      x (e.coefficients x l) =
      Matrix.of (fun i j => cubicConnectionAction (immersionFrameConnection F e x l)
        (immersionFrameThird F e x) i j k) +
      Matrix.of (fun i j => immersionFrameFourth F e x i j k l) := by
  ext i j
  exact congrFun (congrFun (congrFun (immersionFrameThird_frame_derivative F e x hx l) i) j) k

/-- Differentiation of the ordinary trace covector, before it is set to zero. -/
theorem immersionFrameThird_trace_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k l : Fin 4) :
    fderiv ℝ (fun y => cubicTrace (immersionFrameThird F e y) k) x (e.coefficients x l) =
      ordinaryTrace (immersionFrameFourth F e x) k l +
      ∑ r, immersionFrameConnection F e x l k r*cubicTrace (immersionFrameThird F e x) r := by
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (fun y => Matrix.of (fun i j => immersionFrameThird F e y i j k)) x := by
    change DifferentiableAt ℝ (fun y i j => immersionFrameThird F e y i j k) x; fun_prop
  change fderiv ℝ (fun y => Matrix.trace (Matrix.of (fun i j => immersionFrameThird F e y i j k))) x _ = _
  rw [fderiv_matrix_trace _ _ _ hs, immersionFrameThird_slice_derivative F e x hx k l,
    Matrix.trace_add, cubicConnectionAction_last_slot,
    skew_connection_trace _ _ _ (immersionFrameConnection_skew F e x hx l), Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul]
  exact add_comm _ _

/-- Differentiation of the weighted trace includes the derivative of h itself. -/
theorem immersionFrameThird_weighted_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k l : Fin 4) :
    fderiv ℝ (fun y => cubicWeightedTrace (immersionFrameSecond F e y) (immersionFrameThird F e y) k)
      x (e.coefficients x l) =
      weightedTrace (immersionFrameSecond F e x) (immersionFrameFourth F e x) k l +
      cubicGramMatrix (immersionFrameThird F e x) k l +
      ∑ r, immersionFrameConnection F e x l k r *
        cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) r := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (fun y => Matrix.of (fun i j => immersionFrameThird F e y i j k)) x := by
    change DifferentiableAt ℝ (fun y i j => immersionFrameThird F e y i j k) x; fun_prop
  have hK : (Matrix.of (fun i j => immersionFrameThird F e x i j k)).IsSymm := by
    ext i j; exact cubicSymmetric_swap12 (immersionFrameThird_symmetric F e x hx) j i k
  change fderiv ℝ (fun y => matrixInner (immersionFrameSecond F e y)
    (Matrix.of (fun i j => immersionFrameThird F e y i j k))) x _ = _
  rw [fderiv_matrixInner _ _ _ _ hh hs, immersionFrameSecond_frame_derivative F e x hx l,
    immersionFrameThird_slice_derivative F e x hx k l,
    weighted_connection_product _ _ _ _ _ _ k (immersionFrameConnection_skew F e x hx l)
      (immersionFrameSecond_symmetric F e x hx) hK rfl]
  have hG : matrixInner (Matrix.of (fun i j => immersionFrameThird F e x i j l))
      (Matrix.of (fun i j => immersionFrameThird F e x i j k)) = cubicGramMatrix (immersionFrameThird F e x) k l := by
    rw [matrixInner_comm]; rfl
  rw [hG]
  change cubicGramMatrix (immersionFrameThird F e x) k l +
    weightedTrace (immersionFrameSecond F e x) (immersionFrameFourth F e x) k l + _ = _
  ring

/-- Metric compatibility eliminates every connection contribution to |nabla h|^2. -/
theorem immersionFrameThird_norm_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (l : Fin 4) :
    fderiv ℝ (fun y => cubicNormSq (immersionFrameThird F e y)) x (e.coefficients x l) =
      2*cubicContraction (immersionFrameThird F e x) (immersionFrameFourth F e x) l := by
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [fderiv_cubicNormSq _ _ _ ht, immersionFrameThird_frame_derivative F e x hx l]
  have ha (T U V : Cubic4) : cubicInner T (U+V) = cubicInner T U+cubicInner T V := by
    simp only [cubicInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [ha, skew_cubicConnectionAction_inner _ _ (immersionFrameConnection_skew F e x hx l)
    (immersionFrameThird_symmetric F e x hx), zero_add]
  rfl

/-- First raw Hessian contraction, from minimality on the actual open domain. -/
theorem immersionFrameFourth_trace_of_minimality (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (x : Chart4) (hx : x ∈ F.domain) : ordinaryTrace (immersionFrameFourth F e x) = 0 := by
  have hz (y : Chart4) (hy : y ∈ F.domain) (k : Fin 4) : cubicTrace (immersionFrameThird F e y) k = 0 :=
    immersionFrameThird_trace_of_minimal_germ F e y hy
      (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hy) hminimal) k
  ext k l
  have hg : (fun y => cubicTrace (immersionFrameThird F e y) k) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) (fun y hy => hz y hy k)
  have hd := immersionFrameThird_trace_derivative F e x hx k l
  rw [hg.fderiv_eq] at hd
  simp only [fderiv_const_apply, zero_apply, hz x hx, mul_zero, Finset.sum_const_zero, add_zero] at hd
  exact hd.symm

/-- Second raw contraction; all sums use ordered indices. -/
theorem immersionFrameFourth_weighted_of_constant_norm (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (S : ℝ) (hSnorm : ∀ y ∈ F.domain, matrixNormSq (immersionFrameSecond F e y) = S)
    (x : Chart4) (hx : x ∈ F.domain) :
    weightedTrace (immersionFrameSecond F e x) (immersionFrameFourth F e x) =
      -cubicGramMatrix (immersionFrameThird F e x) := by
  have hz (y : Chart4) (hy : y ∈ F.domain) (k : Fin 4) :
      cubicWeightedTrace (immersionFrameSecond F e y) (immersionFrameThird F e y) k = 0 :=
    immersionFrameThird_weighted_of_norm_germ F e S y hy
      (Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hy) hSnorm) k
  ext k l
  have hg : (fun y => cubicWeightedTrace (immersionFrameSecond F e y) (immersionFrameThird F e y) k) =ᶠ[𝓝 x]
      fun _ => (0 : ℝ) := Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx) (fun y hy => hz y hy k)
  have hd := immersionFrameThird_weighted_derivative F e x hx k l
  rw [hg.fderiv_eq] at hd
  simp only [fderiv_const_apply, zero_apply, hz x hx, mul_zero, Finset.sum_const_zero, add_zero] at hd
  change _ = -cubicGramMatrix (immersionFrameThird F e x) k l
  linarith

/-- Third raw contraction needs neighborhood constancy, not an equality at x. -/
theorem immersionFrameFourth_cubic_of_constant_norm_germ (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (c : ℝ) (x : Chart4) (hx : x ∈ F.domain)
    (hTnorm : (fun y => cubicNormSq (immersionFrameThird F e y)) =ᶠ[𝓝 x] fun _ => c) :
    cubicContraction (immersionFrameThird F e x) (immersionFrameFourth F e x) = 0 := by
  funext l
  have hd := immersionFrameThird_norm_derivative F e x hx l
  rw [hTnorm.fderiv_eq] at hd
  simp only [fderiv_const_apply, zero_apply] at hd
  change _ = (0 : ℝ)
  linarith

end
end SecondPinching
