import SecondPinching.RicciDifferentiation
import SecondPinching.CubicBochner
import SecondPinching.ImmersionFifthRicci

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Contraction commutes with the metric connection; the last two connection
terms cancel by skew symmetry, without symmetry in the last two slots of H. -/
theorem roughTrace_fourthConnectionAction (O : Matrix4) (H : Fourth4) (hO : Oᵀ = -O) :
    roughTrace (fourthConnectionAction O H) = O*roughTrace H+roughTrace H*Oᵀ := by
  ext i j
  have hs : (Matrix.of (fun k r => H i j r k+H i j k r)).IsSymm := by
    ext k r; simp only [Matrix.transpose_apply,Matrix.of_apply]; ring
  have hz := skew_matrix_sum O (Matrix.of (fun k r => H i j r k+H i j k r)) hO hs
  have he : roughTrace (fourthConnectionAction O H) i j =
      (O*roughTrace H+roughTrace H*Oᵀ) i j+
      ∑ k, ∑ r, O k r*(H i j r k+H i j k r) := by
    simp only [roughTrace,fourthConnectionAction,cubicConnectionAction,Pi.add_apply,
      Pi.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.mul_apply,
      Matrix.transpose_apply,Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton]
    ring
  rw [he]
  change _+ (∑ k, ∑ r, O k r*(Matrix.of (fun k r => H i j r k+H i j k r)) k r) = _
  rw [hz,add_zero]

/-- Covariant derivative of the actual tensor Simons identity. No constancy
of the squared second-form norm is used. -/
theorem immersionFrameFifth_simons_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (x : Chart4) (hx : x ∈ F.domain) (i j k : Fin 4) :
    (∑ l, immersionFrameFifth F e x i j l l k) =
      (4-matrixNormSq (immersionFrameSecond F e x))*immersionFrameThird F e x i j k-
        2*immersionFrameSecond F e x i j*
          cubicWeightedTrace (immersionFrameSecond F e x) (immersionFrameThird F e x) k := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hH := (((contDiffOn_immersionFrameForms F e).2.2 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hc (a b : Fin 4) : DifferentiableAt ℝ (fun y => immersionFrameSecond F e y a b) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hh a) b
  have hS : DifferentiableAt ℝ (fun y => matrixNormSq (immersionFrameSecond F e y)) x := by
    unfold matrixNormSq
    apply DifferentiableAt.fun_sum; intro a _
    apply DifferentiableAt.fun_sum; intro b _
    exact (hc a b).pow 2
  have hHl (l : Fin 4) : DifferentiableAt ℝ (fun y => immersionFrameFourth F e y i j l l) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hH i) j) l) l
  have hg : (fun y => ∑ l, immersionFrameFourth F e y i j l l) =ᶠ[𝓝 x]
      fun y => (4-matrixNormSq (immersionFrameSecond F e y))*immersionFrameSecond F e y i j := by
    apply Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hx)
    intro y hy
    exact congrFun (congrFun (immersionFrameFourth_simons F e hminimal y hy) i) j
  have hd := congrArg (fun L : Chart4 →L[ℝ] ℝ => L (e.coefficients x k)) hg.fderiv_eq
  erw [fderiv_fun_sum (u := Finset.univ) (fun l _ => hHl l),
    fderiv_fun_mul ((differentiableAt_const (4 : ℝ)).sub hS) (hc i j),
    fderiv_fun_sub (differentiableAt_const (4 : ℝ)) hS] at hd
  simp only [sum_apply,add_apply,smul_apply,smul_eq_mul,Pi.sub_apply,fderiv_const_apply,
    zero_sub,neg_apply,immersionFrameSecond_norm_derivative F e x hx k] at hd
  have dH (l : Fin 4) : fderiv ℝ (fun y => immersionFrameFourth F e y i j l l) x (e.coefficients x k) =
      fourthConnectionAction (immersionFrameConnection F e x k) (immersionFrameFourth F e x) i j l l+
        immersionFrameFifth F e x i j l l k :=
    congrFun (congrFun (congrFun (congrFun (immersionFrameFourth_frame_derivative F e x hx k) i) j) l) l
  have dh : fderiv ℝ (fun y => immersionFrameSecond F e y i j) x (e.coefficients x k) =
      (immersionFrameConnection F e x k*immersionFrameSecond F e x+
        immersionFrameSecond F e x*(immersionFrameConnection F e x k)ᵀ) i j+
        immersionFrameThird F e x i j k :=
    congrFun (congrFun (immersionFrameSecond_frame_derivative F e x hx k) i) j
  simp only [dH,dh,Finset.sum_add_distrib] at hd
  have hconn := congrFun (congrFun (roughTrace_fourthConnectionAction
    (immersionFrameConnection F e x k) (immersionFrameFourth F e x)
    (immersionFrameConnection_skew F e x hx k)) i) j
  rw [immersionFrameFourth_simons F e hminimal x hx,Matrix.mul_smul,Matrix.smul_mul,
    ← smul_add] at hconn
  change (∑ l, fourthConnectionAction (immersionFrameConnection F e x k)
      (immersionFrameFourth F e x) i j l l) =
    (4-matrixNormSq (immersionFrameSecond F e x))*
      (immersionFrameConnection F e x k*immersionFrameSecond F e x+
        immersionFrameSecond F e x*(immersionFrameConnection F e x k)ᵀ) i j at hconn
  rw [hconn] at hd
  unfold cubicWeightedTrace
  nlinarith [hd]

/-- The rough Laplacian of nabla h, derived by two interchanges of covariant
slots and by differentiating the actual Simons identity. -/
theorem immersionFrameFifth_roughTrace (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (hminimal : ∀ y ∈ F.domain, Matrix.trace (immersionFrameSecond F e y) = 0)
    (x : Chart4) (hx : x ∈ F.domain) :
    roughTraceFifth (immersionFrameFifth F e x) =
      pengTerngCubic (immersionFrameSecond F e x) (immersionFrameThird F e x) := by
  funext i j k
  have he (l : Fin 4) : immersionFrameFifth F e x i j k l l =
      immersionFrameFifth F e x i j l l k+
        ricciVariation (immersionFrameSecond F e x) (fun a b => immersionFrameThird F e x a b l) i j k l+
        cubicConnectionAction (fun a r => gaussCurvature (immersionFrameSecond F e x) r a k l)
          (immersionFrameThird F e x) i j l := by
    have h1 := immersionFrameFifth_ricci_differentiated F e x hx i j k l l
    have h2 := immersionFrameFifth_ricci F e x hx i j l k l
    linarith
  simp only [roughTraceFifth,he,Finset.sum_add_distrib,pengTerngCubic,
    ricciVariationDivergence,cubicCurvatureTrace,immersionFrameFifth_simons_derivative F e hminimal x hx i j k]

end
end SecondPinching
