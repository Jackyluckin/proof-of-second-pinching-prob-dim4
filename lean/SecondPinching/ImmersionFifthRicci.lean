import SecondPinching.FifthFrameAlgebra

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 4800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- A single curvature action, with the inverse metric on the contracted coordinate index. -/
def curvatureFirstContraction (ginv : Matrix4) (T : Cubic4) (R : Fourth4) : Fifth4 :=
  fun i j k l m => ∑ a, ∑ b, ginv a b*T a j k*R b i l m

theorem immersionFifthForm_ricci (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) :
    immersionFifthForm F x-(fun i j k l m => immersionFifthForm F x i j k m l) =
      curvatureFirstContraction (immersionMetric F.map x)⁻¹ (immersionThirdForm F.map F.normal x)
        (coordinateGaussTensor (immersionMetric F.map x) (immersionSecondForm F.map F.normal x))+
      (fun i j k l m => curvatureFirstContraction (immersionMetric F.map x)⁻¹
        (immersionThirdForm F.map F.normal x)
        (coordinateGaussTensor (immersionMetric F.map x) (immersionSecondForm F.map F.normal x)) j i k l m)+
      (fun i j k l m => curvatureFirstContraction (immersionMetric F.map x)⁻¹
        (immersionThirdForm F.map F.normal x)
        (coordinateGaussTensor (immersionMetric F.map x) (immersionSecondForm F.map F.normal x)) k i j l m) := by
  let g := immersionMetric F.map x
  let h := immersionSecondForm F.map F.normal x
  let T := immersionThirdForm F.map F.normal x
  let R := coordinateGaussTensor g h
  have hg : g.IsSymm := by
    ext a b
    change inner ℝ (immersionTangent F.map x b) (immersionTangent F.map x a) =
      inner ℝ (immersionTangent F.map x a) (immersionTangent F.map x b)
    exact real_inner_comm _ _
  have ht : CubicSymmetric T := immersionThirdForm_symmetric F x hx
  have hr (l m i a : Fin 4) :
      coordinateCurvature (immersionChristoffel F.map) x l m i a = ∑ b, R b i l m*g⁻¹ b a := by
    have he : coordinateCurvature (immersionChristoffel F.map) x l m =
        (coordinateCurvature (immersionChristoffel F.map) x l m*g)*g⁻¹ := by
      rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv g
        (isUnit_iff_ne_zero.mpr (immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx))),mul_one]
    rw [he,Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro b _
    have hv := immersion_coordinateCurvature_gauss F x hx i b l m
    change _ = g i m*g l b-g i l*g m b+h i m*h b l-h i l*h b m at hv
    rw [hv]
    dsimp [R,coordinateGaussTensor]
    rw [hg.apply b l,hg.apply b m]
    ring
  have hs (i j k l m : Fin 4) :
      (∑ a, coordinateCurvature (immersionChristoffel F.map) x l m i a*T a j k) =
      curvatureFirstContraction g⁻¹ T R i j k l m := by
    simp only [hr,Finset.sum_mul,curvatureFirstContraction]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hg.inv.apply a b]; ring
  have hΓ := (contDiffOn_immersionChristoffel F x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)
  have hT := ((contDiffOn_immersionForms F).2.1 x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)
  funext i j k l m
  have he := congrFun (congrFun (congrFun
    (coordinateCovariant3_ricci (immersionChristoffel F.map) (immersionThirdForm F.map F.normal)
      x hΓ hT (immersionChristoffel_symmetric F x hx) l m) i) j) k
  change immersionFifthForm F x i j k l m-immersionFifthForm F x i j k m l =
      cubicConnectionAction (coordinateCurvature (immersionChristoffel F.map) x l m) T i j k at he
  change _ = curvatureFirstContraction g⁻¹ T R i j k l m+
    curvatureFirstContraction g⁻¹ T R j i k l m+curvatureFirstContraction g⁻¹ T R k i j l m
  simp only [Pi.sub_apply]
  rw [he]
  simp only [cubicConnectionAction,Finset.sum_add_distrib]
  have h2 : (∑ a, coordinateCurvature (immersionChristoffel F.map) x l m j a*T i a k) =
      curvatureFirstContraction g⁻¹ T R j i k l m := by
    simp_rw [cubicSymmetric_swap12 ht i]; exact hs j i k l m
  have h3 : (∑ a, coordinateCurvature (immersionChristoffel F.map) x l m k a*T i j a) =
      curvatureFirstContraction g⁻¹ T R k i j l m := by
    simp_rw [cubicSymmetric_swap23 ht i j,cubicSymmetric_swap12 ht i]; exact hs k i j l m
  rw [hs,h2,h3]

/-- Ricci interchange on nabla h in the actual smooth orthonormal frame. -/
theorem immersionFrameFifth_ricci (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (i j k l m : Fin 4) :
    immersionFrameFifth F e x i j k l m-immersionFrameFifth F e x i j k m l =
      cubicConnectionAction (fun a r => gaussCurvature (immersionFrameSecond F e x) r a l m)
        (immersionFrameThird F e x) i j k := by
  let B := e.coefficients x
  let C := curvatureFirstContraction (immersionMetric F.map x)⁻¹
    (immersionThirdForm F.map F.normal x)
    (coordinateGaussTensor (immersionMetric F.map x) (immersionSecondForm F.map F.normal x))
  have hi := inverse_metric_of_frame B (immersionMetric F.map x)
    (localImmersionFrame_det_ne_zero F e x hx) (e.orthonormal x hx)
  have hc : frameFifth B C = fun a b c d q =>
      ∑ r, immersionFrameThird F e x r b c*gaussCurvature (immersionFrameSecond F e x) r a d q := by
    have hz := frameFifth_curvature_contraction B (immersionMetric F.map x)⁻¹
      (immersionThirdForm F.map F.normal x)
      (coordinateGaussTensor (immersionMetric F.map x) (immersionSecondForm F.map F.normal x)) hi
    rw [frameFourth_coordinateGauss,e.orthonormal x hx] at hz
    exact hz
  have he := congrArg (frameFifthLinear B) (immersionFifthForm_ricci F x hx)
  change frameFifthLinear B (_-_) = frameFifthLinear B (C+(fun a b c d q => C b a c d q)+
    (fun a b c d q => C c a b d q)) at he
  simp only [map_sub,map_add] at he
  change frameFifth B (immersionFifthForm F x)-frameFifth B (fun a b c d q => immersionFifthForm F x a b c q d) =
    frameFifth B C+frameFifth B (fun a b c d q => C b a c d q)+frameFifth B (fun a b c d q => C c a b d q) at he
  rw [frameFifth_swap45 B (immersionFifthForm F x),frameFifth_swap12 B C,
    show (fun a b c d q => C c a b d q) =
      (fun a b c d q => (fun u v w z p => C v u w z p) a c b d q) from rfl,
    frameFifth_swap23 B (fun u v w z p => C v u w z p),frameFifth_swap12 B C,hc] at he
  have hv := congrFun (congrFun (congrFun (congrFun (congrFun he i) j) k) l) m
  change _ = (∑ r, immersionFrameThird F e x r j k*gaussCurvature (immersionFrameSecond F e x) r i l m)+
    (∑ r, immersionFrameThird F e x r i k*gaussCurvature (immersionFrameSecond F e x) r j l m)+
    (∑ r, immersionFrameThird F e x r i j*gaussCurvature (immersionFrameSecond F e x) r k l m) at hv
  simp only [Pi.sub_apply] at hv
  change immersionFrameFifth F e x i j k l m-immersionFrameFifth F e x i j k m l = _ at hv
  erw [hv]
  simp only [cubicConnectionAction,Finset.sum_add_distrib]
  have ht := immersionFrameThird_symmetric F e x hx
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl; intro r _; ring
    · apply Finset.sum_congr rfl; intro r _; rw [cubicSymmetric_swap12 ht r i k]; ring
  · apply Finset.sum_congr rfl; intro r _
    rw [cubicSymmetric_swap12 ht r i j,cubicSymmetric_swap23 ht i r j]; ring

end
end SecondPinching
