import SecondPinching.ImmersionCurvature
import SecondPinching.RicciFrameAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Ricci interchange and the Gauss equation, derived for the actual second
fundamental form in the given arbitrary coordinate chart. -/
theorem immersionFourthForm_ricci (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j k l : Fin 4) :
    immersionFourthForm F.map F.normal x i j k l-immersionFourthForm F.map F.normal x i j l k =
      ricciPolynomial (immersionMetric F.map x) (immersionSecondForm F.map F.normal x)
        (immersionSecondForm F.map F.normal x*(immersionMetric F.map x)⁻¹*
          immersionSecondForm F.map F.normal x) i j k l := by
  have hΓ := (contDiffOn_immersionChristoffel F x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)
  have hh := ((contDiffOn_immersionForms F).1 x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)
  have hs := immersionSecondForm_symmetric F x hx
  have hg : (immersionMetric F.map x).IsSymm := by
    ext a b
    change inner ℝ (immersionTangent F.map x b) (immersionTangent F.map x a) =
      inner ℝ (immersionTangent F.map x a) (immersionTangent F.map x b)
    exact real_inner_comm _ _
  have hq : (immersionSecondForm F.map F.normal x*(immersionMetric F.map x)⁻¹*
      immersionSecondForm F.map F.normal x).IsSymm := by
    change (_*_*_)ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hs.eq, hg.inv.eq, Matrix.mul_assoc]
  have hr := coordinateCovariant_ricci (immersionChristoffel F.map)
    (immersionSecondForm F.map F.normal) x hΓ hh (immersionChristoffel_symmetric F x hx) k l
  rw [ricci_action_of_gauss _ _ _
    (immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx)) hs hq k l
    (fun a b => immersion_coordinateCurvature_gauss F x hx a b k l)] at hr
  exact congrFun (congrFun hr i) j

/-- The full Ricci identity in any orthonormal basis at the point. B need
not be part of a smooth principal frame. No spectral restrictions occur. -/
theorem immersionFourthForm_ricci_in_frame (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (B : Matrix4)
    (hB : frameMatrix B (immersionMetric F.map x) = 1) :
    ∀ i j k l,
      frameFourth B (immersionFourthForm F.map F.normal x) i j k l-
      frameFourth B (immersionFourthForm F.map F.normal x) i j l k =
      ricciPolynomial 1 (frameMatrix B (immersionSecondForm F.map F.normal x))
        (frameMatrix B (immersionSecondForm F.map F.normal x)*
          frameMatrix B (immersionSecondForm F.map F.normal x)) i j k l := by
  have he : immersionFourthForm F.map F.normal x-
      (fun i j k l => immersionFourthForm F.map F.normal x i j l k) =
      ricciPolynomial (immersionMetric F.map x) (immersionSecondForm F.map F.normal x)
        (immersionSecondForm F.map F.normal x*(immersionMetric F.map x)⁻¹*
          immersionSecondForm F.map F.normal x) := by
    funext i j k l; exact immersionFourthForm_ricci F x hx i j k l
  have hf := congrArg (frameFourthLinear B) he
  rw [map_sub] at hf
  simp only [frameFourthLinear, LinearMap.coe_mk, AddHom.coe_mk] at hf
  rw [frameFourth_swap34 B (immersionFourthForm F.map F.normal x), frameFourth_ricciPolynomial, hB] at hf
  have hd : B.det ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse (A := B) (B := immersionMetric F.map x*Bᵀ)
    simpa only [frameMatrix_eq_conjugate,Matrix.mul_assoc] using hB
  rw [frameMatrix_metric_square B _ _ hd hB] at hf
  intro i j k l
  exact congrFun (congrFun (congrFun (congrFun hf i) j) k) l

theorem immersionFrameFourth_ricci (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (i j k l : Fin 4) :
    immersionFrameFourth F e x i j k l-immersionFrameFourth F e x i j l k =
      ricciPolynomial 1 (immersionFrameSecond F e x)
        (immersionFrameSecond F e x*immersionFrameSecond F e x) i j k l :=
  immersionFourthForm_ricci_in_frame F x hx (e.coefficients x) (e.orthonormal x hx) i j k l

/-- Explicitly the curvature convention of eq:gauss in an orthonormal frame. -/
def gaussCurvature (h : Matrix4) : Fourth4 := fun i j k l =>
  (1 : Matrix4) i k*(1 : Matrix4) j l-(1 : Matrix4) i l*(1 : Matrix4) j k+
  h i k*h j l-h i l*h j k

theorem ricciPolynomial_eq_gauss_contraction (h : Matrix4) (hh : h.IsSymm)
    (i j k l : Fin 4) :
    ricciPolynomial 1 h (h*h) i j k l =
      (∑ r, h r j*gaussCurvature h r i k l)+(∑ r, h i r*gaussCurvature h r j k l) := by
  simp only [gaussCurvature, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hdelta (a b c d : Fin 4) :
      (∑ r, h r a*((1 : Matrix4) r b*(1 : Matrix4) c d)) = h b a*(1 : Matrix4) c d := by
    simp [Matrix.one_apply]
  have hdelta' (a b c d : Fin 4) :
      (∑ r, h a r*((1 : Matrix4) r b*(1 : Matrix4) c d)) = h a b*(1 : Matrix4) c d := by
    simp [Matrix.one_apply]
  rw [hdelta,hdelta,hdelta',hdelta']
  have hprod' (a b c d : Fin 4) : (∑ r, h r a*(h r b*h c d)) = (h*h) a b*h c d := by
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro r _
    rw [hh.apply a r]; ring
  have hprod'' (a b c d : Fin 4) : (∑ r, h a r*(h r b*h c d)) = (h*h) a b*h c d := by
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro r _; ring
  rw [hprod',hprod',hprod'',hprod'']
  simp only [ricciPolynomial]
  rw [hh.apply j k,hh.apply j l]
  ring

/-- The manuscript's Ricci equation, now a theorem of the actual immersion. -/
theorem immersionFrameFourth_ricci_manuscript (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (i j k l : Fin 4) :
    immersionFrameFourth F e x i j k l-immersionFrameFourth F e x i j l k =
      (∑ r, immersionFrameSecond F e x r j*gaussCurvature (immersionFrameSecond F e x) r i k l)+
      (∑ r, immersionFrameSecond F e x i r*gaussCurvature (immersionFrameSecond F e x) r j k l) := by
  rw [immersionFrameFourth_ricci F e x hx,
    ricciPolynomial_eq_gauss_contraction _ (immersionFrameSecond_symmetric F e x hx)]

end
end SecondPinching
