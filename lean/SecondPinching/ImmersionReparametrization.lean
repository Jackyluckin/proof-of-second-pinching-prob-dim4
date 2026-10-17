import SecondPinching.ImmersionGerms

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Rows are images of the source coordinate vectors. This is the transpose
of the convention in which the input coordinate labels matrix columns. -/
def coordinateJacobian (φ : Chart4 → Chart4) (x : Chart4) : Matrix4 :=
  fun i a => (fderiv ℝ φ x (coordinateUnit i)) a

/-- A smooth change of parameters on an open domain. The derivative is
invertible pointwise; no globally injective map or global inverse is required. -/
structure ImmersionReparametrization (F : LocalSphereImmersion) where
  domain : Set Chart4
  isOpen_domain : IsOpen domain
  map : Chart4 → Chart4
  smooth_map : ContDiffOn ℝ ∞ map domain
  mapsTo : Set.MapsTo map domain F.domain
  injective_derivative : ∀ x ∈ domain, Function.Injective (fderiv ℝ map x)

theorem coordinateJacobian_smooth {U : Set Chart4} (hU : IsOpen U)
    {φ : Chart4 → Chart4} (hφ : ContDiffOn ℝ ∞ φ U) :
    ContDiffOn ℝ ∞ (coordinateJacobian φ) U := by
  have hd := hφ.fderiv_of_isOpen hU (m := ∞) (by simp)
  unfold coordinateJacobian
  fun_prop

theorem immersionTangent_comp (f : Chart4 → Ambient6) (φ : Chart4 → Chart4)
    (x : Chart4) (hf : DifferentiableAt ℝ f (φ x)) (hφ : DifferentiableAt ℝ φ x)
    (i : Fin 4) :
    immersionTangent (f ∘ φ) x i =
      ∑ a, coordinateJacobian φ x i a • immersionTangent f (φ x) a := by
  unfold immersionTangent
  rw [fderiv_comp x hf hφ]
  exact immersionTangent_expansion f (φ x) (fderiv ℝ φ x (coordinateUnit i))

/-- Pull back the actual sphere immersion and its chosen normal. -/
def reparametrizedImmersion (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) : LocalSphereImmersion where
  domain := P.domain
  isOpen_domain := P.isOpen_domain
  map := F.map ∘ P.map
  normal := F.normal ∘ P.map
  smooth_map := F.smooth_map.comp P.smooth_map P.mapsTo
  smooth_normal := F.smooth_normal.comp P.smooth_map P.mapsTo
  injective_derivative := by
    intro x hx
    have hf := ((F.smooth_map _ (P.mapsTo hx)).contDiffAt
      (F.isOpen_domain.mem_nhds (P.mapsTo hx))).differentiableAt (by simp)
    have hφ := ((P.smooth_map x hx).contDiffAt
      (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
    rw [fderiv_comp x hf hφ]
    exact (F.injective_derivative _ (P.mapsTo hx)).comp (P.injective_derivative x hx)
  sphere := fun x hx => F.sphere _ (P.mapsTo hx)
  normal_unit := fun x hx => F.normal_unit _ (P.mapsTo hx)
  normal_radial := fun x hx => F.normal_radial _ (P.mapsTo hx)
  normal_tangent := by
    intro x hx i
    have hf := ((F.smooth_map _ (P.mapsTo hx)).contDiffAt
      (F.isOpen_domain.mem_nhds (P.mapsTo hx))).differentiableAt (by simp)
    have hφ := ((P.smooth_map x hx).contDiffAt
      (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
    change inner ℝ (F.normal (P.map x))
      (fderiv ℝ (F.map ∘ P.map) x (coordinateUnit i)) = 0
    rw [fderiv_comp x hf hφ]
    exact immersion_normal_tangent F _ (P.mapsTo hx) _

theorem reparametrized_tangent (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain) (i : Fin 4) :
    immersionTangent (reparametrizedImmersion F P).map x i =
      ∑ a, coordinateJacobian P.map x i a • immersionTangent F.map (P.map x) a := by
  change immersionTangent (F.map ∘ P.map) x i = _
  apply immersionTangent_comp
  · exact ((F.smooth_map _ (P.mapsTo hx)).contDiffAt
      (F.isOpen_domain.mem_nhds (P.mapsTo hx))).differentiableAt (by simp)
  · exact ((P.smooth_map x hx).contDiffAt
      (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)

theorem reparametrized_metric (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain) :
    immersionMetric (reparametrizedImmersion F P).map x =
      frameMatrix (coordinateJacobian P.map x) (immersionMetric F.map (P.map x)) := by
  funext i j
  change inner ℝ (immersionTangent _ x i) (immersionTangent _ x j) = _
  rw [reparametrized_tangent F P x hx i,reparametrized_tangent F P x hx j]
  rw [sum_inner]
  simp only [inner_sum,real_inner_smul_left,inner_smul_right,
    Finset.mul_sum,frameMatrix,immersionMetric,Matrix.gram_apply]
  congr 1
  funext a
  congr 1
  funext b
  ring

/-- The second derivative has an extra tangential term involving second
derivatives of the coordinate change. It is retained explicitly here. -/
theorem reparametrized_secondDerivative (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain) (i j : Fin 4) :
    immersionSecondDerivative (reparametrizedImmersion F P).map x i j =
      ∑ a, ((∑ b, (coordinateJacobian P.map x i a * coordinateJacobian P.map x j b) •
        immersionSecondDerivative F.map (P.map x) a b) +
        (fderiv ℝ (fun y => coordinateJacobian P.map y i a) x (coordinateUnit j)) •
          immersionTangent F.map (P.map x) a) := by
  have hφ := ((P.smooth_map x hx).contDiffAt
    (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hj (a : Fin 4) : DifferentiableAt ℝ (fun y => coordinateJacobian P.map y i a) x :=
    (((contDiffOn_pi.mp (contDiffOn_pi.mp (coordinateJacobian_smooth
      P.isOpen_domain P.smooth_map) i)) a) x hx).contDiffAt
      (P.isOpen_domain.mem_nhds hx) |>.differentiableAt (by simp)
  have ht (a : Fin 4) := ((contDiffOn_immersionTangent F.isOpen_domain F.smooth_map a)
    _ (P.mapsTo hx)).contDiffAt (F.isOpen_domain.mem_nhds (P.mapsTo hx))
    |>.differentiableAt (by simp)
  have he : (fun y => immersionTangent (reparametrizedImmersion F P).map y i) =ᶠ[𝓝 x]
      (fun y => ∑ a, coordinateJacobian P.map y i a • immersionTangent F.map (P.map y) a) :=
    Filter.eventuallyEq_of_mem (P.isOpen_domain.mem_nhds hx)
      (fun y hy => reparametrized_tangent F P y hy i)
  unfold immersionSecondDerivative
  rw [he.fderiv_eq (𝕜 := ℝ)]
  have hs (a : Fin 4) : DifferentiableAt ℝ (fun y =>
      coordinateJacobian P.map y i a • immersionTangent F.map (P.map y) a) x :=
    (hj a).smul ((ht a).comp x hφ)
  rw [fderiv_fun_sum (u := Finset.univ) (fun a _ => hs a)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have htc : DifferentiableAt ℝ (fun y => immersionTangent F.map (P.map y) a) x :=
    (ht a).comp x hφ
  rw [fderiv_fun_smul (hj a) htc]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply]
  have hd : fderiv ℝ (fun y => immersionTangent F.map (P.map y) a) x (coordinateUnit j) =
      ∑ b, coordinateJacobian P.map x j b • immersionSecondDerivative F.map (P.map x) a b := by
    change fderiv ℝ ((fun y => immersionTangent F.map y a) ∘ P.map) x _ = _
    rw [fderiv_comp x (ht a) hφ]
    change fderiv ℝ (fun y => immersionTangent F.map y a) (P.map x)
      (fderiv ℝ P.map x (coordinateUnit j)) = _
    conv_lhs => rw [chart4_coordinate_expansion (fderiv ℝ P.map x (coordinateUnit j))]
    simp only [map_sum,map_smul,coordinateJacobian,immersionSecondDerivative]
  rw [hd,Finset.smul_sum]
  simp only [smul_smul,immersionSecondDerivative]

/-- Pairing the preceding chain rule with the normal kills precisely the
extra tangential term; h therefore transforms as a covariant two-tensor. -/
theorem reparametrized_secondForm (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain) :
    immersionSecondForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal x =
      frameMatrix (coordinateJacobian P.map x)
        (immersionSecondForm F.map F.normal (P.map x)) := by
  funext i j
  change inner ℝ (immersionSecondDerivative _ x i j) (F.normal (P.map x)) = _
  rw [reparametrized_secondDerivative F P x hx]
  have hn (a : Fin 4) : inner ℝ (immersionTangent F.map (P.map x) a)
      (F.normal (P.map x)) = 0 := by
    rw [real_inner_comm]
    exact F.normal_tangent _ (P.mapsTo hx) a
  simp only [sum_inner,inner_add_left,real_inner_smul_left,hn,mul_zero,add_zero,
    frameMatrix,immersionSecondForm,Finset.mul_sum,mul_assoc]

/-- The normal sign on an overlap is derived after pullback. Equality is only
required on a neighborhood, so extensions outside the charts are irrelevant. -/
theorem immersion_normals_reparametrization_germ (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4)
    (hxP : x ∈ P.domain) (hxG : x ∈ G.domain) (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) :
    G.normal =ᶠ[𝓝 x] F.normal ∘ P.map ∨ G.normal =ᶠ[𝓝 x] -(F.normal ∘ P.map) :=
  localImmersion_normals_same_map_germ (reparametrizedImmersion F P) G x hxP hxG hf

theorem immersion_secondForm_reparametrization_germ (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4)
    (hxP : x ∈ P.domain) (hxG : x ∈ G.domain) (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) :
    (G.normal =ᶠ[𝓝 x] F.normal ∘ P.map ∧
      immersionSecondForm G.map G.normal =ᶠ[𝓝 x]
        (fun y => frameMatrix (coordinateJacobian P.map y) (immersionSecondForm F.map F.normal (P.map y)))) ∨
    (G.normal =ᶠ[𝓝 x] -(F.normal ∘ P.map) ∧
      immersionSecondForm G.map G.normal =ᶠ[𝓝 x]
        (fun y => -frameMatrix (coordinateJacobian P.map y) (immersionSecondForm F.map F.normal (P.map y)))) := by
  have hh : immersionSecondForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal =ᶠ[𝓝 x]
      (fun y => frameMatrix (coordinateJacobian P.map y) (immersionSecondForm F.map F.normal (P.map y))) :=
    Filter.eventuallyEq_of_mem (P.isOpen_domain.mem_nhds hxP)
      (fun y hy => reparametrized_secondForm F P y hy)
  rcases immersion_normals_reparametrization_germ F G P x hxP hxG hf with hn | hn
  · exact Or.inl ⟨hn,((immersionForms_congr_germs _ _ _ _ x hf hn).1).trans hh⟩
  · right
    refine ⟨hn,?_⟩
    have he := (immersionForms_congr_germs _ _ _ _ x hf hn).1
    rw [(immersion_forms_normal_reversal (F.map ∘ P.map) (F.normal ∘ P.map)).1] at he
    exact he.trans (hh.mono (fun y hy => congrArg Neg.neg hy))

theorem reparametrized_frame_transition (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (e : LocalImmersionFrame F)
    (e' : LocalImmersionFrame (reparametrizedImmersion F P))
    (x : Chart4) (hx : x ∈ P.domain) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      e'.coefficients x * coordinateJacobian P.map x = Q * e.coefficients (P.map x) := by
  let B := e.coefficients (P.map x)
  let C := e'.coefficients x * coordinateJacobian P.map x
  let Q := C * B⁻¹
  have hi : IsUnit B.det := isUnit_iff_ne_zero.mpr
    (localImmersionFrame_det_ne_zero F e _ (P.mapsTo hx))
  have heq : Q*B = C := by
    dsimp [Q]
    rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hi,Matrix.mul_one]
  have hC : frameMatrix C (immersionMetric F.map (P.map x)) = 1 := by
    dsimp [C]
    rw [frameMatrix_composition,← reparametrized_metric F P x hx]
    exact e'.orthonormal x hx
  have hQQ : Q*Qᵀ = 1 := by
    have he := frameMatrix_composition Q B (immersionMetric F.map (P.map x))
    rw [heq,hC,e.orthonormal _ (P.mapsTo hx),frameMatrix_eq_conjugate,Matrix.mul_one] at he
    exact he.symm
  refine ⟨Q,?_,heq.symm⟩
  exact (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mp
    ((Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mpr hQQ)

theorem reparametrized_frameSecond (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (e : LocalImmersionFrame F)
    (e' : LocalImmersionFrame (reparametrizedImmersion F P))
    (x : Chart4) (hx : x ∈ P.domain) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      immersionFrameSecond (reparametrizedImmersion F P) e' x =
        frameMatrix Q (immersionFrameSecond F e (P.map x)) := by
  obtain ⟨Q,hQ,hp⟩ := reparametrized_frame_transition F P e e' x hx
  refine ⟨Q,hQ,?_⟩
  simp only [immersionFrameSecond,reparametrized_secondForm F P x hx,
    ← frameMatrix_composition,hp]

end
end SecondPinching
