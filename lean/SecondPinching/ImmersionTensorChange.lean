import SecondPinching.CoordinateTensorChange

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The actual third form is the pullback of nabla h. All hypotheses concern
the immersion and its smooth parameter change, not component transformation. -/
theorem reparametrized_thirdForm (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain) :
    immersionThirdForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal x =
      frameCubic (coordinateJacobian P.map x) (immersionThirdForm F.map F.normal (P.map x)) := by
  have hφ := ((P.smooth_map x hx).contDiffAt
    (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hJ := (((coordinateJacobian_smooth P.isOpen_domain P.smooth_map) x hx).contDiffAt
    (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hh := (((contDiffOn_immersionForms F).1 _ (P.mapsTo hx)).contDiffAt
    (F.isOpen_domain.mem_nhds (P.mapsTo hx))).differentiableAt (by simp)
  have he : immersionSecondForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal =ᶠ[𝓝 x]
      (fun y => frameMatrix (coordinateJacobian P.map y) (immersionSecondForm F.map F.normal (P.map y))) :=
    Filter.eventuallyEq_of_mem (P.isOpen_domain.mem_nhds hx)
      (fun y hy => reparametrized_secondForm F P y hy)
  have hd := (coordinateCovariant2_congr_germ
    (immersionChristoffel (reparametrizedImmersion F P).map) _ _ x he).self_of_nhds
  unfold immersionThirdForm
  rw [hd]
  exact coordinateCovariant2_pullback P.map _ _ _ x hφ hJ hh
    (fun i k a => reparametrized_Christoffel F P x hx i k a)

/-- Naturality of the actual Hessian, including the connection correction on
the derivative slot of nabla h. No symmetry assumption enters this theorem. -/
theorem reparametrized_fourthForm (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain) :
    immersionFourthForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal x =
      frameFourth (coordinateJacobian P.map x) (immersionFourthForm F.map F.normal (P.map x)) := by
  have hφ := ((P.smooth_map x hx).contDiffAt
    (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hJ := (((coordinateJacobian_smooth P.isOpen_domain P.smooth_map) x hx).contDiffAt
    (P.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hT := (((contDiffOn_immersionForms F).2.1 _ (P.mapsTo hx)).contDiffAt
    (F.isOpen_domain.mem_nhds (P.mapsTo hx))).differentiableAt (by simp)
  have he : immersionThirdForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal =ᶠ[𝓝 x]
      (fun y => frameCubic (coordinateJacobian P.map y) (immersionThirdForm F.map F.normal (P.map y))) :=
    Filter.eventuallyEq_of_mem (P.isOpen_domain.mem_nhds hx)
      (fun y hy => reparametrized_thirdForm F P y hy)
  have hd := (coordinateCovariant3_congr_germ
    (immersionChristoffel (reparametrizedImmersion F P).map) _ _ x he).self_of_nhds
  unfold immersionFourthForm
  rw [hd]
  exact coordinateCovariant3_pullback P.map _ _ _ x hφ hJ hT
    (fun i k a => reparametrized_Christoffel F P x hx i k a)

/-- The same connection law for an independently supplied local description
of the immersion. Equality of maps is required only near the point. -/
theorem immersion_Christoffel_reparametrization (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain)
    (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) (i j a : Fin 4) :
    (∑ r, immersionChristoffel G.map x r i j * coordinateJacobian P.map x r a) =
      fderiv ℝ (fun y => coordinateJacobian P.map y i a) x (coordinateUnit j) +
      ∑ b, ∑ c, coordinateJacobian P.map x i b * coordinateJacobian P.map x j c *
        immersionChristoffel F.map (P.map x) a b c := by
  have hg := (immersionChristoffel_congr_germ _ _ x hf).self_of_nhds
  rw [hg]
  exact reparametrized_Christoffel F P x hx i j a

/-- One local normal sign acts on all three pulled-back tensors. There is no
assumption of a global normal, a connected overlap or any component law. -/
theorem immersion_forms_reparametrization_germ (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4)
    (hxP : x ∈ P.domain) (hxG : x ∈ G.domain) (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) :
    (immersionSecondForm G.map G.normal =ᶠ[𝓝 x]
        (fun y => frameMatrix (coordinateJacobian P.map y) (immersionSecondForm F.map F.normal (P.map y))) ∧
     immersionThirdForm G.map G.normal =ᶠ[𝓝 x]
        (fun y => frameCubic (coordinateJacobian P.map y) (immersionThirdForm F.map F.normal (P.map y))) ∧
     immersionFourthForm G.map G.normal =ᶠ[𝓝 x]
        (fun y => frameFourth (coordinateJacobian P.map y) (immersionFourthForm F.map F.normal (P.map y)))) ∨
    (immersionSecondForm G.map G.normal =ᶠ[𝓝 x]
        (fun y => -frameMatrix (coordinateJacobian P.map y) (immersionSecondForm F.map F.normal (P.map y))) ∧
     immersionThirdForm G.map G.normal =ᶠ[𝓝 x]
        (fun y => -frameCubic (coordinateJacobian P.map y) (immersionThirdForm F.map F.normal (P.map y))) ∧
     immersionFourthForm G.map G.normal =ᶠ[𝓝 x]
        (fun y => -frameFourth (coordinateJacobian P.map y) (immersionFourthForm F.map F.normal (P.map y)))) := by
  have h2 : immersionSecondForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal =ᶠ[𝓝 x] _ :=
    Filter.eventuallyEq_of_mem (P.isOpen_domain.mem_nhds hxP)
      (fun y hy => reparametrized_secondForm F P y hy)
  have h3 : immersionThirdForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal =ᶠ[𝓝 x] _ :=
    Filter.eventuallyEq_of_mem (P.isOpen_domain.mem_nhds hxP)
      (fun y hy => reparametrized_thirdForm F P y hy)
  have h4 : immersionFourthForm (reparametrizedImmersion F P).map
      (reparametrizedImmersion F P).normal =ᶠ[𝓝 x] _ :=
    Filter.eventuallyEq_of_mem (P.isOpen_domain.mem_nhds hxP)
      (fun y hy => reparametrized_fourthForm F P y hy)
  rcases localImmersion_forms_same_map_germ (reparametrizedImmersion F P) G x hxP hxG hf with
    ⟨g2,g3,g4⟩ | ⟨g2,g3,g4⟩
  · exact Or.inl ⟨g2.trans h2,g3.trans h3,g4.trans h4⟩
  · exact Or.inr ⟨g2.trans (h2.mono (fun y hy => congrArg Neg.neg hy)),
      g3.trans (h3.mono (fun y hy => congrArg Neg.neg hy)),
      g4.trans (h4.mono (fun y hy => congrArg Neg.neg hy))⟩

end
end SecondPinching
