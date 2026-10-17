import SecondPinching.ImmersionNormal

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem immersionTangent_congr_germ (f g : Chart4 → Ambient6) (x : Chart4)
    (he : f =ᶠ[𝓝 x] g) : immersionTangent f =ᶠ[𝓝 x] immersionTangent g := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  funext i
  exact congrArg (fun L : Chart4 →L[ℝ] Ambient6 => L (coordinateUnit i)) hy

theorem immersionSecondDerivative_congr_germ (f g : Chart4 → Ambient6) (x : Chart4)
    (he : f =ᶠ[𝓝 x] g) :
    immersionSecondDerivative f =ᶠ[𝓝 x] immersionSecondDerivative g := by
  have ht := immersionTangent_congr_germ f g x he
  have hi (i : Fin 4) : (fun y => immersionTangent f y i) =ᶠ[𝓝 x]
      (fun y => immersionTangent g y i) := ht.mono (fun y hy => congrFun hy i)
  have hd (i : Fin 4) := (hi i).fderiv (𝕜 := ℝ)
  filter_upwards [Filter.eventually_all.mpr hd] with y hy
  funext i j
  exact congrArg (fun L : Chart4 →L[ℝ] Ambient6 => L (coordinateUnit j)) (hy i)

theorem immersionChristoffel_congr_germ (f g : Chart4 → Ambient6) (x : Chart4)
    (he : f =ᶠ[𝓝 x] g) : immersionChristoffel f =ᶠ[𝓝 x] immersionChristoffel g := by
  filter_upwards [immersionTangent_congr_germ f g x he,
    immersionSecondDerivative_congr_germ f g x he] with y h1 h2
  funext r i j
  simp only [immersionChristoffel,immersionMetric,h1,h2]

theorem coordinateCovariant2_congr_germs
    (Γ Γ' : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h g : Chart4 → Matrix4) (x : Chart4)
    (hΓ : Γ =ᶠ[𝓝 x] Γ') (hh : h =ᶠ[𝓝 x] g) :
    coordinateCovariant2 Γ h =ᶠ[𝓝 x] coordinateCovariant2 Γ' g := by
  apply (coordinateCovariant2_congr_germ Γ h g x hh).trans
  filter_upwards [hΓ] with y hy
  funext i j k
  simp only [coordinateCovariant2,hy]

theorem coordinateCovariant3_congr_germs
    (Γ Γ' : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T U : Chart4 → Cubic4) (x : Chart4)
    (hΓ : Γ =ᶠ[𝓝 x] Γ') (hT : T =ᶠ[𝓝 x] U) :
    coordinateCovariant3 Γ T =ᶠ[𝓝 x] coordinateCovariant3 Γ' U := by
  apply (coordinateCovariant3_congr_germ Γ T U x hT).trans
  filter_upwards [hΓ] with y hy
  funext i j k l
  simp only [coordinateCovariant3,hy]

/-- The coordinate tensors depend only on the germs of the actual immersion
and normal, not on extensions outside the coordinate domain. -/
theorem immersionForms_congr_germs (f g N P : Chart4 → Ambient6) (x : Chart4)
    (hf : f =ᶠ[𝓝 x] g) (hN : N =ᶠ[𝓝 x] P) :
    immersionSecondForm f N =ᶠ[𝓝 x] immersionSecondForm g P ∧
    immersionThirdForm f N =ᶠ[𝓝 x] immersionThirdForm g P ∧
    immersionFourthForm f N =ᶠ[𝓝 x] immersionFourthForm g P := by
  have hh : immersionSecondForm f N =ᶠ[𝓝 x] immersionSecondForm g P := by
    filter_upwards [immersionSecondDerivative_congr_germ f g x hf,hN] with y hy hn
    funext i j
    simp only [immersionSecondForm,hy,hn]
  have hΓ := immersionChristoffel_congr_germ f g x hf
  have ht := coordinateCovariant2_congr_germs _ _ _ _ x hΓ hh
  exact ⟨hh,ht,coordinateCovariant3_congr_germs _ _ _ _ x hΓ ht⟩

/-- For two local descriptions with the same parametrization germ, the normal
sign is deduced from the actual sphere, immersion and unit-normal conditions. -/
theorem localImmersion_normals_same_map_germ (F G : LocalSphereImmersion)
    (x : Chart4) (hxF : x ∈ F.domain) (hxG : x ∈ G.domain)
    (hf : G.map =ᶠ[𝓝 x] F.map) :
    G.normal =ᶠ[𝓝 x] F.normal ∨ G.normal =ᶠ[𝓝 x] -F.normal := by
  apply immersion_unit_normal_germ F x hxF G.normal
    ((G.smooth_normal x hxG).contDiffAt (G.isOpen_domain.mem_nhds hxG)).continuousAt
  filter_upwards [G.isOpen_domain.mem_nhds hxG,hf,hf.fderiv (𝕜 := ℝ)] with y hy hm hd
  refine ⟨G.normal_unit y hy,?_,?_⟩
  · rw [← hm]; exact G.normal_radial y hy
  · intro v
    rw [← hd]
    exact immersion_normal_tangent G y hy v

/-- The SAME local sign acts on h, nabla h and nabla^2 h. No equality of their
derivatives, nor any normal-orientation agreement, is an additional premise. -/
theorem localImmersion_forms_same_map_germ (F G : LocalSphereImmersion)
    (x : Chart4) (hxF : x ∈ F.domain) (hxG : x ∈ G.domain)
    (hf : G.map =ᶠ[𝓝 x] F.map) :
    (immersionSecondForm G.map G.normal =ᶠ[𝓝 x] immersionSecondForm F.map F.normal ∧
     immersionThirdForm G.map G.normal =ᶠ[𝓝 x] immersionThirdForm F.map F.normal ∧
     immersionFourthForm G.map G.normal =ᶠ[𝓝 x] immersionFourthForm F.map F.normal) ∨
    (immersionSecondForm G.map G.normal =ᶠ[𝓝 x] -immersionSecondForm F.map F.normal ∧
     immersionThirdForm G.map G.normal =ᶠ[𝓝 x] -immersionThirdForm F.map F.normal ∧
     immersionFourthForm G.map G.normal =ᶠ[𝓝 x] -immersionFourthForm F.map F.normal) := by
  rcases localImmersion_normals_same_map_germ F G x hxF hxG hf with hp | hn
  · exact Or.inl (immersionForms_congr_germs _ _ _ _ x hf hp)
  · right
    have h := immersionForms_congr_germs _ _ _ _ x hf hn
    obtain ⟨h2,h3,h4⟩ := immersion_forms_normal_reversal F.map F.normal
    simpa only [h2,h3,h4] using h

end
end SecondPinching
