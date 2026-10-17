import SecondPinching.ImmersionTensorChange
import SecondPinching.ImmersionCodazzi

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology
namespace SecondPinching
noncomputable section

/-- Actual frames in two coordinate descriptions give an orthogonal Q.
Only the germ of the parametrized immersion is compared; their chosen normals
need not agree. -/
theorem immersion_coordinate_frame_transition (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (e : LocalImmersionFrame F)
    (e' : LocalImmersionFrame G) (x : Chart4)
    (hxP : x ∈ P.domain) (hxG : x ∈ G.domain) (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      e'.coefficients x * coordinateJacobian P.map x = Q * e.coefficients (P.map x) := by
  have ht := (immersionTangent_congr_germ _ _ x hf).self_of_nhds
  have hg : immersionMetric G.map x =
      frameMatrix (coordinateJacobian P.map x) (immersionMetric F.map (P.map x)) := by
    rw [← reparametrized_metric F P x hxP]
    simp only [immersionMetric,ht]
    rfl
  let B := e.coefficients (P.map x)
  let C := e'.coefficients x * coordinateJacobian P.map x
  let Q := C * B⁻¹
  have hi : IsUnit B.det := isUnit_iff_ne_zero.mpr
    (localImmersionFrame_det_ne_zero F e _ (P.mapsTo hxP))
  have heq : Q*B = C := by
    dsimp [Q]
    rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hi,Matrix.mul_one]
  have hC : frameMatrix C (immersionMetric F.map (P.map x)) = 1 := by
    dsimp [C]
    rw [frameMatrix_composition,← hg]
    exact e'.orthonormal x hxG
  have hQQ : Q*Qᵀ = 1 := by
    have he := frameMatrix_composition Q B (immersionMetric F.map (P.map x))
    rw [heq,hC,e.orthonormal _ (P.mapsTo hxP),frameMatrix_eq_conjugate,Matrix.mul_one] at he
    exact he.symm
  refine ⟨Q,?_,heq.symm⟩
  exact (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mp
    ((Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mpr hQQ)

/-- The raw signed overlap law is a conclusion about actual derivatives.
The same Q and the same normal sign apply to h, nabla h and nabla squared h. -/
theorem immersionFrameForms_coordinate_transition (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (e : LocalImmersionFrame F)
    (e' : LocalImmersionFrame G) (x : Chart4)
    (hxP : x ∈ P.domain) (hxG : x ∈ G.domain) (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      ((immersionFrameSecond G e' x = frameMatrix Q (immersionFrameSecond F e (P.map x)) ∧
        immersionFrameThird G e' x = frameCubic Q (immersionFrameThird F e (P.map x)) ∧
        immersionFrameFourth G e' x = frameFourth Q (immersionFrameFourth F e (P.map x))) ∨
       (immersionFrameSecond G e' x = -frameMatrix Q (immersionFrameSecond F e (P.map x)) ∧
        immersionFrameThird G e' x = -frameCubic Q (immersionFrameThird F e (P.map x)) ∧
        immersionFrameFourth G e' x = -frameFourth Q (immersionFrameFourth F e (P.map x)))) := by
  obtain ⟨Q,hQ,hp⟩ := immersion_coordinate_frame_transition F G P e e' x hxP hxG hf
  refine ⟨Q,hQ,?_⟩
  rcases immersion_forms_reparametrization_germ F G P x hxP hxG hf with
    ⟨h2,h3,h4⟩ | ⟨h2,h3,h4⟩
  · left
    refine ⟨?_,?_,?_⟩
    · simp only [immersionFrameSecond,h2.self_of_nhds,← frameMatrix_composition,hp]
    · simp only [immersionFrameThird,h3.self_of_nhds,← frameCubic_composition,hp]
    · simp only [immersionFrameFourth,h4.self_of_nhds,← frameFourth_composition,hp]
  · right
    have hn2 (A : Matrix4) : frameMatrix (e'.coefficients x) (-A) =
        -frameMatrix (e'.coefficients x) A := (frameMatrixLinear _).map_neg A
    have hn3 (T : Cubic4) : frameCubic (e'.coefficients x) (-T) =
        -frameCubic (e'.coefficients x) T := (frameCubicLinear _).map_neg T
    have hn4 (H : Fourth4) : frameFourth (e'.coefficients x) (-H) =
        -frameFourth (e'.coefficients x) H := (frameFourthLinear _).map_neg H
    refine ⟨?_,?_,?_⟩
    · simp only [immersionFrameSecond,h2.self_of_nhds,hn2,← frameMatrix_composition,hp]
    · simp only [immersionFrameThird,h3.self_of_nhds,hn3,← frameCubic_composition,hp]
    · simp only [immersionFrameFourth,h4.self_of_nhds,hn4,← frameFourth_composition,hp]

/-- Normalization, symmetrization and trace removal preserve the derived
signed coordinate transition. The concrete V is not a new independent input. -/
theorem immersionLocalData_coordinate_transition (F G : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (e : LocalImmersionFrame F)
    (e' : LocalImmersionFrame G) (S : ℝ) (x : Chart4)
    (hxP : x ∈ P.domain) (hxG : x ∈ G.domain) (hf : G.map =ᶠ[𝓝 x] F.map ∘ P.map) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      ((immersionNormalizedA G e' S x = frameMatrix Q (immersionNormalizedA F e S (P.map x)) ∧
        immersionNormalizedTau G e' S x = frameCubic Q (immersionNormalizedTau F e S (P.map x)) ∧
        immersionReducedV G e' S x = frameFourth Q (immersionReducedV F e S (P.map x))) ∨
       (immersionNormalizedA G e' S x = -frameMatrix Q (immersionNormalizedA F e S (P.map x)) ∧
        immersionNormalizedTau G e' S x = -frameCubic Q (immersionNormalizedTau F e S (P.map x)) ∧
        immersionReducedV G e' S x = -frameFourth Q (immersionReducedV F e S (P.map x)))) :=
  normalized_reduced_signed_overlap S _ _ _ _ _ _
    (immersionFrameSecond_symmetric F e _ (P.mapsTo hxP))
    (immersionFrameFourth_firstThree F e _ (P.mapsTo hxP))
    (immersionFrameForms_coordinate_transition F G P e e' x hxP hxG hf)

end
end SecondPinching
