import SecondPinching.SmoothGramSchmidt

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
open InnerProductSpace
namespace SecondPinching
noncomputable section
attribute [local fun_prop] ContDiffOn.inner contDiff_inner

def immersionTangentCoordinates (f : Chart4 → Ambient6) (x : Chart4) (w : Ambient6) : Chart4 :=
  (immersionMetric f x)⁻¹ *ᵥ (fun j => inner ℝ (immersionTangent f x j) w)

theorem immersionTangent_inner_derivative (f : Chart4 → Ambient6) (x z : Chart4) (i : Fin 4) :
    inner ℝ (immersionTangent f x i) (fderiv ℝ f x z)=(immersionMetric f x *ᵥ z) i := by
  rw [immersionTangent_expansion,inner_sum]
  simp only [inner_smul_right,Matrix.mulVec,dotProduct,immersionMetric,Matrix.gram_apply]
  apply Finset.sum_congr rfl; intro j _; ring

theorem immersionTangentCoordinates_derivative (f : Chart4 → Ambient6) (x z : Chart4)
    (hi : Function.Injective (fderiv ℝ f x)) :
    immersionTangentCoordinates f x (fderiv ℝ f x z)=z := by
  unfold immersionTangentCoordinates
  simp_rw [immersionTangent_inner_derivative]
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (immersionMetric_det_ne_zero f x hi)),Matrix.one_mulVec]

theorem immersionTangentCoordinates_reconstruct (f : Chart4 → Ambient6) (x : Chart4)
    (hi : Function.Injective (fderiv ℝ f x)) (w : Ambient6)
    (hw : w ∈ (fderiv ℝ f x).toLinearMap.range) :
    fderiv ℝ f x (immersionTangentCoordinates f x w)=w := by
  obtain ⟨z,rfl⟩ := hw
  exact congrArg (fderiv ℝ f x) (immersionTangentCoordinates_derivative f x z hi)

def immersionGramSchmidtVectors (F : LocalSphereImmersion) (x : Chart4) : Fin 4 → Ambient6 :=
  gramSchmidtNormed ℝ (immersionTangent F.map x)

theorem immersionTangent_linearIndependent (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) : LinearIndependent ℝ (immersionTangent F.map x) :=
  (Pi.linearIndependent_single_one (Fin 4) ℝ).map' (fderiv ℝ F.map x).toLinearMap
    (LinearMap.ker_eq_bot.mpr (F.injective_derivative x hx))

theorem immersionGramSchmidtVectors_mem_range (F : LocalSphereImmersion) (x : Chart4) (i : Fin 4) :
    immersionGramSchmidtVectors F x i ∈ (fderiv ℝ F.map x).toLinearMap.range := by
  let P := (fderiv ℝ F.map x).toLinearMap.range
  have hs : Submodule.span ℝ (Set.range (immersionTangent F.map x)) ≤ P := by
    apply Submodule.span_le.mpr
    rintro z ⟨j,rfl⟩
    exact ⟨coordinateUnit j,rfl⟩
  have hg : gramSchmidt ℝ (immersionTangent F.map x) i ∈ P :=
    hs ((Submodule.span_mono (Set.image_subset_range _ _)) (gramSchmidt_mem_span ℝ _ (le_refl i)))
  exact P.smul_mem _ hg

theorem contDiffOn_immersionGramSchmidtVectors (F : LocalSphereImmersion) (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => immersionGramSchmidtVectors F x i) F.domain :=
  contDiffOn_gramSchmidtNormed_four (immersionTangent F.map)
    (fun j => contDiffOn_immersionTangent F.isOpen_domain F.smooth_map j)
    (immersionTangent_linearIndependent F) i

def constructedFrameCoefficients (F : LocalSphereImmersion) (x : Chart4) : Matrix4 :=
  fun i => immersionTangentCoordinates F.map x (immersionGramSchmidtVectors F x i)

theorem contDiffOn_constructedFrameCoefficients (F : LocalSphereImmersion) :
    ContDiffOn ℝ ∞ (constructedFrameCoefficients F) F.domain := by
  have hi := contDiffOn_matrix4_inverse (contDiffOn_immersionMetric F.isOpen_domain F.smooth_map)
    (fun x hx => immersionMetric_det_ne_zero F.map x (F.injective_derivative x hx))
  have ht (i : Fin 4) := contDiffOn_immersionTangent F.isOpen_domain F.smooth_map i
  have hg (i : Fin 4) := contDiffOn_immersionGramSchmidtVectors F i
  unfold constructedFrameCoefficients immersionTangentCoordinates Matrix.mulVec dotProduct
  fun_prop

theorem frameMatrix_metric_eq_inner (f : Chart4 → Ambient6) (x : Chart4) (B : Matrix4) (i j : Fin 4) :
    frameMatrix B (immersionMetric f x) i j =
      inner ℝ (fderiv ℝ f x (B i)) (fderiv ℝ f x (B j)) := by
  rw [immersionTangent_expansion f x (B i),immersionTangent_expansion f x (B j),sum_inner]
  simp only [inner_sum,real_inner_smul_left,inner_smul_right,Finset.mul_sum,
    frameMatrix,immersionMetric,Matrix.gram_apply]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem constructedFrameCoefficients_orthonormal (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) : frameMatrix (constructedFrameCoefficients F x) (immersionMetric F.map x)=1 := by
  have he (i : Fin 4) : fderiv ℝ F.map x (constructedFrameCoefficients F x i)=
      immersionGramSchmidtVectors F x i :=
    immersionTangentCoordinates_reconstruct F.map x (F.injective_derivative x hx) _
      (immersionGramSchmidtVectors_mem_range F x i)
  have ho := gramSchmidtNormed_orthonormal (immersionTangent_linearIndependent F x hx)
  ext i j
  rw [frameMatrix_metric_eq_inner,he i,he j]
  exact (orthonormal_iff_ite.mp ho) i j

/-- A smooth orthonormal frame constructed from the actual coordinate
tangents. This eliminates a supplied-frame premise on every local domain. -/
def constructedImmersionFrame (F : LocalSphereImmersion) : LocalImmersionFrame F where
  coefficients := constructedFrameCoefficients F
  smooth := contDiffOn_constructedFrameCoefficients F
  orthonormal := constructedFrameCoefficients_orthonormal F

end
end SecondPinching
