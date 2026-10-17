import SecondPinching.SphereSecondFundamentalVector
import SecondPinching.GlobalPinchingAverages

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff Manifold
namespace SecondPinching
noncomputable section
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace Chart4 M]
    [IsManifold 𝓘(ℝ,Chart4) ∞ M]

/-- Squared norm of the sphere-valued second fundamental form at the point,
computed from the actual immersion derivatives in its chart-centered frame. -/
def globalSecondFundamentalNormSq (F : GlobalSphereImmersion M) (x : M) : ℝ :=
  localSphereSecondFundamentalNormSq (globalImmersionLocal F x) (globalImmersionLocalFrame F x) (chartAt Chart4 x x)

def globalSphereMeanCurvatureVector (F : GlobalSphereImmersion M) (x : M) : Ambient6 :=
  localSphereMeanCurvatureVector (globalImmersionLocal F x) (globalImmersionLocalFrame F x) (chartAt Chart4 x x)

def globalMeanCurvatureNormSq (F : GlobalSphereImmersion M) (x : M) : ℝ :=
  inner ℝ (globalSphereMeanCurvatureVector F x) (globalSphereMeanCurvatureVector F x)

theorem rawSecondNorm_overlap (F : GlobalSphereImmersion M) (p q x : M)
    (hp : x ∈ globalImmersionLocalSource F p) (hq : x ∈ globalImmersionLocalSource F q) :
    matrixNormSq (immersionFrameSecond (globalImmersionLocal F q) (globalImmersionLocalFrame F q) (chartAt Chart4 q x)) =
      matrixNormSq (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) (chartAt Chart4 p x)) := by
  obtain ⟨Q,hQ,h⟩ := immersionAtlas_raw_transitions (globalImmersionLocal F) (globalImmersionLocalFrame F)
    (fun p => chartAt Chart4 p) (globalImmersionLocalSource F) (fun _ _ hx => hx.2)
    (globalImmersionLocal_coordinate_overlaps F) p q x hp hq
  rcases h with ⟨hh,_,_⟩ | ⟨hh,_,_⟩
  · rw [hh,frameMatrix_normSq Q hQ]
  · rw [hh]
    simpa only [matrixNormSq,Matrix.neg_apply,neg_sq] using
      frameMatrix_normSq Q hQ (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) (chartAt Chart4 p x))

theorem rawMeanNorm_overlap (F : GlobalSphereImmersion M) (p q x : M)
    (hp : x ∈ globalImmersionLocalSource F p) (hq : x ∈ globalImmersionLocalSource F q) :
    (Matrix.trace (immersionFrameSecond (globalImmersionLocal F q) (globalImmersionLocalFrame F q) (chartAt Chart4 q x))/4)^2 =
      (Matrix.trace (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) (chartAt Chart4 p x))/4)^2 := by
  obtain ⟨Q,hQ,h⟩ := immersionAtlas_raw_transitions (globalImmersionLocal F) (globalImmersionLocalFrame F)
    (fun p => chartAt Chart4 p) (globalImmersionLocalSource F) (fun _ _ hx => hx.2)
    (globalImmersionLocal_coordinate_overlaps F) p q x hp hq
  rcases h with ⟨hh,_,_⟩ | ⟨hh,_,_⟩
  · rw [hh,frameMatrix_trace Q hQ]
  · rw [hh,Matrix.trace_neg,frameMatrix_trace Q hQ,neg_div,neg_sq]

/-- These identities establish the meaning of the global invariants in every
actual local frame, including either choice of normal. -/
theorem globalSecondFundamentalNormSq_represent (F : GlobalSphereImmersion M) (p x : M)
    (hx : x ∈ globalImmersionLocalSource F p) :
    globalSecondFundamentalNormSq F x =
      matrixNormSq (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) (chartAt Chart4 p x)) := by
  unfold globalSecondFundamentalNormSq
  rw [localSphereSecondFundamentalNormSq_eq_matrixNormSq _ _ _ (globalImmersionLocal_center F x)]
  exact rawSecondNorm_overlap F p x x hx (globalImmersionLocalSource_center F x)

theorem globalMeanCurvatureNormSq_represent (F : GlobalSphereImmersion M) (p x : M)
    (hx : x ∈ globalImmersionLocalSource F p) :
    globalMeanCurvatureNormSq F x =
      (Matrix.trace (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) (chartAt Chart4 p x))/4)^2 := by
  unfold globalMeanCurvatureNormSq globalSphereMeanCurvatureVector
  rw [localSphereMeanCurvatureVector_normSq _ _ _ (globalImmersionLocal_center F x)]
  exact rawMeanNorm_overlap F p x x hx (globalImmersionLocalSource_center F x)

theorem contMDiff_globalSecondFundamentalNormSq (F : GlobalSphereImmersion M) :
    ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ (globalSecondFundamentalNormSq F) := by
  apply contMDiff_of_immersion_local_representation F _
    (fun p y => matrixNormSq (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) y))
  · intro p
    have hh := (contDiffOn_immersionFrameForms (globalImmersionLocal F p) (globalImmersionLocalFrame F p)).1
    unfold matrixNormSq
    fun_prop
  · exact globalSecondFundamentalNormSq_represent F

theorem contMDiff_globalMeanCurvatureNormSq (F : GlobalSphereImmersion M) :
    ContMDiff 𝓘(ℝ,Chart4) 𝓘(ℝ,ℝ) ∞ (globalMeanCurvatureNormSq F) := by
  apply contMDiff_of_immersion_local_representation F _
    (fun p y => (Matrix.trace (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) y)/4)^2)
  · intro p
    exact ((contDiffOn_matrix_trace
      (contDiffOn_immersionFrameForms (globalImmersionLocal F p) (globalImmersionLocalFrame F p)).1).div_const 4).pow 2
  · exact globalMeanCurvatureNormSq_represent F

/-- Minimality is vanishing of the actual spherical mean-curvature vector. -/
def IsMinimalSphereImmersion (F : GlobalSphereImmersion M) : Prop :=
  ∀ x, globalSphereMeanCurvatureVector F x=0

def HasConstantSecondFundamentalNorm (F : GlobalSphereImmersion M) (S : ℝ) : Prop :=
  ∀ x, globalSecondFundamentalNormSq F x=S

theorem isMinimalSphereImmersion_iff_local_trace (F : GlobalSphereImmersion M) :
    IsMinimalSphereImmersion F ↔ ∀ p y, y ∈ (globalImmersionLocal F p).domain →
      Matrix.trace (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) y)=0 := by
  constructor
  · intro h p y hy
    obtain ⟨hx,he⟩ := inverse_coordinate_mem_localSource F p y hy
    have hz : globalMeanCurvatureNormSq F ((chartAt Chart4 p).symm y)=0 := by
      unfold globalMeanCurvatureNormSq
      rw [h]
      simp
    rw [globalMeanCurvatureNormSq_represent F p _ hx,he] at hz
    have ht : Matrix.trace (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) y)/4=0 :=
      sq_eq_zero_iff.mp hz
    linarith
  · intro h x
    unfold globalSphereMeanCurvatureVector
    rw [localSphereMeanCurvatureVector_eq_trace _ _ _ (globalImmersionLocal_center F x),
      h x _ (globalImmersionLocal_center F x)]
    simp

theorem hasConstantSecondFundamentalNorm_iff_local_norm (F : GlobalSphereImmersion M) (S : ℝ) :
    HasConstantSecondFundamentalNorm F S ↔ ∀ p y, y ∈ (globalImmersionLocal F p).domain →
      matrixNormSq (immersionFrameSecond (globalImmersionLocal F p) (globalImmersionLocalFrame F p) y)=S := by
  constructor
  · intro h p y hy
    obtain ⟨hx,he⟩ := inverse_coordinate_mem_localSource F p y hy
    have hz := h ((chartAt Chart4 p).symm y)
    rw [globalSecondFundamentalNormSq_represent F p _ hx,he] at hz
    exact hz
  · intro h x
    rw [globalSecondFundamentalNormSq_represent F x x (globalImmersionLocalSource_center F x)]
    exact h x _ (globalImmersionLocal_center F x)

end
end SecondPinching
