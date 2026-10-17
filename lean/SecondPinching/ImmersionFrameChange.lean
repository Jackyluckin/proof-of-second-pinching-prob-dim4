import SecondPinching.ImmersionLocalData
import SecondPinching.ImmersionConnection

set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- Composition of covariant component changes, without assuming that the
coordinate basis before either change is orthonormal. -/
theorem frameMatrix_composition (Q P A : Matrix4) :
    frameMatrix (Q*P) A = frameMatrix Q (frameMatrix P A) := by
  simp only [frameMatrix_eq_conjugate,Matrix.transpose_mul]
  noncomm_ring

theorem frameCubic_composition (Q P : Matrix4) (T : Cubic4) :
    frameCubic (Q*P) T = frameCubic Q (frameCubic P T) := by
  funext i j k
  change (∑ a, (Q*P) i a * frameMatrix (Q*P) (T a) j k) =
    ∑ u, Q i u * frameMatrix Q (frameCubic P T u) j k
  have hm u : frameMatrix Q (frameCubic P T u) =
      ∑ a, P u a • frameMatrix Q (frameMatrix P (T a)) := by
    rw [frameCubic_slice P T u]
    change (frameMatrixLinear Q) (∑ a, P u a • frameMatrix P (T a)) = _
    rw [map_sum]
    simp_rw [map_smul]
    rfl
  trans ∑ a, (Q*P) i a * frameMatrix Q (frameMatrix P (T a)) j k
  · apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun X : Matrix4 => (Q*P) i a * X j k)
      (frameMatrix_composition Q P (T a))
  simp only [hm,Matrix.mul_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro a _
  ring

theorem frameFourth_composition (Q P : Matrix4) (D : Fourth4) :
    frameFourth (Q*P) D = frameFourth Q (frameFourth P D) := by
  funext i
  rw [frameFourth_slice,frameFourth_slice]
  simp_rw [frameCubic_composition,Matrix.mul_apply,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  rw [frameFourth_slice]
  change (∑ a, (Q i u * P u a) • frameCubic Q (frameCubic P (D a))) =
    Q i u • (frameCubicLinear Q) (∑ a, P u a • frameCubic P (D a))
  rw [map_sum,Finset.smul_sum]
  simp_rw [map_smul,mul_smul]
  rfl

/-- Two local orthonormal frames for the same parametrization differ by an
actual orthogonal matrix, constructed without choosing eigenvectors. -/
theorem localImmersionFrame_transition (F : LocalSphereImmersion)
    (e e' : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧ e'.coefficients x = Q * e.coefficients x := by
  let P := e.coefficients x
  let P' := e'.coefficients x
  let Q := P' * P⁻¹
  have hi : IsUnit P.det := isUnit_iff_ne_zero.mpr (localImmersionFrame_det_ne_zero F e x hx)
  have heq : Q*P = P' := by
    dsimp [Q]
    rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hi,Matrix.mul_one]
  have hQQ : Q*Qᵀ = 1 := by
    have he := frameMatrix_composition Q P (immersionMetric F.map x)
    rw [heq,e.orthonormal x hx,e'.orthonormal x hx,frameMatrix_eq_conjugate,Matrix.mul_one] at he
    exact he.symm
  refine ⟨Q,?_,heq.symm⟩
  exact (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mp
    ((Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mpr hQQ)

theorem immersionFrameForms_transition (F : LocalSphereImmersion)
    (e e' : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      immersionFrameSecond F e' x = frameMatrix Q (immersionFrameSecond F e x) ∧
      immersionFrameThird F e' x = frameCubic Q (immersionFrameThird F e x) ∧
      immersionFrameFourth F e' x = frameFourth Q (immersionFrameFourth F e x) := by
  obtain ⟨Q,hQ,hp⟩ := localImmersionFrame_transition F e e' x hx
  refine ⟨Q,hQ,?_,?_,?_⟩
  · simp only [immersionFrameSecond,hp,frameMatrix_composition]
  · simp only [immersionFrameThird,hp,frameCubic_composition]
  · simp only [immersionFrameFourth,hp,frameFourth_composition]

theorem immersionFrameSecond_symmetric (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) :
    (immersionFrameSecond F e x).IsSymm :=
  frameMatrix_symmetric _ _ (immersionSecondForm_symmetric F x hx)

/-- The normalized fields and the constructed V satisfy the exact transition
required by LocalIntegrands. The first-three symmetry is still an explicit
geometric input; no new transformation assumption about V is used. -/
theorem immersionLocalData_frame_transition (F : LocalSphereImmersion)
    (e e' : LocalImmersionFrame F) (S : ℝ) (x : Chart4) (hx : x ∈ F.domain)
    (hH : FirstThreeSymmetric (immersionFrameFourth F e x)) :
    ∃ Q : Matrix4, OrthogonalFrame Q ∧
      immersionNormalizedA F e' S x = frameMatrix Q (immersionNormalizedA F e S x) ∧
      immersionNormalizedTau F e' S x = frameCubic Q (immersionNormalizedTau F e S x) ∧
      immersionReducedV F e' S x = frameFourth Q (immersionReducedV F e S x) := by
  obtain ⟨Q,hQ,hh,ht,hd⟩ := immersionFrameForms_transition F e e' x hx
  have hs : (immersionNormalizedA F e S x).IsSymm := by
    ext i j
    simp only [immersionNormalizedA,normalizeSecond,Matrix.transpose_apply,Matrix.smul_apply,
      (immersionFrameSecond_symmetric F e x hx).apply]
  have hD : FirstThreeSymmetric (immersionNormalizedD F e S x) := by
    constructor
    · intro i j k l; simp only [immersionNormalizedD,normalizeFourth,Pi.smul_apply,hH.1]
    · intro i j k l; simp only [immersionNormalizedD,normalizeFourth,Pi.smul_apply,hH.2]
  obtain ⟨ha,hb,hc⟩ := normalize_frame S Q
    (immersionFrameSecond F e x) (immersionFrameThird F e x) (immersionFrameFourth F e x)
  refine ⟨Q,hQ,?_,?_,?_⟩
  · simpa only [immersionNormalizedA,hh] using ha
  · simpa only [immersionNormalizedTau,ht] using hb
  · unfold immersionReducedV immersionNormalizedA immersionNormalizedD
    rw [hh,hd,ha,hc]
    exact frame_intrinsicHessianRemainder Q hQ _ hs _ _ hD

end
end SecondPinching
