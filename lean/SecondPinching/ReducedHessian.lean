import SecondPinching.GeometricNormalization

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

theorem frameFourth_swap12 (Q : Matrix4) (D : Fourth4) :
    frameFourth Q (fun i j k l => D j i k l) =
      fun i j k l => frameFourth Q D j i k l := by
  funext i j k l
  simp only [frameFourth,frameCubic,frameMatrix,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

theorem frameFourth_swap23 (Q : Matrix4) (D : Fourth4) :
    frameFourth Q (fun i j k l => D i k j l) =
      fun i j k l => frameFourth Q D i k j l := by
  funext i j k l
  simp only [frameFourth,frameCubic,frameMatrix,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

theorem frameFourth_swap34 (Q : Matrix4) (D : Fourth4) :
    frameFourth Q (fun i j k l => D i j l k) =
      fun i j k l => frameFourth Q D i j l k := by
  funext i j k l
  simp only [frameFourth,frameCubic,frameMatrix,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

theorem frameFourth_firstThree (Q : Matrix4) (D : Fourth4)
    (hD : FirstThreeSymmetric D) : FirstThreeSymmetric (frameFourth Q D) := by
  have h12 : (fun i j k l => D j i k l) = D := by funext i j k l; exact (hD.1 i j k l).symm
  have h23 : (fun i j k l => D i k j l) = D := by funext i j k l; exact (hD.2 i j k l).symm
  have h1 := frameFourth_swap12 Q D
  have h2 := frameFourth_swap23 Q D
  rw [h12] at h1
  rw [h23] at h2
  exact ⟨fun i j k l => congrFun (congrFun (congrFun (congrFun h1 i) j) k) l,
    fun i j k l => congrFun (congrFun (congrFun (congrFun h2 i) j) k) l⟩

/-- Symmetrization commutes with changing frames; the only symmetry assumed
is the first-three-slot symmetry available for the geometric Hessian. -/
theorem frameFourth_symmetrize (Q : Matrix4) (D : Fourth4)
    (hD : FirstThreeSymmetric D) :
    frameFourth Q (symmetrizeFourth D) = symmetrizeFourth (frameFourth Q D) := by
  have hav (X : Fourth4) (hX : FirstThreeSymmetric X) :
      symmetrizeFourth X = (1/4 : ℝ) •
        (X + (fun i j k l => X i j l k) + (fun i j k l => X i k l j) +
          (fun i j k l => X j k l i)) := by
    rw [symmetrizeFourth_firstThree X hX]
    funext i j k l
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  rw [hav D hD,hav _ (frameFourth_firstThree Q D hD)]
  change frameFourthLinear Q (_ • (_+_+_+_)) = _
  rw [map_smul,map_add,map_add,map_add]
  change (1/4 : ℝ) • (frameFourth Q D +
    frameFourth Q (fun i j k l => D i j l k) +
    frameFourth Q (fun i j k l => D i k l j) +
    frameFourth Q (fun i j k l => D j k l i)) = _
  rw [frameFourth_swap34 Q D]
  have h23 := frameFourth_swap23 Q (fun i j k l => D i j l k)
  rw [frameFourth_swap34 Q D] at h23
  have h12 := frameFourth_swap12 Q (fun i j k l => D i k l j)
  rw [h23] at h12
  rw [h23,h12]

theorem symmetrizeFourth_neg (D : Fourth4) : symmetrizeFourth (-D) = -symmetrizeFourth D := by
  funext i j k l
  simp [symmetrizeFourth,Finset.sum_neg_distrib]

theorem frameFourth_ordinaryTraceAdjoint (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (X : Matrix4) (hX : X.IsSymm) :
    frameFourth Q (ordinaryTraceAdjoint X) = ordinaryTraceAdjoint (frameMatrix Q X) := by
  have he (Y : Matrix4) : weightedTraceAdjoint (1 : Matrix4) Y = ordinaryTraceAdjoint Y := by
    funext i j k l
    simp only [weightedTraceAdjoint,ordinaryTraceAdjoint]
    ring
  rw [← he,frameFourth_weightedTraceAdjoint Q hQ 1 X (Matrix.isSymm_one) hX,
    frameMatrix_one Q hQ,he]

/-- The actual trace correction and reduced Hessian in an arbitrary
orthonormal frame; the diagonal specialization is literally the old construction. -/
def intrinsicHessianTraceCorrection (A : Matrix4) (t : ℝ) : Fourth4 :=
  ordinaryTraceAdjoint ((-3*t/8) • A)

def intrinsicHessianRemainder (A : Matrix4) (t : ℝ) (D : Fourth4) : Fourth4 :=
  symmetrizeFourth D - intrinsicHessianTraceCorrection A t

theorem intrinsicHessianRemainder_diagonal (μ : Vector4) (t : ℝ) (D : Fourth4) :
    intrinsicHessianRemainder (Matrix.diagonal μ) t D = hessianRemainder μ t D := rfl

theorem frame_intrinsicHessianRemainder (Q : Matrix4) (hQ : OrthogonalFrame Q)
    (A : Matrix4) (hA : A.IsSymm) (t : ℝ) (D : Fourth4) (hD : FirstThreeSymmetric D) :
    intrinsicHessianRemainder (frameMatrix Q A) t (frameFourth Q D) =
      frameFourth Q (intrinsicHessianRemainder A t D) := by
  have hs : ((-3*t/8) • A).IsSymm := by
    ext i j; simp only [Matrix.transpose_apply,Matrix.smul_apply,hA.apply]
  unfold intrinsicHessianRemainder intrinsicHessianTraceCorrection
  rw [← frameFourth_symmetrize Q D hD]
  have hm := (frameMatrixLinear Q).map_smul (-3*t/8) A
  change frameMatrix Q ((-3*t/8) • A) = (-3*t/8) • frameMatrix Q A at hm
  rw [← hm,← frameFourth_ordinaryTraceAdjoint Q hQ _ hs]
  exact ((frameFourthLinear Q).map_sub _ _).symm

theorem intrinsicHessianRemainder_normal_reversal (A : Matrix4) (t : ℝ) (D : Fourth4) :
    intrinsicHessianRemainder (-A) t (-D) = -intrinsicHessianRemainder A t D := by
  unfold intrinsicHessianRemainder intrinsicHessianTraceCorrection
  rw [symmetrizeFourth_neg,smul_neg]
  have hn := ordinaryTraceAdjointLinear.map_neg ((-3*t/8) • A)
  change ordinaryTraceAdjoint (-((-3*t/8) • A)) =
    -ordinaryTraceAdjoint ((-3*t/8) • A) at hn
  rw [hn]
  abel

end
end SecondPinching
