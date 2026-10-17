import SecondPinching.ImmersionGaussWeingarten

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The sphere-valued second fundamental vector: remove the induced tangent
connection and add the radial correction of the unit sphere. This formula
depends only on the ambient immersion map, not on a normal choice. -/
def sphereSecondFundamentalVector (f : Chart4 → Ambient6) (x : Chart4) (i j : Fin 4) : Ambient6 :=
  immersionSecondDerivative f x i j -
    (∑ r, immersionChristoffel f x r i j • immersionTangent f x r) +
    immersionMetric f x i j • f x

def frameSphereSecondFundamentalVector (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (i j : Fin 4) : Ambient6 :=
  ∑ a, ∑ b, (e.coefficients x i a * e.coefficients x j b) • sphereSecondFundamentalVector F.map x a b

def localSphereMeanCurvatureVector (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (x : Chart4) : Ambient6 :=
  (1/4 : ℝ) • ∑ i, frameSphereSecondFundamentalVector F e x i i

def localSphereSecondFundamentalNormSq (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (x : Chart4) : ℝ :=
  ∑ i, ∑ j, inner ℝ (frameSphereSecondFundamentalVector F e x i j) (frameSphereSecondFundamentalVector F e x i j)

theorem sphereSecondFundamentalVector_eq_normal (F : LocalSphereImmersion) (x : Chart4)
    (hx : x ∈ F.domain) (i j : Fin 4) :
    sphereSecondFundamentalVector F.map x i j=immersionSecondForm F.map F.normal x i j • F.normal x := by
  unfold sphereSecondFundamentalVector
  rw [immersion_gauss_formula F x hx i j]
  abel

theorem frameSphereSecondFundamentalVector_eq_normal (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (i j : Fin 4) :
    frameSphereSecondFundamentalVector F e x i j=immersionFrameSecond F e x i j • F.normal x := by
  unfold frameSphereSecondFundamentalVector
  simp only [sphereSecondFundamentalVector_eq_normal F x hx,smul_smul,← Finset.sum_smul]
  congr 1
  simp only [immersionFrameSecond,frameMatrix,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem localSphereMeanCurvatureVector_eq_trace (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) :
    localSphereMeanCurvatureVector F e x=(Matrix.trace (immersionFrameSecond F e x)/4) • F.normal x := by
  unfold localSphereMeanCurvatureVector
  simp only [frameSphereSecondFundamentalVector_eq_normal F e x hx,← Finset.sum_smul,smul_smul,
    Matrix.trace,Matrix.diag]
  congr 1
  ring

theorem localSphereMeanCurvatureVector_normSq (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) :
    inner ℝ (localSphereMeanCurvatureVector F e x) (localSphereMeanCurvatureVector F e x)=
      (Matrix.trace (immersionFrameSecond F e x)/4)^2 := by
  rw [localSphereMeanCurvatureVector_eq_trace F e x hx]
  simp only [real_inner_smul_left,inner_smul_right,F.normal_unit x hx,mul_one,pow_two]

theorem localSphereSecondFundamentalNormSq_eq_matrixNormSq (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) :
    localSphereSecondFundamentalNormSq F e x=matrixNormSq (immersionFrameSecond F e x) := by
  unfold localSphereSecondFundamentalNormSq matrixNormSq
  simp only [frameSphereSecondFundamentalVector_eq_normal F e x hx,real_inner_smul_left,
    inner_smul_right,F.normal_unit x hx,mul_one,pow_two]

end
end SecondPinching
