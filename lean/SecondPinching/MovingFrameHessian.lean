import SecondPinching.ImmersionConstancyBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Ordinary component derivatives; all three covariant slots remain visible. -/
def cubicDerivative (T : Chart4 → Cubic4) (x v : Chart4) : Cubic4 :=
  fun i j k => fderiv ℝ (fun y => T y i j k) x v

/-- Connection action on all three slots, including the previous derivative slot. -/
def cubicConnectionAction (O : Matrix4) (T : Cubic4) : Cubic4 := fun i j k =>
  ∑ r, (O i r*T r j k + O j r*T i r k + O k r*T i j r)

theorem matrixDerivative_sum_smul (c : Fin 4 → Chart4 → ℝ)
    (A : Fin 4 → Chart4 → Matrix4) (x v : Chart4)
    (hc : ∀ a, DifferentiableAt ℝ (c a) x)
    (hA : ∀ a, DifferentiableAt ℝ (A a) x) :
    matrixDerivative (fun y => ∑ a, c a y • A a y) x v =
      ∑ a, (fderiv ℝ (c a) x v • A a x + c a x • matrixDerivative (A a) x v) := by
  have ha (a i j : Fin 4) : DifferentiableAt ℝ (fun y => A a y i j) x := by fun_prop
  ext i j
  simp only [matrixDerivative, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  erw [fderiv_fun_sum (u := Finset.univ) (fun a _ => (hc a).mul (ha a i j))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl; intro a _
  erw [fderiv_fun_mul (hc a) (ha a i j)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- A scalar weighted sum of matrix slices packages the first-slot connection. -/
theorem movingFrame_cubic_slice_algebra (B D C O : Matrix4) (T K : Cubic4)
    (hO : O*B = D+B*C) (i : Fin 4) :
    (∑ a, (D i a • frameMatrix B (T a) + B i a •
      (O*frameMatrix B (T a) + frameMatrix B (T a)*Oᵀ +
        frameMatrix B (Matrix.of (K a) + ∑ r, C a r • Matrix.of (T r))))) =
      Matrix.of (fun j k => cubicConnectionAction O (frameCubic B T) i j k) +
        Matrix.of (fun j k => frameCubic B K i j k) := by
  have hf (a : Fin 4) : frameMatrix B (Matrix.of (K a) + ∑ r, C a r • Matrix.of (T r)) =
      frameMatrix B (K a) + ∑ r, C a r • frameMatrix B (T r) := by
    change frameMatrixLinear B _ = _
    rw [map_add, map_sum]
    simp only [map_smul]; rfl
  have hc : (∑ a, D i a • frameMatrix B (T a)) +
      (∑ a, B i a • ∑ r, C a r • frameMatrix B (T r)) =
      ∑ r, O i r • Matrix.of (frameCubic B T r) := by
    simp only [Finset.smul_sum, smul_smul, frameCubic_slice]
    rw [Finset.sum_comm (f := fun a r => (B i a * C a r) • frameMatrix B (T r))]
    simp_rw [← Finset.sum_smul]
    rw [← Finset.sum_add_distrib]
    simp_rw [← add_smul]
    have ho (a : Fin 4) := congrFun (congrFun hO i) a
    simp only [Matrix.mul_apply, Matrix.add_apply] at ho
    simp_rw [← ho, Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    change (∑ a, (O i r * B r a) • frameMatrix B (T a)) = O i r • (∑ a, B r a • frameMatrix B (T a))
    simp only [Finset.smul_sum, smul_smul]
  have hj : (∑ a, B i a • (O*frameMatrix B (T a))) =
      O*Matrix.of (frameCubic B T i) := by
    change _ = O*(∑ a, B i a • frameMatrix B (T a))
    rw [Matrix.mul_sum]
    simp only [Matrix.mul_smul]
  have hk : (∑ a, B i a • (frameMatrix B (T a)*Oᵀ)) =
      Matrix.of (frameCubic B T i)*Oᵀ := by
    change _ = (∑ a, B i a • frameMatrix B (T a))*Oᵀ
    rw [Matrix.sum_mul]
    simp only [Matrix.smul_mul]
  simp only [hf, smul_add, Finset.sum_add_distrib]
  have he : (∑ a, D i a • frameMatrix B (T a)) +
      ((∑ a, B i a • (O*frameMatrix B (T a))) +
        (∑ a, B i a • (frameMatrix B (T a)*Oᵀ)) +
        ((∑ a, B i a • frameMatrix B (K a)) +
          (∑ a, B i a • ∑ r, C a r • frameMatrix B (T r)))) =
      ((∑ a, D i a • frameMatrix B (T a)) +
        (∑ a, B i a • ∑ r, C a r • frameMatrix B (T r))) +
      (∑ a, B i a • (O*frameMatrix B (T a))) +
      (∑ a, B i a • (frameMatrix B (T a)*Oᵀ)) +
      (∑ a, B i a • frameMatrix B (K a)) := by abel
  rw [he, hc, hj, hk]
  have hK : (∑ a, B i a • frameMatrix B (K a)) = Matrix.of (frameCubic B K i) := (frameCubic_slice B K i).symm
  rw [hK]
  ext j k
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, cubicConnectionAction,
    Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl; intro r _; ring


theorem coordinateCovariant3_matrix (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T : Chart4 → Cubic4) (x : Chart4) (a l : Fin 4) :
    matrixDerivative (fun y => T y a) x (coordinateUnit l) =
      (Matrix.of (fun j k => coordinateCovariant3 Γ T x a j k l) +
        ∑ r, coordinateConnectionMatrix Γ x l a r • Matrix.of (T x r)) +
      coordinateConnectionMatrix Γ x l * Matrix.of (T x a) +
      Matrix.of (T x a) * (coordinateConnectionMatrix Γ x l)ᵀ := by
  ext j k
  simp only [matrixDerivative, coordinateCovariant3, coordinateConnectionMatrix,
    Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_add_distrib]
  have he : (∑ r, Γ x r k l*T x a j r) = ∑ r, T x a j r*Γ x r k l := by
    apply Finset.sum_congr rfl; intro r _; ring
  rw [he]; ring

/-- Differentiation in a coordinate direction. The correction on each of the
three slots is present; the fourth slot is transformed in the next theorem. -/
theorem immersionFrameThird_coordinate_derivative (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (x : Chart4) (hx : x ∈ F.domain) (l : Fin 4) :
    cubicDerivative (immersionFrameThird F e) x (coordinateUnit l) =
      cubicConnectionAction (immersionMovingConnection F e x l) (immersionFrameThird F e x) +
      frameCubic (e.coefficients x) (fun i j k => immersionFourthForm F.map F.normal x i j k l) := by
  have hb := ((e.smooth x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have ht := (((contDiffOn_immersionForms F).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hc (i a : Fin 4) : DifferentiableAt ℝ (fun y => e.coefficients y i a) x := by fun_prop
  have hta (a : Fin 4) : DifferentiableAt ℝ (fun y => immersionThirdForm F.map F.normal y a) x := by fun_prop
  have hm (a : Fin 4) : DifferentiableAt ℝ
      (fun y => frameMatrix (e.coefficients y) (immersionThirdForm F.map F.normal y a)) x := by
    unfold frameMatrix; fun_prop
  have he (i : Fin 4) : (fun y => immersionFrameThird F e y i) =
      (fun y => ∑ a, e.coefficients y i a • frameMatrix (e.coefficients y)
        (immersionThirdForm F.map F.normal y a)) := by
    funext y; exact frameCubic_slice _ _ i
  have hd (a : Fin 4) : matrixDerivative
      (fun y => frameMatrix (e.coefficients y) (immersionThirdForm F.map F.normal y a))
      x (coordinateUnit l) =
      immersionMovingConnection F e x l * frameMatrix (e.coefficients x) (immersionThirdForm F.map F.normal x a) +
      frameMatrix (e.coefficients x) (immersionThirdForm F.map F.normal x a) * (immersionMovingConnection F e x l)ᵀ +
      frameMatrix (e.coefficients x) ((Matrix.of (fun j k => immersionFourthForm F.map F.normal x a j k l)) +
        ∑ r, coordinateConnectionMatrix (immersionChristoffel F.map) x l a r • Matrix.of (immersionThirdForm F.map F.normal x r)) := by
    rw [matrixDerivative_frameMatrix _ _ x _ hb (hta a),
      coordinateCovariant3_matrix (immersionChristoffel F.map) (immersionThirdForm F.map F.normal) x a l]
    exact movingFrame_derivative_algebra _ _ _ _ _ _ (immersionMovingConnection_action F e x hx l)
  funext i
  change matrixDerivative (fun y => immersionFrameThird F e y i) x (coordinateUnit l) = _
  rw [he i, matrixDerivative_sum_smul _ _ _ _ (hc i) hm]
  simp_rw [hd]
  exact movingFrame_cubic_slice_algebra _ _ _ _ _ _ (immersionMovingConnection_action F e x hx l) i


/-- The same induced connection evaluated in the actual frame direction e_l. -/
def immersionFrameConnection (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (l : Fin 4) : Matrix4 :=
  ∑ c, e.coefficients x l c • immersionMovingConnection F e x c

theorem immersionFrameConnection_skew (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (l : Fin 4) :
    (immersionFrameConnection F e x l)ᵀ = -immersionFrameConnection F e x l := by
  unfold immersionFrameConnection
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, immersionMovingConnection_skew F e x hx,
    smul_neg, Finset.sum_neg_distrib]

theorem frameFourth_last_slot (B : Matrix4) (H : Fourth4) (l : Fin 4) :
    (fun i j k => frameFourth B H i j k l : Cubic4) =
      ∑ d, B l d • frameCubic B (fun a b c => H a b c d) := by
  funext i j k
  simp only [frameFourth, frameCubic, frameMatrix, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _; ring

theorem immersionFrameSecond_frame_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (l : Fin 4) :
    matrixDerivative (immersionFrameSecond F e) x (e.coefficients x l) =
      immersionFrameConnection F e x l * immersionFrameSecond F e x +
      immersionFrameSecond F e x * (immersionFrameConnection F e x l)ᵀ +
      Matrix.of (fun i j => immersionFrameThird F e x i j l) := by
  have hd : matrixDerivative (immersionFrameSecond F e) x (e.coefficients x l) =
      ∑ c, e.coefficients x l c • matrixDerivative (immersionFrameSecond F e) x (coordinateUnit c) := by
    ext i j
    simp only [matrixDerivative, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    conv_lhs => rw [chart4_coordinate_expansion (e.coefficients x l)]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hd]
  simp_rw [immersionFrameSecond_derivative F e x hx]
  simp only [smul_add, Finset.sum_add_distrib, immersionFrameConnection,
    Matrix.sum_mul, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  exact (frameCubic_last_slot _ _ l).symm

theorem immersionFrameThird_frame_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (l : Fin 4) :
    cubicDerivative (immersionFrameThird F e) x (e.coefficients x l) =
      cubicConnectionAction (immersionFrameConnection F e x l) (immersionFrameThird F e x) +
      (fun i j k => immersionFrameFourth F e x i j k l) := by
  have hd : cubicDerivative (immersionFrameThird F e) x (e.coefficients x l) =
      ∑ c, e.coefficients x l c • cubicDerivative (immersionFrameThird F e) x (coordinateUnit c) := by
    funext i j k
    simp only [cubicDerivative, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [chart4_coordinate_expansion (e.coefficients x l)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have ha : (∑ c, e.coefficients x l c • cubicConnectionAction
      (immersionMovingConnection F e x c) (immersionFrameThird F e x)) =
      cubicConnectionAction (immersionFrameConnection F e x l) (immersionFrameThird F e x) := by
    funext i j k
    simp only [cubicConnectionAction, immersionFrameConnection, Matrix.sum_apply,
      Matrix.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, mul_add]
    simp only [mul_assoc]
    congr 1
    · congr 1 <;> exact Finset.sum_comm
    · exact Finset.sum_comm
  rw [hd]
  simp_rw [immersionFrameThird_coordinate_derivative F e x hx]
  rw [show (fun i j k => immersionFrameFourth F e x i j k l : Cubic4) =
    ∑ c, e.coefficients x l c • frameCubic (e.coefficients x)
      (fun a b d => immersionFourthForm F.map F.normal x a b d c) from frameFourth_last_slot _ _ l]
  simp only [smul_add, Finset.sum_add_distrib, ha]

end
end SecondPinching
