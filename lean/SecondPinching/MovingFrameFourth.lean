import SecondPinching.CubicRicci

set_option autoImplicit false
set_option maxHeartbeats 4800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

theorem movingFrame_arbitrary_cubic_derivative (F : LocalSphereImmersion)
    (e : LocalImmersionFrame F) (T : Chart4 → Cubic4) (x : Chart4) (hx : x ∈ F.domain) (hT : DifferentiableAt ℝ T x) (l : Fin 4) :
    cubicDerivative ((fun y => frameCubic (e.coefficients y) (T y))) x (coordinateUnit l) =
      cubicConnectionAction (immersionMovingConnection F e x l) ((fun y => frameCubic (e.coefficients y) (T y)) x) +
      frameCubic (e.coefficients x) (fun i j k => coordinateCovariant3 (immersionChristoffel F.map) T x i j k l) := by
  have hb := ((e.smooth x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have ht := hT
  have hc (i a : Fin 4) : DifferentiableAt ℝ (fun y => e.coefficients y i a) x := by fun_prop
  have hta (a : Fin 4) : DifferentiableAt ℝ (fun y => T y a) x := by fun_prop
  have hm (a : Fin 4) : DifferentiableAt ℝ
      (fun y => frameMatrix (e.coefficients y) (T y a)) x := by
    unfold frameMatrix; fun_prop
  have he (i : Fin 4) : (fun y => (fun y => frameCubic (e.coefficients y) (T y)) y i) =
      (fun y => ∑ a, e.coefficients y i a • frameMatrix (e.coefficients y)
        (T y a)) := by
    funext y; exact frameCubic_slice _ _ i
  have hd (a : Fin 4) : matrixDerivative
      (fun y => frameMatrix (e.coefficients y) (T y a))
      x (coordinateUnit l) =
      immersionMovingConnection F e x l * frameMatrix (e.coefficients x) (T x a) +
      frameMatrix (e.coefficients x) (T x a) * (immersionMovingConnection F e x l)ᵀ +
      frameMatrix (e.coefficients x) ((Matrix.of (fun j k => coordinateCovariant3 (immersionChristoffel F.map) T x a j k l)) +
        ∑ r, coordinateConnectionMatrix (immersionChristoffel F.map) x l a r • Matrix.of (T x r)) := by
    rw [matrixDerivative_frameMatrix _ _ x _ hb (hta a),
      coordinateCovariant3_matrix (immersionChristoffel F.map) (T) x a l]
    exact movingFrame_derivative_algebra _ _ _ _ _ _ (immersionMovingConnection_action F e x hx l)
  funext i
  change matrixDerivative (fun y => (fun y => frameCubic (e.coefficients y) (T y)) y i) x (coordinateUnit l) = _
  rw [he i, matrixDerivative_sum_smul _ _ _ _ (hc i) hm]
  simp_rw [hd]
  exact movingFrame_cubic_slice_algebra _ _ _ _ _ _ (immersionMovingConnection_action F e x hx l) i


/-- The four covariant slots, including both existing derivative slots. -/
def fourthConnectionAction (O : Matrix4) (H : Fourth4) : Fourth4 := fun i =>
  cubicConnectionAction O (H i)+∑ r, O i r • H r

def fourthDerivative (H : Chart4 → Fourth4) (x v : Chart4) : Fourth4 :=
  fun i j k l => fderiv ℝ (fun y => H y i j k l) x v

def frameFifth (B : Matrix4) (K : Fifth4) : Fifth4 :=
  fun i j k l m => ∑ a, B i a*frameFourth B (K a) j k l m

def immersionFifthForm (F : LocalSphereImmersion) : Chart4 → Fifth4 :=
  coordinateCovariant4 (immersionChristoffel F.map) (immersionFourthForm F.map F.normal)

def immersionFrameFifth (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) : Fifth4 := frameFifth (e.coefficients x) (immersionFifthForm F x)

theorem cubicDerivative_sum_smul (c : Fin 4 → Chart4 → ℝ)
    (T : Fin 4 → Chart4 → Cubic4) (x v : Chart4)
    (hc : ∀ a, DifferentiableAt ℝ (c a) x)
    (hT : ∀ a, DifferentiableAt ℝ (T a) x) :
    cubicDerivative (fun y => ∑ a, c a y • T a y) x v =
      ∑ a, (fderiv ℝ (c a) x v • T a x+c a x • cubicDerivative (T a) x v) := by
  funext i
  change matrixDerivative (fun y => ∑ a, c a y • Matrix.of (T a y i)) x v = _
  exact matrixDerivative_sum_smul c (fun a y => Matrix.of (T a y i)) x v hc
    (fun a => by change DifferentiableAt ℝ (fun y j k => T a y i j k) x; fun_prop)

def cubicActionLinear (O : Matrix4) : Cubic4 →ₗ[ℝ] Cubic4 where
  toFun := cubicConnectionAction O
  map_add' T U := by
    funext i j k
    simp only [cubicConnectionAction, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c T := by
    funext i j k
    simp only [cubicConnectionAction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl; intro r _; ring

theorem movingFrame_fourth_slice_algebra (B D C O : Matrix4) (H K : Fourth4)
    (hO : O*B = D+B*C) (i : Fin 4) :
    (∑ a, (D i a • frameCubic B (H a) + B i a •
      (cubicConnectionAction O (frameCubic B (H a))+
        frameCubic B (K a+∑ r, C a r • H r)))) =
      fourthConnectionAction O (frameFourth B H) i+frameFourth B K i := by
  have hf (a : Fin 4) : frameCubic B (K a+∑ r, C a r • H r) =
      frameCubic B (K a)+∑ r, C a r • frameCubic B (H r) := by
    change frameCubicLinear B _ = _
    rw [map_add,map_sum]; simp only [map_smul]; rfl
  have hc : (∑ a, D i a • frameCubic B (H a))+
      (∑ a, B i a • ∑ r, C a r • frameCubic B (H r)) =
      ∑ r, O i r • frameFourth B H r := by
    simp only [Finset.smul_sum,smul_smul,frameFourth_slice]
    rw [Finset.sum_comm (f := fun a r => (B i a*C a r) • frameCubic B (H r))]
    simp_rw [← Finset.sum_smul]
    rw [← Finset.sum_add_distrib]
    simp_rw [← add_smul]
    have ho (a : Fin 4) := congrFun (congrFun hO i) a
    simp only [Matrix.mul_apply,Matrix.add_apply] at ho
    simp_rw [← ho,Finset.sum_smul]
    rw [Finset.sum_comm]
  have ha : (∑ a, B i a • cubicConnectionAction O (frameCubic B (H a))) =
      cubicConnectionAction O (frameFourth B H i) := by
    rw [frameFourth_slice]
    change _ = cubicActionLinear O _
    rw [map_sum]; simp only [map_smul]; rfl
  simp only [hf,smul_add,Finset.sum_add_distrib]
  have he : (∑ a, D i a • frameCubic B (H a))+
      ((∑ a, B i a • cubicConnectionAction O (frameCubic B (H a)))+
        ((∑ a, B i a • frameCubic B (K a))+
          (∑ a, B i a • ∑ r, C a r • frameCubic B (H r)))) =
      ((∑ a, D i a • frameCubic B (H a))+
        (∑ a, B i a • ∑ r, C a r • frameCubic B (H r)))+
      (∑ a, B i a • cubicConnectionAction O (frameCubic B (H a)))+
      (∑ a, B i a • frameCubic B (K a)) := by abel
  rw [he,hc,ha,← frameFourth_slice]
  unfold fourthConnectionAction
  abel

theorem coordinateCovariant4_slice (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (H : Chart4 → Fourth4) (x : Chart4) (a m : Fin 4) :
    (fun j k l => coordinateCovariant3 Γ (fun y => H y a) x j k l m : Cubic4) =
      (fun j k l => coordinateCovariant4 Γ H x a j k l m)+∑ r, Γ x r a m • H x r := by
  funext j k l
  simp only [coordinateCovariant3,coordinateCovariant4,cubicConnectionAction,coordinateConnectionMatrix,
    Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib]
  ring

/-- Differentiation of an arbitrary actual four-tensor in the moving frame. -/
theorem movingFrame_arbitrary_fourth_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (H : Chart4 → Fourth4) (x : Chart4) (hx : x ∈ F.domain)
    (hH : DifferentiableAt ℝ H x) (m : Fin 4) :
    fourthDerivative (fun y => frameFourth (e.coefficients y) (H y)) x (coordinateUnit m) =
      fourthConnectionAction (immersionMovingConnection F e x m) (frameFourth (e.coefficients x) (H x))+
      frameFourth (e.coefficients x) (fun i j k l => coordinateCovariant4 (immersionChristoffel F.map) H x i j k l m) := by
  have hb := ((e.smooth x hx).contDiffAt (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hc (i a : Fin 4) : DifferentiableAt ℝ (fun y => e.coefficients y i a) x := by fun_prop
  have hs (a : Fin 4) : DifferentiableAt ℝ (fun y => H y a) x := by fun_prop
  have hf (a : Fin 4) : DifferentiableAt ℝ (fun y => frameCubic (e.coefficients y) (H y a)) x := by
    unfold frameCubic frameMatrix; fun_prop
  have hd (a : Fin 4) :
      cubicDerivative (fun y => frameCubic (e.coefficients y) (H y a)) x (coordinateUnit m) =
      cubicConnectionAction (immersionMovingConnection F e x m) (frameCubic (e.coefficients x) (H x a))+
      frameCubic (e.coefficients x) ((fun j k l => coordinateCovariant4 (immersionChristoffel F.map) H x a j k l m)+
        ∑ r, immersionChristoffel F.map x r a m • H x r) := by
    have hr := movingFrame_arbitrary_cubic_derivative F e (fun y => H y a) x hx (hs a) m
    rw [coordinateCovariant4_slice] at hr
    exact hr
  funext i
  change cubicDerivative (fun y => frameFourth (e.coefficients y) (H y) i) x (coordinateUnit m) = _
  simp_rw [frameFourth_slice]
  rw [cubicDerivative_sum_smul _ _ x _ (hc i) hf]
  simp_rw [hd]
  exact movingFrame_fourth_slice_algebra _ _ _ _ _ _ (immersionMovingConnection_action F e x hx m) i

theorem frameFifth_last_slot (B : Matrix4) (K : Fifth4) (m : Fin 4) :
    (fun i j k l => frameFifth B K i j k l m : Fourth4) =
      ∑ d, B m d • frameFourth B (fun a b c e => K a b c e d) := by
  funext i j k l
  simp only [frameFifth,frameFourth,frameCubic,frameMatrix,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro d _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro q _; ring

theorem immersionFrameFourth_coordinate_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (m : Fin 4) :
    fourthDerivative (immersionFrameFourth F e) x (coordinateUnit m) =
      fourthConnectionAction (immersionMovingConnection F e x m) (immersionFrameFourth F e x)+
      frameFourth (e.coefficients x) (fun i j k l => immersionFifthForm F x i j k l m) :=
  movingFrame_arbitrary_fourth_derivative F e (immersionFourthForm F.map F.normal) x hx
    ((((contDiffOn_immersionForms F).2.2 x hx).contDiffAt
      (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)) m

theorem immersionFrameFourth_frame_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (m : Fin 4) :
    fourthDerivative (immersionFrameFourth F e) x (e.coefficients x m) =
      fourthConnectionAction (immersionFrameConnection F e x m) (immersionFrameFourth F e x)+
      (fun i j k l => immersionFrameFifth F e x i j k l m) := by
  have hd : fourthDerivative (immersionFrameFourth F e) x (e.coefficients x m) =
      ∑ c, e.coefficients x m c • fourthDerivative (immersionFrameFourth F e) x (coordinateUnit c) := by
    funext i j k l
    simp only [fourthDerivative,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    conv_lhs => rw [chart4_coordinate_expansion (e.coefficients x m)]
    simp only [map_sum,map_smul,smul_eq_mul]
  have ha : (∑ c, e.coefficients x m c • fourthConnectionAction
      (immersionMovingConnection F e x c) (immersionFrameFourth F e x)) =
      fourthConnectionAction (immersionFrameConnection F e x m) (immersionFrameFourth F e x) := by
    funext i j k l
    simp only [fourthConnectionAction,cubicConnectionAction,immersionFrameConnection,Matrix.sum_apply,
      Matrix.smul_apply,Finset.sum_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib,mul_add,mul_assoc]
    congr 1
    · congr 1
      · congr 1 <;> exact Finset.sum_comm
      · exact Finset.sum_comm
    · exact Finset.sum_comm
  rw [hd]
  simp_rw [immersionFrameFourth_coordinate_derivative F e x hx]
  rw [show (fun i j k l => immersionFrameFifth F e x i j k l m : Fourth4) =
    ∑ c, e.coefficients x m c • frameFourth (e.coefficients x)
      (fun i j k l => immersionFifthForm F x i j k l c) from frameFifth_last_slot _ _ m]
  simp only [smul_add,Finset.sum_add_distrib,ha]

end
end SecondPinching
