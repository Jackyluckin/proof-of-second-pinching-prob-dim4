import SecondPinching.ImmersionRicciSimonsBridge

set_option autoImplicit false
set_option maxHeartbeats 4800000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

abbrev Fifth4 := Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- The covariant derivative of a four-tensor, with the new derivative slot last. -/
def coordinateCovariant4 (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (H : Chart4 → Fourth4) (x : Chart4) : Fifth4 := fun i j k l m =>
  fderiv ℝ (fun y => H y i j k l) x (coordinateUnit m) -
    cubicConnectionAction (coordinateConnectionMatrix Γ x m) (fun a b c => H x a b c l) i j k -
    ∑ r, Γ x r l m * H x i j k r

/-- The induced action on three covariant slots is a Lie algebra representation. -/
theorem cubicConnectionAction_commutator (C D : Matrix4) (T : Cubic4) :
    cubicConnectionAction C (cubicConnectionAction D T) -
      cubicConnectionAction D (cubicConnectionAction C T) =
      cubicConnectionAction (C*D-D*C) T := by
  funext i j k
  simp only [cubicConnectionAction, Pi.sub_apply, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_succ, Finset.univ_unique, Finset.sum_singleton]
  ring

theorem cubicConnectionAction_linear_left (C D : Matrix4) (T : Cubic4) :
    cubicConnectionAction (C-D) T = cubicConnectionAction C T-cubicConnectionAction D T := by
  funext i j k
  simp only [cubicConnectionAction, Matrix.sub_apply, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

theorem cubicConnectionAction_linear_right (C : Matrix4) (T U : Cubic4) :
    cubicConnectionAction C (T-U) = cubicConnectionAction C T-cubicConnectionAction C U := by
  funext i j k
  simp only [cubicConnectionAction, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

theorem cubicDerivative_sub (T U : Chart4 → Cubic4) (x v : Chart4)
    (hT : DifferentiableAt ℝ T x) (hU : DifferentiableAt ℝ U x) :
    cubicDerivative (fun y => T y-U y) x v = cubicDerivative T x v-cubicDerivative U x v := by
  funext i j k
  have ht : DifferentiableAt ℝ (fun y => T y i j k) x := by fun_prop
  have hu : DifferentiableAt ℝ (fun y => U y i j k) x := by fun_prop
  exact congrArg (fun L : Chart4 →L[ℝ] ℝ => L v) (fderiv_fun_sub ht hu)

theorem cubicDerivative_action (C : Chart4 → Matrix4) (T : Chart4 → Cubic4) (x v : Chart4)
    (hC : DifferentiableAt ℝ C x) (hT : DifferentiableAt ℝ T x) :
    cubicDerivative (fun y => cubicConnectionAction (C y) (T y)) x v =
      cubicConnectionAction (matrixDerivative C x v) (T x) +
      cubicConnectionAction (C x) (cubicDerivative T x v) := by
  have hc (i j : Fin 4) : DifferentiableAt ℝ (fun y => C y i j) x := by fun_prop
  have ht (i j k : Fin 4) : DifferentiableAt ℝ (fun y => T y i j k) x := by fun_prop
  funext i j k
  simp only [cubicDerivative, cubicConnectionAction, Pi.add_apply, matrixDerivative]
  erw [fderiv_fun_sum (u := Finset.univ) (fun r _ =>
    (((hc i r).mul (ht r j k)).add ((hc j r).mul (ht i r k))).add ((hc k r).mul (ht i j r)))]
  simp only [sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro r _
  erw [fderiv_fun_add, fderiv_fun_add, fderiv_fun_mul, fderiv_fun_mul, fderiv_fun_mul] <;> try fun_prop
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem cubicDerivative_mixed (T : Chart4 → Cubic4) (x : Chart4)
    (hT : ContDiffAt ℝ ∞ T x) (k l : Fin 4) :
    cubicDerivative (fun y => cubicDerivative T y (coordinateUnit k)) x (coordinateUnit l) =
    cubicDerivative (fun y => cubicDerivative T y (coordinateUnit l)) x (coordinateUnit k) := by
  funext i j a
  have hs : ContDiffAt ℝ ∞ (fun y => T y i j a) x := by fun_prop
  have hd := (hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  simp only [cubicDerivative]
  rw [fderiv_clm_apply hd (differentiableAt_const (coordinateUnit k)),
    fderiv_clm_apply hd (differentiableAt_const (coordinateUnit l))]
  simpa using (hs.isSymmSndFDerivAt (by simp)).eq (coordinateUnit l) (coordinateUnit k)

theorem coordinateCovariant3_cubic (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T : Chart4 → Cubic4) (x : Chart4) (l : Fin 4) :
    (fun i j k => coordinateCovariant3 Γ T x i j k l : Cubic4) =
      cubicDerivative T x (coordinateUnit l)-cubicConnectionAction (coordinateConnectionMatrix Γ x l) (T x) := by
  funext i j k
  simp only [coordinateCovariant3, cubicDerivative, cubicConnectionAction,
    coordinateConnectionMatrix, Pi.sub_apply]

/-- Ricci interchange for an arbitrary smooth covariant three-tensor. All
three curvature actions are present, including that on the previous derivative slot. -/
theorem coordinateCovariant3_ricci (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T : Chart4 → Cubic4) (x : Chart4)
    (hΓ : ContDiffAt ℝ ∞ Γ x) (hT : ContDiffAt ℝ ∞ T x)
    (htorsion : ∀ r l m, Γ x r l m = Γ x r m l) (l m : Fin 4) :
    (fun i j k => coordinateCovariant4 Γ (coordinateCovariant3 Γ T) x i j k l m -
      coordinateCovariant4 Γ (coordinateCovariant3 Γ T) x i j k m l : Cubic4) =
      cubicConnectionAction (coordinateCurvature Γ x l m) (T x) := by
  let C := fun y k => coordinateConnectionMatrix Γ y k
  have hc (a : Fin 4) : DifferentiableAt ℝ (fun y => C y a) x := by
    have hs : ContDiffAt ℝ ∞ (fun y => C y a) x := by
      apply contDiffAt_pi.mpr; intro i
      apply contDiffAt_pi.mpr; intro r
      change ContDiffAt ℝ ∞ (fun y => Γ y r i a) x; fun_prop
    exact hs.differentiableAt (by simp)
  have ht := hT.differentiableAt (by simp)
  have hd (a : Fin 4) : DifferentiableAt ℝ (fun y => cubicDerivative T y (coordinateUnit a)) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    apply differentiableAt_pi.mpr; intro k
    have hs : ContDiffAt ℝ ∞ (fun y => T y i j k) x := by fun_prop
    exact ((hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).clm_apply
      (differentiableAt_const _)
  have ha (a : Fin 4) : DifferentiableAt ℝ (fun y => cubicConnectionAction (C y a) (T y)) x := by
    unfold cubicConnectionAction; fun_prop
  have he (a b : Fin 4) :
      cubicDerivative (fun y i j k => coordinateCovariant3 Γ T y i j k a) x (coordinateUnit b) =
      cubicDerivative (fun y => cubicDerivative T y (coordinateUnit a)) x (coordinateUnit b) -
        (cubicConnectionAction (matrixDerivative (fun y => C y a) x (coordinateUnit b)) (T x)+
          cubicConnectionAction (C x a) (cubicDerivative T x (coordinateUnit b))) := by
    have hf : (fun y i j k => coordinateCovariant3 Γ T y i j k a) =
        (fun y => cubicDerivative T y (coordinateUnit a)-cubicConnectionAction (C y a) (T y)) := by
      funext y; exact coordinateCovariant3_cubic Γ T y a
    rw [hf]
    rw [cubicDerivative_sub _ _ _ _ (hd a) (ha a),cubicDerivative_action _ _ _ _ (hc a) ht]
  have hlm := cubicConnectionAction_commutator (C x m) (C x l) (T x)
  have hh := cubicDerivative_mixed T x hT l m
  have hleft : (fun i j k => coordinateCovariant4 Γ (coordinateCovariant3 Γ T) x i j k l m -
      coordinateCovariant4 Γ (coordinateCovariant3 Γ T) x i j k m l : Cubic4) =
      cubicDerivative (fun y i j k => coordinateCovariant3 Γ T y i j k l) x (coordinateUnit m)-
      cubicDerivative (fun y i j k => coordinateCovariant3 Γ T y i j k m) x (coordinateUnit l)-
      cubicConnectionAction (C x m) (fun i j k => coordinateCovariant3 Γ T x i j k l)+
      cubicConnectionAction (C x l) (fun i j k => coordinateCovariant3 Γ T x i j k m) := by
    funext i j k
    simp only [coordinateCovariant4, htorsion _ l m, cubicDerivative, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hleft,he,he,hh,coordinateCovariant3_cubic,coordinateCovariant3_cubic,
    cubicConnectionAction_linear_right,cubicConnectionAction_linear_right]
  have hr : coordinateCurvature Γ x l m =
      (matrixDerivative (fun y => C y m) x (coordinateUnit l)-
        matrixDerivative (fun y => C y l) x (coordinateUnit m)) -
      (C x l*C x m-C x m*C x l) := by unfold coordinateCurvature C; abel
  rw [hr,cubicConnectionAction_linear_left,cubicConnectionAction_linear_left]
  have hcmt := cubicConnectionAction_commutator (C x l) (C x m) (T x)
  rw [← hcmt]
  abel

end
end SecondPinching
