import SecondPinching.ImmersionHessianBridge

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Row convention: this is the curvature action on a covariant slot for
H_ijkl-H_ijlk, with the derivative index last. -/
def coordinateCurvature (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Chart4) (k l : Fin 4) : Matrix4 :=
  matrixDerivative (fun y => coordinateConnectionMatrix Γ y l) x (coordinateUnit k) -
  matrixDerivative (fun y => coordinateConnectionMatrix Γ y k) x (coordinateUnit l) +
  coordinateConnectionMatrix Γ x l * coordinateConnectionMatrix Γ x k -
  coordinateConnectionMatrix Γ x k * coordinateConnectionMatrix Γ x l

theorem matrixDerivative_sub (A B : Chart4 → Matrix4) (x v : Chart4)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    matrixDerivative (fun y => A y-B y) x v = matrixDerivative A x v-matrixDerivative B x v := by
  ext i j
  have ha : DifferentiableAt ℝ (fun y => A y i j) x := by fun_prop
  have hb : DifferentiableAt ℝ (fun y => B y i j) x := by fun_prop
  exact congrArg (fun L : Chart4 →L[ℝ] ℝ => L v) (fderiv_fun_sub ha hb)

theorem matrixDerivative_mixed (h : Chart4 → Matrix4) (x : Chart4)
    (hh : ContDiffAt ℝ ∞ h x) (k l : Fin 4) :
    matrixDerivative (fun y => matrixDerivative h y (coordinateUnit k)) x (coordinateUnit l) =
    matrixDerivative (fun y => matrixDerivative h y (coordinateUnit l)) x (coordinateUnit k) := by
  ext i j
  have hs : ContDiffAt ℝ ∞ (fun y => h y i j) x := by fun_prop
  have hd := (hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  simp only [matrixDerivative]
  rw [fderiv_clm_apply hd (differentiableAt_const (coordinateUnit k)),
    fderiv_clm_apply hd (differentiableAt_const (coordinateUnit l))]
  simpa using (hs.isSymmSndFDerivAt (by simp)).eq (coordinateUnit l) (coordinateUnit k)

theorem coordinateCovariant3_last_matrix (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (T : Chart4 → Cubic4) (x : Chart4) (k l : Fin 4) :
    Matrix.of (fun i j => coordinateCovariant3 Γ T x i j k l) =
      matrixDerivative (fun y => Matrix.of (fun i j => T y i j k)) x (coordinateUnit l) -
      coordinateConnectionMatrix Γ x l * Matrix.of (fun i j => T x i j k) -
      Matrix.of (fun i j => T x i j k) * (coordinateConnectionMatrix Γ x l)ᵀ -
      ∑ r, Γ x r k l • Matrix.of (fun i j => T x i j r) := by
  ext i j
  simp only [coordinateCovariant3, matrixDerivative, coordinateConnectionMatrix, Matrix.of_apply,
    Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [show (∑ r, Γ x r j l*T x i r k) = ∑ r, T x i r k*Γ x r j l by
    apply Finset.sum_congr rfl; intro r _; ring]
  ring

/-- Ricci interchange for the explicitly defined coordinate derivatives.
Only smoothness and torsion-freeness enter; the curvature is not prescribed. -/
theorem coordinateCovariant_ricci (Γ : Chart4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : Chart4 → Matrix4) (x : Chart4)
    (hΓ : ContDiffAt ℝ ∞ Γ x) (hh : ContDiffAt ℝ ∞ h x)
    (htorsion : ∀ r k l, Γ x r k l = Γ x r l k) (k l : Fin 4) :
    Matrix.of (fun i j => coordinateCovariant3 Γ (coordinateCovariant2 Γ h) x i j k l) -
    Matrix.of (fun i j => coordinateCovariant3 Γ (coordinateCovariant2 Γ h) x i j l k) =
      coordinateCurvature Γ x k l * h x + h x * (coordinateCurvature Γ x k l)ᵀ := by
  let C := fun y k => coordinateConnectionMatrix Γ y k
  let T := fun y k => Matrix.of (fun i j => coordinateCovariant2 Γ h y i j k)
  have hc (a : Fin 4) : DifferentiableAt ℝ (fun y => C y a) x := by
    have hs : ContDiffAt ℝ ∞ (fun y => C y a) x := by
      apply contDiffAt_pi.mpr; intro i
      apply contDiffAt_pi.mpr; intro r
      change ContDiffAt ℝ ∞ (fun y => Γ y r i a) x
      fun_prop
    exact hs.differentiableAt (by simp)
  have hd : DifferentiableAt ℝ h x := hh.differentiableAt (by simp)
  have hdc (a : Fin 4) : DifferentiableAt ℝ (fun y => matrixDerivative h y (coordinateUnit a)) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    have hs : ContDiffAt ℝ ∞ (fun y => h y i j) x := by fun_prop
    have hf := (hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    exact hf.clm_apply (differentiableAt_const _)
  have hch (a : Fin 4) : DifferentiableAt ℝ (fun y => C y a*h y) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    simp only [Matrix.mul_apply]; fun_prop
  have hhct (a : Fin 4) : DifferentiableAt ℝ (fun y => h y*(C y a)ᵀ) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]; fun_prop
  have he (y : Chart4) (a : Fin 4) :
      T y a = matrixDerivative h y (coordinateUnit a)-C y a*h y-h y*(C y a)ᵀ := by
    have hs := coordinateCovariant2_matrix Γ h y a
    change _ = T y a + C y a*h y + h y*(C y a)ᵀ at hs
    rw [hs]; abel
  have ht (a b : Fin 4) :
      matrixDerivative (fun y => T y a) x (coordinateUnit b) =
      matrixDerivative (fun y => matrixDerivative h y (coordinateUnit a)) x (coordinateUnit b) -
      (matrixDerivative (fun y => C y a) x (coordinateUnit b)*h x + C x a*matrixDerivative h x (coordinateUnit b)) -
      (matrixDerivative h x (coordinateUnit b)*(C x a)ᵀ +
        h x*(matrixDerivative (fun y => C y a) x (coordinateUnit b))ᵀ) := by
    simp_rw [he]
    erw [matrixDerivative_sub _ _ x _ ((hdc a).sub (hch a)) (hhct a),
      matrixDerivative_sub _ _ x _ (hdc a) (hch a),
      matrixDerivative_mul _ _ x _ (hc a) hd,
      matrixDerivative_mul _ _ x _ hd (by
        apply differentiableAt_pi.mpr; intro i
        apply differentiableAt_pi.mpr; intro j
        change DifferentiableAt ℝ (fun y => C y a j i) x; fun_prop),
      matrixDerivative_transpose (fun y => C y a) x (coordinateUnit b)]
  rw [coordinateCovariant3_last_matrix, coordinateCovariant3_last_matrix]
  simp_rw [htorsion _ l k]
  change (matrixDerivative (fun y => T y k) x (coordinateUnit l)-C x l*T x k-T x k*(C x l)ᵀ-_) -
    (matrixDerivative (fun y => T y l) x (coordinateUnit k)-C x k*T x l-T x l*(C x k)ᵀ-_) = _
  rw [ht, ht, matrixDerivative_mixed h x hh k l]
  simp_rw [he]
  dsimp [coordinateCurvature, C]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul]
  noncomm_ring

end
end SecondPinching
