import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

set_option autoImplicit false

/-! # Appendix A.1: positivity of the Bernstein--Gram certificate -/

open scoped BigOperators Matrix

namespace SecondPinching

noncomputable section

/-- The unordered quadratic monomials in twelve variables. -/
abbrev QuadraticIndex := {ij : Fin 12 × Fin 12 // ij.1 ≤ ij.2}

/-- There are exactly 78 monomials, as in Appendix A. -/
theorem quadraticIndex_card : Fintype.card QuadraticIndex = 78 := by decide

/-- An explicit identification with the 78 coordinates of the paper. -/
def quadraticIndexEquivFin : QuadraticIndex ≃ Fin 78 :=
  (Fintype.equivFin QuadraticIndex).trans (finCongr quadraticIndex_card)

/-- `z(x)` in the paper, indexed by pairs `a ≤ b`. -/
def quadraticMonomials (x : Fin 12 → ℝ) : QuadraticIndex → ℝ :=
  fun ij => x ij.val.1 * x ij.val.2

/-- Auxiliary used explicitly in the proof of Lemma A.1. -/
theorem quadraticMonomials_ne_zero {x : Fin 12 → ℝ} (hx : x ≠ 0) :
    quadraticMonomials x ≠ 0 := by
  intro hz
  apply hx
  funext i
  have hi : x i * x i = 0 := congrFun hz ⟨(i,i), le_refl i⟩
  exact (mul_self_eq_zero.mp hi)

/-- The univariate factor in equation (A.6). -/
def bernsteinWeight (n : ℕ) (i : Fin (n+1)) (t : ℝ) : ℝ :=
  (n.choose i.val : ℝ) * t ^ i.val * (1-t) ^ (n-i.val)

theorem bernsteinWeight_nonneg (n : ℕ) (i : Fin (n+1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ bernsteinWeight n i t := by
  unfold bernsteinWeight
  have h0 := ht.1
  have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  positivity

theorem bernsteinWeight_sum (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i : Fin (n+1), bernsteinWeight n i t = 1 := by
  simpa only [bernstein_apply, bernsteinWeight] using bernstein.probability n ⟨t,ht⟩

abbrev ControlIndex := Fin 15 × Fin 15

/-- The tensor-product Bernstein weight on a closed rectangle. -/
def rectangleWeight (r₀ r₁ y₀ y₁ r y : ℝ) (ij : ControlIndex) : ℝ :=
  bernsteinWeight 14 ij.1 ((r-r₀)/(r₁-r₀)) *
  bernsteinWeight 14 ij.2 ((y-y₀)/(y₁-y₀))

theorem intervalCoordinate_mem {a b t : ℝ} (hab : a < b) (ht : t ∈ Set.Icc a b) :
    (t-a)/(b-a) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le
  · exact (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right ht.2 a)

theorem rectangleWeight_nonneg {r₀ r₁ y₀ y₁ r y : ℝ}
    (hr : r₀ < r₁) (hy : y₀ < y₁)
    (hrr : r ∈ Set.Icc r₀ r₁) (hyy : y ∈ Set.Icc y₀ y₁)
    (ij : ControlIndex) : 0 ≤ rectangleWeight r₀ r₁ y₀ y₁ r y ij := by
  exact mul_nonneg (bernsteinWeight_nonneg _ _ (intervalCoordinate_mem hr hrr))
    (bernsteinWeight_nonneg _ _ (intervalCoordinate_mem hy hyy))

theorem rectangleWeight_sum {r₀ r₁ y₀ y₁ r y : ℝ}
    (hr : r₀ < r₁) (hy : y₀ < y₁)
    (hrr : r ∈ Set.Icc r₀ r₁) (hyy : y ∈ Set.Icc y₀ y₁) :
    ∑ ij : ControlIndex, rectangleWeight r₀ r₁ y₀ y₁ r y ij = 1 := by
  simp only [rectangleWeight, Fintype.sum_prod_type, ← Finset.mul_sum]
  rw [bernsteinWeight_sum 14 (intervalCoordinate_mem hy hyy)]
  simp only [mul_one]
  exact bernsteinWeight_sum 14 (intervalCoordinate_mem hr hrr)

/-- Auxiliary: a finite convex combination of positive real numbers is positive. -/
theorem weighted_sum_pos {ι : Type*} [Fintype ι]
    (w q : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hq : ∀ i, 0 < q i) : 0 < ∑ i, w i * q i := by
  classical
  have hex : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have hzero : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hw i))
    linarith
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (hq j).le)
    ⟨i,Finset.mem_univ i,mul_pos hi (hq i)⟩

/-- Paper Lemma A.1. `P` has variables `(r,y,x₁,...,x₁₂)`; `D` has
variables `(r,y)`. The two displayed expansions are both retained.
The fixed-order vector in R^78 is represented by its 78 unordered pairs. -/
theorem bernstein_positivity
    (r₀ r₁ y₀ y₁ : ℝ) (hr : r₀ < r₁) (hy : y₀ < y₁)
    (P : MvPolynomial (Fin 14) ℝ) (D : MvPolynomial (Fin 2) ℝ)
    (C : ControlIndex → MvPolynomial (Fin 12) ℝ)
    (d : ControlIndex → ℝ)
    (G : ControlIndex → Matrix QuadraticIndex QuadraticIndex ℝ)
    (hP : ∀ r ∈ Set.Icc r₀ r₁, ∀ y ∈ Set.Icc y₀ y₁, ∀ x : Fin 12 → ℝ,
      MvPolynomial.eval (Fin.append ![r,y] x) P =
        ∑ ij, rectangleWeight r₀ r₁ y₀ y₁ r y ij * MvPolynomial.eval x (C ij))
    (_hD : ∀ r ∈ Set.Icc r₀ r₁, ∀ y ∈ Set.Icc y₀ y₁,
      MvPolynomial.eval ![r,y] D = ∑ ij, rectangleWeight r₀ r₁ y₀ y₁ r y ij * d ij)
    (hd : ∀ ij, 0 < d ij) (hG : ∀ ij, (G ij).PosDef)
    (hC : ∀ ij x, MvPolynomial.eval x (C ij) =
      d ij * (quadraticMonomials x ⬝ᵥ (G ij *ᵥ quadraticMonomials x)))
    (r y : ℝ) (hrr : r ∈ Set.Icc r₀ r₁) (hyy : y ∈ Set.Icc y₀ y₁)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    0 < MvPolynomial.eval (Fin.append ![r,y] x) P := by
  rw [hP r hrr y hyy x]
  apply weighted_sum_pos
  · exact rectangleWeight_nonneg hr hy hrr hyy
  · exact rectangleWeight_sum hr hy hrr hyy
  · intro ij
    rw [hC ij x]
    apply mul_pos (hd ij)
    simpa only [star_trivial] using (hG ij).dotProduct_mulVec_pos (quadraticMonomials_ne_zero hx)

end
end SecondPinching
