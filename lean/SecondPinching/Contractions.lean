import SecondPinching.TraceFreeProjection
import SecondPinching.CubicSymmetry

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The two remaining contractions in Definition 3.1, with their actual
adjoints for the ordered-index pairings. Ambient arrays are used with explicit
symmetry predicates; no assumption on eigenvalue multiplicities is made. -/

abbrev Vector4 := Fin 4 → ℝ

/-- In any frame, T_A contracts the first two slots against A. -/
def weightedTrace (A : Matrix4) (U : Fourth4) : Matrix4 :=
  fun k l => ∑ i, ∑ j, A i j * U i j k l

/-- N_tau in eq:maps, also defined on arrays with only partial symmetry. -/
def cubicContraction (τ : Cubic4) (U : Fourth4) : Vector4 :=
  fun l => ∑ i, ∑ j, ∑ k, τ i j k * U i j k l

/-- The six-term expression for Sym(A tensor Y). -/
def weightedTraceAdjoint (A Y : Matrix4) : Fourth4 := fun i j k l =>
  (A i j * Y k l + A i k * Y j l + A i l * Y j k +
    A j k * Y i l + A j l * Y i k + A k l * Y i j) / 6

/-- The four-term expression for Sym(tau tensor v). -/
def cubicContractionAdjoint (τ : Cubic4) (v : Vector4) : Fourth4 := fun i j k l =>
  (τ i j k * v l + τ i j l * v k + τ i k l * v j + τ j k l * v i) / 4

theorem weightedTrace_diagonal (μ : Vector4) (U : Fourth4) :
    weightedTrace (Matrix.diagonal μ) U = fun k l => ∑ i, μ i * U i i k l := by
  ext k l
  simp [weightedTrace, Matrix.diagonal_apply]

theorem weightedTrace_symmetric (A : Matrix4) {U : Fourth4}
    (hU : FourthSymmetric U) : (weightedTrace A U).IsSymm := by
  ext k l
  simp only [Matrix.transpose_apply, weightedTrace, fourthSymmetric_swap34 hU]

/-- Tracing the remaining pair equals pairing A with the ordinary trace. -/
theorem trace_weightedTrace (A : Matrix4) (U : Fourth4) (hU : FourthSymmetric U) :
    Matrix.trace (weightedTrace A U) = matrixInner A (ordinaryTrace U) := by
  simp [Matrix.trace, Matrix.diag, weightedTrace, matrixInner, ordinaryTrace,
    Fin.sum_univ_succ, fourthSymmetric_swap12 hU, fourthSymmetric_swap23 hU,
    fourthSymmetric_swap34 hU]
  ring

/-- T_A maps H_4 into Sym^2_0, without any restriction on the eigenvalues. -/
theorem weightedTrace_traceFree (A : Matrix4) (U : Fourth4) (hU : TraceFreeFourth U) :
    (weightedTrace A U).IsSymm ∧ Matrix.trace (weightedTrace A U) = 0 := by
  refine ⟨weightedTrace_symmetric A hU.1, ?_⟩
  rw [trace_weightedTrace A U hU.1, hU.2]
  simp [matrixInner]

theorem weightedTraceAdjoint_symmetric (A Y : Matrix4)
    (hA : A.IsSymm) (hY : Y.IsSymm) : FourthSymmetric (weightedTraceAdjoint A Y) := by
  apply (fourthSymmetric_iff_swaps _).mpr
  refine ⟨?_, ?_, ?_⟩
  all_goals intro i j k l
  all_goals simp only [weightedTraceAdjoint, hA.apply, hY.apply]
  all_goals ring

theorem cubicContractionAdjoint_symmetric (τ : Cubic4) (hτ : CubicSymmetric τ)
    (v : Vector4) : FourthSymmetric (cubicContractionAdjoint τ v) := by
  apply (fourthSymmetric_iff_swaps _).mpr
  refine ⟨?_, ?_, ?_⟩
  all_goals intro i j k l
  all_goals simp only [cubicContractionAdjoint, cubicSymmetric_swap12 hτ,
    cubicSymmetric_swap23 hτ]
  all_goals ring

theorem weightedTraceAdjoint_eq_sym (A Y : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm) :
    weightedTraceAdjoint A Y = symmetrizeFourth (fun i j k l => A i j * Y k l) := by
  funext i j k l
  unfold symmetrizeFourth
  rw [← fourthSlotPermutations_sum]
  simp only [Fin.sum_univ_succ]
  unfold fourthSlotPermutations
  dsimp [weightedTraceAdjoint]
  simp only [hA.apply, hY.apply]
  ring

theorem cubicContractionAdjoint_eq_sym (τ : Cubic4) (hτ : CubicSymmetric τ)
    (v : Vector4) :
    cubicContractionAdjoint τ v = symmetrizeFourth (fun i j k l => τ i j k * v l) := by
  funext i j k l
  unfold symmetrizeFourth
  rw [← fourthSlotPermutations_sum]
  simp only [Fin.sum_univ_succ]
  unfold fourthSlotPermutations
  dsimp [cubicContractionAdjoint]
  simp only [cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ]
  ring

theorem weightedTrace_adjoint_pairing (A Y : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm)
    (U : Fourth4) (hU : FourthSymmetric U) :
    fourthInner U (weightedTraceAdjoint A Y) = matrixInner (weightedTrace A U) Y := by
  simp [fourthInner, weightedTraceAdjoint, matrixInner, weightedTrace,
    Fin.sum_univ_succ, fourthSymmetric_swap12 hU, fourthSymmetric_swap23 hU,
    fourthSymmetric_swap34 hU, hA.apply, hY.apply]
  ring

theorem cubicContraction_adjoint_pairing (τ : Cubic4) (hτ : CubicSymmetric τ)
    (v : Vector4) (U : Fourth4) (hU : FourthSymmetric U) :
    fourthInner U (cubicContractionAdjoint τ v) = cubicContraction τ U ⬝ᵥ v := by
  simp [fourthInner, cubicContractionAdjoint, cubicContraction, dotProduct,
    Fin.sum_univ_succ, fourthSymmetric_swap12 hU, fourthSymmetric_swap23 hU,
    fourthSymmetric_swap34 hU, cubicSymmetric_swap12 hτ, cubicSymmetric_swap23 hτ]
  ring

/-- Universal properties over all of Sym^4, not just H_4. -/
def IsWeightedTraceAdjointAt (A Y : Matrix4) (T : Fourth4) : Prop :=
  FourthSymmetric T ∧ ∀ U : Fourth4, FourthSymmetric U →
    fourthInner U T = matrixInner (weightedTrace A U) Y

def IsCubicContractionAdjointAt (τ : Cubic4) (v : Vector4) (T : Fourth4) : Prop :=
  FourthSymmetric T ∧ ∀ U : Fourth4, FourthSymmetric U →
    fourthInner U T = cubicContraction τ U ⬝ᵥ v

theorem weightedTraceAdjoint_spec (A Y : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm) :
    IsWeightedTraceAdjointAt A Y (weightedTraceAdjoint A Y) :=
  ⟨weightedTraceAdjoint_symmetric A Y hA hY, weightedTrace_adjoint_pairing A Y hA hY⟩

theorem cubicContractionAdjoint_spec (τ : Cubic4) (hτ : CubicSymmetric τ) (v : Vector4) :
    IsCubicContractionAdjointAt τ v (cubicContractionAdjoint τ v) :=
  ⟨cubicContractionAdjoint_symmetric τ hτ v, fun U hU =>
    cubicContraction_adjoint_pairing τ hτ v U hU⟩

theorem weightedTraceAdjoint_unique (A Y : Matrix4) (hA : A.IsSymm) (hY : Y.IsSymm)
    (T : Fourth4) (hT : IsWeightedTraceAdjointAt A Y T) : T = weightedTraceAdjoint A Y := by
  have hD := fourthSymmetric_sub hT.1 (weightedTraceAdjoint_symmetric A Y hA hY)
  have hz : fourthNormSq (T - weightedTraceAdjoint A Y) = 0 := by
    rw [← fourthInner_self, fourthInner_sub_right, hT.2 _ hD,
      weightedTrace_adjoint_pairing A Y hA hY _ hD, sub_self]
  exact sub_eq_zero.mp ((fourthNormSq_eq_zero_iff _).mp hz)

theorem cubicContractionAdjoint_unique (τ : Cubic4) (hτ : CubicSymmetric τ)
    (v : Vector4) (T : Fourth4) (hT : IsCubicContractionAdjointAt τ v T) :
    T = cubicContractionAdjoint τ v := by
  have hD := fourthSymmetric_sub hT.1 (cubicContractionAdjoint_symmetric τ hτ v)
  have hz : fourthNormSq (T - cubicContractionAdjoint τ v) = 0 := by
    rw [← fourthInner_self, fourthInner_sub_right, hT.2 _ hD,
      cubicContraction_adjoint_pairing τ hτ v _ hD, sub_self]
  exact sub_eq_zero.mp ((fourthNormSq_eq_zero_iff _).mp hz)

def weightedTraceLinear (A : Matrix4) : Fourth4 →ₗ[ℝ] Matrix4 where
  toFun := weightedTrace A
  map_add' U V := by ext k l; simp [weightedTrace, mul_add, Finset.sum_add_distrib]
  map_smul' c U := by ext k l; simp [weightedTrace, mul_left_comm, Finset.mul_sum]

def cubicContractionLinear (τ : Cubic4) : Fourth4 →ₗ[ℝ] Vector4 where
  toFun := cubicContraction τ
  map_add' U V := by ext l; simp [cubicContraction, mul_add, Finset.sum_add_distrib]
  map_smul' c U := by ext l; simp [cubicContraction, mul_left_comm, Finset.mul_sum]

def weightedTraceAdjointLinear (A : Matrix4) : Matrix4 →ₗ[ℝ] Fourth4 where
  toFun := weightedTraceAdjoint A
  map_add' X Y := by funext i j k l; simp only [weightedTraceAdjoint, Matrix.add_apply, Pi.add_apply]; ring
  map_smul' c Y := by
    funext i j k l
    simp only [weightedTraceAdjoint, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def cubicContractionAdjointLinear (τ : Cubic4) : Vector4 →ₗ[ℝ] Fourth4 where
  toFun := cubicContractionAdjoint τ
  map_add' v w := by funext i j k l; simp only [cubicContractionAdjoint, Pi.add_apply]; ring
  map_smul' c v := by
    funext i j k l
    simp only [cubicContractionAdjoint, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end
end SecondPinching
