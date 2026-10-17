import SecondPinching.OrdinaryTrace

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! The literal average over all 4! permutations in Section 3. -/

/-- Explicit enumeration of all four-slot permutations, for exact finite rewriting. -/
def fourthSlotPermutations : Fin 24 → Equiv.Perm (Fin 4) :=
  ![
    ⟨![0,1,2,3], ![0,1,2,3], by decide, by decide⟩,
    ⟨![0,1,3,2], ![0,1,3,2], by decide, by decide⟩,
    ⟨![0,2,1,3], ![0,2,1,3], by decide, by decide⟩,
    ⟨![0,2,3,1], ![0,3,1,2], by decide, by decide⟩,
    ⟨![0,3,1,2], ![0,2,3,1], by decide, by decide⟩,
    ⟨![0,3,2,1], ![0,3,2,1], by decide, by decide⟩,
    ⟨![1,0,2,3], ![1,0,2,3], by decide, by decide⟩,
    ⟨![1,0,3,2], ![1,0,3,2], by decide, by decide⟩,
    ⟨![1,2,0,3], ![2,0,1,3], by decide, by decide⟩,
    ⟨![1,2,3,0], ![3,0,1,2], by decide, by decide⟩,
    ⟨![1,3,0,2], ![2,0,3,1], by decide, by decide⟩,
    ⟨![1,3,2,0], ![3,0,2,1], by decide, by decide⟩,
    ⟨![2,0,1,3], ![1,2,0,3], by decide, by decide⟩,
    ⟨![2,0,3,1], ![1,3,0,2], by decide, by decide⟩,
    ⟨![2,1,0,3], ![2,1,0,3], by decide, by decide⟩,
    ⟨![2,1,3,0], ![3,1,0,2], by decide, by decide⟩,
    ⟨![2,3,0,1], ![2,3,0,1], by decide, by decide⟩,
    ⟨![2,3,1,0], ![3,2,0,1], by decide, by decide⟩,
    ⟨![3,0,1,2], ![1,2,3,0], by decide, by decide⟩,
    ⟨![3,0,2,1], ![1,3,2,0], by decide, by decide⟩,
    ⟨![3,1,0,2], ![2,1,3,0], by decide, by decide⟩,
    ⟨![3,1,2,0], ![3,1,2,0], by decide, by decide⟩,
    ⟨![3,2,0,1], ![2,3,1,0], by decide, by decide⟩,
    ⟨![3,2,1,0], ![3,2,1,0], by decide, by decide⟩
  ]

/-- No slot permutation is omitted or duplicated. -/
theorem fourthSlotPermutations_bijective : Function.Bijective fourthSlotPermutations := by
  decide

/-- The averaging sum is exactly the sum over the whole permutation group. -/
theorem fourthSlotPermutations_sum (f : Equiv.Perm (Fin 4) → ℝ) :
    ∑ s : Fin 24, f (fourthSlotPermutations s) = ∑ σ : Equiv.Perm (Fin 4), f σ := by
  exact Fintype.sum_bijective fourthSlotPermutations fourthSlotPermutations_bijective _ _ (fun _ => rfl)

/-- Literal Sym U from Section 3: average over all 4! slot permutations. -/
def symmetrizeFourth (U : Fourth4) : Fourth4 := fun i j k l =>
  (1/24 : ℝ) * ∑ σ : Equiv.Perm (Fin 4),
    U (![i,j,k,l] (σ 0)) (![i,j,k,l] (σ 1)) (![i,j,k,l] (σ 2)) (![i,j,k,l] (σ 3))

/-- The unsymmetrized tensor product I tensor X, with the paper's slot order. -/
def identityTensorProduct (X : Matrix4) : Fourth4 :=
  fun i j k l => (1 : Matrix4) i j * X k l

/-- First formula of Lemma 3.2, with Sym defined as the complete permutation average. -/
theorem ordinaryTraceAdjoint_eq_sym (X : Matrix4) (hX : X.IsSymm) :
    ordinaryTraceAdjoint X = symmetrizeFourth (identityTensorProduct X) := by
  funext i j k l
  unfold symmetrizeFourth
  rw [← fourthSlotPermutations_sum]
  simp only [Fin.sum_univ_succ]
  unfold fourthSlotPermutations
  dsimp [identityTensorProduct,ordinaryTraceAdjoint]
  simp only [hX.apply,identityEntry_comm]
  ring

end
end SecondPinching
