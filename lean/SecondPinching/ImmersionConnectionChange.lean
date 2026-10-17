import SecondPinching.ImmersionReparametrization
import SecondPinching.ImmersionGaussWeingarten

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- Coefficients in the actual coordinate tangent basis are unique. -/
theorem immersionTangent_coefficients_unique (F : LocalSphereImmersion)
    (x : Chart4) (hx : x ∈ F.domain) (u v : Chart4)
    (he : (∑ a, u a • immersionTangent F.map x a) =
      ∑ a, v a • immersionTangent F.map x a) : u = v := by
  apply F.injective_derivative x hx
  simpa only [immersionTangent_expansion] using he

/-- The nonlinear connection law for the two connections constructed from
the actual immersions. The derivative index is last and J has source rows. -/
theorem reparametrized_Christoffel (F : LocalSphereImmersion)
    (P : ImmersionReparametrization F) (x : Chart4) (hx : x ∈ P.domain)
    (i j a : Fin 4) :
    (∑ r, immersionChristoffel (reparametrizedImmersion F P).map x r i j *
      coordinateJacobian P.map x r a) =
      fderiv ℝ (fun y => coordinateJacobian P.map y i a) x (coordinateUnit j) +
      ∑ b, ∑ c, coordinateJacobian P.map x i b * coordinateJacobian P.map x j c *
        immersionChristoffel F.map (P.map x) a b c := by
  let J := coordinateJacobian P.map x
  let dJ := fun b => fderiv ℝ (fun y => coordinateJacobian P.map y i b) x (coordinateUnit j)
  let Γ := immersionChristoffel F.map (P.map x)
  let Γ' := immersionChristoffel (reparametrizedImmersion F P).map x
  let u : Chart4 := fun b => ∑ r, Γ' r i j * J r b
  let v : Chart4 := fun b => dJ b + ∑ c, ∑ d, J i c * J j d * Γ b c d
  have ht : (∑ r, Γ' r i j • immersionTangent (reparametrizedImmersion F P).map x r) =
      ∑ b, u b • immersionTangent F.map (P.map x) b := by
    simp only [reparametrized_tangent F P x hx,Finset.smul_sum,smul_smul,u,
      Finset.sum_smul,J]
    rw [Finset.sum_comm]
  have hs : immersionSecondDerivative (reparametrizedImmersion F P).map x i j =
      (∑ b, v b • immersionTangent F.map (P.map x) b) +
      frameMatrix J (immersionSecondForm F.map F.normal (P.map x)) i j • F.normal (P.map x) -
      frameMatrix J (immersionMetric F.map (P.map x)) i j • F.map (P.map x) := by
    rw [reparametrized_secondDerivative F P x hx]
    simp_rw [immersion_gauss_formula F (P.map x) (P.mapsTo hx)]
    simp only [smul_sub,smul_add,Finset.smul_sum,smul_smul,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,v,add_smul,
      Finset.sum_smul,frameMatrix,Finset.mul_sum]
    have he : (∑ b, ∑ c, ∑ r,
        (J i b * J j c * Γ r b c) • immersionTangent F.map (P.map x) r) =
        ∑ r, ∑ b, ∑ c,
          (J i b * J j c * Γ r b c) • immersionTangent F.map (P.map x) r := by
      simp_rw [Finset.sum_comm (f := fun c r =>
        (J i _ * J j c * Γ r _ c) • immersionTangent F.map (P.map x) r)]
      rw [Finset.sum_comm]
    simp only [← mul_assoc]
    rw [he]
    dsimp [dJ,J,Γ]
    abel
  have hg := immersion_gauss_formula (reparametrizedImmersion F P) x hx i j
  rw [reparametrized_secondForm F P x hx,reparametrized_metric F P x hx] at hg
  change _ = (∑ r, Γ' r i j • immersionTangent (reparametrizedImmersion F P).map x r) +
    frameMatrix J (immersionSecondForm F.map F.normal (P.map x)) i j • F.normal (P.map x) -
    frameMatrix J (immersionMetric F.map (P.map x)) i j • F.map (P.map x) at hg
  rw [ht,hs] at hg
  have huv : u = v := immersionTangent_coefficients_unique F (P.map x) (P.mapsTo hx) u v
    (add_right_cancel (sub_left_inj.mp hg)).symm
  exact congrFun huv a

end
end SecondPinching
