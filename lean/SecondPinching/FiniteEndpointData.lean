import SecondPinching.IntrinsicIntegral

set_option autoImplicit false
open scoped Matrix
namespace SecondPinching
noncomputable section

/-- Finite algebraic input for the endpoint certificate. The positive scale
clears the Bernstein coefficient arrays; it is the sigma in the existing
finite-check interface, not the denominator-channel coefficient d_ij. -/
structure FiniteEndpointData where
  polynomial : MvPolynomial (Fin 14) ℚ
  controls : Fin 24 → ControlIndex → MvPolynomial (Fin 12) ℚ
  gramNumerator : Fin 24 → ControlIndex → (b : Fin 8) →
    Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) ℤ
  congruenceWitness : Fin 24 → ControlIndex → (b : Fin 8) →
    Matrix (Fin (certificateBlockSize b)) (Fin (certificateBlockSize b)) ℤ
  bernsteinIntegerScale : Fin 24 → ControlIndex → ℤ

/-- Precisely the five finite families accepted by the previously proved
endpoint theorem. This predicate contains no geometric or infinite endpoint
inequality, and no acceptance proof for a released instance is asserted here. -/
def FiniteEndpointAccepted (D : FiniteEndpointData) : Prop :=
  exactCoefficientCheck 14 D.polynomial endpointPolynomial=true ∧
  (∀ leaf, exactCoefficientCheck 14 D.polynomial (certificateExpansionPolynomial leaf (D.controls leaf))=true) ∧
  (∀ leaf ij, 0 < D.bernsteinIntegerScale leaf ij) ∧
  (∀ leaf ij, exactCoefficientCheck 12 (D.controls leaf ij)
    (integerBlockQuartic (D.gramNumerator leaf ij)
      ((compressedGramConstant : ℚ)*(D.bernsteinIntegerScale leaf ij : ℚ)))=true) ∧
  (∀ leaf ij b, integerCertificateCheck (certificateBlockSize b)
    (D.gramNumerator leaf ij b) (D.congruenceWitness leaf ij b)=true)

theorem finiteEndpointAccepted_endpoint (D : FiniteEndpointData) (hD : FiniteEndpointAccepted D)
    (A : Matrix4) (τ : Cubic4) (had : PaperAdmissible A τ) :
    intrinsicPinchingW A τ (1/2) ≤ -(1/10000 : ℝ) := by
  rcases hD with ⟨hP,he,hs,hc,hb⟩
  exact intrinsic_endpoint_of_finite_certificate D.polynomial D.controls D.gramNumerator
    D.congruenceWitness D.bernsteinIntegerScale hP he hs hc hb A τ had

end
end SecondPinching
