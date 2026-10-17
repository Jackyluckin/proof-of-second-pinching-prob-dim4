import SecondPinching.CurvatureCorrection
import SecondPinching.HessianTraceCorrection

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching
noncomputable section

/-! Algebraic content of Proposition 4.1. The Ricci commutator, differentiated
trace identities, and normalized Peng--Terng identity remain explicit inputs.
This module does not define an immersion or prove those geometric inputs. -/

/-- The normalized Ricci identity, in a principal frame with kappa=1/S. -/
def HasRicciCommutator (μ : Vector4) (κ : ℝ) (D : Fourth4) : Prop :=
  ∀ i j k l, D i j k l - D i j l k =
    (μ i - μ j) * (κ + μ i * μ j) *
      ((1 : Matrix4) i k * (1 : Matrix4) j l -
       (1 : Matrix4) i l * (1 : Matrix4) j k)

theorem symmetrizeFourth_sub (U W : Fourth4) :
    symmetrizeFourth (U-W) = symmetrizeFourth U - symmetrizeFourth W := by
  funext i j k l
  simp [symmetrizeFourth, Finset.sum_sub_distrib, mul_sub]

theorem symmetrizeFourth_eq_self (U : Fourth4) (hU : FourthSymmetric U) :
    symmetrizeFourth U = U := by
  funext i j k l
  have h : ∀ σ : Equiv.Perm (Fin 4),
      U (![i,j,k,l] (σ 0)) (![i,j,k,l] (σ 1))
        (![i,j,k,l] (σ 2)) (![i,j,k,l] (σ 3)) = U i j k l := by
    intro σ
    simpa using hU σ ![i,j,k,l]
  norm_num [symmetrizeFourth, h, Fintype.card_perm, Nat.factorial]
  ring

/-- Removing the explicit Ricci defect restores full four-slot symmetry. -/
theorem hessian_sub_correction_symmetric (μ : Vector4) (κ : ℝ) (D : Fourth4)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ κ D) :
    FourthSymmetric (D - curvatureCorrection μ κ) := by
  apply (fourthSymmetric_iff_swaps _).mpr
  have hC := curvatureCorrection_firstThree μ κ
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    change D i j k l - _ = D j i k l - _
    rw [hD.1 i j k l, hC.1 i j k l]
  · intro i j k l
    change D i j k l - _ = D i k j l - _
    rw [hD.2 i j k l, hC.2 i j k l]
  · intro i j k l
    change D i j k l - _ = D i j l k - _
    have hr := hRicci i j k l
    have hc := curvatureCorrection_commutator μ κ i j k l
    linarith

/-- The correction is proved equal to D-Sym D, rather than assumed to be so. -/
theorem hessian_symmetrization (μ : Vector4) (κ : ℝ) (D : Fourth4)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ κ D) :
    symmetrizeFourth D = D - curvatureCorrection μ κ := by
  have hs := symmetrizeFourth_eq_self (D-curvatureCorrection μ κ)
    (hessian_sub_correction_symmetric μ κ D hD hRicci)
  rwa [symmetrizeFourth_sub, curvatureCorrection_symmetrize, sub_zero] at hs

/-- The actual tensor V = Sym D - U_0 used in Proposition 4.1. -/
def hessianRemainder (μ : Vector4) (t : ℝ) (D : Fourth4) : Fourth4 :=
  symmetrizeFourth D - hessianTraceCorrection μ t

theorem hessianRemainder_mem (μ : Vector4) (t : ℝ) (D : Fourth4)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ ((1-t)/4) D)
    (htr : ordinaryTrace D = 0) : TraceFreeFourth (hessianRemainder μ t D) := by
  rw [hessianRemainder, hessian_symmetrization μ ((1-t)/4) D hD hRicci]
  refine ⟨fourthSymmetric_sub (hessian_sub_correction_symmetric μ _ D hD hRicci)
    (hessianTraceCorrection_symmetric μ t), ?_⟩
  rw [ordinaryTrace_sub, ordinaryTrace_sub, htr,
    ordinaryTrace_curvatureCorrection μ t hμ hn, ordinaryTrace_hessianTraceCorrection μ t hμ]
  ext k l
  simp
  ring

/-- The weighted contraction E_t, derived from T_A D=-tR. -/
theorem weightedTrace_hessianRemainder (μ : Vector4) (τ : Cubic4) (t : ℝ) (D : Fourth4)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ ((1-t)/4) D)
    (hweighted : weightedTrace (Matrix.diagonal μ) D = (-t) • cubicGramMatrix τ) :
    weightedTrace (Matrix.diagonal μ) (hessianRemainder μ t D) =
      hessianE (Matrix.diagonal μ) τ t := by
  rw [hessianRemainder, hessian_symmetrization μ ((1-t)/4) D hD hRicci]
  change weightedTraceLinear (Matrix.diagonal μ) ((_ - _) - _) = _
  rw [map_sub, map_sub]
  change weightedTrace _ D - weightedTrace _ _ - weightedTrace _ _ = _
  rw [hweighted, weightedTrace_curvatureCorrection μ _ hμ hn,
    weightedTrace_hessianTraceCorrection μ t hμ hn]
  ext k l
  simp [hessianE, normalizedPhi, hessianPsi]
  ring

/-- The second contraction, keeping the nonzero vector d. -/
theorem cubicContraction_hessianRemainder (μ : Vector4) (τ : Cubic4) (t : ℝ) (D : Fourth4)
    (hτ : CubicSymmetric τ) (ht : ∀ k, ∑ i, τ i i k = 0)
    (hw : ∀ k, ∑ i, μ i * τ i i k = 0)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ ((1-t)/4) D)
    (hcubic : cubicContraction τ D = 0) :
    cubicContraction τ (hessianRemainder μ t D) = hessianB0 μ τ := by
  rw [hessianRemainder, hessian_symmetrization μ ((1-t)/4) D hD hRicci]
  change cubicContractionLinear τ ((_ - _) - _) = _
  rw [map_sub, map_sub]
  change cubicContraction τ D - cubicContraction τ _ - cubicContraction τ _ = _
  rw [hcubic, cubicContraction_curvatureCorrection μ _ τ hτ ht hw,
    cubicContraction_hessianTraceCorrection μ τ hτ ht hw t]
  funext l
  simp [hessianB0]

/-- The ordered norm identity from the two orthogonal removals. -/
theorem hessian_norm_decomposition (μ : Vector4) (t : ℝ) (D : Fourth4)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ ((1-t)/4) D)
    (htr : ordinaryTrace D = 0) :
    fourthNormSq D = fourthNormSq (hessianRemainder μ t D) +
      (3/2 : ℝ) * phiNormSq (Matrix.diagonal μ) + (9/16 : ℝ) * t^2 := by
  have hsym := hessian_sub_correction_symmetric μ ((1-t)/4) D hD hRicci
  have hc := curvatureCorrection_orthogonal μ ((1-t)/4) _ hsym
  rw [fourthInner_sub_right, fourthInner_self, fourthInner_comm] at hc
  have hu := hessianTraceCorrection_orthogonal μ t _
    (hessianRemainder_mem μ t D hμ hn hD hRicci htr)
  rw [hessianRemainder, hessian_symmetrization μ ((1-t)/4) D hD hRicci,
    fourthInner_sub_right, fourthInner_self, fourthInner_comm] at hu
  have hv : fourthNormSq (hessianRemainder μ t D) =
      fourthNormSq D - 2 * fourthInner D (curvatureCorrection μ ((1-t)/4)) +
      fourthNormSq (curvatureCorrection μ ((1-t)/4)) -
      2 * fourthInner (D-curvatureCorrection μ ((1-t)/4)) (hessianTraceCorrection μ t) +
      fourthNormSq (hessianTraceCorrection μ t) := by
    rw [hessianRemainder, hessian_symmetrization μ ((1-t)/4) D hD hRicci,
      fourthNormSq_sub, fourthNormSq_sub]
  rw [curvatureCorrection_norm μ t hμ hn] at hc hv
  rw [hessianTraceCorrection_norm μ t hμ hn] at hu hv
  linarith

/-- The norm in eq:Vnorm, conditional on the normalized Peng--Terng identity. -/
theorem hessianRemainder_norm (μ : Vector4) (τ : Cubic4) (t : ℝ) (D : Fourth4)
    (hμ : ∑ i, μ i = 0) (hn : ∑ i, (μ i)^2 = 1)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ ((1-t)/4) D)
    (htr : ordinaryTrace D = 0)
    (hPT : fourthNormSq D = 3*t*(cubicA μ τ - 2*cubicB μ τ) + t*(11*t-7)/4) :
    fourthNormSq (hessianRemainder μ t D) =
      3*t*(cubicA μ τ - 2*cubicB μ τ) + t*(35*t-28)/16 -
        (3/2 : ℝ) * phiNormSq (Matrix.diagonal μ) := by
  have hd := hessian_norm_decomposition μ t D hμ hn hD hRicci htr
  rw [hPT] at hd
  linarith

/-- All finite-dimensional conclusions of prop:reduction from its explicit
geometric component inputs. This is not the proposition for immersions. -/
theorem hessian_algebraic_reduction (μ : Vector4) (τ : Cubic4) (t : ℝ) (D : Fourth4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ ((1-t)/4) D)
    (htr : ordinaryTrace D = 0)
    (hweighted : weightedTrace (Matrix.diagonal μ) D = (-t) • cubicGramMatrix τ)
    (hcubic : cubicContraction τ D = 0)
    (hPT : fourthNormSq D = 3*t*(cubicA μ τ - 2*cubicB μ τ) + t*(11*t-7)/4) :
    ∃ V : Fourth4, TraceFreeFourth V ∧
      weightedTrace (Matrix.diagonal μ) V = hessianE (Matrix.diagonal μ) τ t ∧
      cubicContraction τ V = hessianB0 μ τ ∧
      fourthNormSq V = 3*t*(cubicA μ τ - 2*cubicB μ τ) + t*(35*t-28)/16 -
        (3/2 : ℝ) * phiNormSq (Matrix.diagonal μ) := by
  obtain ⟨hτ,hμ,hn,_hτn,ht,hw⟩ := (admissible_diagonal_iff μ τ).mp
    ((admissible_iff_paper _ _).mpr had)
  exact ⟨hessianRemainder μ t D,
    hessianRemainder_mem μ t D hμ hn hD hRicci htr,
    weightedTrace_hessianRemainder μ τ t D hμ hn hD hRicci hweighted,
    cubicContraction_hessianRemainder μ τ t D hτ ht hw hD hRicci hcubic,
    hessianRemainder_norm μ τ t D hμ hn hD hRicci htr hPT⟩

/-- Sections 3 and 4 joined: the exact square remainder before the three
zero-average terms are added. No pointwise identity for W_t is asserted. -/
theorem hessian_joint_remainder (μ : Vector4) (τ : Cubic4) (t : ℝ) (D : Fourth4)
    (had : PaperAdmissible (Matrix.diagonal μ) τ)
    (hD : FirstThreeSymmetric D) (hRicci : HasRicciCommutator μ ((1-t)/4) D)
    (htr : ordinaryTrace D = 0)
    (hweighted : weightedTrace (Matrix.diagonal μ) D = (-t) • cubicGramMatrix τ)
    (hcubic : cubicContraction τ D = 0)
    (hPT : fourthNormSq D = 3*t*(cubicA μ τ - 2*cubicB μ τ) + t*(11*t-7)/4)
    (Y : Matrix4) (hY : Y.IsSymm) (hYtr : Matrix.trace Y = 0) (v : Vector4) :
    (3*t*(cubicA μ τ - 2*cubicB μ τ) + t*(35*t-28)/16 -
      (3/2 : ℝ) * phiNormSq (Matrix.diagonal μ)) -
      (2 * matrixInner (hessianE (Matrix.diagonal μ) τ t) Y + 2 * (hessianB0 μ τ ⬝ᵥ v) -
        matrixInner Y (matrixGramOperator (Matrix.diagonal μ) Y) -
        2 * (v ⬝ᵥ mixedGramOperator μ τ Y) - v ⬝ᵥ (vectorGramOperator τ *ᵥ v)) =
      fourthNormSq (hessianRemainder μ t D - jointTrialTensor (Matrix.diagonal μ) Y τ v) := by
  have ha := (admissible_iff_paper _ _).mpr had
  obtain ⟨hτ,hμ,hn,_hτn,ht,hw⟩ := (admissible_diagonal_iff μ τ).mp ha
  have hr := joint_contraction_remainder_diagonal μ τ ha _ Y hY hYtr _ v
    (hessianRemainder μ t D) (hessianRemainder_mem μ t D hμ hn hD hRicci htr)
    (weightedTrace_hessianRemainder μ τ t D hμ hn hD hRicci hweighted)
    (cubicContraction_hessianRemainder μ τ t D hτ ht hw hD hRicci hcubic)
  rwa [hessianRemainder_norm μ τ t D hμ hn hD hRicci htr hPT] at hr

end
end SecondPinching
