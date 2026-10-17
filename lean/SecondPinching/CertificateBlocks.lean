import SecondPinching.FiniteCertificateInterface

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators Matrix
namespace SecondPinching

/-- The literal lexicographic order in DATA_SPEC.md. This is separate from
`quadraticIndexEquivFin`, whose arbitrary enumeration was never a data order. -/
def certificateLexPair : Fin 78 → QuadraticIndex :=
  ![⟨(0, 0), by decide⟩, ⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(0, 3), by decide⟩, ⟨(0, 4), by decide⟩, ⟨(0, 5), by decide⟩, ⟨(0, 6), by decide⟩, ⟨(0, 7), by decide⟩, ⟨(0, 8), by decide⟩, ⟨(0, 9), by decide⟩, ⟨(0, 10), by decide⟩, ⟨(0, 11), by decide⟩, ⟨(1, 1), by decide⟩, ⟨(1, 2), by decide⟩, ⟨(1, 3), by decide⟩, ⟨(1, 4), by decide⟩, ⟨(1, 5), by decide⟩, ⟨(1, 6), by decide⟩, ⟨(1, 7), by decide⟩, ⟨(1, 8), by decide⟩, ⟨(1, 9), by decide⟩, ⟨(1, 10), by decide⟩, ⟨(1, 11), by decide⟩, ⟨(2, 2), by decide⟩, ⟨(2, 3), by decide⟩, ⟨(2, 4), by decide⟩, ⟨(2, 5), by decide⟩, ⟨(2, 6), by decide⟩, ⟨(2, 7), by decide⟩, ⟨(2, 8), by decide⟩, ⟨(2, 9), by decide⟩, ⟨(2, 10), by decide⟩, ⟨(2, 11), by decide⟩, ⟨(3, 3), by decide⟩, ⟨(3, 4), by decide⟩, ⟨(3, 5), by decide⟩, ⟨(3, 6), by decide⟩, ⟨(3, 7), by decide⟩, ⟨(3, 8), by decide⟩, ⟨(3, 9), by decide⟩, ⟨(3, 10), by decide⟩, ⟨(3, 11), by decide⟩, ⟨(4, 4), by decide⟩, ⟨(4, 5), by decide⟩, ⟨(4, 6), by decide⟩, ⟨(4, 7), by decide⟩, ⟨(4, 8), by decide⟩, ⟨(4, 9), by decide⟩, ⟨(4, 10), by decide⟩, ⟨(4, 11), by decide⟩, ⟨(5, 5), by decide⟩, ⟨(5, 6), by decide⟩, ⟨(5, 7), by decide⟩, ⟨(5, 8), by decide⟩, ⟨(5, 9), by decide⟩, ⟨(5, 10), by decide⟩, ⟨(5, 11), by decide⟩, ⟨(6, 6), by decide⟩, ⟨(6, 7), by decide⟩, ⟨(6, 8), by decide⟩, ⟨(6, 9), by decide⟩, ⟨(6, 10), by decide⟩, ⟨(6, 11), by decide⟩, ⟨(7, 7), by decide⟩, ⟨(7, 8), by decide⟩, ⟨(7, 9), by decide⟩, ⟨(7, 10), by decide⟩, ⟨(7, 11), by decide⟩, ⟨(8, 8), by decide⟩, ⟨(8, 9), by decide⟩, ⟨(8, 10), by decide⟩, ⟨(8, 11), by decide⟩, ⟨(9, 9), by decide⟩, ⟨(9, 10), by decide⟩, ⟨(9, 11), by decide⟩, ⟨(10, 10), by decide⟩, ⟨(10, 11), by decide⟩, ⟨(11, 11), by decide⟩]

/-- The literal list contains every unordered quadratic label exactly once. -/
theorem certificateLexPair_bijective : Function.Bijective certificateLexPair := by decide

/-- The list is increasing in the lexicographic order of the amplitude labels. -/
theorem certificateLexPair_order : ∀ i j : Fin 78, i < j →
    (certificateLexPair i).val.1 < (certificateLexPair j).val.1 ∨
    ((certificateLexPair i).val.1 = (certificateLexPair j).val.1 ∧
      (certificateLexPair i).val.2 < (certificateLexPair j).val.2) := by decide

/-- The eight sign-character block sizes in the release. -/
def certificateBlockSize : Fin 8 → ℕ := ![16, 9, 9, 9, 9, 9, 9, 8]

/-- All blocks are nonempty. -/
theorem certificateBlockSize_pos : ∀ b, 1 ≤ certificateBlockSize b := by decide

/-- Amplitude frame-sign characters, with zero-based amplitude indices. -/
def certificateAmplitudeCharacter : Fin 12 → ℕ := ![14, 13, 11, 7, 1, 1, 2, 2, 4, 4, 8, 8]

/-- The block order is the increasing order of XOR characters. -/
def certificateBlockCharacter : Fin 8 → ℕ := ![0, 3, 5, 6, 9, 10, 12, 15]

/-- Quadratic labels in each block, retaining the global lexicographic order. -/
def certificateBlockPair : (b : Fin 8) → Fin (certificateBlockSize b) → QuadraticIndex := by
  intro b
  refine Fin.cases ?_ (fun b => ?_) b
  · exact ![⟨(0, 0), by decide⟩, ⟨(1, 1), by decide⟩, ⟨(2, 2), by decide⟩, ⟨(3, 3), by decide⟩, ⟨(4, 4), by decide⟩, ⟨(4, 5), by decide⟩, ⟨(5, 5), by decide⟩, ⟨(6, 6), by decide⟩, ⟨(6, 7), by decide⟩, ⟨(7, 7), by decide⟩, ⟨(8, 8), by decide⟩, ⟨(8, 9), by decide⟩, ⟨(9, 9), by decide⟩, ⟨(10, 10), by decide⟩, ⟨(10, 11), by decide⟩, ⟨(11, 11), by decide⟩]
  · refine Fin.cases ?_ (fun b => ?_) b
    · exact ![⟨(0, 1), by decide⟩, ⟨(2, 10), by decide⟩, ⟨(2, 11), by decide⟩, ⟨(3, 8), by decide⟩, ⟨(3, 9), by decide⟩, ⟨(4, 6), by decide⟩, ⟨(4, 7), by decide⟩, ⟨(5, 6), by decide⟩, ⟨(5, 7), by decide⟩]
    · refine Fin.cases ?_ (fun b => ?_) b
      · exact ![⟨(0, 2), by decide⟩, ⟨(1, 10), by decide⟩, ⟨(1, 11), by decide⟩, ⟨(3, 6), by decide⟩, ⟨(3, 7), by decide⟩, ⟨(4, 8), by decide⟩, ⟨(4, 9), by decide⟩, ⟨(5, 8), by decide⟩, ⟨(5, 9), by decide⟩]
      · refine Fin.cases ?_ (fun b => ?_) b
        · exact ![⟨(0, 10), by decide⟩, ⟨(0, 11), by decide⟩, ⟨(1, 2), by decide⟩, ⟨(3, 4), by decide⟩, ⟨(3, 5), by decide⟩, ⟨(6, 8), by decide⟩, ⟨(6, 9), by decide⟩, ⟨(7, 8), by decide⟩, ⟨(7, 9), by decide⟩]
        · refine Fin.cases ?_ (fun b => ?_) b
          · exact ![⟨(0, 3), by decide⟩, ⟨(1, 8), by decide⟩, ⟨(1, 9), by decide⟩, ⟨(2, 6), by decide⟩, ⟨(2, 7), by decide⟩, ⟨(4, 10), by decide⟩, ⟨(4, 11), by decide⟩, ⟨(5, 10), by decide⟩, ⟨(5, 11), by decide⟩]
          · refine Fin.cases ?_ (fun b => ?_) b
            · exact ![⟨(0, 8), by decide⟩, ⟨(0, 9), by decide⟩, ⟨(1, 3), by decide⟩, ⟨(2, 4), by decide⟩, ⟨(2, 5), by decide⟩, ⟨(6, 10), by decide⟩, ⟨(6, 11), by decide⟩, ⟨(7, 10), by decide⟩, ⟨(7, 11), by decide⟩]
            · refine Fin.cases ?_ (fun b => ?_) b
              · exact ![⟨(0, 6), by decide⟩, ⟨(0, 7), by decide⟩, ⟨(1, 4), by decide⟩, ⟨(1, 5), by decide⟩, ⟨(2, 3), by decide⟩, ⟨(8, 10), by decide⟩, ⟨(8, 11), by decide⟩, ⟨(9, 10), by decide⟩, ⟨(9, 11), by decide⟩]
              · refine Fin.cases ?_ (fun b => ?_) b
                · exact ![⟨(0, 4), by decide⟩, ⟨(0, 5), by decide⟩, ⟨(1, 6), by decide⟩, ⟨(1, 7), by decide⟩, ⟨(2, 8), by decide⟩, ⟨(2, 9), by decide⟩, ⟨(3, 10), by decide⟩, ⟨(3, 11), by decide⟩]
                · exact Fin.elim0 b

/-- All 78 quadratic labels occur in precisely one block coordinate. -/
theorem certificateBlockPair_bijective :
    Function.Bijective (fun q : (b : Fin 8) × Fin (certificateBlockSize b) =>
      certificateBlockPair q.1 q.2) := by decide

/-- The literal partition agrees with the frame-sign character rule. -/
theorem certificateBlockPair_character : ∀ b i,
    Nat.xor (certificateAmplitudeCharacter (certificateBlockPair b i).val.1)
      (certificateAmplitudeCharacter (certificateBlockPair b i).val.2) =
        certificateBlockCharacter b := by decide

/-- Each block retains the lexicographic order, as specified in the release. -/
theorem certificateBlockPair_order : ∀ b, ∀ i j : Fin (certificateBlockSize b), i < j →
    (certificateBlockPair b i).val.1 < (certificateBlockPair b j).val.1 ∨
    ((certificateBlockPair b i).val.1 = (certificateBlockPair b j).val.1 ∧
      (certificateBlockPair b i).val.2 < (certificateBlockPair b j).val.2) := by decide

/-- The monomial vector of one sign block. -/
def certificateBlockMonomials (x : Fin 12 → ℝ) (b : Fin 8) :
    Fin (certificateBlockSize b) → ℝ :=
  fun i => quadraticMonomials x (certificateBlockPair b i)

/-- A nonzero amplitude vector gives a nonzero vector in at least one block. -/
theorem certificateBlockMonomials_some_ne_zero (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    ∃ b, certificateBlockMonomials x b ≠ 0 := by
  by_contra h
  push Not at h
  apply quadraticMonomials_ne_zero hx
  funext q
  obtain ⟨⟨b,i⟩, hi⟩ := certificateBlockPair_bijective.2 q
  have hz := congrFun (h b) i
  simpa [certificateBlockMonomials, hi] using hz

/-- Each of the eight integer tests is required at the control under consideration. -/
theorem certificateBlock_forms_pos
    (Q V : (b : Fin 8) → Matrix (Fin (certificateBlockSize b))
      (Fin (certificateBlockSize b)) ℤ)
    (hchecks : ∀ b, integerCertificateCheck (certificateBlockSize b) (Q b) (V b) = true)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    0 < ∑ b, certificateBlockMonomials x b ⬝ᵥ
      (integerMatrixToReal (Q b) *ᵥ certificateBlockMonomials x b) := by
  have hpos b := integerCertificateCheck_sound _ (certificateBlockSize_pos b) (Q b) (V b) (hchecks b)
  obtain ⟨b,hb⟩ := certificateBlockMonomials_some_ne_zero x hx
  apply Finset.sum_pos'
  · intro c _
    simpa only [star_trivial] using (hpos c).posSemidef.dotProduct_mulVec_nonneg
      (certificateBlockMonomials x c)
  · exact ⟨b, Finset.mem_univ b, by
      simpa only [star_trivial] using (hpos b).dotProduct_mulVec_pos hb⟩

/-- The quartic represented by the eight integer blocks and a common scale.
Every ordered matrix entry is included, so off-diagonal multiplicity is two. -/
noncomputable def integerBlockQuartic
    (Q : (b : Fin 8) → Matrix (Fin (certificateBlockSize b))
      (Fin (certificateBlockSize b)) ℤ) (scale : ℚ) : MvPolynomial (Fin 12) ℚ :=
  ∑ b, ∑ i, ∑ j, MvPolynomial.C ((Q b i j : ℚ) / scale) *
    (MvPolynomial.X (certificateBlockPair b i).val.1 *
      MvPolynomial.X (certificateBlockPair b i).val.2) *
    (MvPolynomial.X (certificateBlockPair b j).val.1 *
      MvPolynomial.X (certificateBlockPair b j).val.2)

/-- Evaluation of the actual block quartic, with its common denominator. -/
theorem integerBlockQuartic_eval
    (Q : (b : Fin 8) → Matrix (Fin (certificateBlockSize b))
      (Fin (certificateBlockSize b)) ℤ) (scale : ℚ) (x : Fin 12 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (integerBlockQuartic Q scale) =
      (∑ b, certificateBlockMonomials x b ⬝ᵥ
        (integerMatrixToReal (Q b) *ᵥ certificateBlockMonomials x b)) / (scale : ℝ) := by
  simp only [integerBlockQuartic, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    certificateBlockMonomials, quadraticMonomials,
    integerMatrixToReal, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  norm_num
  ring

/-- Complete polynomial equality plus the eight block tests imply positivity
of the control quartic. The data and finite test results remain explicit inputs. -/
theorem block_quartic_positivity_from_external_finite_checks
    (P : MvPolynomial (Fin 12) ℚ)
    (Q V : (b : Fin 8) → Matrix (Fin (certificateBlockSize b))
      (Fin (certificateBlockSize b)) ℤ)
    (scale : ℚ) (hscale : 0 < scale)
    (hcoeff : exactCoefficientCheck 12 P (integerBlockQuartic Q scale) = true)
    (hchecks : ∀ b, integerCertificateCheck (certificateBlockSize b) (Q b) (V b) = true)
    (x : Fin 12 → ℝ) (hx : x ≠ 0) :
    0 < MvPolynomial.eval₂ (algebraMap ℚ ℝ) x P := by
  rw [exactCoefficientCheck_real_identity 12 P _ hcoeff x, integerBlockQuartic_eval]
  exact div_pos (certificateBlock_forms_pos Q V hchecks x hx) (by exact_mod_cast hscale)

end SecondPinching
