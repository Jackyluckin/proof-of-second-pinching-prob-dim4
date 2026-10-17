import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SecondPinching

/-! The 24 closed rectangles used by the unchanged rational certificate.
The four entries are r₀,r₁,y₀,y₁. Data are exact rational numbers.
This file proves coverage, valid boundaries and disjoint interiors;
it does not assert positivity of any Bernstein control or Gram block. -/

abbrev CertificateRectangle := Fin 4 → ℚ

/-- The actual binary leaf paths, in their order in certificate.json. -/
def certificatePaths : Fin 24 → List Bool :=
  ![[false, false, false],
    [false, false, true],
    [false, true, false],
    [false, true, true, false],
    [false, true, true, true, false],
    [false, true, true, true, true],
    [true, false, false, false, false],
    [true, false, false, false, true],
    [true, false, false, true, false, false],
    [true, false, false, true, false, true],
    [true, false, false, true, true],
    [true, false, true, false],
    [true, false, true, true],
    [true, true, false, false, false],
    [true, true, false, false, true],
    [true, true, false, true],
    [true, true, true, false, false, false],
    [true, true, true, false, false, true],
    [true, true, true, false, true, false, false, false],
    [true, true, true, false, true, false, false, true],
    [true, true, true, false, true, false, true, false],
    [true, true, true, false, true, false, true, true],
    [true, true, true, false, true, true],
    [true, true, true, true]]

/-- The dyadic rectangles attached to the 24 leaf paths. -/
def certificateRectangles : Fin 24 → CertificateRectangle :=
  ![![0, (1/4), 0, (1/2)],
    ![(1/4), (1/2), 0, (1/2)],
    ![0, (1/4), (1/2), 1],
    ![(1/4), (1/2), (1/2), (3/4)],
    ![(1/4), (3/8), (3/4), 1],
    ![(3/8), (1/2), (3/4), 1],
    ![(1/2), (5/8), 0, (1/4)],
    ![(5/8), (3/4), 0, (1/4)],
    ![(1/2), (5/8), (1/4), (3/8)],
    ![(1/2), (5/8), (3/8), (1/2)],
    ![(5/8), (3/4), (1/4), (1/2)],
    ![(3/4), 1, 0, (1/4)],
    ![(3/4), 1, (1/4), (1/2)],
    ![(1/2), (5/8), (1/2), (3/4)],
    ![(5/8), (3/4), (1/2), (3/4)],
    ![(1/2), (3/4), (3/4), 1],
    ![(3/4), (7/8), (1/2), (5/8)],
    ![(3/4), (7/8), (5/8), (3/4)],
    ![(7/8), (15/16), (1/2), (9/16)],
    ![(7/8), (15/16), (9/16), (5/8)],
    ![(15/16), 1, (1/2), (9/16)],
    ![(15/16), 1, (9/16), (5/8)],
    ![(7/8), 1, (5/8), (3/4)],
    ![(3/4), 1, (3/4), 1]]

/-- One alternating bisection, beginning with r at depth zero. -/
def bisectCertificateRectangle (depth : ℕ) (q : CertificateRectangle)
    (right : Bool) : CertificateRectangle :=
  if depth % 2 = 0 then
    if right then ![(q 0+q 1)/2,q 1,q 2,q 3]
    else ![q 0,(q 0+q 1)/2,q 2,q 3]
  else
    if right then ![q 0,q 1,(q 2+q 3)/2,q 3]
    else ![q 0,q 1,q 2,(q 2+q 3)/2]

def rectangleFromPathAux (depth : ℕ) (q : CertificateRectangle) :
    List Bool → CertificateRectangle
  | [] => q
  | b::bs => rectangleFromPathAux (depth+1) (bisectCertificateRectangle depth q b) bs

/-- Reconstruct a rectangle from a path by the paper's alternating bisections. -/
def rectangleFromPath (p : List Bool) : CertificateRectangle :=
  rectangleFromPathAux 0 ![0,1,0,1] p

/-- All paths are distinct. -/
theorem certificatePaths_injective : Function.Injective certificatePaths := by decide

/-- The literal endpoint table agrees with every path's exact dyadic bisections. -/
theorem certificateRectangles_from_paths :
    ∀ i, rectangleFromPath (certificatePaths i) = certificateRectangles i := by
  intro i
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [rectangleFromPath,rectangleFromPathAux,bisectCertificateRectangle,
      certificatePaths,certificateRectangles]

/-- Every rectangle is nondegenerate and lies within the unit square. -/
theorem certificateRectangles_bounds : ∀ i,
    0 ≤ certificateRectangles i 0 ∧ certificateRectangles i 0 < certificateRectangles i 1 ∧
    certificateRectangles i 1 ≤ 1 ∧ 0 ≤ certificateRectangles i 2 ∧
    certificateRectangles i 2 < certificateRectangles i 3 ∧ certificateRectangles i 3 ≤ 1 := by
  intro i
  fin_cases i <;> norm_num [certificateRectangles]

/-- Membership includes all four boundary edges. -/
def inClosedCertificateRectangle (q : CertificateRectangle) (r y : ℝ) : Prop :=
  (q 0 : ℝ) ≤ r ∧ r ≤ (q 1 : ℝ) ∧ (q 2 : ℝ) ≤ y ∧ y ≤ (q 3 : ℝ)

/-- Strict membership is used only for the disjoint-interior assertion. -/
def inOpenCertificateRectangle (q : CertificateRectangle) (r y : ℝ) : Prop :=
  (q 0 : ℝ) < r ∧ r < (q 1 : ℝ) ∧ (q 2 : ℝ) < y ∧ y < (q 3 : ℝ)

/-- Every real point of the closed unit square is covered by an actual leaf. -/
theorem certificateRectangles_cover (r y : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin 24, inClosedCertificateRectangle (certificateRectangles i) r y := by
  obtain ⟨hr0,hr1⟩ := hr
  obtain ⟨hy0,hy1⟩ := hy
  by_cases hroot : r ≤ (1/2)
  · by_cases h0 : y ≤ (1/2)
    · by_cases h00 : r ≤ (1/4)
      · refine ⟨0, ?_⟩
        norm_num [inClosedCertificateRectangle, certificateRectangles]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · refine ⟨1, ?_⟩
        norm_num [inClosedCertificateRectangle, certificateRectangles]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · by_cases h01 : r ≤ (1/4)
      · refine ⟨2, ?_⟩
        norm_num [inClosedCertificateRectangle, certificateRectangles]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · by_cases h011 : y ≤ (3/4)
        · refine ⟨3, ?_⟩
          norm_num [inClosedCertificateRectangle, certificateRectangles]
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · by_cases h0111 : r ≤ (3/8)
          · refine ⟨4, ?_⟩
            norm_num [inClosedCertificateRectangle, certificateRectangles]
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · refine ⟨5, ?_⟩
            norm_num [inClosedCertificateRectangle, certificateRectangles]
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · by_cases h1 : y ≤ (1/2)
    · by_cases h10 : r ≤ (3/4)
      · by_cases h100 : y ≤ (1/4)
        · by_cases h1000 : r ≤ (5/8)
          · refine ⟨6, ?_⟩
            norm_num [inClosedCertificateRectangle, certificateRectangles]
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · refine ⟨7, ?_⟩
            norm_num [inClosedCertificateRectangle, certificateRectangles]
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · by_cases h1001 : r ≤ (5/8)
          · by_cases h10010 : y ≤ (3/8)
            · refine ⟨8, ?_⟩
              norm_num [inClosedCertificateRectangle, certificateRectangles]
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩
            · refine ⟨9, ?_⟩
              norm_num [inClosedCertificateRectangle, certificateRectangles]
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · refine ⟨10, ?_⟩
            norm_num [inClosedCertificateRectangle, certificateRectangles]
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · by_cases h101 : y ≤ (1/4)
        · refine ⟨11, ?_⟩
          norm_num [inClosedCertificateRectangle, certificateRectangles]
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · refine ⟨12, ?_⟩
          norm_num [inClosedCertificateRectangle, certificateRectangles]
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · by_cases h11 : r ≤ (3/4)
      · by_cases h110 : y ≤ (3/4)
        · by_cases h1100 : r ≤ (5/8)
          · refine ⟨13, ?_⟩
            norm_num [inClosedCertificateRectangle, certificateRectangles]
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · refine ⟨14, ?_⟩
            norm_num [inClosedCertificateRectangle, certificateRectangles]
            exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · refine ⟨15, ?_⟩
          norm_num [inClosedCertificateRectangle, certificateRectangles]
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · by_cases h111 : y ≤ (3/4)
        · by_cases h1110 : r ≤ (7/8)
          · by_cases h11100 : y ≤ (5/8)
            · refine ⟨16, ?_⟩
              norm_num [inClosedCertificateRectangle, certificateRectangles]
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩
            · refine ⟨17, ?_⟩
              norm_num [inClosedCertificateRectangle, certificateRectangles]
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩
          · by_cases h11101 : y ≤ (5/8)
            · by_cases h111010 : r ≤ (15/16)
              · by_cases h1110100 : y ≤ (9/16)
                · refine ⟨18, ?_⟩
                  norm_num [inClosedCertificateRectangle, certificateRectangles]
                  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
                · refine ⟨19, ?_⟩
                  norm_num [inClosedCertificateRectangle, certificateRectangles]
                  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
              · by_cases h1110101 : y ≤ (9/16)
                · refine ⟨20, ?_⟩
                  norm_num [inClosedCertificateRectangle, certificateRectangles]
                  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
                · refine ⟨21, ?_⟩
                  norm_num [inClosedCertificateRectangle, certificateRectangles]
                  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
            · refine ⟨22, ?_⟩
              norm_num [inClosedCertificateRectangle, certificateRectangles]
              exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        · refine ⟨23, ?_⟩
          norm_num [inClosedCertificateRectangle, certificateRectangles]
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Any two distinct leaves are separated in at least one coordinate. -/
theorem certificateRectangles_separated : ∀ i j : Fin 24, i ≠ j →
    certificateRectangles i 1 ≤ certificateRectangles j 0 ∨
    certificateRectangles j 1 ≤ certificateRectangles i 0 ∨
    certificateRectangles i 3 ≤ certificateRectangles j 2 ∨
    certificateRectangles j 3 ≤ certificateRectangles i 2 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [certificateRectangles] at *

/-- The open interiors of any two distinct certificate rectangles are disjoint. -/
theorem certificateRectangles_disjoint_interiors (i j : Fin 24) (hij : i ≠ j)
    (r y : ℝ) (hi : inOpenCertificateRectangle (certificateRectangles i) r y)
    (hj : inOpenCertificateRectangle (certificateRectangles j) r y) : False := by
  obtain ⟨hi0,hi1,hi2,hi3⟩ := hi
  obtain ⟨hj0,hj1,hj2,hj3⟩ := hj
  rcases certificateRectangles_separated i j hij with h | h | h | h
  · have hh : (certificateRectangles i 1 : ℝ) ≤ (certificateRectangles j 0 : ℝ) := by exact_mod_cast h
    linarith
  · have hh : (certificateRectangles j 1 : ℝ) ≤ (certificateRectangles i 0 : ℝ) := by exact_mod_cast h
    linarith
  · have hh : (certificateRectangles i 3 : ℝ) ≤ (certificateRectangles j 2 : ℝ) := by exact_mod_cast h
    linarith
  · have hh : (certificateRectangles j 3 : ℝ) ≤ (certificateRectangles i 2 : ℝ) := by exact_mod_cast h
    linarith

end SecondPinching
