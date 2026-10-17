import SecondPinching.MatrixPowerCalculus

set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix Matrix.Norms.Elementwise Topology ContDiff
namespace SecondPinching
noncomputable section

/-- The local representatives of the cubic and quartic traces in eq:f3--eq:f4. -/
def immersionCubicTrace (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (x : Chart4) : ℝ :=
  cubicMoment (immersionFrameSecond F e x)

def immersionQuarticTrace (F : LocalSphereImmersion) (e : LocalImmersionFrame F) (x : Chart4) : ℝ :=
  quarticMoment (immersionFrameSecond F e x)

/-- Covariant differential of the square, evaluated on a matrix variation. -/
def squareVariation (A U : Matrix4) : Matrix4 := U*A+A*U

def cubeVariation (A U : Matrix4) : Matrix4 := U*A^2+A*U*A+A^2*U

theorem immersionFrameSquare_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (l : Fin 4) :
    matrixDerivative (fun y => (immersionFrameSecond F e y)^2) x (e.coefficients x l) =
      immersionFrameConnection F e x l*(immersionFrameSecond F e x)^2+
      (immersionFrameSecond F e x)^2*(immersionFrameConnection F e x l)ᵀ+
      squareVariation (immersionFrameSecond F e x)
        (Matrix.of (fun i j => immersionFrameThird F e x i j l)) := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [matrixDerivative_square _ _ _ hh,immersionFrameSecond_frame_derivative F e x hx l,
    square_connection_derivative _ _ _ (immersionFrameConnection_skew F e x hx l)]
  rfl

theorem immersionFrameCube_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (l : Fin 4) :
    matrixDerivative (fun y => (immersionFrameSecond F e y)^3) x (e.coefficients x l) =
      immersionFrameConnection F e x l*(immersionFrameSecond F e x)^3+
      (immersionFrameSecond F e x)^3*(immersionFrameConnection F e x l)ᵀ+
      cubeVariation (immersionFrameSecond F e x)
        (Matrix.of (fun i j => immersionFrameThird F e x i j l)) := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  rw [matrixDerivative_cube _ _ _ hh,immersionFrameSecond_frame_derivative F e x hx l,
    cube_connection_derivative _ _ _ (immersionFrameConnection_skew F e x hx l)]
  rfl

theorem immersionCubicTrace_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    fderiv ℝ (immersionCubicTrace F e) x (e.coefficients x k) =
      3*cubicWeightedTrace ((immersionFrameSecond F e x)^2) (immersionFrameThird F e x) k := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hs : (Matrix.of (fun i j => immersionFrameThird F e x i j k)).IsSymm := by
    ext i j; exact cubicSymmetric_swap12 (immersionFrameThird_symmetric F e x hx) j i k
  unfold immersionCubicTrace
  rw [fderiv_cubicMoment _ _ _ hh,immersionFrameSecond_frame_derivative F e x hx k,
    trace_power_connection _ _ _ (immersionFrameConnection_skew F e x hx k) 2,
    ← matrixInner_eq_trace_mul _ _ hs]
  rfl

theorem immersionQuarticTrace_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k : Fin 4) :
    fderiv ℝ (immersionQuarticTrace F e) x (e.coefficients x k) =
      4*cubicWeightedTrace ((immersionFrameSecond F e x)^3) (immersionFrameThird F e x) k := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hs : (Matrix.of (fun i j => immersionFrameThird F e x i j k)).IsSymm := by
    ext i j; exact cubicSymmetric_swap12 (immersionFrameThird_symmetric F e x hx) j i k
  unfold immersionQuarticTrace
  rw [fderiv_quarticMoment _ _ _ hh,immersionFrameSecond_frame_derivative F e x hx k,
    trace_power_connection _ _ _ (immersionFrameConnection_skew F e x hx k) 3,
    ← matrixInner_eq_trace_mul _ _ hs]
  rfl

/-- The three paired tensor slots lose their connection terms. The free
covector slot retains its connection term, as required before taking divergence. -/
theorem immersion_weightedTrace_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (Q : Chart4 → Matrix4) (x : Chart4) (hx : x ∈ F.domain) (k l : Fin 4)
    (hQ : DifferentiableAt ℝ Q x) (hsQ : (Q x).IsSymm) (U : Matrix4)
    (hdQ : matrixDerivative Q x (e.coefficients x l) =
      immersionFrameConnection F e x l*Q x+Q x*(immersionFrameConnection F e x l)ᵀ+U) :
    fderiv ℝ (fun y => cubicWeightedTrace (Q y) (immersionFrameThird F e y) k) x (e.coefficients x l) =
      matrixInner U (Matrix.of (fun i j => immersionFrameThird F e x i j k))+
      weightedTrace (Q x) (immersionFrameFourth F e x) k l+
      ∑ r, immersionFrameConnection F e x l k r*cubicWeightedTrace (Q x) (immersionFrameThird F e x) r := by
  have ht := (((contDiffOn_immersionFrameForms F e).2.1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (fun y => Matrix.of (fun i j => immersionFrameThird F e y i j k)) x := by
    apply differentiableAt_pi.mpr; intro i
    apply differentiableAt_pi.mpr; intro j
    exact differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp ht i) j) k
  have hK : (Matrix.of (fun i j => immersionFrameThird F e x i j k)).IsSymm := by
    ext i j; exact cubicSymmetric_swap12 (immersionFrameThird_symmetric F e x hx) j i k
  change fderiv ℝ (fun y => matrixInner (Q y)
    (Matrix.of (fun i j => immersionFrameThird F e y i j k))) x _ = _
  rw [fderiv_matrixInner _ _ _ _ hQ hs,hdQ,immersionFrameThird_slice_derivative F e x hx k l,
    weighted_connection_product _ _ _ _ _ _ k (immersionFrameConnection_skew F e x hx l) hsQ hK rfl]
  rfl

theorem immersion_squareTrace_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k l : Fin 4) :
    fderiv ℝ (fun y => cubicWeightedTrace ((immersionFrameSecond F e y)^2)
      (immersionFrameThird F e y) k) x (e.coefficients x l) =
      matrixInner (squareVariation (immersionFrameSecond F e x)
        (Matrix.of (fun i j => immersionFrameThird F e x i j l)))
        (Matrix.of (fun i j => immersionFrameThird F e x i j k))+
      weightedTrace ((immersionFrameSecond F e x)^2) (immersionFrameFourth F e x) k l+
      ∑ r, immersionFrameConnection F e x l k r*cubicWeightedTrace
        ((immersionFrameSecond F e x)^2) (immersionFrameThird F e x) r := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  exact immersion_weightedTrace_derivative F e _ x hx k l
    (differentiableAt_matrix_pow _ _ hh 2) ((immersionFrameSecond_symmetric F e x hx).pow 2) _
    (immersionFrameSquare_derivative F e x hx l)

theorem immersion_cubeTrace_derivative (F : LocalSphereImmersion) (e : LocalImmersionFrame F)
    (x : Chart4) (hx : x ∈ F.domain) (k l : Fin 4) :
    fderiv ℝ (fun y => cubicWeightedTrace ((immersionFrameSecond F e y)^3)
      (immersionFrameThird F e y) k) x (e.coefficients x l) =
      matrixInner (cubeVariation (immersionFrameSecond F e x)
        (Matrix.of (fun i j => immersionFrameThird F e x i j l)))
        (Matrix.of (fun i j => immersionFrameThird F e x i j k))+
      weightedTrace ((immersionFrameSecond F e x)^3) (immersionFrameFourth F e x) k l+
      ∑ r, immersionFrameConnection F e x l k r*cubicWeightedTrace
        ((immersionFrameSecond F e x)^3) (immersionFrameThird F e x) r := by
  have hh := (((contDiffOn_immersionFrameForms F e).1 x hx).contDiffAt
    (F.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  exact immersion_weightedTrace_derivative F e _ x hx k l
    (differentiableAt_matrix_pow _ _ hh 3) ((immersionFrameSecond_symmetric F e x hx).pow 3) _
    (immersionFrameCube_derivative F e x hx l)

end
end SecondPinching
