import SecondPinching.PengTerngExpressions

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32000
set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix Matrix.Norms.Elementwise
namespace SecondPinching
noncomputable section

/-- The symmetric component formula after the Gauss and differentiated Ricci contractions. -/
def pengTerngReduced (s : ℝ) (h q : Matrix4) (T : Cubic4) (w : Vector4) : Cubic4 := fun i j k =>
  (11-s)*T i j k-
  (∑ r, (q i r*T r j k+q j r*T i r k+q k r*T i j r))+
  2*(∑ r, ∑ a, (h i r*h j a*T r a k+h i r*h k a*T r j a+h j r*h k a*T i r a))-
  2*(h i j*w k+h i k*w j+h j k*w i)

/-- Expand the matrix products before substituting a cubic slice. -/
theorem ricciVariation_expanded (h U : Matrix4) (i j k l : Fin 4) :
    ricciVariation h U i j k l =
  (1 : Matrix4) i l*U j k-(1 : Matrix4) i k*U j l+U i k*(1 : Matrix4) j l-U i l*(1 : Matrix4) j k+
  U i l*(h*h) j k+h i l*((∑ r, U j r*h r k)+(∑ r, h j r*U r k))-U i k*(h*h) j l-h i k*((∑ r, U j r*h r l)+(∑ r, h j r*U r l))+
  ((∑ r, U i r*h r k)+(∑ r, h i r*U r k))*h j l+(h*h) i k*U j l-((∑ r, U i r*h r l)+(∑ r, h i r*U r l))*h j k-(h*h) i l*U j k := rfl

theorem ricciVariationDivergence_expanded (h : Matrix4) (T : Cubic4) :
    ricciVariationDivergence h T = fun i j k => ∑ l, (
      (1 : Matrix4) i l*T j k l-(1 : Matrix4) i k*T j l l+T i k l*(1 : Matrix4) j l-T i l l*(1 : Matrix4) j k+
      T i l l*(h*h) j k+h i l*((∑ r, T j r l*h r k)+(∑ r, h j r*T r k l))-T i k l*(h*h) j l-h i k*((∑ r, T j r l*h r l)+(∑ r, h j r*T r l l))+
      ((∑ r, T i r l*h r k)+(∑ r, h i r*T r k l))*h j l+(h*h) i k*T j l l-((∑ r, T i r l*h r l)+(∑ r, h i r*T r l l))*h j k-(h*h) i l*T j k l) := by
  funext i j k
  apply Finset.sum_congr rfl
  intro l _
  exact ricciVariation_expanded h (fun a b => T a b l) i j k l

theorem pengTerngCubic_reduced (h : Matrix4) (T : Cubic4)
    (hh : h.IsSymm) (hT : CubicSymmetric T)
    (htr : Matrix.trace h = 0) (hTtr : cubicTrace T = 0) :
    pengTerngCubic h T = pengTerngReduced (matrixNormSq h) h (h*h) T (cubicWeightedTrace h T) := by
  have hh10 : h 1 0 = h 0 1 := hh.apply 0 1
  have hh20 : h 2 0 = h 0 2 := hh.apply 0 2
  have hh21 : h 2 1 = h 1 2 := hh.apply 1 2
  have hh30 : h 3 0 = h 0 3 := hh.apply 0 3
  have hh31 : h 3 1 = h 1 3 := hh.apply 1 3
  have hh32 : h 3 2 = h 2 3 := hh.apply 2 3
  have ht010 : T 0 1 0 = T 0 0 1 := (cubicSymmetric_swap23 hT 0 1 0)
  have ht020 : T 0 2 0 = T 0 0 2 := (cubicSymmetric_swap23 hT 0 2 0)
  have ht021 : T 0 2 1 = T 0 1 2 := (cubicSymmetric_swap23 hT 0 2 1)
  have ht030 : T 0 3 0 = T 0 0 3 := (cubicSymmetric_swap23 hT 0 3 0)
  have ht031 : T 0 3 1 = T 0 1 3 := (cubicSymmetric_swap23 hT 0 3 1)
  have ht032 : T 0 3 2 = T 0 2 3 := (cubicSymmetric_swap23 hT 0 3 2)
  have ht100 : T 1 0 0 = T 0 0 1 := ((cubicSymmetric_swap12 hT 1 0 0).trans (cubicSymmetric_swap23 hT 0 1 0))
  have ht101 : T 1 0 1 = T 0 1 1 := (cubicSymmetric_swap12 hT 1 0 1)
  have ht102 : T 1 0 2 = T 0 1 2 := (cubicSymmetric_swap12 hT 1 0 2)
  have ht103 : T 1 0 3 = T 0 1 3 := (cubicSymmetric_swap12 hT 1 0 3)
  have ht110 : T 1 1 0 = T 0 1 1 := ((cubicSymmetric_swap23 hT 1 1 0).trans (cubicSymmetric_swap12 hT 1 0 1))
  have ht120 : T 1 2 0 = T 0 1 2 := ((cubicSymmetric_swap23 hT 1 2 0).trans (cubicSymmetric_swap12 hT 1 0 2))
  have ht121 : T 1 2 1 = T 1 1 2 := (cubicSymmetric_swap23 hT 1 2 1)
  have ht130 : T 1 3 0 = T 0 1 3 := ((cubicSymmetric_swap23 hT 1 3 0).trans (cubicSymmetric_swap12 hT 1 0 3))
  have ht131 : T 1 3 1 = T 1 1 3 := (cubicSymmetric_swap23 hT 1 3 1)
  have ht132 : T 1 3 2 = T 1 2 3 := (cubicSymmetric_swap23 hT 1 3 2)
  have ht200 : T 2 0 0 = T 0 0 2 := ((cubicSymmetric_swap12 hT 2 0 0).trans (cubicSymmetric_swap23 hT 0 2 0))
  have ht201 : T 2 0 1 = T 0 1 2 := ((cubicSymmetric_swap12 hT 2 0 1).trans (cubicSymmetric_swap23 hT 0 2 1))
  have ht202 : T 2 0 2 = T 0 2 2 := (cubicSymmetric_swap12 hT 2 0 2)
  have ht203 : T 2 0 3 = T 0 2 3 := (cubicSymmetric_swap12 hT 2 0 3)
  have ht210 : T 2 1 0 = T 0 1 2 := (((cubicSymmetric_swap12 hT 2 1 0).trans (cubicSymmetric_swap23 hT 1 2 0)).trans (cubicSymmetric_swap12 hT 1 0 2))
  have ht211 : T 2 1 1 = T 1 1 2 := ((cubicSymmetric_swap12 hT 2 1 1).trans (cubicSymmetric_swap23 hT 1 2 1))
  have ht212 : T 2 1 2 = T 1 2 2 := (cubicSymmetric_swap12 hT 2 1 2)
  have ht213 : T 2 1 3 = T 1 2 3 := (cubicSymmetric_swap12 hT 2 1 3)
  have ht220 : T 2 2 0 = T 0 2 2 := ((cubicSymmetric_swap23 hT 2 2 0).trans (cubicSymmetric_swap12 hT 2 0 2))
  have ht221 : T 2 2 1 = T 1 2 2 := ((cubicSymmetric_swap23 hT 2 2 1).trans (cubicSymmetric_swap12 hT 2 1 2))
  have ht230 : T 2 3 0 = T 0 2 3 := ((cubicSymmetric_swap23 hT 2 3 0).trans (cubicSymmetric_swap12 hT 2 0 3))
  have ht231 : T 2 3 1 = T 1 2 3 := ((cubicSymmetric_swap23 hT 2 3 1).trans (cubicSymmetric_swap12 hT 2 1 3))
  have ht232 : T 2 3 2 = T 2 2 3 := (cubicSymmetric_swap23 hT 2 3 2)
  have ht300 : T 3 0 0 = T 0 0 3 := ((cubicSymmetric_swap12 hT 3 0 0).trans (cubicSymmetric_swap23 hT 0 3 0))
  have ht301 : T 3 0 1 = T 0 1 3 := ((cubicSymmetric_swap12 hT 3 0 1).trans (cubicSymmetric_swap23 hT 0 3 1))
  have ht302 : T 3 0 2 = T 0 2 3 := ((cubicSymmetric_swap12 hT 3 0 2).trans (cubicSymmetric_swap23 hT 0 3 2))
  have ht303 : T 3 0 3 = T 0 3 3 := (cubicSymmetric_swap12 hT 3 0 3)
  have ht310 : T 3 1 0 = T 0 1 3 := (((cubicSymmetric_swap12 hT 3 1 0).trans (cubicSymmetric_swap23 hT 1 3 0)).trans (cubicSymmetric_swap12 hT 1 0 3))
  have ht311 : T 3 1 1 = T 1 1 3 := ((cubicSymmetric_swap12 hT 3 1 1).trans (cubicSymmetric_swap23 hT 1 3 1))
  have ht312 : T 3 1 2 = T 1 2 3 := ((cubicSymmetric_swap12 hT 3 1 2).trans (cubicSymmetric_swap23 hT 1 3 2))
  have ht313 : T 3 1 3 = T 1 3 3 := (cubicSymmetric_swap12 hT 3 1 3)
  have ht320 : T 3 2 0 = T 0 2 3 := (((cubicSymmetric_swap12 hT 3 2 0).trans (cubicSymmetric_swap23 hT 2 3 0)).trans (cubicSymmetric_swap12 hT 2 0 3))
  have ht321 : T 3 2 1 = T 1 2 3 := (((cubicSymmetric_swap12 hT 3 2 1).trans (cubicSymmetric_swap23 hT 2 3 1)).trans (cubicSymmetric_swap12 hT 2 1 3))
  have ht322 : T 3 2 2 = T 2 2 3 := ((cubicSymmetric_swap12 hT 3 2 2).trans (cubicSymmetric_swap23 hT 2 3 2))
  have ht323 : T 3 2 3 = T 2 3 3 := (cubicSymmetric_swap12 hT 3 2 3)
  have ht330 : T 3 3 0 = T 0 3 3 := ((cubicSymmetric_swap23 hT 3 3 0).trans (cubicSymmetric_swap12 hT 3 0 3))
  have ht331 : T 3 3 1 = T 1 3 3 := ((cubicSymmetric_swap23 hT 3 3 1).trans (cubicSymmetric_swap12 hT 3 1 3))
  have ht332 : T 3 3 2 = T 2 3 3 := ((cubicSymmetric_swap23 hT 3 3 2).trans (cubicSymmetric_swap12 hT 3 2 3))
  have h33 : h 3 3 = -h 0 0-h 1 1-h 2 2 := by
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_succ] at htr
    linarith
  have ht0 := congrFun hTtr 0
  have ht1 := congrFun hTtr 1
  have ht2 := congrFun hTtr 2
  have ht3 := congrFun hTtr 3
  simp [cubicTrace,Fin.sum_univ_succ,
    ht110,ht220,ht330,ht221,ht331,ht332] at ht0 ht1 ht2 ht3
  have h033 : T 0 3 3 = -T 0 0 0-T 0 1 1-T 0 2 2 := by linarith
  have h133 : T 1 3 3 = -T 0 0 1-T 1 1 1-T 1 2 2 := by linarith
  have h233 : T 2 3 3 = -T 0 0 2-T 1 1 2-T 2 2 2 := by linarith
  have h333 : T 3 3 3 = -T 0 0 3-T 1 1 3-T 2 2 3 := by linarith
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [pengTerngCubic,pengTerngReduced,ricciVariationDivergence_expanded,cubicCurvatureTrace,
      cubicConnectionAction,gaussCurvature,cubicWeightedTrace,Matrix.mul_apply,Matrix.add_apply,
      Matrix.one_apply,Fin.sum_univ_succ,hh10,hh20,hh21,hh30,hh31,hh32,ht010,ht020,ht021,ht030,ht031,ht032,ht100,ht101,ht102,ht103,ht110,ht120,ht121,ht130,ht131,ht132,ht200,ht201,ht202,ht203,ht210,ht211,ht212,ht213,ht220,ht221,ht230,ht231,ht232,ht300,ht301,ht302,ht303,ht310,ht311,ht312,ht313,ht320,ht321,ht322,ht323,ht330,ht331,ht332,h33,h033,h133,h233,h333] <;> ring

end
end SecondPinching
