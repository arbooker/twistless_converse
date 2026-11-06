module

public import QuantitativeEulerEndpointGeneratorCheckV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode AsymptoticCongruenceLabels
open AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- True projective right transport of the periodic matrix action. The
right label need NOT have a determinant-one integral representative. -/
def matrixProjectiveRightAction (g : G) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : MatrixAlgebra →+ (Space →L[ℂ] Space) where
  toFun A := (branchTransport (symbolBranch g) hs hε t x).comp
    (matrixCompactAction (branchImage_compact (symbolBranch g) hs) hε t x A)
  map_zero' := by rw [map_zero,ContinuousLinearMap.comp_zero]
  map_add' A B := by rw [map_add,ContinuousLinearMap.comp_add]

theorem matrixProjectiveRight_periodic (g : G) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (j : ℤ) (M : IntegerMatrix2) :
    matrixProjectiveRightAction g hs hε t x (matrixSymbol (upperUnipotent j)*matrixSymbol M)=
      matrixProjectiveRightAction g hs hε t x (matrixSymbol M) :=
  congrArg (fun T : Space →L[ℂ] Space => (branchTransport (symbolBranch g) hs hε t x).comp T)
    (matrixCompactAction_periodic (branchImage_compact (symbolBranch g) hs) hε t x j M)

/-- On every actual unimodular defect, the transported matrix action is
exactly the original projective group action with the COMPOSED right label. -/
theorem matrixProjectiveRight_integral_defect (g : G) (γ β : SL(2,ℤ))
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    matrixProjectiveRightAction g hs hε t x
      ((matrixSymbol γ.val-1)*matrixSymbol β.val)=
    compactAction hs hε t x
      ((symbol (integralLabel γ)-1)*symbol (integralLabel β*g)) := by
  change (branchTransport (symbolBranch g) hs hε t x).comp
    (matrixCompactAction (branchImage_compact (symbolBranch g) hs) hε t x
      ((matrixSymbol γ.val-1)*matrixSymbol β.val))=_
  rw [matrixCompactAction_integral_defect]
  have h := compactAction_mul_symbol (symbolBranch g) hs hε t x
    ((symbol (integralLabel γ)-1)*symbol (integralLabel β))
  rw [symbolBranch_label] at h
  have he : ((symbol (integralLabel γ)-1)*symbol (integralLabel β))*symbol g=
      (symbol (integralLabel γ)-1)*symbol (integralLabel β*g) := by
    rw [symbol.map_mul,mul_assoc]
  exact h.symm.trans (congrArg (compactAction hs hε t x) he)

theorem matrixProjectiveRight_defect (g : G) (γ : SL(2,ℤ))
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    matrixProjectiveRightAction g hs hε t x (matrixSymbol γ.val-1)=
    compactAction hs hε t x ((symbol (integralLabel γ)-1)*symbol g) := by
  have h := matrixProjectiveRight_integral_defect g γ 1 hs hε t x
  have hm : matrixSymbol (1 : SL(2,ℤ)).val=1 := rfl
  simpa only [hm,mul_one,map_one,one_mul] using h

/-- The original prepared-prime identity remains valid after an arbitrary
projective right label. No scalar law or kernel hypothesis is introduced. -/
theorem projective_prime_defect {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (a : UnitResidue N) (i : Option (Generator N)) {d q : ℤ}
    (cert : PolynomialPrimeCertificate
      (P.Q a) (P.B a i) N (P.c a i) (P.D a i) d q P.K)
    (g : G) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
      upperUnipotent cert.l,cert.canonical_det⟩
    let U := upperSL (-cert.l)
    compactAction hs hε t x ((symbol (integralLabel (family N a i))-1)*symbol g)=
      compactAction hs hε t x
        ((symbol (integralLabel (lowerSL N 1))-1)*symbol (integralLabel (C*U)*g))+
      compactAction hs hε t x ((symbol (integralLabel C)-1)*symbol (integralLabel U*g))-
      compactAction hs hε t x
        ((symbol (integralLabel (lowerSL N cert.r))-1)*symbol (integralLabel (preparationMatrix P a i)*g))-
      compactAction hs hε t x
        ((symbol (integralLabel (lowerSL N (P.n a i)))-1)*symbol (integralLabel (family N a i)*g)) := by
  let C : SL(2,ℤ) := ⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
    upperUnipotent cert.l,cert.canonical_det⟩
  let U := upperSL (-cert.l)
  let F := matrixProjectiveRightAction g hs hε t x
  have h := P.prime_defect a i cert F (matrixProjectiveRight_periodic g hs hε t x)
  have he : F (matrixSymbol (family N a i).val-1)=
      F ((matrixSymbol (lowerSL N 1).val-1)*matrixSymbol (C*U).val)+
      F ((matrixSymbol C.val-1)*matrixSymbol U.val)-
      F ((matrixSymbol (lowerSL N cert.r).val-1)*matrixSymbol (preparationMatrix P a i).val)-
      F ((matrixSymbol (lowerSL N (P.n a i)).val-1)*matrixSymbol (family N a i).val) := by
    have hm : matrixSymbol (C*U).val=matrixSymbol C.val*matrixSymbol U.val := matrixSymbol_mul _ _
    rw [map_sub,hm,←mul_assoc]
    exact h
  have h1 := matrixProjectiveRight_integral_defect g (lowerSL N 1) (C*U) hs hε t x
  have h2 := matrixProjectiveRight_integral_defect g C U hs hε t x
  have h3 := matrixProjectiveRight_integral_defect g (lowerSL N cert.r) (preparationMatrix P a i) hs hε t x
  have h4 := matrixProjectiveRight_integral_defect g (lowerSL N (P.n a i)) (family N a i) hs hε t x
  have htotal := congrArg₂ (fun A B : Space →L[ℂ] Space => A-B)
    (congrArg₂ (fun A B : Space →L[ℂ] Space => A-B)
      (congrArg₂ (fun A B : Space →L[ℂ] Space => A+B) h1 h2) h3) h4
  exact (matrixProjectiveRight_defect g (family N a i) hs hε t x).symm.trans (he.trans htotal)

#print axioms matrixProjectiveRight_periodic
#print axioms matrixProjectiveRight_integral_defect
#print axioms projective_prime_defect
end QuantitativeEulerEndpointPrepared
