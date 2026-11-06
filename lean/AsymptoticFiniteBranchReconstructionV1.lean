module

public import AsymptoticFiniteBranchCertificateV1
public import AsymptoticFiniteBranchPolynomialV1
public import AsymptoticFiniteBranchCornersV1
public import AsymptoticFiniteFoldReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCertificateOperators

noncomputable def neumannExpression (K B : Expression) (n : ℕ) : Expression :=
  composeExpression (geometricExpression K n) B

theorem holomorphicSum_neumann (K B : Expression) (n m : ℕ) :
    holomorphicSum (neumannExpression K B n) m=
      AsymptoticReconstruction.finiteLow (holomorphicSum K m) (holomorphicSum B m) n := by
  rw [neumannExpression,holomorphicSum_compose,holomorphicSum_geometric]
  rfl

theorem regularSum_neumann (K B : Expression) (n : ℕ) (z : ℍ) :
    regularSum (neumannExpression K B n) z=
      AsymptoticReconstruction.finiteLow (regularSum K z) (regularSum B z) n :=
  (regularSum_compose (geometricExpression K n) B z).trans
    (congrArg (fun T => T.comp (regularSum B z)) (regularSum_geometric K n z))

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def fullExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) : Expression :=
  composeExpression ([identity]++neumannExpression (lowExpression A hN P χ (P.s+3) I)
    (terminalExpression A hN P χ (by omega : 2≤P.s+3) I) n)
    [corner (highStrip P.ε) (highStrip_measurable P.ε)]

theorem holomorphicSum_fullExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    holomorphicSum (fullExpression A hN P χ n I) m=
      (1+AsymptoticReconstruction.finiteLow (AsymptoticCertificateOperators.finiteLow A hN P χ (P.s+3) I m)
        (AsymptoticCertificateOperators.finiteTerminal A hN P χ (by omega : 2≤P.s+3) I m) n).comp
          (highProjection A P) := by
  rw [fullExpression,holomorphicSum_compose,holomorphicSum_append,holomorphicSum_neumann,
    holomorphicSum_lowExpression,holomorphicSum_terminalExpression]
  simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    holomorphic_identity,holomorphic_corner]
  rfl

theorem regularSum_fullExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    regularSum (fullExpression A hN P χ n I) z=
      AsymptoticRegularReconstruction.finiteFoldFull A hN P χ n I z := by
  rw [fullExpression,regularSum_compose,regularSum_append,regularSum_neumann,
    regularSum_lowExpression,regularSum_terminalExpression]
  simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    regular_identity,regular_corner]
  rfl

/-- The common ambient finite branch expression restricts to the
actual holomorphic terminal reconstruction. -/
theorem holomorphicSum_fullExpression_on_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    (holomorphicSum (fullExpression A hN P χ n I) m).comp
      (AsymptoticGeometricReconstruction.TerminalSpace A P).subtypeL=
        AsymptoticGeometricReconstruction.finiteFoldExtension A hN P χ n I m := by
  rw [holomorphicSum_fullExpression]
  apply ContinuousLinearMap.ext
  intro g
  have hg : highProjection A P (g:AsymptoticHyperbolicSlash.Space)=(g:AsymptoticHyperbolicSlash.Space) :=
    (AsymptoticRegionL2.mem_space _ _ _ _).mp g.property
  change (1+AsymptoticReconstruction.finiteLow
    (AsymptoticCertificateOperators.finiteLow A hN P χ (P.s+3) I m)
    (AsymptoticCertificateOperators.finiteTerminal A hN P χ (by omega : 2≤P.s+3) I m) n)
      (highProjection A P (g:AsymptoticHyperbolicSlash.Space))=_
  rw [hg]
  rfl

#print axioms holomorphicSum_neumann
#print axioms regularSum_neumann
#print axioms holomorphicSum_fullExpression
#print axioms regularSum_fullExpression
#print axioms holomorphicSum_fullExpression_on_terminal

end AsymptoticFiniteBranch
