module

public import QuantitativeMaassAmbientLocalExpressionV1
public import QuantitativeMaassAmbientSectorBoundV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticFiniteBranch QuantitativeNinaMaass AsymptoticSectorSigns QuantitativeNewGap
namespace QuantitativeMaass

/-- Ordered products retain all coefficients and all rational labels. -/
def orderedProductExpression {ι : Type*} (E : ι→Expression) : List ι→Expression
  | [] => [AsymptoticFiniteBranch.identity]
  | i::L => composeExpression (E i) (orderedProductExpression E L)

theorem QuotientRealizes.list_prod {N : ℕ} {ι : Type*} (E : ι→Expression)
    (A : ι→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (h : ∀ i,QuotientRealizes N (E i) (A i)) (L : List ι) :
    QuotientRealizes N (orderedProductExpression E L) (L.map A).prod := by
  induction L with
  | nil => exact QuotientRealizes.one N
  | cons i L ih => exact (h i).mul ih

def ambientLocalNewExpression (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ)
    (p : ↥N.primeFactors) : Expression :=
  if p.val∣N/p.val then
    ambientRepeatedTwoNewExpression hN (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property))
  else ambientSimpleNewExpression hN (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property)) p.val m

theorem ambientLocalNewExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ)
    (p : ↥N.primeFactors) :
    QuotientRealizes N (ambientLocalNewExpression N hN m p) (ambientAdmissibleLocalNewFilter N hN m p) := by
  classical
  by_cases hp : p.val∣N/p.val
  · simp only [ambientLocalNewExpression,ambientAdmissibleLocalNewFilter,ite_eq_left hp]
    exact ambientRepeatedTwoNewExpression_realizes hN _
  · simp only [ambientLocalNewExpression,ambientAdmissibleLocalNewFilter,ite_eq_right hp]
    exact ambientSimpleNewExpression_realizes hN _ p.val m

def ambientTotalNewExpression (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ) : Expression :=
  orderedProductExpression (ambientLocalNewExpression N hN m)
    (Finset.univ : Finset ↥N.primeFactors).toList

theorem ambientTotalNewExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ) :
    QuotientRealizes N (ambientTotalNewExpression N hN m) (ambientAdmissibleTotalNewFilter N hN m) :=
  QuotientRealizes.list_prod _ _ (ambientLocalNewExpression_realizes N hN m) _

def ambientSignFactorExpression (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) : Expression :=
  scaleExpression (1/2:ℂ) ([AsymptoticFiniteBranch.identity]++
    scaleExpression (sectorNormalizerSign e i:ℂ)
      (quotientPullbackExpression (sectorNormalizerGroup N hN i).val))

theorem ambientSignFactorExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N)
    (i : SectorSignIndex N) :
    QuotientRealizes N (ambientSignFactorExpression N hN e i) (ambientSectorSignFactor N hN e i) :=
  ((QuotientRealizes.one N).add
    ((quotientSectorNormalizer_realizes N hN i).smul (sectorNormalizerSign e i:ℂ))).smul (1/2:ℂ)

def ambientSignProductExpression (N : ℕ) (hN : 0<N) (e : Sector N) : Expression :=
  orderedProductExpression (ambientSignFactorExpression N hN e)
    (Finset.univ : Finset (SectorSignIndex N)).toList

theorem ambientSignProductExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) :
    QuotientRealizes N (ambientSignProductExpression N hN e) (ambientSectorSignProduct N hN e) :=
  QuotientRealizes.list_prod _ _ (ambientSignFactorExpression_realizes N hN e) _

/-- A common finite rational expression for the entire actual local-new
and sign filter, retaining its order of composition. -/
def ambientSectorNewExpression (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) (m : ℕ) : Expression :=
  composeExpression (ambientTotalNewExpression N hN m) (ambientSignProductExpression N hN e)

theorem ambientSectorNewExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) (m : ℕ) :
    QuotientRealizes N (ambientSectorNewExpression N hN e m) (ambientSectorNewFilter N hN e m) :=
  (ambientTotalNewExpression_realizes N hN m).mul (ambientSignProductExpression_realizes N hN e)

#print axioms QuotientRealizes.list_prod
#print axioms ambientLocalNewExpression_realizes
#print axioms ambientTotalNewExpression_realizes
#print axioms ambientSignFactorExpression_realizes
#print axioms ambientSignProductExpression_realizes
#print axioms ambientSectorNewExpression_realizes
end QuantitativeMaass
