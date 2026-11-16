module

public import QuantitativeMaassCountingLocalExpressionV1
public import QuantitativeMaassAmbientSectorExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticFiniteBranch AsymptoticSectorSigns AsymptoticCongruenceStrip QuantitativeNewGap
namespace QuantitativeMaass.Counting

attribute [local instance] Classical.propDecidable

theorem Realizes.list_prod {N : ℕ} {ι : Type*} (E : ι→Expression)
    (A : ι→Space N→L[ℂ]Space N) (h : ∀ i,Realizes (gamma N) (E i) (A i)) (L : List ι) :
    Realizes (gamma N) (orderedProductExpression E L) (L.map A).prod := by
  induction L with
  | nil => exact Realizes.one (gamma N)
  | cons i L ih => exact (h i).mul ih

def localNewFilter (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ) (p : ↥N.primeFactors) :
    Space N→L[ℂ]Space N :=
  if p.val∣N/p.val then
    repeatedTwoNewFilter hN (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property))
  else simpleNewFilter hN (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property)) p.val m

theorem ambientLocalNewExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ)
    (p : ↥N.primeFactors) :
    Realizes (gamma N) (ambientLocalNewExpression N hN m p) (localNewFilter N hN m p) := by
  by_cases hp : p.val∣N/p.val
  · simp only [ambientLocalNewExpression,localNewFilter,ite_eq_left hp]
    exact ambientRepeatedTwoNewExpression_realizes hN _
  · simp only [ambientLocalNewExpression,localNewFilter,ite_eq_right hp]
    exact ambientSimpleNewExpression_realizes hN _ p.val m

def totalNewFilter (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ) : Space N→L[ℂ]Space N :=
  ((Finset.univ : Finset ↥N.primeFactors).toList.map (localNewFilter N hN m)).prod

theorem ambientTotalNewExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N) (m : ℕ) :
    Realizes (gamma N) (ambientTotalNewExpression N hN m) (totalNewFilter N hN m) :=
  Realizes.list_prod _ _ (ambientLocalNewExpression_realizes N hN m) _

def signFactor (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    Space N→L[ℂ]Space N :=
  (1/2:ℂ) • (1+(sectorNormalizerSign e i:ℂ) •
    normalizerOperator N (sectorNormalizerGroup N hN i))

theorem ambientSignFactorExpression_realizes (N : ℕ) (hN : 0<N) (e : Sector N)
    (i : SectorSignIndex N) :
    Realizes (gamma N) (ambientSignFactorExpression N hN e i) (signFactor N hN e i) :=
  ((Realizes.one (gamma N)).add
    ((normalizerOperator_realizes N (sectorNormalizerGroup N hN i)).smul
      (sectorNormalizerSign e i:ℂ))).smul (1/2:ℂ)

def signProduct (N : ℕ) (hN : 0<N) (e : Sector N) : Space N→L[ℂ]Space N :=
  ((Finset.univ : Finset (SectorSignIndex N)).toList.map (signFactor N hN e)).prod

theorem ambientSignProductExpression_realizes (N : ℕ) (hN : 0<N) (e : Sector N) :
    Realizes (gamma N) (ambientSignProductExpression N hN e) (signProduct N hN e) :=
  Realizes.list_prod _ _ (ambientSignFactorExpression_realizes N hN e) _

def sectorNewFilter (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) (m : ℕ) :
    Space N→L[ℂ]Space N := (totalNewFilter N hN m).comp (signProduct N hN e)

theorem ambientSectorNewExpression_realizes (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) :
    Realizes (gamma N) (ambientSectorNewExpression N hN e m) (sectorNewFilter N hN e m) :=
  (ambientTotalNewExpression_realizes N hN m).mul (ambientSignProductExpression_realizes N hN e)

/-- The regular coefficient is an actual counting-space diagonal entry,
independent of the point in the upper half-plane. -/
theorem ambientSectorNewExpression_root (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) (x : UpperHalfPlane) :
    (sectorNewFilter N hN e m (AsymptoticRegularTrace.delta
      (AsymptoticNestedQuotients.classOf (gamma N) 1)))
      (AsymptoticNestedQuotients.classOf (gamma N) 1)=
    ((ambientSectorNewExpression N hN e m).map
      (fun b => if b.label∈gamma N then b.coefficient x else 0)).sum :=
  (ambientSectorNewExpression_realizes N hN e m).root_coefficient x

#print axioms ambientLocalNewExpression_realizes
#print axioms ambientTotalNewExpression_realizes
#print axioms ambientSignFactorExpression_realizes
#print axioms ambientSectorNewExpression_realizes
#print axioms ambientSectorNewExpression_root
end QuantitativeMaass.Counting
