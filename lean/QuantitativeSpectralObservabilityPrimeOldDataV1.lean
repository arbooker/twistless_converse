module

public import QuantitativeSpectralObservabilityOldFamilyControlV1
public import QuantitativeNewGapIndexedV1

set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticRegularBranchFamily QuantitativeSpectralFiniteReduction
open QuantitativeSpectralExceptionalReducedRows QuantitativeNewGap
open scoped MatrixGroups lp

abbrev primeOldGroup (N : ℕ) (hN : 0<N) (i : PrimeOldIndex N) :=
  QuantitativeArithmeticCrossPrime.oldGroup N hN i.1.val i.2

abbrev PrimeOldClasses (N : ℕ) (hN : 0<N) (i : PrimeOldIndex N) :=
  primeOldGroup N hN i ⧸ (gamma N).subgroupOf (primeOldGroup N hN i)

instance primeOldClasses_fintype (N : ℕ) (hN : 0<N) (i : PrimeOldIndex N) :
    Fintype (PrimeOldClasses N hN i) := Fintype.ofFinite _

def primeOldRepresentatives (N : ℕ) (hN : 0<N) (i : PrimeOldIndex N) :
    PrimeOldClasses N hN i → primeOldGroup N hN i := Quotient.out

/-- Actual finite coset representatives supply every residual witness for
both old directions at every prime. No factorization data is assumed. -/
def primeOldData (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (i : PrimeOldIndex N) :
    OldResidualData N hN S (primeOldGroup N hN i) (primeOld_le N hN i)
      (primeOldRepresentatives N hN i) :=
  oldResidualData N hN S hS _ _ _ (Equiv.refl _) (fun q => (Quotient.out_eq q).symm)

def primeOldCost (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (Y ε : ℝ) (t : ℕ) : ℝ :=
  ∑ i : PrimeOldIndex N,
    ((primeOldData N hN S hS i).L*
      (1+ε*(primeOldData N hN S hS i).K*(Y/(primeOldData N hN S hS i).C+3)^2)^(2*t))^2

theorem primeOldCost_nonneg (N : ℕ) (hN : 0<N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (Y ε : ℝ) (t : ℕ) : 0≤primeOldCost N hN S hS Y ε t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

#print axioms primeOldData

end QuantitativeSpectralObservability
