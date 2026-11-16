module

public import QuantitativeMaassCuspHeckeIntertwiningV1
public import QuantitativeMaassCuspLogComplexV1
public import QuantitativeMaassLVActualFilterV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass
open Wave

/-- The actual Hecke-minus-wave difference has zero local constant term
at every cusp. The Hecke and wave intertwining laws are proved, not assumed. -/
theorem lvDifference_cuspLogConstant_zero (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (s : SL(2,ℤ)) (A B : ℝ)
    (f : AutomorphicSpace N) :
    cuspLogConstant N hN s A B (lvDifference N p hN hpN a b hab f)=0 := by
  change cuspLogConstant N hN s A B
    (HeckeL2.operator N p hN hpN a b hab f-(2:ℂ) • shiftedQuotientWave N (Real.log p) f)=0
  rw [two_smul,map_sub,map_add,cuspLogConstant_hecke N p hN hpN hNp hpres a b hab s A B f,
    cuspLogConstant_wave_eq_free,cuspLogFreeWave]
  module

/-- Every vector in the actual LV polynomial range lies in the geometric
all-cusp kernel, including d=0. This is an unconditional range result under
the stated arithmetic choice of p; no spectral decomposition is presumed. -/
theorem actualLVFilter_cuspLogConstant_zero (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ)
    (s : SL(2,ℤ)) (A B : ℝ) (f : AutomorphicSpace N) :
    cuspLogConstant N hN s A B (actualLVFilter N p hN hpN a b hab d f)=0 := by
  obtain ⟨g,hg⟩ := actualLVFilter_mem_range N p hN hpN a b hab d f
  rw [← hg]
  exact lvDifference_cuspLogConstant_zero N p hN hpN hNp hpres a b hab s A B g

theorem actualLVFilter_mem_localCuspidalSpace (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) (f : AutomorphicSpace N) :
    actualLVFilter N p hN hpN a b hab d f∈localCuspidalSpace N hN := by
  rw [mem_localCuspidalSpace]
  exact fun s A B => actualLVFilter_cuspLogConstant_zero N p hN hpN hNp hpres a b hab d s A B f

/-- The range of the literal bounded LV operator is contained in a proved
closed complex subspace defined by vanishing actual local constant terms. -/
theorem actualLVFilter_range_le_localCuspidalSpace (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) :
    LinearMap.range (actualLVFilter N p hN hpN a b hab d).toLinearMap≤localCuspidalSpace N hN := by
  rintro f ⟨g,rfl⟩
  exact actualLVFilter_mem_localCuspidalSpace N p hN hpN hNp hpres a b hab d g

#print axioms lvDifference_cuspLogConstant_zero
#print axioms actualLVFilter_cuspLogConstant_zero
#print axioms actualLVFilter_range_le_localCuspidalSpace

end QuantitativeMaass
