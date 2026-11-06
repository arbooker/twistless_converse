module
public import QuantitativeArithmeticPrimitiveResiduePairV4

public import SmallLevelThirtyGeneratorDataV1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
@[expose] public section

namespace SmallLevelThirty
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

theorem edgeSRow_checked : ∀ c d : ZMod 30, (∃ a b : ZMod 30, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 30,
    Nat.gcd (Nat.gcd c.val d.val) 30 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeTRow_checked : ∀ c d : ZMod 30, (∃ a b : ZMod 30, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 30,
    Nat.gcd (Nat.gcd c.val d.val) 30 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 30)) :
    rep g*S*(rep (g*reduction 30 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 30 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 30 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 30)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 30)) :
    rep g*T*(rep (g*reduction 30 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 30 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 30 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 30)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 30)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 30, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 26, generator i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 30) : γ∈K := by
  apply transversal_mem (reduction 30) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hK hZ _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hK hZ _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edgeSRow_checked
#print axioms edgeTRow_checked
#print axioms gamma0_mem

end SmallLevelThirty
