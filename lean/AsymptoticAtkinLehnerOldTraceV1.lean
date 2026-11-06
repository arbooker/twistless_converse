module

public import AsymptoticAtkinLehnerRamanujanV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticAtkinLehner

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticFreshMatrices AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticReconstructionBranch AsymptoticOrbitDecode AsymptoticRamifiedTwistedLaw
open scoped MatrixGroups

noncomputable def localAtkin (M p : ℕ) (hM : 0<M) (hp : 0<p) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : AsymptoticRationalGroup.Group :=
  frickeLabel (p*M) (Nat.mul_pos hp hM)*complement M p hM A B hAB

/-- The p nonidentity representatives in the classical old trace
I+W_p U_p, written as integral determinant-one matrices. -/
def traceSL (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (a : ℤ) : SL(2,ℤ) :=
  ⟨!![1,a+B;-(M:ℤ),(p:ℤ)*A-(M:ℤ)*a],by
    rw [Matrix.det_fin_two]
    change 1*((p:ℤ)*A-(M:ℤ)*a)-(a+B)*(-(M:ℤ))=1
    linear_combination hAB⟩

theorem traceSL_mem (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (a : ℤ) :
    traceSL M p A B hAB a∈CongruenceSubgroup.Gamma0 M := by
  rw [gamma0_mem_dvd]
  exact ⟨-1,by change -(M:ℤ)=(M:ℤ)*(-1); ring⟩

theorem localAtkin_mul_ramified (M p : ℕ) (hM : 0<M) (hp : 0<p) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (a : Fin p) :
    localAtkin M p hM hp A B hAB*ramifiedLabel p hp a=integralLabel (traceSL M p A B hAB a.val) := by
  have hn : ((p*M:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos hp hM).ne'
  have he : branch ((p*M:ℕ):ℚ) 0 0 hn*complementGL M p hM A B hAB*
      AsymptoticRamifiedBranch.branch (p:ℚ) (a.val:ℚ) (by exact_mod_cast hp.ne')=
      rationalGL (traceSL M p A B hAB a.val)*
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-((p*M:ℕ):ℚ)) (neg_ne_zero.mpr hn)) := by
    apply Units.ext
    change (branch ((p*M:ℕ):ℚ) 0 0 hn).val*(complementGL M p hM A B hAB).val*
      (AsymptoticRamifiedBranch.branch (p:ℚ) (a.val:ℚ) _).val=
      (traceSL M p A B hAB a.val).val.map (fun z : ℤ => (z:ℚ))*
        (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-((p*M:ℕ):ℚ)) (neg_ne_zero.mpr hn))).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [branch,complementGL,AsymptoticFreshMatrices.representative,entries,
        AsymptoticRamifiedBranch.branch,traceSL,GeneralLinearGroup.scalar,
        Matrix.scalar,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  apply Subtype.ext
  apply Subtype.ext
  change (rationalMap (branch ((p*M:ℕ):ℚ) 0 0 hn)*rationalMap (complementGL M p hM A B hAB))*
    rationalMap (AsymptoticRamifiedBranch.branch (p:ℚ) (a.val:ℚ) (by exact_mod_cast hp.ne'))=
      rationalMap (rationalGL (traceSL M p A B hAB a.val))
  rw [← map_mul,← map_mul,he,map_mul,rationalMap_scalar,mul_one]

variable (M p : ℕ) [Fact p.Prime] (hM : 0<M) (hpM : ¬p∣M)
variable (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
variable (F : AsymptoticRationalGroup.Group → ℂ)
variable (hF : ∀ a : gamma (p*M),∀ g,F (a.val*g)=F g)
variable (w δ : ℂ) (hδ : δ^2=1)
variable (hW : ∀ g,w*F (frickeLabel (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM)*g)=F g)
variable (hU : ∀ g,∑ a : Fin p,F (ramifiedLabel p (Fact.out : p.Prime).pos a*g)=δ*F g)

include hpM hF hδ hW hU

theorem local_eigen (g : AsymptoticRationalGroup.Group) :
    F (localAtkin M p hM (Fact.out : p.Prime).pos A B hAB*g)= -δ*F g := by
  have hww := hW g
  rw [reverse_fricke_equation (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) F w hW] at hww
  rw [localAtkin,mul_assoc,
    reverse_fricke_equation (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) F w hW,
    complement_eigen M p hM hpM A B hAB F hF w δ hδ hW hU]
  linear_combination -δ*hww

/-- Vanishing of the literal old trace, deduced from the local sign
and ramified recurrence rather than supplied as a newness hypothesis. -/
theorem old_trace_zero (g : AsymptoticRationalGroup.Group) :
    F g+∑ a : Fin p,F (integralLabel (traceSL M p A B hAB a.val)*g)=0 := by
  simp_rw [← localAtkin_mul_ramified M p hM (Fact.out : p.Prime).pos A B hAB,
    mul_assoc,local_eigen M p hM hpM A B hAB F hF w δ hδ hW hU]
  rw [← Finset.mul_sum,hU]
  linear_combination -F g*hδ

#print axioms traceSL_mem
#print axioms localAtkin_mul_ramified
#print axioms local_eigen
#print axioms old_trace_zero

end AsymptoticAtkinLehner
