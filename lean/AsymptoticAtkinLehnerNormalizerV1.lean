module

public import AsymptoticAtkinLehnerOldTraceV1
public import AsymptoticFrickeNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public section

namespace AsymptoticAtkinLehner

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticFreshMatrices
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticReconstructionBranch
open scoped MatrixGroups

/-- Integral conjugate by the local determinant-p representative
[[p,B],[-pM,pA]], where pA+MB=1. -/
def localConjugate (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (g : SL(2,ℤ)) (c : ℤ) (hc : g 1 0=(p:ℤ)*(M:ℤ)*c) : SL(2,ℤ) :=
  ⟨!![(p:ℤ)*A*g 0 0+(p:ℤ)*M*A*B*c+(p:ℤ)*M*g 0 1+(M:ℤ)*B*g 1 1,
      -B*g 0 0-(M:ℤ)*B^2*c+(p:ℤ)*g 0 1+B*g 1 1;
      (p:ℤ)*M*(-A*g 0 0+(p:ℤ)*A^2*c-(M:ℤ)*g 0 1+A*g 1 1),
      (M:ℤ)*B*g 0 0-(p:ℤ)*M*A*B*c-(p:ℤ)*M*g 0 1+(p:ℤ)*A*g 1 1],by
    rw [Matrix.det_fin_two]
    dsimp
    have hd := g.property
    rw [Matrix.det_fin_two] at hd
    change g 0 0*g 1 1-g 0 1*g 1 0=1 at hd
    rw [hc] at hd
    calc
      _=((p:ℤ)*A+(M:ℤ)*B)^2*(g 0 0*g 1 1-g 0 1*((p:ℤ)*M*c)) := by ring
      _=1 := by rw [hAB,hd]; norm_num⟩

theorem localConjugate_mem (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (g : SL(2,ℤ)) (c : ℤ) (hc : g 1 0=(p:ℤ)*(M:ℤ)*c) :
    localConjugate M p A B hAB g c hc∈CongruenceSubgroup.Gamma0 (p*M) := by
  rw [gamma0_mem_dvd]
  refine ⟨-A*g 0 0+(p:ℤ)*A^2*c-(M:ℤ)*g 0 1+A*g 1 1,?_⟩
  change (p:ℤ)*M*_=((p*M:ℕ):ℤ)*_
  rw [Nat.cast_mul]

theorem local_conjugate_label (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (g : SL(2,ℤ)) (c : ℤ) (hc : g 1 0=(p:ℤ)*(M:ℤ)*c) :
    localAtkin M p hM hp A B hAB*integralLabel g=
      integralLabel (localConjugate M p A B hAB g c hc)*localAtkin M p hM hp A B hAB := by
  have hn : ((p*M:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos hp hM).ne'
  have hab : (p:ℚ)*(A:ℚ)+(M:ℚ)*(B:ℚ)=1 := by exact_mod_cast hAB
  have hm : (rationalGL (localConjugate M p A B hAB g c hc)).val*
      (branch ((p*M:ℕ):ℚ) 0 0 hn*complementGL M p hM A B hAB).val=
      ((p:ℚ)*(A:ℚ)+(M:ℚ)*(B:ℚ)) •
        ((branch ((p*M:ℕ):ℚ) 0 0 hn*complementGL M p hM A B hAB).val*(rationalGL g).val) := by
    change (localConjugate M p A B hAB g c hc).val.map (fun z : ℤ => (z:ℚ))*
      ((branch ((p*M:ℕ):ℚ) 0 0 hn).val*(complementGL M p hM A B hAB).val)=
      ((p:ℚ)*(A:ℚ)+(M:ℚ)*(B:ℚ)) •
        (((branch ((p*M:ℕ):ℚ) 0 0 hn).val*(complementGL M p hM A B hAB).val)*
          g.val.map (fun z : ℤ => (z:ℚ)))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [branch,complementGL,AsymptoticFreshMatrices.representative,entries,localConjugate,
        GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hc]
    all_goals ring
  rw [hab,one_smul] at hm
  have he : (branch ((p*M:ℕ):ℚ) 0 0 hn*complementGL M p hM A B hAB)*rationalGL g=
      rationalGL (localConjugate M p A B hAB g c hc)*
        (branch ((p*M:ℕ):ℚ) 0 0 hn*complementGL M p hM A B hAB) := Units.ext hm.symm
  apply Subtype.ext
  apply Subtype.ext
  change (rationalMap (branch ((p*M:ℕ):ℚ) 0 0 hn)*rationalMap (complementGL M p hM A B hAB))*
    rationalMap (rationalGL g)=rationalMap (rationalGL (localConjugate M p A B hAB g c hc))*
      (rationalMap (branch ((p*M:ℕ):ℚ) 0 0 hn)*rationalMap (complementGL M p hM A B hAB))
  simp only [← map_mul]
  rw [he]

theorem local_conj_mem (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    {g : AsymptoticRationalGroup.Group} (hg : g∈gamma (p*M)) :
    localAtkin M p hM hp A B hAB*g*(localAtkin M p hM hp A B hAB)⁻¹∈gamma (p*M) := by
  obtain ⟨a,ha,rfl⟩ := hg
  obtain ⟨c,hc⟩ := (gamma0_mem_dvd (p*M) a).mp ha
  have hc' : a 1 0=(p:ℤ)*(M:ℤ)*c := by simpa only [Nat.cast_mul] using hc
  rw [local_conjugate_label M p hM hp A B hAB a c hc',mul_inv_cancel_right]
  exact ⟨localConjugate M p A B hAB a c hc',localConjugate_mem M p A B hAB a c hc',rfl⟩

#print axioms localConjugate_mem
#print axioms local_conjugate_label
#print axioms local_conj_mem

end AsymptoticAtkinLehner
