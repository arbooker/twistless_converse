module

public import AsymptoticProjectiveCongruenceIndexV1
public import AsymptoticCongruenceTransvectionsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceLabels

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticFreshMatrices AsymptoticFreshCRT AsymptoticReconstructionBranch
open scoped MatrixGroups

/-- Fricke is an involution in the actual positive projective group. -/
theorem frickeLabel_mul_self (N : ℕ) (hN : 0<N) :
    frickeLabel N hN*frickeLabel N hN=1 := by
  have hn : (N:ℚ)≠0 := by exact_mod_cast hN.ne'
  have he : branch (N:ℚ) 0 0 hn*branch (N:ℚ) 0 0 hn=
      GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-(N:ℚ)) (neg_ne_zero.mpr hn)) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [branch,GeneralLinearGroup.mkOfDetNeZero,GeneralLinearGroup.scalar,
        Matrix.scalar,Matrix.mul_apply,Fin.sum_univ_two]
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch (N:ℚ) 0 0 hn)*rationalMap (branch (N:ℚ) 0 0 hn)=1
  rw [← map_mul,he,rationalMap_scalar]

theorem frickeLabel_inv (N : ℕ) (hN : 0<N) :
    (frickeLabel N hN)⁻¹=frickeLabel N hN :=
  inv_eq_of_mul_eq_one_left (frickeLabel_mul_self N hN)

/-- The integral conjugate of a congruence matrix, with its divisible
lower-left entry written as N*c. -/
def frickeConjugate (N : ℕ) (A : SL(2,ℤ)) (c : ℤ) (hc : A 1 0=(N:ℤ)*c) : SL(2,ℤ) :=
  ⟨!![A 1 1,-c;-(N:ℤ)*A 0 1,A 0 0],by
    rw [Matrix.det_fin_two]
    change A 1 1*A 0 0-(-c)*(-(N:ℤ)*A 0 1)=1
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    change A 0 0*A 1 1-A 0 1*A 1 0=1 at hd
    rw [hc] at hd
    nlinarith [hd]⟩

theorem frickeConjugate_mem (N : ℕ) (A : SL(2,ℤ)) (c : ℤ) (hc : A 1 0=(N:ℤ)*c) :
    frickeConjugate N A c hc∈CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_dvd]
  exact ⟨-A 0 1,by change -(N:ℤ)*A 0 1=(N:ℤ)*(-A 0 1); ring⟩

theorem fricke_conjugate_label (N : ℕ) (hN : 0<N) (A : SL(2,ℤ))
    (c : ℤ) (hc : A 1 0=(N:ℤ)*c) :
    frickeLabel N hN*integralLabel A=integralLabel (frickeConjugate N A c hc)*frickeLabel N hN := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branch (N:ℚ) 0 0 _)*rationalMap (rationalGL A)=
    rationalMap (rationalGL (frickeConjugate N A c hc))*rationalMap (branch (N:ℚ) 0 0 _)
  rw [← map_mul,← map_mul]
  congr 1
  apply Units.ext
  change (branch (N:ℚ) 0 0 _).val*A.val.map (fun z : ℤ => (z:ℚ))=
    (frickeConjugate N A c hc).val.map (fun z : ℤ => (z:ℚ))*(branch (N:ℚ) 0 0 _).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [branch,GeneralLinearGroup.mkOfDetNeZero,frickeConjugate,
      Matrix.mul_apply,Fin.sum_univ_two,hc]
  all_goals ring

#print axioms frickeLabel_mul_self
#print axioms frickeLabel_inv
#print axioms frickeConjugate_mem
#print axioms fricke_conjugate_label

end AsymptoticCongruenceLabels

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels AsymptoticFreshCRT AsymptoticFreshMatrices

theorem fricke_conj_mem (N : ℕ) (hN : 0<N) {g : AsymptoticRationalGroup.Group}
    (hg : g∈gamma N) : frickeLabel N hN*g*(frickeLabel N hN)⁻¹∈gamma N := by
  obtain ⟨A,hA,rfl⟩ := hg
  obtain ⟨c,hc⟩ := (gamma0_mem_dvd N A).mp hA
  rw [fricke_conjugate_label N hN A c hc,mul_inv_cancel_right]
  exact ⟨frickeConjugate N A c hc,frickeConjugate_mem N A c hc,rfl⟩

/-- The global Fricke involution normalizes the literal projective Γ₀(N). -/
theorem gamma_map_fricke (N : ℕ) (hN : 0<N) :
    (gamma N).map (MulAut.conj (frickeLabel N hN)).toMonoidHom=gamma N := by
  apply le_antisymm
  · rintro g ⟨a,ha,rfl⟩
    exact fricke_conj_mem N hN ha
  · intro g hg
    refine ⟨frickeLabel N hN*g*(frickeLabel N hN)⁻¹,fricke_conj_mem N hN hg,?_⟩
    change frickeLabel N hN*(frickeLabel N hN*g*(frickeLabel N hN)⁻¹)*(frickeLabel N hN)⁻¹=g
    rw [frickeLabel_inv]
    simp only [← mul_assoc,frickeLabel_mul_self,one_mul]
    rw [mul_assoc,frickeLabel_mul_self,mul_one]

#print axioms fricke_conj_mem
#print axioms gamma_map_fricke

end AsymptoticCongruenceStrip
