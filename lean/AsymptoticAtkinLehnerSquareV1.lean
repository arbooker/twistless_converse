module

public import AsymptoticAtkinLehnerNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public section

namespace AsymptoticAtkinLehner

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticFreshMatrices
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticReconstructionBranch
open scoped MatrixGroups

/-- The square of the determinant-p representative divided by p. -/
def localSquare (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : SL(2,ℤ) :=
  ⟨!![(p:ℤ)-(M:ℤ)*B,B*(A+1);-(p:ℤ)*M*(A+1),(p:ℤ)*A^2-(M:ℤ)*B],by
    rw [Matrix.det_fin_two]
    dsimp
    calc
      _=((p:ℤ)*A+(M:ℤ)*B)^2 := by ring
      _=1 := by rw [hAB]; norm_num⟩

theorem localSquare_mem (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    localSquare M p A B hAB∈CongruenceSubgroup.Gamma0 (p*M) := by
  rw [gamma0_mem_dvd]
  refine ⟨-(A+1),?_⟩
  change -(p:ℤ)*M*(A+1)=((p*M:ℕ):ℤ)*(-(A+1))
  rw [Nat.cast_mul]
  ring

theorem localAtkin_square (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    localAtkin M p hM hp A B hAB*localAtkin M p hM hp A B hAB=
      integralLabel (localSquare M p A B hAB) := by
  have hn : ((p*M:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos hp hM).ne'
  have hs : (p:ℚ)*(M:ℚ)^2≠0 := by
    have hp' : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
    have hM' : (M:ℚ)≠0 := by exact_mod_cast hM.ne'
    exact mul_ne_zero hp' (pow_ne_zero _ hM')
  have he : (branch ((p*M:ℕ):ℚ) 0 0 hn*complementGL M p hM A B hAB)*
      (branch ((p*M:ℕ):ℚ) 0 0 hn*complementGL M p hM A B hAB)=
      rationalGL (localSquare M p A B hAB)*
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ((p:ℚ)*(M:ℚ)^2) hs) := by
    apply Units.ext
    change ((branch ((p*M:ℕ):ℚ) 0 0 hn).val*(complementGL M p hM A B hAB).val)*
      ((branch ((p*M:ℕ):ℚ) 0 0 hn).val*(complementGL M p hM A B hAB).val)=
      (localSquare M p A B hAB).val.map (fun z : ℤ => (z:ℚ))*
        (GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ((p:ℚ)*(M:ℚ)^2) hs)).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [branch,complementGL,AsymptoticFreshMatrices.representative,entries,localSquare,
        GeneralLinearGroup.mkOfDetNeZero,GeneralLinearGroup.scalar,Matrix.scalar,Matrix.natCast_apply,
        Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  apply Subtype.ext
  apply Subtype.ext
  change (rationalMap (branch ((p*M:ℕ):ℚ) 0 0 hn)*rationalMap (complementGL M p hM A B hAB))*
    (rationalMap (branch ((p*M:ℕ):ℚ) 0 0 hn)*rationalMap (complementGL M p hM A B hAB))=
      rationalMap (rationalGL (localSquare M p A B hAB))
  simp only [← map_mul]
  rw [he,map_mul,rationalMap_scalar,mul_one]

theorem localAtkin_square_mem (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    localAtkin M p hM hp A B hAB*localAtkin M p hM hp A B hAB∈gamma (p*M) := by
  rw [localAtkin_square]
  exact ⟨localSquare M p A B hAB,localSquare_mem M p A B hAB,rfl⟩

theorem local_inv_conj_mem (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    {g : AsymptoticRationalGroup.Group} (hg : g∈gamma (p*M)) :
    (localAtkin M p hM hp A B hAB)⁻¹*g*localAtkin M p hM hp A B hAB∈gamma (p*M) := by
  let W := localAtkin M p hM hp A B hAB
  have hs : W*W∈gamma (p*M) := localAtkin_square_mem M p hM hp A B hAB
  have hh := (gamma (p*M)).mul_mem
    ((gamma (p*M)).mul_mem ((gamma (p*M)).inv_mem hs)
      (local_conj_mem M p hM hp A B hAB hg)) hs
  have he : (W*W)⁻¹*(W*g*W⁻¹)*(W*W)=W⁻¹*g*W := by group
  change (W*W)⁻¹*(W*g*W⁻¹)*(W*W)∈gamma (p*M) at hh
  rwa [he] at hh

#print axioms localSquare_mem
#print axioms localAtkin_square
#print axioms localAtkin_square_mem
#print axioms local_inv_conj_mem

end AsymptoticAtkinLehner
