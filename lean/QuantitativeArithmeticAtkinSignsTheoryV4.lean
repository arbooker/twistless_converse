module

public import AsymptoticAtkinLehnerSquareV1
public import QuantitativeArithmeticAtkinSignsOldV1
public import QuantitativeArithmeticCrossPrimeV1

/-! Consolidated chapter: QuantitativeArithmeticAtkinSigns. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticAtkinSignsCommutatorV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
@[expose] public section

namespace QuantitativeArithmeticAtkinSigns

open Matrix AsymptoticAtkinLehner AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticFreshMatrices AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticReconstructionBranch
open scoped MatrixGroups

/-- The actual integral commutator of a local Atkin--Lehner matrix and Fricke. -/
def localFrickeCommutator (M p : ℕ) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1) : SL(2,ℤ) :=
  ⟨!![(p:ℤ)+(M:ℤ)*B^2,A*B-1;
      (p:ℤ)*M*(A*B-1),(p:ℤ)*A^2+(M:ℤ)], by
    rw [Matrix.det_fin_two]
    dsimp
    calc
      _ = ((p:ℤ)*A+(M:ℤ)*B)^2 := by ring
      _ = 1 := by rw [hAB]; norm_num⟩

theorem localFrickeCommutator_mem (M p : ℕ) (A B : ℤ)
    (hAB : (p : ℤ)*A+(M : ℤ)*B=1) :
    localFrickeCommutator M p A B hAB ∈ CongruenceSubgroup.Gamma0 (p*M) := by
  rw [gamma0_mem_dvd]
  refine ⟨A*B-1, ?_⟩
  change (p:ℤ)*M*(A*B-1)=((p*M:ℕ):ℤ)*(A*B-1)
  rw [Nat.cast_mul]

theorem localAtkin_fricke_commute_mod_gamma (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    localAtkin M p hM hp A B hAB * frickeLabel (p*M) (Nat.mul_pos hp hM) =
      integralLabel (localFrickeCommutator M p A B hAB) *
        frickeLabel (p*M) (Nat.mul_pos hp hM) * localAtkin M p hM hp A B hAB := by
  have hn : ((p*M:ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos hp hM).ne'
  have hab : (p:ℚ)*(A:ℚ)+(M:ℚ)*(B:ℚ)=1 := by exact_mod_cast hAB
  let F := branch ((p*M:ℕ):ℚ) 0 0 hn
  let L := F * complementGL M p hM A B hAB
  have hm : (rationalGL (localFrickeCommutator M p A B hAB)).val * F.val * L.val =
      ((p:ℚ)*(A:ℚ)+(M:ℚ)*(B:ℚ)) • (L.val * F.val) := by
    change (localFrickeCommutator M p A B hAB).val.map (fun z : ℤ => (z:ℚ)) *
      F.val * (F.val * (complementGL M p hM A B hAB).val) =
        ((p:ℚ)*(A:ℚ)+(M:ℚ)*(B:ℚ)) •
          ((F.val * (complementGL M p hM A B hAB).val) * F.val)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [F,branch,complementGL,AsymptoticFreshMatrices.representative,entries,
        localFrickeCommutator,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two,Nat.cast_mul]
    all_goals ring
  rw [hab,one_smul] at hm
  have he : L*F=rationalGL (localFrickeCommutator M p A B hAB)*F*L :=
    Units.ext hm.symm
  apply Subtype.ext
  apply Subtype.ext
  change (rationalMap F * rationalMap (complementGL M p hM A B hAB))*rationalMap F =
    rationalMap (rationalGL (localFrickeCommutator M p A B hAB))*rationalMap F*
      (rationalMap F*rationalMap (complementGL M p hM A B hAB))
  simp only [← map_mul]
  exact congrArg rationalMap he

/-- The local and global involutions commute on the actual congruence quotient. -/
theorem localAtkin_fricke_commutator_mem (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    localAtkin M p hM hp A B hAB * frickeLabel (p*M) (Nat.mul_pos hp hM) *
      (localAtkin M p hM hp A B hAB)⁻¹ *
      (frickeLabel (p*M) (Nat.mul_pos hp hM))⁻¹ ∈ gamma (p*M) := by
  rw [localAtkin_fricke_commute_mod_gamma M p hM hp A B hAB,
    mul_inv_cancel_right,mul_inv_cancel_right]
  exact ⟨localFrickeCommutator M p A B hAB,
    localFrickeCommutator_mem M p A B hAB,rfl⟩

#print axioms localFrickeCommutator_mem
#print axioms localAtkin_fricke_commute_mod_gamma
#print axioms localAtkin_fricke_commutator_mem

end QuantitativeArithmeticAtkinSigns
end
end

/-! ## QuantitativeArithmeticAtkinSignsCommutatorPairV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 6000000
@[expose] public section

namespace QuantitativeArithmeticAtkinSigns

open Matrix AsymptoticAtkinLehner AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticFreshMatrices AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticReconstructionBranch
open scoped MatrixGroups

/-- Integral entries of the commutator at level p*q*R. -/
def localPairEntries (R p q : ℕ) (A B C D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  let u := 1-B*(R:ℤ)
  let v := A*C-B*(R:ℤ)
  let w := A*C-(R:ℤ)*D
  let z := 1-(R:ℤ)*D
  let r := (p:ℤ)*D+B*(q:ℤ)*C
  let s := (p:ℤ)*A*D+B*(q:ℤ)
  !![(p:ℤ)*q*u*v+(R:ℤ)*r*((q:ℤ)*C+p), -u*s+r*z;
     (p:ℤ)*q*R*(w*((q:ℤ)*C+p)-((q:ℤ)+(p:ℤ)*A)*v),
     (R:ℤ)*((q:ℤ)+(p:ℤ)*A)*s+(p:ℤ)*q*w*z]

def localPairCommutator (R p q : ℕ) (A B C D : ℤ)
    (hAB : (p:ℤ)*A+((q*R:ℕ):ℤ)*B=1)
    (hCD : (q:ℤ)*C+((p*R:ℕ):ℤ)*D=1) : SL(2,ℤ) :=
  ⟨localPairEntries R p q A B C D, by
    rw [Matrix.det_fin_two]
    dsimp [localPairEntries]
    calc
      _ = ((p:ℤ)*A+((q*R:ℕ):ℤ)*B)^2 *
          ((q:ℤ)*C+((p*R:ℕ):ℤ)*D)^2 := by push_cast; ring
      _ = 1 := by rw [hAB,hCD]; norm_num⟩

theorem localPairCommutator_mem (R p q : ℕ) (A B C D : ℤ)
    (hAB : (p:ℤ)*A+((q*R:ℕ):ℤ)*B=1)
    (hCD : (q:ℤ)*C+((p*R:ℕ):ℤ)*D=1) :
    localPairCommutator R p q A B C D hAB hCD ∈ CongruenceSubgroup.Gamma0 (p*(q*R)) := by
  rw [gamma0_mem_dvd]
  refine ⟨(A*C-(R:ℤ)*D)*((q:ℤ)*C+p)-((q:ℤ)+(p:ℤ)*A)*(A*C-B*(R:ℤ)), ?_⟩
  change (p:ℤ)*q*R*_=((p*(q*R):ℕ):ℤ)*_
  push_cast
  ring

theorem localAtkin_pair_commute_mod_gamma (R p q : ℕ)
    (hR : 0<R) (hp : 0<p) (hq : 0<q) (A B C D : ℤ)
    (hAB : (p:ℤ)*A+((q*R:ℕ):ℤ)*B=1)
    (hCD : (q:ℤ)*C+((p*R:ℕ):ℤ)*D=1) :
    localAtkin (q*R) p (Nat.mul_pos hq hR) hp A B hAB *
      localAtkin (p*R) q (Nat.mul_pos hp hR) hq C D hCD =
    integralLabel (localPairCommutator R p q A B C D hAB hCD) *
      localAtkin (p*R) q (Nat.mul_pos hp hR) hq C D hCD *
      localAtkin (q*R) p (Nat.mul_pos hq hR) hp A B hAB := by
  have hnp : ((p*(q*R):ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos hp (Nat.mul_pos hq hR)).ne'
  have hnq : ((q*(p*R):ℕ):ℚ)≠0 := by exact_mod_cast (Nat.mul_pos hq (Nat.mul_pos hp hR)).ne'
  have hab : (p:ℚ)*(A:ℚ)+((q*R:ℕ):ℚ)*(B:ℚ)=1 := by exact_mod_cast hAB
  have hcd : (q:ℚ)*(C:ℚ)+((p*R:ℕ):ℚ)*(D:ℚ)=1 := by exact_mod_cast hCD
  let Fp := branch ((p*(q*R):ℕ):ℚ) 0 0 hnp
  let Fq := branch ((q*(p*R):ℕ):ℚ) 0 0 hnq
  let Lp := Fp * complementGL (q*R) p (Nat.mul_pos hq hR) A B hAB
  let Lq := Fq * complementGL (p*R) q (Nat.mul_pos hp hR) C D hCD
  have hm : (rationalGL (localPairCommutator R p q A B C D hAB hCD)).val * Lq.val * Lp.val =
      (((p:ℚ)*(A:ℚ)+((q*R:ℕ):ℚ)*(B:ℚ))*
        ((q:ℚ)*(C:ℚ)+((p*R:ℕ):ℚ)*(D:ℚ))) • (Lp.val*Lq.val) := by
    change (localPairCommutator R p q A B C D hAB hCD).val.map (fun z : ℤ => (z:ℚ)) *
      (Fq.val * (complementGL (p*R) q (Nat.mul_pos hp hR) C D hCD).val) *
      (Fp.val * (complementGL (q*R) p (Nat.mul_pos hq hR) A B hAB).val) =
      (((p:ℚ)*(A:ℚ)+((q*R:ℕ):ℚ)*(B:ℚ))*
        ((q:ℚ)*(C:ℚ)+((p*R:ℕ):ℚ)*(D:ℚ))) •
        ((Fp.val * (complementGL (q*R) p (Nat.mul_pos hq hR) A B hAB).val) *
          (Fq.val * (complementGL (p*R) q (Nat.mul_pos hp hR) C D hCD).val))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Fp,Fq,branch,complementGL,AsymptoticFreshMatrices.representative,entries,
        localPairCommutator,localPairEntries,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two,Nat.cast_mul]
    all_goals ring
  rw [hab,hcd,one_mul,one_smul] at hm
  have he : Lp*Lq=rationalGL (localPairCommutator R p q A B C D hAB hCD)*Lq*Lp :=
    Units.ext hm.symm
  apply Subtype.ext
  apply Subtype.ext
  change (rationalMap Fp*rationalMap (complementGL (q*R) p (Nat.mul_pos hq hR) A B hAB))*
      (rationalMap Fq*rationalMap (complementGL (p*R) q (Nat.mul_pos hp hR) C D hCD)) =
    rationalMap (rationalGL (localPairCommutator R p q A B C D hAB hCD))*
      (rationalMap Fq*rationalMap (complementGL (p*R) q (Nat.mul_pos hp hR) C D hCD))*
      (rationalMap Fp*rationalMap (complementGL (q*R) p (Nat.mul_pos hq hR) A B hAB))
  simp only [← map_mul]
  exact congrArg rationalMap he

/-- Distinct coprime local Atkin--Lehner directions commute modulo Γ₀. -/
theorem localAtkin_pair_commutator_mem (R p q : ℕ)
    (hR : 0<R) (hp : 0<p) (hq : 0<q) (A B C D : ℤ)
    (hAB : (p:ℤ)*A+((q*R:ℕ):ℤ)*B=1)
    (hCD : (q:ℤ)*C+((p*R:ℕ):ℤ)*D=1) :
    localAtkin (q*R) p (Nat.mul_pos hq hR) hp A B hAB *
      localAtkin (p*R) q (Nat.mul_pos hp hR) hq C D hCD *
      (localAtkin (q*R) p (Nat.mul_pos hq hR) hp A B hAB)⁻¹ *
      (localAtkin (p*R) q (Nat.mul_pos hp hR) hq C D hCD)⁻¹ ∈ gamma (p*(q*R)) := by
  rw [localAtkin_pair_commute_mod_gamma R p q hR hp hq A B C D hAB hCD,
    mul_inv_cancel_right,mul_inv_cancel_right]
  exact ⟨localPairCommutator R p q A B C D hAB hCD,
    localPairCommutator_mem R p q A B C D hAB hCD,rfl⟩

#print axioms localPairCommutator_mem
#print axioms localAtkin_pair_commute_mod_gamma
#print axioms localAtkin_pair_commutator_mem

end QuantitativeArithmeticAtkinSigns
end
end

/-! ## QuantitativeArithmeticAtkinSignsCommutatorLevelV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace QuantitativeArithmeticAtkinSigns

open AsymptoticAtkinLehner AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticFreshMatrices

/-- The actual local/global commutator for a prime dividing the stated level. -/
theorem localAtkin_fricke_commutator_mem_level (N p : ℕ) (hN : 0<N)
    (hp : p.Prime) (hpN : p∣N) (hM : 0<N/p) (A B : ℤ)
    (hAB : (p:ℤ)*A+((N/p:ℕ):ℤ)*B=1) :
    localAtkin (N/p) p hM hp.pos A B hAB * frickeLabel N hN *
      (localAtkin (N/p) p hM hp.pos A B hAB)⁻¹ *
      (frickeLabel N hN)⁻¹ ∈ gamma N := by
  simpa only [Nat.mul_div_cancel' hpN] using
    localAtkin_fricke_commutator_mem (N/p) p hM hp.pos A B hAB

/-- Distinct simple-prime involutions commute on the literal Γ₀(N) quotient.
The Bezout relations already express the required coprimality. -/
theorem localAtkin_pair_commutator_mem_level (N p q : ℕ) (hN : 0<N)
    (hp : p.Prime) (hq : q.Prime) (hpN : p∣N) (hqN : q∣N) (hpq : p≠q)
    (hMp : 0<N/p) (hMq : 0<N/q) (A B C D : ℤ)
    (hAB : (p:ℤ)*A+((N/p:ℕ):ℤ)*B=1)
    (hCD : (q:ℤ)*C+((N/q:ℕ):ℤ)*D=1) :
    localAtkin (N/p) p hMp hp.pos A B hAB *
      localAtkin (N/q) q hMq hq.pos C D hCD *
      (localAtkin (N/p) p hMp hp.pos A B hAB)⁻¹ *
      (localAtkin (N/q) q hMq hq.pos C D hCD)⁻¹ ∈ gamma N := by
  obtain ⟨R,hR,he,hNp,hNq⟩ :=
    QuantitativeArithmeticCrossPrime.two_prime_level N p q hN hp hq hpN hqN hpq
  have hab : (p:ℤ)*A+((q*R:ℕ):ℤ)*B=1 := by simpa only [hNp] using hAB
  have hcd : (q:ℤ)*C+((p*R:ℕ):ℤ)*D=1 := by simpa only [hNq] using hCD
  have hh := localAtkin_pair_commutator_mem R p q hR hp.pos hq.pos A B C D hab hcd
  rw [← he] at hh
  simpa only [hNp,hNq] using hh

#print axioms localAtkin_fricke_commutator_mem_level
#print axioms localAtkin_pair_commutator_mem_level

end QuantitativeArithmeticAtkinSigns
end
end

/-! ## QuantitativeArithmeticAtkinSignsV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticAtkinSigns

open AsymptoticAtkinLehner AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open QuantitativeArithmeticCrossPrime

/-- Local Atkin conjugation swaps the two actual old overgroups at its own prime. -/
theorem own_old_iff (M p : ℕ) (hM : 0<M) (hp : 0<p) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (b : Bool) (g : AsymptoticRationalGroup.Group) :
    g∈oldGroup (p*M) (Nat.mul_pos hp hM) p b ↔
      localAtkin M p hM hp A B hAB*g*(localAtkin M p hM hp A B hAB)⁻¹∈
        oldGroup (p*M) (Nat.mul_pos hp hM) p (!b) := by
  have hdiv : p*M/p=M := Nat.mul_div_right M hp
  cases b <;> simp only [oldGroup,Bool.not_false,Bool.not_true,Bool.false_eq_true,
    ite_false,ite_true,hdiv,frickeOldGroup_eq_degeneracy M p hM hp]
  · exact own_first_iff M p hM hp A B hAB g
  · exact own_second_iff M p hM hp A B hAB g

/-- A local Atkin involution preserves each old direction at a distinct prime,
including repeated primes. Only the explicit Bezout relation is needed for p. -/
theorem other_old_iff (M p q : ℕ) (hM : 0<M) (hp : p.Prime) (hq : q.Prime)
    (hqN : q∣p*M) (hpq : p≠q) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (b : Bool) (g : AsymptoticRationalGroup.Group) :
    g∈oldGroup (p*M) (Nat.mul_pos hp.pos hM) q b ↔
      localAtkin M p hM hp.pos A B hAB*g*(localAtkin M p hM hp.pos A B hAB)⁻¹∈
        oldGroup (p*M) (Nat.mul_pos hp.pos hM) q b := by
  have hqM : q∣M := (hq.dvd_mul.mp hqN).resolve_left (by
    intro hqp
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).symm)
  obtain ⟨L,rfl⟩ := hqM
  have hL : 0<L := Nat.pos_of_mul_pos_left hM
  have hdiv : p*(q*L)/q=p*L := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_div_right (p*L) hq.pos
  have he : frickeOldGroup (p*(q*L)) (p*L) (Nat.mul_pos hp.pos hM)=
      degeneracyGroup (p*L) q hq.pos := by
    simpa only [Nat.mul_left_comm] using
      frickeOldGroup_eq_degeneracy (p*L) q (Nat.mul_pos hp.pos hL) hq.pos
  cases b <;> simp only [oldGroup,Bool.false_eq_true,ite_false,ite_true,hdiv,he]
  · exact lower_first_iff L q p hL hq.pos hp.pos A B hAB g
  · exact lower_second_iff L q p hL hq.pos hp.pos A B hAB g

/-- Level-indexed own-prime swap, directly usable on the stated quotient. -/
theorem own_old_iff_level (N p : ℕ) (hN : 0<N) (hp : p.Prime) (hpN : p∣N)
    (hM : 0<N/p) (A B : ℤ) (hAB : (p:ℤ)*A+((N/p:ℕ):ℤ)*B=1)
    (b : Bool) (g : AsymptoticRationalGroup.Group) :
    g∈oldGroup N hN p b ↔
      localAtkin (N/p) p hM hp.pos A B hAB*g*(localAtkin (N/p) p hM hp.pos A B hAB)⁻¹∈
        oldGroup N hN p (!b) := by
  simpa only [Nat.mul_div_cancel' hpN] using own_old_iff (N/p) p hM hp.pos A B hAB b g

/-- Level-indexed preservation at every other prime dividing N. -/
theorem other_old_iff_level (N p q : ℕ) (hN : 0<N) (hp : p.Prime) (hq : q.Prime)
    (hpN : p∣N) (hqN : q∣N) (hpq : p≠q) (hM : 0<N/p)
    (A B : ℤ) (hAB : (p:ℤ)*A+((N/p:ℕ):ℤ)*B=1)
    (b : Bool) (g : AsymptoticRationalGroup.Group) :
    g∈oldGroup N hN q b ↔
      localAtkin (N/p) p hM hp.pos A B hAB*g*(localAtkin (N/p) p hM hp.pos A B hAB)⁻¹∈
        oldGroup N hN q b := by
  have hqd : q∣p*(N/p) := by simpa only [Nat.mul_div_cancel' hpN] using hqN
  simpa only [Nat.mul_div_cancel' hpN] using
    other_old_iff (N/p) p q hM hp hq hqd hpq A B hAB b g

#print axioms own_old_iff_level
#print axioms other_old_iff_level
#print axioms own_old_iff
#print axioms other_old_iff

end QuantitativeArithmeticAtkinSigns
end
end
