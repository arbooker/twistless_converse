module

public import AsymptoticLocalCongruenceSLV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticLocalCongruence

open Matrix AsymptoticRationalLocalIntegral AsymptoticIntegralSubgroup
open scoped MatrixGroups

/-- Global local integrality lifts a rational special-linear matrix
to an actual integral special-linear matrix. -/
theorem integral_lift (N : ℕ) (hN : 0<N) (A : SL(2,ℚ))
    (hA : A∈outside N ∅) :
    ∃ B : SL(2,ℤ),B∈CongruenceSubgroup.Gamma0 N ∧
      SpecialLinearGroup.map (Int.castRingHom ℚ) B=A := by
  classical
  have hloc (q : ℕ) (hq : q.Prime) : Condition N q A :=
    (mem_outside N ∅ A).mp hA q hq (Set.notMem_empty q)
  have he (i j : Fin 2) : ∃ a : ℤ,A.val i j=(a:ℚ) :=
    integer_of_all_padic _ (fun q hq => (hloc q hq).1 i j)
  choose b hb using he
  let Bmat : Matrix (Fin 2) (Fin 2) ℤ := b
  have hmat : Bmat.map (Int.castRingHom ℚ)=A.val := by
    ext i j
    exact (hb i j).symm
  have hdet : Bmat.det=1 := by
    have hd := congrArg Matrix.det hmat
    change (Bmat.map (fun z : ℤ => (z:ℚ))).det=A.val.det at hd
    rw [← Int.cast_det,A.property] at hd
    exact_mod_cast hd
  let B : SL(2,ℤ) := ⟨Bmat,hdet⟩
  refine ⟨B,?_,?_⟩
  · obtain ⟨c,hc⟩ := integer_of_all_padic (A.val 1 0/(N:ℚ)) (fun q hq => (hloc q hq).2)
    have hN' : (N:ℚ)≠0 := by exact_mod_cast hN.ne'
    have hd : Bmat 1 0=(N:ℤ)*c := by
      have hb10 := hb (1:Fin 2) (0:Fin 2)
      have hh : (Bmat 1 0:ℚ)=(N:ℚ)*(c:ℚ) := by
        rw [← hb10]
        exact (div_eq_iff hN').mp hc |>.trans (mul_comm _ _)
      exact_mod_cast hh
    rw [CongruenceSubgroup.Gamma0_mem]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr
    exact ⟨c,hd⟩
  · apply Subtype.ext
    exact hmat

/-- An integral congruence matrix satisfies all local level conditions. -/
theorem integral_mem_outside (N : ℕ) (hN : 0<N) (S : Set ℕ) (B : SL(2,ℤ))
    (hB : B∈CongruenceSubgroup.Gamma0 N) :
    SpecialLinearGroup.map (Int.castRingHom ℚ) B∈outside N S := by
  rw [mem_outside]
  intro q hq _
  let : Fact q.Prime := ⟨hq⟩
  constructor
  · intro i j
    change padicNorm q (B.val i j:ℚ)≤1
    exact padicNorm.of_int _
  · rw [CongruenceSubgroup.Gamma0_mem] at hB
    obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hB
    change padicNorm q ((B.val 1 0:ℚ)/(N:ℚ))≤1
    have hN' : (N:ℚ)≠0 := by exact_mod_cast hN.ne'
    rw [hc,Int.cast_mul,Int.cast_natCast,mul_div_cancel_left₀ _ hN']
    exact padicNorm.of_int c

#print axioms integral_lift
#print axioms integral_mem_outside

end AsymptoticLocalCongruence
