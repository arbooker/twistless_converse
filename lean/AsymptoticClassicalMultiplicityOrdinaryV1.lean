module

public import AsymptoticClassicalMultiplicityTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane Matrix AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped ModularForm

/-- The intersection of actual integral levels is their least-common-multiple level. -/
theorem level_inf (A B : ℕ) : level A ⊓ level B = level (Nat.lcm A B) := by
  change (CongruenceSubgroup.Gamma0 A).map (SpecialLinearGroup.mapGL ℝ) ⊓
    (CongruenceSubgroup.Gamma0 B).map (SpecialLinearGroup.mapGL ℝ) =
      (CongruenceSubgroup.Gamma0 (Nat.lcm A B)).map (SpecialLinearGroup.mapGL ℝ)
  rw [← Subgroup.map_inf _ _ _ SpecialLinearGroup.mapGL_injective]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, gamma0_mem_dvd, Int.natCast_dvd, Nat.lcm_dvd_iff]

/-- Removing distinct prime directions forms an exact intersection diamond. -/
theorem coprime_level_inf (M p q : ℕ) (hc : p.Coprime q) :
    level (q * M) ⊓ level (p * M) = level (p * (q * M)) := by
  rw [level_inf, Nat.lcm_mul_right, hc.symm.lcm_eq_mul]
  congr 1
  ring

/-- The relative q-index is unchanged by an additional coprime factor p. -/
theorem coprime_level_index (M p q : ℕ) (hM : 0 < M) (hp : 0 < p)
    (hq : q.Prime) (hc : p.Coprime q) :
    (level (p * (q * M))).relIndex (level (p * M)) =
      (level (q * M)).relIndex (level M) := by
  rw [show p * (q * M) = q * (p * M) by ring, level_relIndex, level_relIndex]
  by_cases hqM : q ∣ M
  · rw [AsymptoticRamifiedCosets.projective_index (p * M) q (Nat.mul_pos hp hM) hq.pos
      (dvd_mul_of_dvd_right hqM p),
      AsymptoticRamifiedCosets.projective_index M q hM hq.pos hqM]
  · have hqpM : ¬q ∣ p * M := fun h => hqM (hc.symm.dvd_mul_left.mp h)
    rw [AsymptoticRamifiedCosets.projective_index_coprime (p * M) q (Nat.mul_pos hp hM) hq
      (hq.coprime_iff_not_dvd.mpr hqpM),
      AsymptoticRamifiedCosets.projective_index_coprime M q hM hq
      (hq.coprime_iff_not_dvd.mpr hqM)]

/-- Ordinary restriction at p commutes with the actual lower-level q trace.
 All coset and arithmetic hypotheses are discharged for coprime p and q. -/
theorem ordinary_cross_trace (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p)
    (hq : q.Prime) (hc : p.Coprime q) (k : ℤ)
    (f : CuspForm (level (q * M)) k) :
    arithmeticTrace (level (p * (q * M))) (level (p * M)) k
      (restrict k (level_antitone (Nat.dvd_mul_left (q * M) p)) f) =
    restrict k (level_antitone (Nat.dvd_mul_left M p))
      (arithmeticTrace (level (q * M)) (level M) k f) := by
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero (q * M) := ⟨(Nat.mul_pos hq.pos hM).ne'⟩
  let : NeZero (p * M) := ⟨(Nat.mul_pos hp hM).ne'⟩
  let : NeZero (p * (q * M)) := ⟨(Nat.mul_pos hp (Nat.mul_pos hq.pos hM)).ne'⟩
  exact arithmeticTrace_restrict_diamond k _ _ (coprime_level_inf M p q hc)
    (coprime_level_index M p q hM hp hq hc) f

#print axioms level_inf
#print axioms coprime_level_inf
#print axioms coprime_level_index
#print axioms ordinary_cross_trace

end AsymptoticClassicalCusp
