module

public import AsymptoticClassicalMultiplicityMixedGroupsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

/-- Ordinary p restriction commutes with the second, dilated q trace. -/
theorem mixed_cross_trace (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hc : p.Coprime q) (k : ℤ)
    (f : CuspForm (level (q * M)) k) :
    arithmeticTrace (level (p * (q * M))) (dilationLevel (p * M) q hq.pos) k
      (restrict k (level_antitone (Nat.dvd_mul_left (q * M) p)) f) =
    restrict k (dilationLevel_mono hq.pos (Nat.dvd_mul_left M p))
      (arithmeticTrace (level (q * M)) (dilationLevel M q hq.pos) k f) :=
  arithmeticTrace_restrict_diamond k _ _ (mixed_level_inf M p q hq.pos)
    (mixed_level_index M p q hM hp hq hc) f

/-- The ordinary p degeneracy preserves both q-new trace equations, with
 all cross-prime group and coset compatibility proved explicitly. -/
theorem ordinary_restrict_cross_new (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hc : p.Coprime q) (k : ℤ)
    (f : CuspForm (level (q * M)) k)
    (hfirst : arithmeticTrace (level (q * M)) (level M) k f = 0)
    (hsecond : arithmeticTrace (level (q * M)) (dilationLevel M q hq.pos) k f = 0) :
    arithmeticTrace (level (p * (q * M))) (level (p * M)) k
        (restrict k (level_antitone (Nat.dvd_mul_left (q * M) p)) f) = 0 ∧
      arithmeticTrace (level (p * (q * M))) (dilationLevel (p * M) q hq.pos) k
        (restrict k (level_antitone (Nat.dvd_mul_left (q * M) p)) f) = 0 := by
  constructor
  · rw [ordinary_cross_trace M p q hM hp hq hc k f, hfirst, map_zero]
  · rw [mixed_cross_trace M p q hM hp hq hc k f, hsecond, map_zero]

#print axioms mixed_cross_trace
#print axioms ordinary_restrict_cross_new

end AsymptoticClassicalCusp
