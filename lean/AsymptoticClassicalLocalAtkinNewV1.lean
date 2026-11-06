module

public import AsymptoticClassicalLocalAtkinSymmetryV1
public import AsymptoticClassicalLocalAtkinOldIntertwineV1
public import AsymptoticClassicalHeckeNewV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

variable (M p : ℕ) [NeZero M] [Fact p.Prime] (hM : 0 < M)
variable (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1) (k : ℤ)

/-- Atkin action exchanges the two p-old directions and preserves both
 directions at every other prime. -/
theorem localAtkin_primeOld_invariant (q : {q : ℕ // q.Prime ∧ q ∣ p * M}) :
    primeOldSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k q ≤
      (primeOldSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k q).comap
        (localAtkinOperator M p (Fact.out : p.Prime).pos A B hAB k) := by
  let hp := (Fact.out : p.Prime).pos
  rcases q with ⟨q, hq, hqN⟩
  by_cases hqp : q = p
  · subst q
    rw [primeOldSpace_factor_ranges (p * M) (Nat.mul_pos hp hM) k
      ⟨p, Fact.out, hqN⟩ M rfl (dvd_mul_left M p), frickeOld_range_eq_degeneracy M p hM hp k]
    apply sup_le
    · rintro f ⟨g, rfl⟩
      simp only [Submodule.mem_comap]
      rw [localAtkin_restrict]
      exact Submodule.mem_sup_right ⟨(p : ℂ) ^ (k - 1) • g, map_smul _ _ _⟩
    · rintro f ⟨g, rfl⟩
      simp only [Submodule.mem_comap]
      rw [localAtkin_degeneracy]
      exact Submodule.mem_sup_left ⟨_, map_smul _ _ _⟩
  · have hqM : q ∣ M := (hq.dvd_mul.mp hqN).resolve_left
      (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h))
    obtain ⟨L, rfl⟩ := hqM
    have hL : 0 < L := Nat.pos_of_mul_pos_left hM
    have hPL : 0 < p * L := Nat.mul_pos hp hL
    have he : p * (q * L) = q * (p * L) := by ac_rfl
    have hd : p * L ∣ p * (q * L) := by rw [he]; exact dvd_mul_left _ _
    rw [primeOldSpace_factor_ranges (p * (q * L)) (Nat.mul_pos hp hM) k
      ⟨q, hq, hqN⟩ (p * L) he hd]
    apply sup_le
    · rintro f ⟨g, rfl⟩
      simp only [Submodule.mem_comap]
      apply Submodule.mem_sup_left
      refine ⟨localAtkinOperator L p hp A ((q : ℤ) * B)
        (localAtkin_lower_bezout L q p A B hAB) k g, ?_⟩
      apply DFunLike.coe_injective
      exact (localAtkin_slash_lower p hp A B L q hAB k g).symm
    · intro f hf
      simp only [Submodule.mem_comap]
      apply Submodule.mem_sup_right
      obtain ⟨g, hg⟩ := (mem_frickeOld_range_iff (p * (q * L)) (p * L) q
        (Nat.mul_pos hp hM) hPL hq.pos he hd k f).mp hf
      apply (mem_frickeOld_range_iff (p * (q * L)) (p * L) q
        (Nat.mul_pos hp hM) hPL hq.pos he hd k _).mpr
      refine ⟨localAtkinOperator L p hp A ((q : ℤ) * B)
        (localAtkin_lower_bezout L q p A B hAB) k g, ?_⟩
      change (f : ℍ → ℂ) ∣[k] localAtkinReal (q * L) p hp A B hAB = _
      rw [hg, localAtkin_slash_degeneracy_lower p hp A B L q hq.pos hAB k g]

/-- The full oldspace is invariant under the local Atkin operator. -/
theorem localAtkin_old_invariant :
    oldSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k ≤
      (oldSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k).comap
        (localAtkinOperator M p (Fact.out : p.Prime).pos A B hAB k) := by
  change (⨆ q : {q : ℕ // q.Prime ∧ q ∣ p * M},
    primeOldSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k q) ≤ _
  apply iSup_le
  intro q f hf
  exact (le_iSup (fun q => primeOldSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k q) q)
    (localAtkin_primeOld_invariant M p hM A B hAB k q hf)

/-- Symmetry and oldspace invariance preserve the actual joint trace kernel. -/
theorem localAtkin_mem_newSpace (f : CuspForm (level (p * M)) k)
    (hf : f ∈ newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k) :
    localAtkinOperator M p (Fact.out : p.Prime).pos A B hAB k f ∈
      newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k := by
  let : NeZero (p * M) := ⟨(Nat.mul_pos (Fact.out : p.Prime).pos hM).ne'⟩
  have hs := localAtkinOperator_isSymmetric M p (Fact.out : p.Prime).pos A B hAB k
  rw [newSpace_eq_orthogonal, Submodule.mem_orthogonal'] at hf ⊢
  intro g hg
  rw [hs]
  exact hf _ (localAtkin_old_invariant M p hM A B hAB k hg)

#print axioms localAtkin_primeOld_invariant
#print axioms localAtkin_old_invariant
#print axioms localAtkin_mem_newSpace

end AsymptoticClassicalCusp
