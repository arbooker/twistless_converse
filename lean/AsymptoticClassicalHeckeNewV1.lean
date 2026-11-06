module

public import AsymptoticClassicalHeckeSymmetryV1
public import AsymptoticClassicalHeckeOldIntertwineV1
public import AsymptoticClassicalNewOrthogonalV1
public import AsymptoticClassicalHeckeCommutationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalPetersson
open scoped ModularForm InnerProduct

/-- Restriction images depend only on the honest source subgroup. -/
theorem hecke_restrict_range_congr {G H J : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] [J.HasDetOne] (k : ℤ)
    (hH : G ≤ H) (hJ : G ≤ J) (he : H = J) :
    LinearMap.range (restrict k hH) = LinearMap.range (restrict k hJ) := by
  subst J
  rfl

/-- The two old ranges at an explicitly factored level. -/
theorem primeOldSpace_factor_ranges (N : ℕ) (hN : 0 < N) (k : ℤ)
    (q : {q : ℕ // q.Prime ∧ q ∣ N}) (M : ℕ) (he : N = q.val * M) (hMN : M ∣ N) :
    primeOldSpace N hN k q =
      LinearMap.range (restrict k (level_antitone hMN)) ⊔
        LinearMap.range (restrict k (level_le_frickeOldLevel hN hMN)) := by
  have hd : N / q.val = M :=
    (congrArg (fun n => n / q.val) he).trans (Nat.mul_div_cancel_left M q.property.1.pos)
  unfold primeOldSpace
  apply congrArg₂ (· ⊔ ·)
  · exact hecke_restrict_range_congr k _ _ (congrArg level hd)
  · exact hecke_restrict_range_congr k _ _ (congrArg (fun L => frickeOldLevel N L hN) hd)

variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (k : ℤ)

include hpN

/-- Each of the two genuine old directions at a bad prime is stable
 under every good-prime Hecke correspondence. -/
theorem dilationTrace_primeOld_invariant (q : {q : ℕ // q.Prime ∧ q ∣ N}) :
    primeOldSpace N hN k q ≤ (primeOldSpace N hN k q).comap
      (dilationTrace N p (Fact.out : p.Prime).pos k) := by
  rcases q with ⟨q, hq, hqN⟩
  obtain ⟨M, rfl⟩ := hqN
  have hM : 0 < M := Nat.pos_of_mul_pos_left hN
  let : NeZero M := ⟨hM.ne'⟩
  rw [primeOldSpace_factor_ranges (q * M) hN k ⟨q, hq, dvd_mul_right q M⟩ M rfl
    (dvd_mul_left M q)]
  rw [frickeOld_range_eq_degeneracy M q hM hq.pos k]
  apply sup_le
  · rintro f ⟨g, rfl⟩
    simp only [Submodule.mem_comap]
    rw [dilationTrace_restrict M q p hpN k]
    exact Submodule.mem_sup_left ⟨_, rfl⟩
  · rintro f ⟨g, rfl⟩
    simp only [Submodule.mem_comap]
    rw [dilationTrace_degeneracy M q p hq.pos hpN k]
    exact Submodule.mem_sup_right ⟨_, rfl⟩

/-- The total classical oldspace is invariant, with no sector decomposition. -/
theorem dilationTrace_old_invariant :
    oldSpace N hN k ≤ (oldSpace N hN k).comap
      (dilationTrace N p (Fact.out : p.Prime).pos k) := by
  change (⨆ q : {q : ℕ // q.Prime ∧ q ∣ N}, primeOldSpace N hN k q) ≤ _
  apply iSup_le
  intro q f hf
  exact (le_iSup (fun q => primeOldSpace N hN k q) q)
    (dilationTrace_primeOld_invariant N hN p hpN k q hf)

/-- Symmetry and oldspace invariance preserve the actual newspace,
 defined by both families of lower-level trace equations. -/
theorem dilationTrace_mem_newSpace (f : CuspForm (level N) k) (hf : f ∈ newSpace N hN k) :
    dilationTrace N p (Fact.out : p.Prime).pos k f ∈ newSpace N hN k := by
  have hc : p.Coprime N := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN
  have hAB : (p : ℤ) * Nat.gcdA p N + (N : ℤ) * Nat.gcdB p N = 1 := by
    have hh := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one, Nat.cast_one] at hh
    exact hh.symm
  have hs := dilationTrace_isSymmetric N p (Fact.out : p.Prime).pos k
    (Nat.gcdA p N) (Nat.gcdB p N) hAB
  rw [newSpace_eq_orthogonal, Submodule.mem_orthogonal'] at hf ⊢
  intro g hg
  rw [hs]
  exact hf _ (dilationTrace_old_invariant N hN p hpN k hg)

/-- A good-prime Hecke operator on the actual total classical newspace. -/
def newHecke : newSpace N hN k →ₗ[ℂ] newSpace N hN k where
  toFun f := ⟨dilationTrace N p (Fact.out : p.Prime).pos k f.val,
    dilationTrace_mem_newSpace N hN p hpN k f.val f.property⟩
  map_add' f g := Subtype.ext (map_add _ f.val g.val)
  map_smul' a f := Subtype.ext (map_smul _ a f.val)

@[simp] theorem newHecke_val (f : newSpace N hN k) :
    (newHecke N hN p hpN k f).val = dilationTrace N p (Fact.out : p.Prime).pos k f.val := rfl

/-- The restriction retains Petersson symmetry on the total newspace. -/
theorem newHecke_isSymmetric : (newHecke N hN p hpN k).IsSymmetric := by
  have hc : p.Coprime N := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN
  have hAB : (p : ℤ) * Nat.gcdA p N + (N : ℤ) * Nat.gcdB p N = 1 := by
    have hh := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one, Nat.cast_one] at hh
    exact hh.symm
  intro f g
  exact dilationTrace_isSymmetric N p (Fact.out : p.Prime).pos k
    (Nat.gcdA p N) (Nat.gcdB p N) hAB f.val g.val

/-- First coefficients of the restricted actual operators recover the
 corresponding prime coefficients. -/
theorem newCoefficient_first_hecke (f : newSpace N hN k) :
    newCoefficient N hN k 1 (newHecke N hN p hpN k f) = newCoefficient N hN k p f :=
  first_dilationTrace_prime N p hpN k f.val

/-- Coprime good-prime operators commute on the actual newspace. -/
theorem newHecke_commute (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N) (hpq : p.Coprime q) :
    Function.Commute (newHecke N hN p hpN k) (newHecke N hN q hqN k) := by
  intro f
  apply Subtype.ext
  exact dilationTrace_commute_of_coprime N p q hpN hqN hpq k f.val

#print axioms hecke_restrict_range_congr
#print axioms primeOldSpace_factor_ranges
#print axioms newHecke_isSymmetric
#print axioms newCoefficient_first_hecke
#print axioms newHecke_commute

#print axioms dilationTrace_primeOld_invariant
#print axioms dilationTrace_old_invariant
#print axioms dilationTrace_mem_newSpace
#print axioms newHecke_val

end AsymptoticClassicalCusp
