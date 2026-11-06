module

public import QuantitativeArithmeticSmallLevelCircAllHeckeTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalDiscriminant
open scoped ModularForm

theorem allPrimeHecke_zero_atInfty (N p : ℕ) [NeZero N] (hN : 0 < N)
    (hp : p.Prime) (k : ℤ) (F : ModularForm (level N) k)
    (hF : IsZeroAtImInfty (F : ℍ → ℂ)) :
    IsZeroAtImInfty (ModularHecke.primeHecke N p hp k F : ℍ → ℂ) := by
  by_cases hpN : p ∣ N
  · simp only [ModularHecke.primeHecke, hpN, ite_true]
    rw [ModularHecke.upperTrace_bad_slash N p hp hpN k F]
    classical
    have hs (s : Finset (Fin p)) : IsZeroAtImInfty
        (∑ a ∈ s, (F : ℍ → ℂ) ∣[k]
          triangularGL 1 a.val p (by norm_num) (by exact_mod_cast hp.pos)) := by
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using
          (show IsZeroAtImInfty (0 : ℍ → ℂ) from tendsto_const_nhds)
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (hF.slash k (show
          triangularGL 1 a.val p (by norm_num) (by exact_mod_cast hp.pos) 1 0 = 0 from rfl)).add ih
    exact hs Finset.univ
  · exact primeHecke_zero_atInfty N p hN hp hpN k F hF

/-- Full Mcirc is invariant under every actual prime Hecke operator.
Both trace kernels and both vanishing constants are retained. -/
theorem allPrimeHecke_mem_space (N p k : ℕ) [NeZero N] (hN : 0 < N)
    (hp : p.Prime) (hk : Even k) (F : ModularForm (level N) (k : ℤ))
    (hF : F ∈ space N hN k) :
    ModularHecke.primeHecke N p hp (k : ℤ) F ∈ space N hN k := by
  have hF' := hF
  obtain ⟨G,hG,hF0,hG0,_⟩ := hF
  have hGmem := fricke_mem_space hk F G hF' hG
  have hGF : G = ModularHecke.frickeOperator N hN (k : ℤ) F :=
    DFunLike.coe_injective (hG.trans (ModularHecke.frickeOperator_coe N hN (k : ℤ) F).symm)
  refine ⟨ModularHecke.primeHecke N p hp (k : ℤ) G, ?_,
    allPrimeHecke_zero_atInfty N p hN hp (k : ℤ) F hF0,
    allPrimeHecke_zero_atInfty N p hN hp (k : ℤ) G hG0, ?_⟩
  · rw [hGF, primeHecke_fricke_circ N k hN hk F hF' p hp]
    exact ModularHecke.frickeOperator_coe N hN (k : ℤ) _
  · intro q
    exact ⟨allPrimeHecke_first_trace_zero N p k hN hp hk F hF' q,
      allPrimeHecke_first_trace_zero N p k hN hp hk G hGmem q⟩

/-- The full family of commuting actual Hecke endomorphisms on Mcirc. -/
def allHecke (N k : ℕ) [NeZero N] (hN : 0 < N) (hk : Even k) (p : Nat.Primes) :
    space N hN k →ₗ[ℂ] space N hN k where
  toFun F := ⟨ModularHecke.primeHecke N p.val p.property (k : ℤ) F.val,
    allPrimeHecke_mem_space N p.val k hN p.property hk F.val F.property⟩
  map_add' F G := Subtype.ext (map_add _ F.val G.val)
  map_smul' c F := Subtype.ext (map_smul _ c F.val)

theorem allHecke_commute (N k : ℕ) [NeZero N] (hN : 0 < N) (hk : Even k)
    (p q : Nat.Primes) : Function.Commute (allHecke N k hN hk p) (allHecke N k hN hk q) := by
  by_cases he : p = q
  · subst q
    exact Function.Commute.refl _
  · have hpq : p.val.Coprime q.val := p.property.coprime_iff_not_dvd.mpr (fun hd =>
      he (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp hd)))
    intro F
    apply Subtype.ext
    exact ModularHecke.primeHecke_commute N p.val q.val p.property q.property hpq (k : ℤ) F.val

#print axioms allPrimeHecke_mem_space
#print axioms allHecke
#print axioms allHecke_commute
end QuantitativeArithmeticSmallLevelCirc
