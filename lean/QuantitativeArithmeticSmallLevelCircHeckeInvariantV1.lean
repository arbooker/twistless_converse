module

public import QuantitativeArithmeticSmallLevelCircModularHeckeTheoryV4
public import QuantitativeArithmeticSmallLevelCircHeckeFirstTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalDiscriminant
open scoped ModularForm

theorem primeHecke_fricke_commute (N p : ℕ) [NeZero N] (hN : 0<N)
    (hp : p.Prime) (hpN : ¬p∣N) (k : ℤ) :
    Function.Commute (ModularHecke.primeHecke N p hp k)
      (ModularHecke.frickeOperator N hN k) := by
  have hc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
  have hAB : (p : ℤ)*Nat.gcdA p N+(N : ℤ)*Nat.gcdB p N=1 := by
    have h := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  simp only [ModularHecke.primeHecke, hpN, ite_false]
  exact ModularHecke.dilationTrace_fricke_commute N p hN hp.pos
    (Nat.gcdA p N) (Nat.gcdB p N) hAB k

/-- An upper-triangular Hecke correspondence preserves vanishing at infinity. -/
theorem primeHecke_zero_atInfty (N p : ℕ) [NeZero N] (hN : 0<N)
    (hp : p.Prime) (hpN : ¬p∣N) (k : ℤ) (F : ModularForm (level N) k)
    (hF : IsZeroAtImInfty (F : ℍ → ℂ)) :
    IsZeroAtImInfty (ModularHecke.primeHecke N p hp k F : ℍ → ℂ) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
  have hAB : (p : ℤ)*Nat.gcdA p N+(N : ℤ)*Nat.gcdB p N=1 := by
    have h := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  simp only [ModularHecke.primeHecke, hpN, ite_false]
  rw [ModularHecke.dilationTrace_prime_slash N p hN hpN (Nat.gcdA p N) (Nat.gcdB p N) hAB]
  have hD : dilationReal p hp.pos 1 0 = 0 := by
    simp [dilationReal, AsymptoticCongruenceLabels.dilationGL,
      Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  refine (hF.slash k hD).add ?_
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

/-- Actual full Mcirc is invariant under every good-prime Hecke operator,
in every weight. Both genuine trace kernels and both cusp zeros are preserved. -/
theorem primeHecke_mem_space (N p k : ℕ) [NeZero N] (hN : 0<N)
    (hp : p.Prime) (hpN : ¬p∣N) (F : ModularForm (level N) (k : ℤ))
    (hF : F ∈ space N hN k) :
    ModularHecke.primeHecke N p hp (k : ℤ) F ∈ space N hN k := by
  obtain ⟨G,hG,hF0,hG0,ht⟩ := hF
  have hGF : G=ModularHecke.frickeOperator N hN (k : ℤ) F :=
    DFunLike.coe_injective (hG.trans (ModularHecke.frickeOperator_coe N hN (k : ℤ) F).symm)
  refine ⟨ModularHecke.primeHecke N p hp (k : ℤ) G, ?_,
    primeHecke_zero_atInfty N p hN hp hpN (k : ℤ) F hF0,
    primeHecke_zero_atInfty N p hN hp hpN (k : ℤ) G hG0, ?_⟩
  · rw [hGF, primeHecke_fricke_commute N p hN hp hpN (k : ℤ) F]
    exact ModularHecke.frickeOperator_coe N hN (k : ℤ) _
  · intro q
    exact ⟨primeHecke_first_trace_zero N p hN hp hpN (k : ℤ) F q (ht q).1,
      primeHecke_first_trace_zero N p hN hp hpN (k : ℤ) G q (ht q).2⟩

/-- The actual restricted good-prime operator on full Mcirc. -/
def hecke (N p k : ℕ) [NeZero N] (hN : 0<N) (hp : p.Prime) (hpN : ¬p∣N) :
    space N hN k →ₗ[ℂ] space N hN k where
  toFun F := ⟨ModularHecke.primeHecke N p hp (k : ℤ) F.val,
    primeHecke_mem_space N p k hN hp hpN F.val F.property⟩
  map_add' F G := Subtype.ext (map_add _ F.val G.val)
  map_smul' c F := Subtype.ext (map_smul _ c F.val)

#print axioms primeHecke_fricke_commute
#print axioms primeHecke_zero_atInfty
#print axioms primeHecke_mem_space
#print axioms hecke
end QuantitativeArithmeticSmallLevelCirc
