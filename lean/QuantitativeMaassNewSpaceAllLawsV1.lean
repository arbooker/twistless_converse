module

public import QuantitativeMaassAllModulusLawsV1
public import QuantitativeNewGapLocalAtkinV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceStrip
open AsymptoticClassicalPetersson AsymptoticSectorSigns AsymptoticOrbitDecode
open QuantitativeNinaMaass AsymptoticAtkinLehner QuantitativeNewGap

namespace QuantitativeMaass

theorem newSpace_simple_ramified (N : ℕ) (hN : 0<N) [NeZero N]
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hx : AutomorphicL2.denseEmbedding _ _ f∈newSpace N hN)
    (p : ℕ) (hp : p.Prime) (hpN : p∣N) (hp2 : ¬p^2∣N) (s : ℂ)
    (hS : ∀ z,f.val (localAtkinLabel N hN ⟨p,mem_simplePrimes.mpr ⟨hp,hpN,hp2⟩⟩ • z)=s*f.val z)
    (z : ℍ) : ∑ a : Fin p,f.val (ramifiedLabel p hp.pos a • z)=-s*f.val z := by
  obtain ⟨M,rfl⟩ := hpN
  let : Fact p.Prime := ⟨hp⟩
  have hM : 0<M := Nat.pos_of_mul_pos_left hN
  have hd : p*M/p=M := Nat.mul_div_cancel_left M hp.pos
  have hpM : ¬p∣M := by
    intro h
    exact hp2 (by simpa only [pow_two] using Nat.mul_dvd_mul_left p h)
  have hAB : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    have h := Nat.gcd_eq_gcd_ab p M
    rw [(hp.coprime_iff_not_dvd.mpr hpM).gcd_eq_one,Nat.cast_one] at h
    exact h.symm
  have ht : levelTrace (Nat.dvd_mul_left M p) (AutomorphicL2.denseEmbedding _ _ f)=0 := by
    simp only [newSpace,Submodule.mem_iInf] at hx
    have hh := hx ⟨p,hp,Nat.dvd_mul_right p M⟩
    have hk : AutomorphicL2.denseEmbedding _ _ f∈newTraceKernel hN (Nat.dvd_mul_left M p) := by
      simpa only [hd] using hh
    exact hk.1
  apply simple_trace_sign_ramified M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hAB f hf s ht
  intro y
  simpa only [localAtkinLabel,hd] using hS y

/-- Every continuous representative of the genuine newspace with the
specified local/global signs satisfies the full analytic reconstruction laws.
All U_p relations are consequences of newness, not additional assumptions. -/
theorem newSpace_all_analytic_laws (N : ℕ) (hN : 0<N) [NeZero N]
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hx : AutomorphicL2.denseEmbedding _ _ f∈newSpace N hN)
    (e : Sector N)
    (hW : ∀ z,sign e.1*f.val (frickeLabel N hN • z)=f.val z)
    (hS : ∀ p : SimplePrime N,∀ z,
      f.val (localAtkinLabel N hN p • z)= -delta e p.val*f.val z) :
    ∀ q : ℕ,0<q → ∀ z : ℂ,
      FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) q z=
        multiplier e q*FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) q
          (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
  apply modular_ramified_all_analytic_laws N hN f e hW
  · intro p hp hpN hp2 z
    simpa only [neg_neg] using newSpace_simple_ramified N hN f hf hx p hp hpN hp2
      (-delta e p) (hS ⟨p,mem_simplePrimes.mpr ⟨hp,hpN,hp2⟩⟩) z
  · intro p hp hp2 z
    exact newSpace_repeated_ramified_zero N p hN hp hp2 f hf hx z

#print axioms newSpace_simple_ramified
#print axioms newSpace_all_analytic_laws

end QuantitativeMaass
