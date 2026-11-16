module

public import QuantitativeMaassZeroExtensionLawsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane AsymptoticFreshMatrices AsymptoticCongruenceStrip
open AsymptoticAtkinLehner AsymptoticClassicalPetersson QuantitativeNinaMaass MeasureTheory

namespace QuantitativeMaass

/-- An actual local Atkin eigenfunction has sign square one unless it
is the zero function; this follows from the checked congruence square. -/
theorem localAtkin_eigen_square_or_zero (M p : ℕ) (hM : 0<M) (hp : 0<p)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    (f : AutomorphicL2.representatives (gamma (p*M)) (quotientMeasure (p*M)))
    (s : ℂ) (hS : ∀ z,f.val (localAtkin M p hM hp A B hAB • z)=s*f.val z) :
    s^2=1 ∨ f.val=0 := by
  by_cases hs : s^2=1
  · exact Or.inl hs
  · right
    funext z
    have hi := f.property.2.1 ⟨_,localAtkin_square_mem M p hM hp A B hAB⟩ z
    change f.val ((localAtkin M p hM hp A B hAB*localAtkin M p hM hp A B hAB) • z)=f.val z at hi
    rw [mul_smul,hS,hS] at hi
    have hz : (s^2-1)*f.val z=0 := by linear_combination hi
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hs)

/-- The actual new trace kernel and Atkin/Fricke equations imply every
simply ramified prime-power analytic law. No U_p equation is assumed. -/
theorem newTrace_simple_prime_power_law (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1)
    [NeZero (p*M)]
    (f : AutomorphicL2.representatives (gamma (p*M)) (quotientMeasure (p*M)))
    (hf : Continuous f.val)
    (hx : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel (Nat.mul_pos (Fact.out : p.Prime).pos hM) (Nat.dvd_mul_left M p))
    (w s : ℂ)
    (hS : ∀ z,f.val (localAtkin M p hM (Fact.out : p.Prime).pos A B hAB • z)=s*f.val z)
    (hW : ∀ z,w*f.val (frickeLabel (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) • z)=f.val z)
    (k : ℕ) (z : ℂ) (hz : 0<z.im) :
    FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) (p^(k+1)) z=
      (w*s)*FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) (p^(k+1))
        (-1/((Nat.lcm (p*M) ((p^(k+1))^2):ℂ)*z)) := by
  rcases localAtkin_eigen_square_or_zero M p hM (Fact.out : p.Prime).pos A B hAB f s hS with hs|hzero
  · have hU (y : ℂ) : ramifiedAverage p (upperZeroExtension f.val) y=(-s)*upperZeroExtension f.val y :=
      upperZeroExtension_ramified p (Fact.out : p.Prime).pos f.val (-s)
        (fun t => simple_trace_sign_ramified M p hM hpM A B hAB f hf s hx.1 hS t) y
    have hδ : (-s)^2=1 := by simpa only [neg_sq] using hs
    have hz0 : z≠0 := by intro he; simp [he] at hz
    have he := simple_prime_power_analytic_law M p hM (Fact.out : p.Prime)
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM).symm k (upperZeroExtension f.val) w (-s) hδ hU
      (upperZeroExtension_fricke (p*M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) f.val w hW) z hz0
    simpa only [neg_mul_neg] using he
  · simp [hzero,upperZeroExtension,FinitenessAnalyticReconstruction.twist]

/-- The genuine repeated-prime new equation implies every prime-power
law, including identically zero twists above the first power. -/
theorem newSpace_repeated_prime_power_law (N p : ℕ) (hN : 0<N) (hp : p.Prime)
    (hp2 : p^2∣N) [NeZero N]
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hx : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN)
    (w : ℂ) (hW : ∀ z,w*f.val (frickeLabel N hN • z)=f.val z)
    (k : ℕ) (z : ℂ) :
    FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) (p^(k+1)) z=
      w*FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) (p^(k+1))
        (-1/((Nat.lcm N ((p^(k+1))^2):ℂ)*z)) := by
  have hU (y : ℂ) : ramifiedAverage p (upperZeroExtension f.val) y=0 := by
    simpa only [zero_mul] using upperZeroExtension_ramified p hp.pos f.val 0
      (fun t => by simpa only [zero_mul] using newSpace_repeated_ramified_zero N p hN hp hp2 f hf hx t) y
  cases k with
  | zero =>
    have ht (y : ℂ) : FinitenessAnalyticReconstruction.twist (upperZeroExtension f.val) p y=
        -upperZeroExtension f.val y := by
      simpa using analytic_twist_prime_power_of_ramified p hp 0 (upperZeroExtension f.val) 0
        (fun t => by simpa only [zero_mul] using hU t) y
    rw [Nat.zero_add,pow_one,Nat.lcm_eq_left hp2,ht,ht,mul_neg,
      upperZeroExtension_fricke N hN f.val w hW]
  | succ k =>
    have ht := analytic_twist_repeated_power_zero p hp k (upperZeroExtension f.val) hU
    simp only [Nat.add_assoc,ht,mul_zero]

#print axioms localAtkin_eigen_square_or_zero
#print axioms newTrace_simple_prime_power_law
#print axioms newSpace_repeated_prime_power_law

end QuantitativeMaass
