module

public import QuantitativeArithmeticCrossPrimeBandsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
@[expose] public noncomputable section
open QuantitativeMaass QuantitativeNinaMaass QuantitativeArithmeticCrossPrimeBands

namespace QuantitativeArithmeticNewBandProjections

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance



/-- A divisor-indexed interface to pairwise local new projection commutation.
Use A=N/p and B=N/q; the multiplication identities remove all level casts. -/
theorem distinct_prime_projections_commute {A B N p q : ℕ}
    [NeZero A] [NeZero B] [NeZero N] [NeZero p] [NeZero q]
    (hA : 0<A) (hB : 0<B) (hN : 0<N) (hp : p.Prime) (hq : q.Prime)
    (hc : p.Coprime q) (hpA : p*A=N) (hqB : q*B=N) (hAN : A∣N) (hBN : B∣N)
    (S : CuspEnergySpectrum A hA) (R : CuspEnergySpectrum B hB)
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    Commute (S.traceNewParityBand T hAN a b σ).starProjection
      (R.traceNewParityBand T hBN a b σ).starProjection := by
  have hqN : q∣N := by rw [←hqB]; exact Nat.dvd_mul_right q B
  have hqA : q∣A := hc.symm.dvd_mul_left.mp (by simpa only [hpA] using hqN)
  obtain ⟨M,rfl⟩ := hqA
  have hM : 0<M := Nat.pos_of_mul_pos_left hA
  have he : B=p*M := by
    apply Nat.eq_of_mul_eq_mul_left hq.pos
    calc
      q*B=N := hqB
      _=p*(q*M) := hpA.symm
      _=q*(p*M) := by ring
  subst B
  clear hqB
  subst N
  let : NeZero M := ⟨hM.ne'⟩
  exact local_new_projections_commute M p q hM hp hq hc S R T a b σ

theorem prime_quotient_pos (N p : ℕ) (hN : 0<N) (hp : p.Prime) (hpN : p∣N) :
    0<N/p := Nat.div_pos (Nat.le_of_dvd hN hpN) hp.pos

/-- Pairwise commutation at the literal levels N/p and N/q. -/
theorem prime_divisor_projections_commute (N p q : ℕ)
    [NeZero N] [NeZero p] [NeZero q] [NeZero (N/p)] [NeZero (N/q)]
    (hN : 0<N) (hp : p.Prime) (hq : q.Prime) (hpN : p∣N) (hqN : q∣N) (hpq : p≠q)
    (S : CuspEnergySpectrum (N/p) (prime_quotient_pos N p hN hp hpN))
    (R : CuspEnergySpectrum (N/q) (prime_quotient_pos N q hN hq hqN))
    (T : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    Commute (S.traceNewParityBand T (Nat.div_dvd_of_dvd hpN) a b σ).starProjection
      (R.traceNewParityBand T (Nat.div_dvd_of_dvd hqN) a b σ).starProjection :=
  distinct_prime_projections_commute _ _ hN hp hq ((Nat.coprime_primes hp hq).mpr hpq)
    (Nat.mul_div_cancel' hpN) (Nat.mul_div_cancel' hqN) _ _ S R T a b σ

/-- Every local new projection also commutes with global Fricke on a
fixed cusp parity band. -/
theorem local_projection_fricke {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0<M} {hN : 0<N} (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum N hN) (hMN : M∣N) (a b σ : ℝ) :
    Commute (S.traceNewParityBand T hMN a b σ).starProjection
      (frickeMap T a b σ) := by
  apply invariantSpace_projection_commute _ _ (fricke_selfAdjoint T a b σ)
  intro x hx
  apply (S.mem_traceNewParityBand T hMN a b σ _).mpr
  exact newTraceKernel_fricke hN hMN _ ((S.mem_traceNewParityBand T hMN a b σ x).mp hx)

#print axioms distinct_prime_projections_commute
#print axioms prime_divisor_projections_commute
#print axioms local_projection_fricke
end QuantitativeArithmeticNewBandProjections
