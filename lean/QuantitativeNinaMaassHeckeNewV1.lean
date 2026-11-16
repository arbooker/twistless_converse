module

public import QuantitativeNinaMaassPartialNewV1
public import QuantitativeNinaMaassHeckeOperatorsV1
public import QuantitativeNinaMaassHeckeAlgebraV1
public import AsymptoticClassicalEigenbasisV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory QuantitativeMaass
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticFreshMatrices
open scoped Topology InnerProductSpace

/-!
Actual good-prime operators on the simultaneous trace-new parity band.
Preservation of the new equations is proved from the trace diamonds and
physical Fricke factorization. Symmetry is inherited from the existing
bounded Hecke operator. All-prime commutation and the full joint family are proved together in
JointOperators using the literal Fourier action. This chapter supplies
the actual good-prime restrictions and their symmetry.
-/

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance

local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

theorem dilationTraceOperator_partial_continuous (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : p.Prime) (P : Set ℕ) (hpP : p ∉ P)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hv : AutomorphicL2.denseEmbedding _ _ f ∈ partialNewSpace N hN P) :
    dilationTraceOperator N p hN hp.pos (AutomorphicL2.denseEmbedding _ _ f) ∈
      partialNewSpace N hN P := by
  rw [dilationTraceOperator_apply]
  apply (partialNewSpace N hN P).smul_mem
  apply levelTrace_partialNewSpace N p hN hp.pos P
  apply fricke_mem_partialNewSpace (p * N) (Nat.mul_pos hp.pos hN) P
  rw [frickeIsometry_apply]
  apply levelCover_partialNewSpace_continuous N p hN hp P hpP (frickeRepresentative N hN f)
  · exact hf.comp (rational_action_continuous (frickeLabel N hN))
  · rw [← frickeIsometry_apply]
    exact fricke_mem_partialNewSpace N hN P _ hv

/-- At a good prime, all prime divisors of the original level belong to
the preserved partial-new set, while the auxiliary raising prime does not. -/
theorem dilationTraceOperator_new_continuous (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hv : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN) :
    dilationTraceOperator N p hN hp.pos (AutomorphicL2.denseEmbedding _ _ f) ∈ newSpace N hN := by
  have hP : partialNewSpace N hN {q : ℕ | q ∣ N} = newSpace N hN :=
    partialNewSpace_eq_newSpace_of_covers N hN _ (fun _ _ h => h)
  rw [← hP] at hv ⊢
  exact dilationTraceOperator_partial_continuous N p hN hp _ hpN f hf hv

theorem hecke_new_continuous (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0 < N) (hpN : ¬ p ∣ N) (A B : ℤ)
    (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hv : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN) :
    HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ f) ∈ newSpace N hN := by
  rw [hecke_eq_dilationTraceOperator]
  exact dilationTraceOperator_new_continuous N p hN (Fact.out : p.Prime) hpN f hf hv

namespace CuspEnergySpectrum

local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance

local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    NormedAddCommGroup (S.partialParityBand a b σ P) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    InnerProductSpace ℂ (S.partialParityBand a b σ P) := inferInstance

/-- Restrict the actual factorized correspondence to the same geometric
spectral interval and reflection-parity range. -/
def dilationTraceParityBandMap {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [NeZero p] (hp : 0 < p) (a b σ : ℝ) :
    S.parityBand a b σ →ₗ[ℂ] S.parityBand a b σ :=
  S.parityBandMap S (dilationTraceOperator N p hN hp)
    (dilationTraceOperator_mem_cuspidal N p hN hp)
    (dilationTraceOperator_friedrichsGraph N p hN hp)
    (dilationTraceOperator_reflection N p hN hp) a b σ

theorem dilationTraceParityBandMap_new {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : ¬ p ∣ N)
    (a b σ : ℝ) (v : S.parityBand a b σ) (hv : v ∈ S.partialParityBand a b σ univ) :
    S.dilationTraceParityBandMap p hp.pos a b σ v ∈ S.partialParityBand a b σ univ := by
  obtain ⟨f, hf, he⟩ := exists_continuous_window_representative N hN S.basis S.energy
    S.energy_nonneg S.graph a b v.val.val v.val.property
  rw [mem_partialParityBand, partialNewSpace_univ] at hv ⊢
  have hh := dilationTraceOperator_new_continuous N p hN hp hpN f hf (by rw [he]; exact hv)
  rw [he] at hh
  exact hh

/-- The actual good-prime operator on the finite simultaneous newspace,
with the original spectral interval and reflection parity unchanged. -/
def newHeckeOperator {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : ¬ p ∣ N)
    (a b σ : ℝ) : S.partialParityBand a b σ univ →ₗ[ℂ] S.partialParityBand a b σ univ :=
  (S.dilationTraceParityBandMap p hp.pos a b σ).restrict
    (S.dilationTraceParityBandMap_new p hp hpN a b σ)

theorem newHeckeOperator_actual {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1)
    (a b σ : ℝ) (v : S.partialParityBand a b σ univ) :
    ((S.newHeckeOperator p (Fact.out : p.Prime) hpN a b σ v).val.val.val : AutomorphicSpace N) =
      HeckeL2.operator N p hN hpN A B hAB (v.val.val.val : AutomorphicSpace N) := by
  rw [hecke_eq_dilationTraceOperator]
  rfl

theorem newHeckeOperator_symmetric {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1) (a b σ : ℝ) :
    (S.newHeckeOperator p (Fact.out : p.Prime) hpN a b σ).IsSymmetric := by
  intro v w
  change inner ℂ
      (((S.newHeckeOperator p (Fact.out : p.Prime) hpN a b σ v).val.val.val) : AutomorphicSpace N)
      (w.val.val.val : AutomorphicSpace N) =
    inner ℂ (v.val.val.val : AutomorphicSpace N)
      (((S.newHeckeOperator p (Fact.out : p.Prime) hpN a b σ w).val.val.val) : AutomorphicSpace N)
  rw [S.newHeckeOperator_actual p hpN A B hAB, S.newHeckeOperator_actual p hpN A B hAB]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (HeckeL2.operator_selfAdjoint N p hN hpN A B hAB) _ _

/-- Canonical indexing of the actual good-prime operators, without
auxiliary choices of Bezout coefficients in the public interface. -/
def goodPrimeHecke {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) :
    S.partialParityBand a b σ univ →ₗ[ℂ] S.partialParityBand a b σ univ :=
  let : NeZero p.val := ⟨p.property.1.ne_zero⟩
  S.newHeckeOperator p.val p.property.1 p.property.2 a b σ

theorem goodPrimeHecke_symmetric {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) : (S.goodPrimeHecke a b σ p).IsSymmetric := by
  let : Fact p.val.Prime := ⟨p.property.1⟩
  have hc : p.val.Coprime N := p.property.1.coprime_iff_not_dvd.mpr p.property.2
  have hAB : (p.val : ℤ) * Nat.gcdA p.val N + (N : ℤ) * Nat.gcdB p.val N = 1 := by
    have h := Nat.gcd_eq_gcd_ab p.val N
    rw [hc.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  exact S.newHeckeOperator_symmetric p.val p.property.2 _ _ hAB a b σ

#print axioms dilationTraceParityBandMap_new
#print axioms newHeckeOperator_actual
#print axioms newHeckeOperator_symmetric
#print axioms goodPrimeHecke_symmetric

end CuspEnergySpectrum

#print axioms dilationTraceOperator_partial_continuous
#print axioms dilationTraceOperator_new_continuous
#print axioms hecke_new_continuous

end QuantitativeNinaMaass
