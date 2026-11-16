module

public import QuantitativeNinaMaassRamifiedOperatorsV1
public import QuantitativeNinaMaassHeckeNewV1
public import QuantitativeNinaMaassHeckeSymmetriesV1
public import QuantitativeArithmeticMaassHeckeResolventV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory QuantitativeMaass
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace

/-!
All-prime commutation is proved by the literal height-dependent Fourier
action and actual physical uniqueness. Both ramified and unramified
operators act on the same finite new-parity band. No simultaneous
eigenfamily or multiplicity-one statement is supplied as an assumption.
-/

namespace QuantitativeNinaMaass

def heightPrime (N p : ℕ) (hp : 0 < p) : Module.End ℂ HeightCoefficients :=
  if p ∣ N then (Real.sqrt (p : ℝ) : ℂ) • heightUp p hp else heightHecke p hp

theorem height_correspondences_commute (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : p.Coprime q) (α β γ δ : ℂ) :
    Commute (α • heightUp p hp + β • heightDown p hp)
      (γ • heightUp q hq + δ • heightDown q hq) := by
  apply LinearMap.ext
  intro c
  change (α • heightUp p hp + β • heightDown p hp)
      ((γ • heightUp q hq + δ • heightDown q hq) c) =
    (γ • heightUp q hq + δ • heightDown q hq)
      ((α • heightUp p hp + β • heightDown p hp) c)
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
  rw [heightUp_up p q hp hq, heightDown_up p q hp hq hc,
    ← heightDown_up q p hq hp hc.symm, heightDown_down p q hp hq]
  module

theorem heightPrime_commute (N p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : p.Coprime q) :
    Commute (heightPrime N p hp) (heightPrime N q hq) := by
  have he (m : ℕ) (hm : 0 < m) : heightPrime N m hm =
      (if m ∣ N then (Real.sqrt (m : ℝ) : ℂ) else
        (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) * (m : ℂ)) • heightUp m hm +
      (if m ∣ N then 0 else (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ)) • heightDown m hm := by
    by_cases hd : m ∣ N <;> simp only [heightPrime, heightHecke, hd, ite_true, ite_false,
      zero_smul, add_zero]
  rw [he p hp, he q hq]
  exact height_correspondences_commute p q hp hq hc _ _ _ _

theorem involution_eigenvalue_sign {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) (hT : Function.Involutive T) (v : E) (hv : v ≠ 0) (χ : ℂ)
    (he : T v = χ • v) : χ = 1 ∨ χ = -1 := by
  have h := congrArg T he
  rw [hT v, map_smul, he, smul_smul] at h
  have hs : χ ^ 2 = 1 := by
    apply smul_left_injective ℂ hv
    simpa only [pow_two, one_smul] using h.symm
  exact sq_eq_one_iff.mp hs

/-- Transfer commutation through an injective, possibly nonlinear,
coordinate map with proved intertwining identities. -/
theorem linear_commute_of_coordinates {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (H : E → F) (hH : Function.Injective H)
    (A B : Module.End ℂ E) (C D : Module.End ℂ F)
    (hA : ∀ v, H (A v) = C (H v)) (hB : ∀ v, H (B v) = D (H v))
    (hCD : Commute C D) : Commute A B := by
  apply LinearMap.ext
  intro v
  apply hH
  change H (A (B v)) = H (B (A v))
  rw [hA, hB, hB, hA]
  exact DFunLike.congr_fun hCD (H v)

/-- A proved property of every nonzero joint eigenvector transfers to a
full independent family. The operators and the property remain arbitrary. -/
theorem joint_family_of_eigenvector_property {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : I → Module.End ℂ E) (hT : ∀ i, (T i).IsSymmetric)
    (hcomm : Pairwise fun i j => Commute (T i) (T j)) (P : E → Prop)
    (hP : ∀ v, v ≠ 0 → ∀ μ : I → ℂ, (∀ i, T i v = μ i • v) → P v) :
    ∃ v : Fin (Module.finrank ℂ E) → E, LinearIndependent ℂ v ∧ ∀ j, P (v j) := by
  obtain ⟨v, hv, he⟩ := AsymptoticClassicalEigenbasis.exists_joint_family T hT hcomm
  refine ⟨v, hv, fun j => ?_⟩
  obtain ⟨μ, hμ⟩ := he j
  exact hP (v j) (hv.ne_zero j) μ hμ

namespace CuspEnergySpectrum

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance
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

def newBandRepresentative {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (v : S.partialParityBand a b σ univ) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
  (exists_continuous_window_representative N hN S.basis S.energy
    S.energy_nonneg S.graph a b v.val.val.val v.val.val.property).choose

theorem newBandRepresentative_continuous {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (v : S.partialParityBand a b σ univ) :
    Continuous (S.newBandRepresentative a b σ v).val :=
  (exists_continuous_window_representative N hN S.basis S.energy
    S.energy_nonneg S.graph a b v.val.val.val v.val.val.property).choose_spec.1

theorem newBandRepresentative_embedding {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (v : S.partialParityBand a b σ univ) :
    AutomorphicL2.denseEmbedding _ _ (S.newBandRepresentative a b σ v) =
      (v.val.val.val : AutomorphicSpace N) :=
  (exists_continuous_window_representative N hN S.basis S.energy
    S.energy_nonneg S.graph a b v.val.val.val v.val.val.property).choose_spec.2

theorem newBand_reflection {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (hσ : σ ^ 2 = 1)
    (v : S.partialParityBand a b σ univ) :
    reflectionIsometry N (v.val.val.val : AutomorphicSpace N) =
      (σ : ℂ) • (v.val.val.val : AutomorphicSpace N) := by
  obtain ⟨u, hu⟩ := v.val.property
  have hh := parityProjection_eigen N σ hσ (u.val : AutomorphicSpace N)
  have hu' := congrArg (fun w : S.band a b => (w.val : AutomorphicSpace N)) hu
  change parityProjection N σ (u.val : AutomorphicSpace N) =
    (v.val.val.val : AutomorphicSpace N) at hu'
  rwa [hu'] at hh

def newBandHeight {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (v : S.partialParityBand a b σ univ) :
    HeightCoefficients := actualHeightCoefficients (S.newBandRepresentative a b σ v).val

theorem newBandHeight_injective {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (hσ : σ ^ 2 = 1) :
    Function.Injective (S.newBandHeight a b σ) := by
  intro v w he
  have hr (u : S.partialParityBand a b σ univ) :
      reflectionIsometry N (AutomorphicL2.denseEmbedding _ _ (S.newBandRepresentative a b σ u)) =
        (σ : ℂ) • AutomorphicL2.denseEmbedding _ _ (S.newBandRepresentative a b σ u) := by
    rw [S.newBandRepresentative_embedding]
    exact S.newBand_reflection a b σ hσ u
  have hf := actualHeightCoefficients_separate N _ _
    (S.newBandRepresentative_continuous a b σ v) (S.newBandRepresentative_continuous a b σ w)
    (σ : ℂ) (hr v) (hr w) he
  have h := congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N)) hf
  rw [S.newBandRepresentative_embedding, S.newBandRepresentative_embedding] at h
  exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext h)))

theorem goodPrimeHecke_actual {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) (A B : ℤ)
    (hAB : (p.val : ℤ) * A + (N : ℤ) * B = 1) (v : S.partialParityBand a b σ univ) :
    let : Fact p.val.Prime := ⟨p.property.1⟩
    ((S.goodPrimeHecke a b σ p v).val.val.val : AutomorphicSpace N) =
      HeckeL2.operator N p.val hN p.property.2 A B hAB (v.val.val.val : AutomorphicSpace N) := by
  let : Fact p.val.Prime := ⟨p.property.1⟩
  exact S.newHeckeOperator_actual p.val p.property.2 A B hAB a b σ v

theorem goodPrimeHecke_height {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) (v : S.partialParityBand a b σ univ) :
    S.newBandHeight a b σ (S.goodPrimeHecke a b σ p v) =
      heightHecke p.val p.property.1.pos (S.newBandHeight a b σ v) := by
  let : Fact p.val.Prime := ⟨p.property.1⟩
  have hc : p.val.Coprime N := p.property.1.coprime_iff_not_dvd.mpr p.property.2
  have hAB : (p.val : ℤ) * Nat.gcdA p.val N + (N : ℤ) * Nat.gcdB p.val N = 1 := by
    have h := Nat.gcd_eq_gcd_ab p.val N
    rw [hc.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have hNp : (N : ZMod p.val) ≠ 0 :=
    fun h => p.property.2 ((ZMod.natCast_eq_zero_iff N p.val).mp h)
  let f := S.newBandRepresentative a b σ v
  have hf := S.newBandRepresentative_continuous a b σ v
  have he : S.newBandRepresentative a b σ (S.goodPrimeHecke a b σ p v) =
      HeckeL2.heckeRepresentative N p.val hN p.property.2 _ _ hAB f := by
    apply continuous_representative_unique N _ _
      (S.newBandRepresentative_continuous a b σ _) (heckeRepresentative_continuous N p.val hN
        p.property.2 hNp _ _ hAB f hf)
    rw [S.newBandRepresentative_embedding, ← HeckeL2.operator_on_representatives,
      S.goodPrimeHecke_actual a b σ p _ _ hAB, S.newBandRepresentative_embedding]
  unfold newBandHeight
  rw [he]
  exact actualHeightCoefficients_hecke N p.val hN p.property.2 hNp _ _ hAB f hf

def allPrimeHecke {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (p : {p : ℕ // p.Prime}) :
    S.partialParityBand a b σ univ →ₗ[ℂ] S.partialParityBand a b σ univ :=
  if hpN : p.val ∣ N then
    (Classical.choice (S.exists_ramifiedBandOperator a b σ p.val p.property hpN)).operator
  else S.goodPrimeHecke a b σ ⟨p.val, p.property, hpN⟩

theorem allPrimeHecke_symmetric {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (p : {p : ℕ // p.Prime}) :
    (S.allPrimeHecke a b σ p).IsSymmetric := by
  unfold allPrimeHecke
  split_ifs with hpN
  · exact (Classical.choice (S.exists_ramifiedBandOperator a b σ p.val p.property hpN)).symmetric
  · exact S.goodPrimeHecke_symmetric a b σ _

theorem newBandRepresentative_smul {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (v : S.partialParityBand a b σ univ) (c : ℂ) :
    S.newBandRepresentative a b σ (c • v) = c • S.newBandRepresentative a b σ v := by
  apply continuous_representative_unique N _ _
    (S.newBandRepresentative_continuous a b σ _) 
    (continuous_const.mul (S.newBandRepresentative_continuous a b σ v))
  rw [S.newBandRepresentative_embedding, map_smul, S.newBandRepresentative_embedding]
  rfl

/-- The simultaneous spectral eigenrelations imply the literal good- and
bad-prime eigenrelations of the actual continuous representative. -/
theorem allPrimeHecke_eigen_relations {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (v : S.partialParityBand a b σ univ) (ell : ℕ → ℂ)
    (he : ∀ p : {p : ℕ // p.Prime}, S.allPrimeHecke a b σ p v = ell p.val • v) :
    (∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N),
      let : Fact p.Prime := ⟨hp⟩
      ∀ (A B : ℤ) (hAB : (p : ℤ) * A + (N : ℤ) * B = 1),
        HeckeL2.operator N p hN hpN A B hAB
          (AutomorphicL2.denseEmbedding _ _ (S.newBandRepresentative a b σ v)) =
          ell p • AutomorphicL2.denseEmbedding _ _ (S.newBandRepresentative a b σ v)) ∧
    (∀ (p : ℕ) (hp : p.Prime), p ∣ N →
      normalizedUpperBranches p hp.pos (S.newBandRepresentative a b σ v).val =
        fun z => ell p * (S.newBandRepresentative a b σ v).val z) := by
  constructor
  · intro p hp hpN _ A B hAB
    have h := he ⟨p, hp⟩
    simp only [allPrimeHecke, dite_eq_right hpN] at h
    have h' := congrArg (fun u : S.partialParityBand a b σ univ =>
      (u.val.val.val : AutomorphicSpace N)) h
    rw [S.goodPrimeHecke_actual a b σ ⟨p, hp, hpN⟩ A B hAB] at h'
    simpa only [S.newBandRepresentative_embedding, Submodule.coe_smul] using h'
  · intro p hp hpN
    let T := Classical.choice (S.exists_ramifiedBandOperator a b σ p hp hpN)
    have h := he ⟨p, hp⟩
    simp only [allPrimeHecke, dite_eq_left hpN] at h
    change T.operator v = ell p • v at h
    have ht := T.representative v (S.newBandRepresentative a b σ v)
      (S.newBandRepresentative a b σ (T.operator v))
      (S.newBandRepresentative_continuous a b σ v)
      (S.newBandRepresentative_continuous a b σ _)
      (S.newBandRepresentative_embedding a b σ v)
      (S.newBandRepresentative_embedding a b σ _)
    rw [h, S.newBandRepresentative_smul] at ht
    exact ht.symm

theorem allPrimeHecke_height {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (p : {p : ℕ // p.Prime})
    (v : S.partialParityBand a b σ univ) :
    S.newBandHeight a b σ (S.allPrimeHecke a b σ p v) =
      heightPrime N p.val p.property.pos (S.newBandHeight a b σ v) := by
  by_cases hpN : p.val ∣ N
  · let T := Classical.choice (S.exists_ramifiedBandOperator a b σ p.val p.property hpN)
    have he := T.representative v (S.newBandRepresentative a b σ v)
      (S.newBandRepresentative a b σ (T.operator v))
      (S.newBandRepresentative_continuous a b σ v)
      (S.newBandRepresentative_continuous a b σ (T.operator v))
      (S.newBandRepresentative_embedding a b σ v)
      (S.newBandRepresentative_embedding a b σ (T.operator v))
    simp only [allPrimeHecke, dite_eq_left hpN, heightPrime, ite_eq_left hpN, newBandHeight]
    rw [he, actualHeightCoefficients_upper p.val p.property.pos _
      (S.newBandRepresentative_continuous a b σ v)]
    rfl
  · simpa only [allPrimeHecke, dite_eq_right hpN, heightPrime, ite_eq_right hpN] using
      S.goodPrimeHecke_height a b σ ⟨p.val, p.property, hpN⟩ v

theorem allPrimeHecke_pairwise_commute {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (hσ : σ ^ 2 = 1) :
    Pairwise (fun p q => Commute (S.allPrimeHecke a b σ p) (S.allPrimeHecke a b σ q)) := by
  intro p q hpq
  have hc : p.val.Coprime q.val := p.property.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp hd)))
  exact linear_commute_of_coordinates (S.newBandHeight a b σ)
    (S.newBandHeight_injective a b σ hσ)
    (S.allPrimeHecke a b σ p) (S.allPrimeHecke a b σ q)
    (heightPrime N p.val p.property.pos) (heightPrime N q.val q.property.pos)
    (S.allPrimeHecke_height a b σ p) (S.allPrimeHecke_height a b σ q)
    (heightPrime_commute N p.val q.val p.property.pos q.property.pos hc)

theorem goodPrimeHecke_resolvent {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) :
    Commute (S.goodPrimeHecke a b σ p) (S.partialNewResolvent a b σ univ) := by
  let : Fact p.val.Prime := ⟨p.property.1⟩
  have hc : p.val.Coprime N := p.property.1.coprime_iff_not_dvd.mpr p.property.2
  have hAB : (p.val : ℤ) * Nat.gcdA p.val N + (N : ℤ) * Nat.gcdB p.val N = 1 := by
    have h := Nat.gcd_eq_gcd_ab p.val N
    rw [hc.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ((S.goodPrimeHecke a b σ p (S.partialNewResolvent a b σ univ v)).val.val.val :
      AutomorphicSpace N) = friedrichsResolvent N
        ((S.goodPrimeHecke a b σ p v).val.val.val : AutomorphicSpace N)
  rw [S.goodPrimeHecke_actual a b σ p _ _ hAB, S.goodPrimeHecke_actual a b σ p _ _ hAB]
  exact DFunLike.congr_fun (QuantitativeArithmeticMaassHecke.hecke_resolvent_commute
    N p.val hN p.property.2 _ _ hAB) (v.val.val.val : AutomorphicSpace N)

theorem goodPrimeHecke_fricke {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) :
    Commute (S.goodPrimeHecke a b σ p) (S.partialNewFricke a b σ univ) := by
  let : Fact p.val.Prime := ⟨p.property.1⟩
  have hc : p.val.Coprime N := p.property.1.coprime_iff_not_dvd.mpr p.property.2
  have hAB : (p.val : ℤ) * Nat.gcdA p.val N + (N : ℤ) * Nat.gcdB p.val N = 1 := by
    have h := Nat.gcd_eq_gcd_ab p.val N
    rw [hc.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ((S.goodPrimeHecke a b σ p (S.partialNewFricke a b σ univ v)).val.val.val :
      AutomorphicSpace N) = frickeIsometry N hN
        ((S.goodPrimeHecke a b σ p v).val.val.val : AutomorphicSpace N)
  rw [S.goodPrimeHecke_actual a b σ p _ _ hAB, S.goodPrimeHecke_actual a b σ p _ _ hAB]
  exact DFunLike.congr_fun (hecke_fricke_commute N p.val hN p.property.2 _ _ hAB)
    (v.val.val.val : AutomorphicSpace N)

theorem allPrimeHecke_resolvent {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (p : {p : ℕ // p.Prime}) :
    Commute (S.allPrimeHecke a b σ p) (S.partialNewResolvent a b σ univ) := by
  unfold allPrimeHecke
  split_ifs with hpN
  · exact (Classical.choice (S.exists_ramifiedBandOperator a b σ p.val p.property hpN)).resolvent_commute
  · exact S.goodPrimeHecke_resolvent a b σ _

theorem allPrimeHecke_fricke {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (p : {p : ℕ // p.Prime}) :
    Commute (S.allPrimeHecke a b σ p) (S.partialNewFricke a b σ univ) := by
  unfold allPrimeHecke
  split_ifs with hpN
  · exact (Classical.choice (S.exists_ramifiedBandOperator a b σ p.val p.property hpN)).fricke_commute
  · exact S.goodPrimeHecke_fricke a b σ _

def jointNewOperator {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    Option (Option {p : ℕ // p.Prime}) →
      (S.partialParityBand a b σ univ →ₗ[ℂ] S.partialParityBand a b σ univ)
  | none => S.partialNewResolvent a b σ univ
  | some none => S.partialNewFricke a b σ univ
  | some (some p) => S.allPrimeHecke a b σ p

theorem jointNewOperator_symmetric {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (i : Option (Option {p : ℕ // p.Prime})) : (S.jointNewOperator a b σ i).IsSymmetric := by
  cases i with
  | none => exact S.partialNewResolvent_symmetric a b σ univ
  | some i =>
    cases i with
    | none => exact S.partialNewFricke_symmetric a b σ univ
    | some p => exact S.allPrimeHecke_symmetric a b σ p

theorem jointNewOperator_commute {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (hσ : σ ^ 2 = 1)
    (i j : Option (Option {p : ℕ // p.Prime})) :
    Commute (S.jointNewOperator a b σ i) (S.jointNewOperator a b σ j) := by
  cases i with
  | none =>
    cases j with
    | none => exact Commute.refl _
    | some j =>
      cases j with
      | none => exact S.partialNewResolvent_fricke_commute a b σ univ
      | some q => exact (S.allPrimeHecke_resolvent a b σ q).symm
  | some i =>
    cases i with
    | none =>
      cases j with
      | none => exact (S.partialNewResolvent_fricke_commute a b σ univ).symm
      | some j =>
        cases j with
        | none => exact Commute.refl _
        | some q => exact (S.allPrimeHecke_fricke a b σ q).symm
    | some p =>
      cases j with
      | none => exact S.allPrimeHecke_resolvent a b σ p
      | some j =>
        cases j with
        | none => exact S.allPrimeHecke_fricke a b σ p
        | some q =>
          by_cases hpq : p = q
          · subst q; exact Commute.refl _
          · exact S.allPrimeHecke_pairwise_commute a b σ hσ hpq

set_option maxHeartbeats 4000000 in
theorem jointNewOperator_eigenvector_data {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ)
    (v : S.partialParityBand a b σ univ) (hv : v ≠ 0)
    (μ : Option (Option {p : ℕ // p.Prime}) → ℂ)
    (hμ : ∀ i, S.jointNewOperator a b σ i v = μ i • v) :
    ∃ r : ℝ, 0 ≤ r ∧ r ∈ Icc a b ∧
      ∃ χ : ℂ, (χ = 1 ∨ χ = -1) ∧
        FriedrichsGraph N (v.val.val.val : AutomorphicSpace N)
          (((1 / 4 + r ^ 2 : ℝ) : ℂ) • (v.val.val.val : AutomorphicSpace N)) ∧
        S.partialNewFricke a b σ univ v = χ • v ∧
        ∃ ell : {p : ℕ // p.Prime} → ℂ,
          ∀ p, S.allPrimeHecke a b σ p v = ell p • v := by
  have hR : S.partialNewResolvent a b σ univ v = μ none • v := hμ none
  have hW : S.partialNewFricke a b σ univ v = μ (some none) • v := hμ (some none)
  have hparam : ∃ r : ℝ, 0 ≤ r ∧ r ∈ Icc a b ∧
      FriedrichsGraph N (v.val.val.val : AutomorphicSpace N)
        (((1 / 4 + r ^ 2 : ℝ) : ℂ) • (v.val.val.val : AutomorphicSpace N)) :=
    @partialNewResolvent_eigen_parameter N _ hN S a b σ univ v hv (μ none) hR
  obtain ⟨r, hr, hwin, hg⟩ := hparam
  have hsign := involution_eigenvalue_sign (S.partialNewFricke a b σ univ)
    (S.partialNewFricke_involutive a b σ univ) v hv (μ (some none)) hW
  exact ⟨r, hr, hwin, μ (some none), hsign, hg, hW,
    (fun p => μ (some (some p))), fun p => hμ (some (some p))⟩

/-- Full simultaneous eigenfamily in the actual new-parity space, with
the original spectral parameter interval and the actual Fricke sign.
The number of vectors is the dimension of that physical space. -/
theorem exists_full_new_eigenfamily {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (hσ : σ ^ 2 = 1) :
    ∃ v : Fin (Module.finrank ℂ (S.partialParityBand a b σ univ)) →
        S.partialParityBand a b σ univ,
      LinearIndependent ℂ v ∧ ∀ j, ∃ r : ℝ, 0 ≤ r ∧ r ∈ Icc a b ∧
        ∃ χ : ℂ, (χ = 1 ∨ χ = -1) ∧
          FriedrichsGraph N ((v j).val.val.val : AutomorphicSpace N)
            (((1 / 4 + r ^ 2 : ℝ) : ℂ) • ((v j).val.val.val : AutomorphicSpace N)) ∧
          S.partialNewFricke a b σ univ (v j) = χ • v j ∧
          ∃ ell : {p : ℕ // p.Prime} → ℂ,
            ∀ p, S.allPrimeHecke a b σ p (v j) = ell p • v j := by
  let := S.band_finiteDimensional a b
  refine joint_family_of_eigenvector_property
    (S.jointNewOperator a b σ) (S.jointNewOperator_symmetric a b σ)
    (fun i j _ => S.jointNewOperator_commute a b σ hσ i j)
    (fun v => ∃ r : ℝ, 0 ≤ r ∧ r ∈ Icc a b ∧
      ∃ χ : ℂ, (χ = 1 ∨ χ = -1) ∧
        FriedrichsGraph N (v.val.val.val : AutomorphicSpace N)
          (((1 / 4 + r ^ 2 : ℝ) : ℂ) • (v.val.val.val : AutomorphicSpace N)) ∧
        S.partialNewFricke a b σ univ v = χ • v ∧
        ∃ ell : {p : ℕ // p.Prime} → ℂ,
          ∀ p, S.allPrimeHecke a b σ p v = ell p • v) ?_
  exact S.jointNewOperator_eigenvector_data a b σ

#print axioms newBandRepresentative_continuous
#print axioms newBandRepresentative_embedding
#print axioms newBand_reflection
#print axioms newBandHeight_injective
#print axioms goodPrimeHecke_actual
#print axioms goodPrimeHecke_height
#print axioms allPrimeHecke_symmetric
#print axioms newBandRepresentative_smul
#print axioms allPrimeHecke_eigen_relations
#print axioms allPrimeHecke_height
#print axioms allPrimeHecke_pairwise_commute
#print axioms goodPrimeHecke_resolvent
#print axioms goodPrimeHecke_fricke
#print axioms allPrimeHecke_resolvent
#print axioms allPrimeHecke_fricke
#print axioms jointNewOperator_symmetric
#print axioms jointNewOperator_commute
#print axioms jointNewOperator_eigenvector_data
#print axioms exists_full_new_eigenfamily

end CuspEnergySpectrum

#print axioms height_correspondences_commute
#print axioms heightPrime_commute
#print axioms involution_eigenvalue_sign
#print axioms linear_commute_of_coordinates
#print axioms joint_family_of_eigenvector_property

end QuantitativeNinaMaass
