module

public import QuantitativeNinaMaassOldBandsV1
public import AsymptoticClassicalMultiplicityRelativeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeMaass AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped InnerProductSpace

/-!
Partial newness on the actual Maass spaces and finite parity bands.
Every imposed equation is a physical finite-cover trace equation. The
generic projection lemma used below is independent of holomorphic forms;
its intertwining hypotheses are proved here for the actual Maass maps.

This chapter is a draft until its full dependency closure passes the pinned
compiler and the printed axiom audits. It contains no counting hypothesis.
-/

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance

local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

def partialNewSpace (N : ℕ) [NeZero N] (hN : 0 < N) (P : Set ℕ) :
    Submodule ℂ (AutomorphicSpace N) :=
  ⨅ p : {p : ℕ // p.Prime ∧ p ∣ N}, ⨅ (_ : p.val ∈ P),
    newTraceKernel hN (Nat.div_dvd_of_dvd p.property.2)

theorem mem_partialNewSpace (N : ℕ) [NeZero N] (hN : 0 < N) (P : Set ℕ)
    (v : AutomorphicSpace N) :
    v ∈ partialNewSpace N hN P ↔
      ∀ p : {p : ℕ // p.Prime ∧ p ∣ N}, p.val ∈ P →
        v ∈ newTraceKernel hN (Nat.div_dvd_of_dvd p.property.2) := by
  simp only [partialNewSpace, Submodule.mem_iInf]

theorem partialNewSpace_univ (N : ℕ) [NeZero N] (hN : 0 < N) :
    partialNewSpace N hN Set.univ = newSpace N hN := by
  ext v
  simp only [mem_partialNewSpace, newSpace, Submodule.mem_iInf,
    Set.mem_univ, true_implies]

theorem partialNewSpace_empty (N : ℕ) [NeZero N] (hN : 0 < N) :
    partialNewSpace N hN ∅ = ⊤ := by
  ext v
  simp only [mem_partialNewSpace, Set.mem_empty_iff_false, false_implies,
    implies_true, Submodule.mem_top]

theorem partialNewSpace_eq_newSpace_of_covers (N : ℕ) [NeZero N] (hN : 0 < N)
    (P : Set ℕ) (hP : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ P) :
    partialNewSpace N hN P = newSpace N hN := by
  ext v
  simp only [mem_partialNewSpace, newSpace, Submodule.mem_iInf]
  exact ⟨fun hv p => hv p (hP p.val p.property.1 p.property.2), fun hv p _ => hv p⟩

theorem partialNewSpace_insert (N : ℕ) [NeZero N] (hN : 0 < N) (P : Set ℕ)
    (p : {p : ℕ // p.Prime ∧ p ∣ N}) :
    partialNewSpace N hN (insert p.val P) =
      newTraceKernel hN (Nat.div_dvd_of_dvd p.property.2) ⊓ partialNewSpace N hN P := by
  ext v
  simp only [mem_partialNewSpace, Set.mem_insert_iff, Submodule.mem_inf]
  constructor
  · intro hv
    exact ⟨hv p (Or.inl rfl), fun q hq => hv q (Or.inr hq)⟩
  · rintro ⟨hp, hP⟩ q (hq | hq)
    · have he : q = p := Subtype.ext hq
      simpa only [he] using hp
    · exact hP q hq

theorem fricke_mem_partialNewSpace (N : ℕ) [NeZero N] (hN : 0 < N)
    (P : Set ℕ) (v : AutomorphicSpace N) (hv : v ∈ partialNewSpace N hN P) :
    frickeIsometry N hN v ∈ partialNewSpace N hN P := by
  rw [mem_partialNewSpace] at hv ⊢
  exact fun p hp => newTraceKernel_fricke hN _ v (hv p hp)

theorem levelCover_preserves_prime_new (M p q : ℕ) [NeZero M]
    (hM : 0 < M) (hp : p.Prime) (hq : q.Prime) (hqM : q ∣ M)
    (hc : p.Coprime q)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M))
    (hf : Continuous f.val)
    (hnew : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel hM (Nat.div_dvd_of_dvd hqM)) :
    let : NeZero p := ⟨hp.ne_zero⟩
    levelCover (Nat.dvd_mul_left M p) (AutomorphicL2.denseEmbedding _ _ f) ∈
      newTraceKernel (Nat.mul_pos hp.pos hM)
        (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right hqM p)) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨L, hL⟩ := hqM
  subst M
  have hLpos : 0 < L := by
    by_contra he
    have hz : L = 0 := by omega
    simp [hz] at hM
  let : NeZero L := ⟨hLpos.ne'⟩
  have hs : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel (Nat.mul_pos hq.pos hLpos) (Nat.dvd_mul_left L q) := by
    simpa only [Nat.mul_div_cancel_left L hq.pos] using hnew
  have ht := ordinary_cover_cross_new_continuous L p q hLpos hp.pos hq hc f hf hs
  have hd : p * (q * L) / q = p * L := by
    rw [Nat.mul_left_comm p q L, Nat.mul_div_cancel_left (p * L) hq.pos]
  simpa only [hd] using ht

/-- A new ordinary prime cover preserves all previously imposed trace
equations. Existing primes may have higher valuation, including 2. -/
theorem levelCover_partialNewSpace_continuous (M p : ℕ) [NeZero M]
    (hM : 0 < M) (hp : p.Prime) (P : Set ℕ) (hpP : p ∉ P)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M))
    (hf : Continuous f.val)
    (hv : AutomorphicL2.denseEmbedding _ _ f ∈ partialNewSpace M hM P) :
    let : NeZero p := ⟨hp.ne_zero⟩
    levelCover (Nat.dvd_mul_left M p) (AutomorphicL2.denseEmbedding _ _ f) ∈
      partialNewSpace (p * M) (Nat.mul_pos hp.pos hM) P := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [mem_partialNewSpace] at hv ⊢
  intro q hqP
  have hne : q.val ≠ p := fun he => hpP (he ▸ hqP)
  have hn : ¬ q.val ∣ p := fun hd =>
    hne ((Nat.prime_dvd_prime_iff_eq q.property.1 hp).mp hd)
  have hqM : q.val ∣ M := (q.property.1.dvd_mul.mp q.property.2).resolve_left hn
  have hc : p.Coprime q.val := (q.property.1.coprime_iff_not_dvd.mpr hn).symm
  exact levelCover_preserves_prime_new M p q.val hM hp q.property.1 hqM hc f hf
    (hv ⟨q.val, q.property.1, hqM⟩ hqP)

theorem levelTrace_preserves_prime_new (M p q : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hqM : q ∣ M)
    (v : AutomorphicSpace (p * M))
    (hnew : v ∈ newTraceKernel (Nat.mul_pos hp hM)
      (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right hqM p))) :
    levelTrace (Nat.dvd_mul_left M p) v ∈
      newTraceKernel hM (Nat.div_dvd_of_dvd hqM) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨L, hL⟩ := hqM
  subst M
  have hLpos : 0 < L := by
    by_contra he
    have hz : L = 0 := by omega
    simp [hz] at hM
  let : NeZero L := ⟨hLpos.ne'⟩
  have hd : p * (q * L) / q = p * L := by
    rw [Nat.mul_left_comm p q L, Nat.mul_div_cancel_left (p * L) hq.pos]
  have hs : v ∈ newTraceKernel (Nat.mul_pos hp (Nat.mul_pos hq.pos hLpos))
      (show p * L ∣ p * (q * L) from ⟨q, by ring⟩) := by
    simpa only [hd] using hnew
  have ht := levelTrace_cross_new L p q hLpos hp hq.pos v hs
  simpa only [Nat.mul_div_cancel_left L hq.pos] using ht

/-- Actual adjoint traces preserve partial newness without any regularity
assumption on the input vector. -/
theorem levelTrace_partialNewSpace (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : 0 < p) (P : Set ℕ) (v : AutomorphicSpace (p * M))
    (hv : v ∈ partialNewSpace (p * M) (Nat.mul_pos hp hM) P) :
    levelTrace (Nat.dvd_mul_left M p) v ∈ partialNewSpace M hM P := by
  rw [mem_partialNewSpace] at hv ⊢
  intro q hqP
  exact levelTrace_preserves_prime_new M p q.val hM hp q.property.1 q.property.2 v
    (hv ⟨q.val, q.property.1, dvd_mul_of_dvd_right q.property.2 p⟩ hqP)

/-- Rank arithmetic is kept abstract; all geometric preservation and
overlap statements are supplied by their proved physical counterparts. -/
theorem relative_new_finrank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (V A B K : Submodule ℂ E) [CompleteSpace V]
    (hA : ∀ x ∈ A, V.starProjection x ∈ A)
    (hB : ∀ x ∈ B, V.starProjection x ∈ B)
    (hd : Disjoint A B) (n : ℕ)
    (ha : Module.finrank ℂ ↥(A ⊓ V) = n) (hb : Module.finrank ℂ ↥(B ⊓ V) = n)
    (hK : K = (A ⊔ B)ᗮ ⊓ V) :
    Module.finrank ℂ K + 2 * n = Module.finrank ℂ V := by
  have h := AsymptoticClassicalCusp.relative_two_old_finrank V A B hA hB
  rw [hd.eq_bot, bot_inf_eq, finrank_bot, add_zero, ha, hb, ← hK] at h
  omega

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
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance

/-- The ambient physical vector map from a fixed geometric parity band. -/
def parityAmbientMap {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    S.parityBand a b σ →ₗ[ℂ] AutomorphicSpace N :=
  ((localCuspidalSpace N hN).subtype.comp (S.band a b).subtype).comp
    (S.parityBand a b σ).subtype

def partialParityBand {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    Submodule ℂ (S.parityBand a b σ) :=
  (partialNewSpace N hN P).comap (S.parityAmbientMap a b σ)

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    FiniteDimensional ℂ (S.partialParityBand a b σ P) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    CompleteSpace (S.partialParityBand a b σ P) := FiniteDimensional.complete ℂ _

theorem mem_partialParityBand {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ)
    (v : S.parityBand a b σ) :
    v ∈ S.partialParityBand a b σ P ↔
      (v.val.val : AutomorphicSpace N) ∈ partialNewSpace N hN P := Iff.rfl

theorem partialParityBand_empty {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) : S.partialParityBand a b σ ∅ = ⊤ := by
  rw [partialParityBand, partialNewSpace_empty, Submodule.comap_top]

theorem coverParityBandMap_partialNew (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : p.Prime)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM))
    (a b σ : ℝ) (P : Set ℕ) (hpP : p ∉ P)
    (v : S.parityBand a b σ) (hv : v ∈ S.partialParityBand a b σ P) :
    S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ v ∈ T.partialParityBand a b σ P := by
  obtain ⟨f, hf, he⟩ := exists_continuous_window_representative M hM
    S.basis S.energy S.energy_nonneg S.graph a b v.val.val v.val.property
  have hh := levelCover_partialNewSpace_continuous M p hM hp P hpP f hf (by
    rw [he]
    exact hv)
  rw [he] at hh
  exact hh

theorem traceParityBandMap_partialNew (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : 0 < p)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp hM))
    (a b σ : ℝ) (P : Set ℕ)
    (v : T.parityBand a b σ) (hv : v ∈ T.partialParityBand a b σ P) :
    S.traceParityBandMap T (Nat.dvd_mul_left M p) a b σ v ∈ S.partialParityBand a b σ P :=
  levelTrace_partialNewSpace M p hM hp P (v.val.val : AutomorphicSpace (p * M)) hv

theorem frickeParityBandMap_partialNew {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ)
    (v : S.parityBand a b σ) (hv : v ∈ S.partialParityBand a b σ P) :
    S.frickeParityBandMap a b σ v ∈ S.partialParityBand a b σ P :=
  fricke_mem_partialNewSpace N hN P (v.val.val : AutomorphicSpace N) hv

/-- Both sides of the adjoint pair preserve the imposed prime conditions,
so the actual ordinary cover intertwines the orthogonal projections. -/
theorem cover_partial_projection (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : p.Prime)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM))
    (a b σ : ℝ) (P : Set ℕ) (hpP : p ∉ P) (v : S.parityBand a b σ) :
    let := S.band_finiteDimensional a b
    let := T.band_finiteDimensional a b
    (T.partialParityBand a b σ P).starProjection
        (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ v) =
      S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ
        ((S.partialParityBand a b σ P).starProjection v) := by
  let := S.band_finiteDimensional a b
  let := T.band_finiteDimensional a b
  apply AsymptoticClassicalCusp.projection_intertwine_of_adjoint
    (S.partialParityBand a b σ P) (T.partialParityBand a b σ P)
    (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ)
    (S.traceParityBandMap T (Nat.dvd_mul_left M p) a b σ)
  · intro y x
    change ⟪S.traceBandMap T (Nat.dvd_mul_left M p) a b y.val, x.val⟫_ℂ =
      ⟪y.val, S.coverBandMap T (Nat.dvd_mul_left M p) a b x.val⟫_ℂ
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ)
      (S.traceBandMap_pairing T (Nat.dvd_mul_left M p) a b x.val y.val)
  · exact coverParityBandMap_partialNew M p hM hp S T a b σ P hpP
  · exact traceParityBandMap_partialNew M p hM hp.pos S T a b σ P

/-- Global Fricke also intertwines the projection onto every partial
newspace, within the unchanged reflection-parity band. -/
theorem fricke_partial_projection {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ)
    (v : S.parityBand a b σ) :
    let := S.band_finiteDimensional a b
    (S.partialParityBand a b σ P).starProjection (S.frickeParityBandMap a b σ v) =
      S.frickeParityBandMap a b σ ((S.partialParityBand a b σ P).starProjection v) := by
  let := S.band_finiteDimensional a b
  apply AsymptoticClassicalCusp.projection_intertwine_of_adjoint
    (S.partialParityBand a b σ P) (S.partialParityBand a b σ P)
    (S.frickeParityBandMap a b σ) (S.frickeParityBandMap a b σ)
  · intro y x
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (frickeIsometry_selfAdjoint N hN) (y.val.val : AutomorphicSpace N)
        (x.val.val : AutomorphicSpace N)
  · exact S.frickeParityBandMap_partialNew a b σ P
  · exact S.frickeParityBandMap_partialNew a b σ P

/-- The old image inside a partial newspace is exactly the image of the
lower-level partial newspace. The preimage is constructed by projection. -/
theorem cover_partial_range (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : p.Prime)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM))
    (a b σ : ℝ) (P : Set ℕ) (hpP : p ∉ P) :
    (S.partialParityBand a b σ P).map (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ) =
      (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ).range ⊓
        T.partialParityBand a b σ P := by
  let := S.band_finiteDimensional a b
  let := T.band_finiteDimensional a b
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, coverParityBandMap_partialNew M p hM hp S T a b σ P hpP x hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨(S.partialParityBand a b σ P).starProjection x,
      (S.partialParityBand a b σ P).starProjection_apply_mem x, ?_⟩
    rw [← cover_partial_projection M p hM hp S T a b σ P hpP,
      (T.partialParityBand a b σ P).starProjection_eq_self_iff.mpr hx]

theorem fricke_map_inf_partial {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ)
    (A : Submodule ℂ (S.parityBand a b σ)) :
    (A ⊓ S.partialParityBand a b σ P).map (S.frickeParityBandMap a b σ) =
      A.map (S.frickeParityBandMap a b σ) ⊓ S.partialParityBand a b σ P := by
  ext v
  constructor
  · rintro ⟨x, ⟨hxA, hxP⟩, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, S.frickeParityBandMap_partialNew a b σ P x hxP⟩
  · rintro ⟨⟨x, hx, rfl⟩, hv⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    have hh := S.frickeParityBandMap_partialNew a b σ P _ hv
    rw [S.frickeParityBandMap_involutive a b σ x] at hh
    exact hh

/-- Adding the new prime imposes exactly its pair of physical trace
equations on the previously selected parity band. -/
theorem partialParityBand_insert (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : p.Prime)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM))
    (a b σ : ℝ) (P : Set ℕ) :
    T.partialParityBand a b σ (insert p P) =
      S.traceNewParityBand T (Nat.dvd_mul_left M p) a b σ ⊓ T.partialParityBand a b σ P := by
  ext v
  rw [mem_partialParityBand, partialNewSpace_insert (p * M) (Nat.mul_pos hp.pos hM) P
    ⟨p, hp, Nat.dvd_mul_right p M⟩]
  simp only [Submodule.mem_inf, mem_traceNewParityBand, mem_partialParityBand,
    Nat.mul_div_cancel_left M hp.pos]

/-- The exact relative recurrence at a simply ramified prime. This
removes two copies of the lower partial newspace, preserving the original
spectral interval and reflection parity, including any earlier condition
at the repeated prime 2. -/
theorem partialParityBand_simple_finrank (M p : ℕ) [NeZero M] [NeZero p]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM))
    (a b σ : ℝ) (P : Set ℕ) (hpP : p ∉ P) :
    Module.finrank ℂ (T.partialParityBand a b σ (insert p P)) +
      2 * Module.finrank ℂ (S.partialParityBand a b σ P) =
        Module.finrank ℂ (T.partialParityBand a b σ P) := by
  let := S.band_finiteDimensional a b
  let := T.band_finiteDimensional a b
  let C := S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ
  let W := T.frickeParityBandMap a b σ
  let A := C.range
  let B := (W.comp C).range
  let V := T.partialParityBand a b σ P
  have hA : ∀ x ∈ A, V.starProjection x ∈ A := by
    rintro x ⟨u, rfl⟩
    change (T.partialParityBand a b σ P).starProjection
      (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ u) ∈ C.range
    rw [cover_partial_projection M p hM hp S T a b σ P hpP]
    exact ⟨_, rfl⟩
  have hB : ∀ x ∈ B, V.starProjection x ∈ B := by
    rintro x ⟨u, rfl⟩
    change (T.partialParityBand a b σ P).starProjection
      (T.frickeParityBandMap a b σ (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ u)) ∈ B
    rw [fricke_partial_projection, cover_partial_projection M p hM hp S T a b σ P hpP]
    exact ⟨_, rfl⟩
  have hdimA : Module.finrank ℂ ↥(A ⊓ V) = Module.finrank ℂ (S.partialParityBand a b σ P) := by
    rw [← cover_partial_range M p hM hp S T a b σ P hpP]
    exact AsymptoticClassicalCusp.finrank_map_of_injective _ _
      (S.coverParityBandMap_injective T (Nat.dvd_mul_left M p) a b σ)
  have hmap : (A ⊓ V).map W = B ⊓ V := by
    rw [T.fricke_map_inf_partial a b σ P A]
    change A.map W ⊓ V = (W.comp C).range ⊓ V
    rw [LinearMap.range_comp]
  have hdimB : Module.finrank ℂ ↥(B ⊓ V) = Module.finrank ℂ ↥(A ⊓ V) := by
    rw [← hmap]
    exact AsymptoticClassicalCusp.finrank_map_of_injective _ _
      (T.frickeParityBandMap_involutive a b σ).injective
  have hAB : Disjoint A B := simple_old_parity_disjoint M p hM hp hcp S T a b σ
  have hK : T.partialParityBand a b σ (insert p P) = (A ⊔ B)ᗮ ⊓ V :=
    (partialParityBand_insert M p hM hp S T a b σ P).trans
      (congrArg (fun K => K ⊓ V)
        (S.traceNewParityBand_orthogonal T (Nat.dvd_mul_left M p) a b σ))
  exact relative_new_finrank V A B _ hA hB hAB _ hdimA (hdimB.trans hdimA) hK

#print axioms mem_partialParityBand
#print axioms partialParityBand_empty
#print axioms coverParityBandMap_partialNew
#print axioms traceParityBandMap_partialNew
#print axioms frickeParityBandMap_partialNew
#print axioms cover_partial_projection
#print axioms fricke_partial_projection
#print axioms cover_partial_range
#print axioms fricke_map_inf_partial
#print axioms partialParityBand_insert
#print axioms partialParityBand_simple_finrank

end CuspEnergySpectrum

#print axioms mem_partialNewSpace
#print axioms partialNewSpace_univ
#print axioms partialNewSpace_empty
#print axioms partialNewSpace_eq_newSpace_of_covers
#print axioms partialNewSpace_insert
#print axioms fricke_mem_partialNewSpace
#print axioms levelCover_preserves_prime_new
#print axioms levelTrace_preserves_prime_new
#print axioms levelCover_partialNewSpace_continuous
#print axioms levelTrace_partialNewSpace
#print axioms relative_new_finrank

end QuantitativeNinaMaass
