module

public import QuantitativeNinaMaassOldDescentV1
public import QuantitativeNinaMaassTraceDiamondsV1
public import QuantitativeMaassCuspEigenWindowV1
public import QuantitativeMaassSpectralWindowInvariantV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeMaass AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticClassicalCusp
open scoped Topology InnerProductSpace

/-!
The actual level, trace and Fricke maps on finite cuspidal spectral bands.
The spectrum bundle below merely packages the already constructed geometric
energy basis. Its canonical constructor uses that existence theorem. It
contains no newform decomposition, coefficient map, or counting assumption.
-/

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance

local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

/-- The general representative theorem specializes to the actual principal
band; its spectral-window definition is used only at this stage. -/
theorem exists_continuous_window_representative {κ : Type*} (N : ℕ) (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
      ((e j : ℂ) • (basis j : AutomorphicSpace N)))
    (a b : ℝ) (x : localCuspidalSpace N hN)
    (hx : x ∈ cuspPrincipalWindowSpace N hN basis e a b) :
    ∃ f : AutomorphicL2.representatives (gamma N) (quotientMeasure N),
      Continuous f.val ∧ AutomorphicL2.denseEmbedding _ _ f = (x : AutomorphicSpace N) :=
  exists_continuous_span_representative N hN basis e henergy hgraph
    (principalWindowIndices e a b) x hx

#print axioms exists_continuous_window_representative

/-- The simply ramified overlap vanishes on the whole actual principal
spectral band, including sums of different eigenvalues. Hence it vanishes
on either reflection-parity subspace of that band as well. -/
theorem simple_old_window_intersection_zero {κ : Type*} (M p : ℕ) [NeZero (p * M)]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace (p * M) (Nat.mul_pos hp.pos hM)))
    (e : κ → ℝ) (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph (p * M) (basis j : AutomorphicSpace (p * M))
      ((e j : ℂ) • (basis j : AutomorphicSpace (p * M)))) (a b : ℝ)
    (v : cuspPrincipalWindowSpace (p * M) (Nat.mul_pos hp.pos hM) basis e a b)
    (hold : (v.val : AutomorphicSpace (p * M)) ∈ (levelCover (Nat.dvd_mul_left M p)).range ⊓
      ((frickeIsometry (p * M) (Nat.mul_pos hp.pos hM)).toContinuousLinearMap.comp
        (levelCover (Nat.dvd_mul_left M p))).range) : v = 0 := by
  obtain ⟨f, hf, hfv⟩ := exists_continuous_window_representative (p * M)
    (Nat.mul_pos hp.pos hM) basis e henergy hgraph a b v.val v.property
  have hz := continuous_simple_old_intersection_zero M p hM hp hcp f hf
    (by rw [hfv]; exact v.val.property) (by rw [hfv]; exact hold)
  rw [hfv] at hz
  exact Subtype.ext (Subtype.ext hz)

#print axioms simple_old_window_intersection_zero

/-- Restriction of an intertwiner to the ranges of two actual projections. -/
def projectedRangeMap {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (P : E →ₗ[ℂ] E) (Q : F →ₗ[ℂ] F)
    (f : E →ₗ[ℂ] F) (h : ∀ x, f (P x) = Q (f x)) : P.range →ₗ[ℂ] Q.range :=
  f.restrict (by rintro _ ⟨x, rfl⟩; exact ⟨f x, (h x).symm⟩)

/-- An old preimage of a projected vector can itself be projected. This
does not assume that a chosen preimage already has the required parity. -/
theorem projectedRangeMap_range_iff {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (P : E →ₗ[ℂ] E) (Q : F →ₗ[ℂ] F)
    (f : E →ₗ[ℂ] F) (h : ∀ x, f (P x) = Q (f x))
    (hQ : IsIdempotentElem Q) (v : Q.range) :
    v ∈ (projectedRangeMap P Q f h).range ↔ v.val ∈ f.range := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.val, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨P x, ⟨x, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change f (P x) = v.val
    rw [h, hx]
    obtain ⟨w, hw⟩ := v.property
    rw [← hw]
    exact DFunLike.congr_fun hQ w

structure CuspEnergySpectrum (N : ℕ) (hN : 0 < N) where
  Index : Type
  basis : HilbertBasis Index ℂ (localCuspidalSpace N hN)
  energy : Index → ℝ
  energy_nonneg : ∀ j, 0 ≤ energy j
  graph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
    ((energy j : ℂ) • (basis j : AutomorphicSpace N))

/-- Kernel/range orthogonality needs the actual pairing identity only. -/
theorem paired_kernel_eq_range_orthogonal {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (C : E →ₗ[ℂ] F) (D : F →ₗ[ℂ] E)
    (h : ∀ x y, inner ℂ x (D y) = inner ℂ (C x) y) : D.ker = C.rangeᗮ := by
  apply Submodule.ext
  intro y
  constructor
  · intro hy
    change D y = 0 at hy
    apply (Submodule.mem_orthogonal C.range y).mpr
    rintro _ ⟨x, rfl⟩
    rw [← h, hy, inner_zero_right]
  · intro hy
    change D y = 0
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [h]
    exact (Submodule.mem_orthogonal C.range y).mp hy (C (D y)) ⟨D y, rfl⟩

theorem paired_two_kernel_orthogonal {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (C : E →ₗ[ℂ] F) (D : F →ₗ[ℂ] E) (W : F →ₗ[ℂ] F)
    (hC : ∀ x y, inner ℂ x (D y) = inner ℂ (C x) y)
    (hW : ∀ x y, inner ℂ x (W y) = inner ℂ (W x) y) :
    D.ker ⊓ (D.comp W).ker = (C.range ⊔ (W.comp C).range)ᗮ := by
  have hWC : ∀ x y, inner ℂ x ((D.comp W) y) = inner ℂ ((W.comp C) x) y := by
    intro x y
    change inner ℂ x (D (W y)) = inner ℂ (W (C x)) y
    rw [hC, hW]
  rw [paired_kernel_eq_range_orthogonal C D hC,
    paired_kernel_eq_range_orthogonal (W.comp C) (D.comp W) hWC,
    Submodule.inf_orthogonal]

/-- These dimension identities are proved with abstract maps so that the
kernel need not unfold the physical operators during rank arithmetic. -/
theorem disjoint_injective_ranges_finrank {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (f g : E →ₗ[ℂ] F) (hf : Function.Injective f) (hg : Function.Injective g)
    (hd : Disjoint f.range g.range) :
    Module.finrank ℂ ↥(f.range ⊔ g.range) = 2 * Module.finrank ℂ E := by
  have he := Submodule.finrank_sup_add_finrank_inf_eq f.range g.range
  rw [hd.eq_bot, finrank_bot, add_zero,
    LinearMap.finrank_range_of_inj hf, LinearMap.finrank_range_of_inj hg] at he
  simpa only [two_mul] using he

theorem orthogonal_injective_ranges_finrank {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (f g : E →ₗ[ℂ] F) (hf : Function.Injective f) (hg : Function.Injective g) :
    Module.finrank ℂ (f.range ⊔ g.range)ᗮ + 2 * Module.finrank ℂ E =
      Module.finrank ℂ F + Module.finrank ℂ ↥(f.range ⊓ g.range) := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq f.range g.range
  rw [LinearMap.finrank_range_of_inj hf, LinearMap.finrank_range_of_inj hg] at hs
  have ho := Submodule.finrank_add_finrank_orthogonal (f.range ⊔ g.range)
  omega

theorem orthogonal_disjoint_injective_ranges_finrank {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (f g : E →ₗ[ℂ] F) (hf : Function.Injective f) (hg : Function.Injective g)
    (hd : Disjoint f.range g.range) :
    Module.finrank ℂ (f.range ⊔ g.range)ᗮ + 2 * Module.finrank ℂ E =
      Module.finrank ℂ F := by
  have h := orthogonal_injective_ranges_finrank f g hf hg
  rw [hd.eq_bot, finrank_bot, add_zero] at h
  exact h

/-- Substitute a proved physical overlap dimension without unfolding the
underlying operators during arithmetic on ranks. -/
theorem paired_new_finrank_of_overlap {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (f g : E →ₗ[ℂ] F) (hf : Function.Injective f) (hg : Function.Injective g)
    (K : Submodule ℂ F) (hK : K = (f.range ⊔ g.range)ᗮ)
    (k : ℕ) (hk : Module.finrank ℂ ↥(f.range ⊓ g.range) = k) :
    Module.finrank ℂ K + 2 * Module.finrank ℂ E = Module.finrank ℂ F + k := by
  rw [hK, ← hk]
  exact orthogonal_injective_ranges_finrank f g hf hg

/-- A spectrum of the actual cusp space, constructed at every positive level. -/
def geometricCuspSpectrum (N : ℕ) (hN : 0 < N) : CuspEnergySpectrum N hN := by
  exact Classical.choice (show Nonempty (CuspEnergySpectrum N hN) from by
    obtain ⟨κ, basis, e, he, hgraph, _⟩ :=
      QuantitativeArithmeticMaassCuspBand.exists_cuspidal_energy_basis N hN
    exact ⟨⟨κ, basis, e, he, hgraph⟩⟩)

namespace CuspEnergySpectrum

abbrev band {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    Submodule ℂ (localCuspidalSpace N hN) :=
  cuspPrincipalWindowSpace N hN S.basis S.energy a b

local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance

local instance {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

theorem band_finiteDimensional {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) : FiniteDimensional ℂ (S.band a b) :=
  cuspPrincipalWindowSpace_finiteDimensional N hN S.basis S.energy S.energy_nonneg S.graph a b

/-- A graph- and cusp-preserving operator between two actual levels maps
the identical principal interval into the target's actual spectral band. -/
theorem map_mem_band {M N : ℕ} {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (U : AutomorphicSpace M →L[ℂ] AutomorphicSpace N)
    (hc : ∀ x, x ∈ localCuspidalSpace M hM → U x ∈ localCuspidalSpace N hN)
    (hg : ∀ x y, FriedrichsGraph M x y → FriedrichsGraph N (U x) (U y))
    (a b : ℝ) (x : localCuspidalSpace M hM) (hx : x ∈ S.band a b) :
    U.toLinearMap.restrict hc x ∈ T.band a b := by
  let L := U.toLinearMap.restrict hc
  have hgen (j : principalWindowIndices S.energy a b) : L (S.basis j.val) ∈ T.band a b := by
    have he : 1 / 4 + (Real.sqrt (S.energy j.val - 1 / 4)) ^ 2 = S.energy j.val := by
      rw [Real.sq_sqrt (sub_nonneg.mpr j.property.1)]
      ring
    apply cusp_principal_eigen_mem_window N hN T.basis T.energy T.energy_nonneg T.graph
      a b (Real.sqrt (S.energy j.val - 1 / 4)) (Real.sqrt_nonneg _) j.property.2
    change FriedrichsGraph N (U (S.basis j.val : AutomorphicSpace M))
      (((1 / 4 + (Real.sqrt (S.energy j.val - 1 / 4)) ^ 2 : ℝ) : ℂ) •
        U (S.basis j.val : AutomorphicSpace M))
    rw [he]
    simpa only [map_smul] using hg _ _ (S.graph j.val)
  change L x ∈ T.band a b
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact hgen j
  | zero => simpa only [map_zero] using (T.band a b).zero_mem
  | add y z _ _ hy hz => simpa only [map_add] using (T.band a b).add_mem hy hz
  | smul c y _ hy => simpa only [map_smul] using (T.band a b).smul_mem c hy

def bandMap {M N : ℕ} {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (U : AutomorphicSpace M →L[ℂ] AutomorphicSpace N)
    (hc : ∀ x, x ∈ localCuspidalSpace M hM → U x ∈ localCuspidalSpace N hN)
    (hg : ∀ x y, FriedrichsGraph M x y → FriedrichsGraph N (U x) (U y)) (a b : ℝ) :
    S.band a b →ₗ[ℂ] T.band a b :=
  (U.toLinearMap.restrict hc).restrict (S.map_mem_band T U hc hg a b)

theorem bandMap_injective {M N : ℕ} {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (U : AutomorphicSpace M →L[ℂ] AutomorphicSpace N)
    (hc : ∀ x, x ∈ localCuspidalSpace M hM → U x ∈ localCuspidalSpace N hN)
    (hg : ∀ x y, FriedrichsGraph M x y → FriedrichsGraph N (U x) (U y))
    (hU : Function.Injective U) (a b : ℝ) : Function.Injective (S.bandMap T U hc hg a b) := by
  intro x y he
  have hh := congrArg (fun v : T.band a b => (v.val : AutomorphicSpace N)) he
  exact Subtype.ext (Subtype.ext (hU hh))

/-- The literal finite-cover pullback on the two geometric spectral bands. -/
def coverBandMap {M N : ℕ} [NeZero M] [NeZero N] {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b : ℝ) : S.band a b →ₗ[ℂ] T.band a b :=
  S.bandMap T (levelCover hMN)
    (fun v hv => (levelCover_mem_cuspidal_iff hM hN hMN v).mpr hv)
    (fun _ _ h => levelCover_friedrichsGraph hMN h) a b

/-- The literal adjoint trace on those same intervals. -/
def traceBandMap {M N : ℕ} [NeZero M] [NeZero N] {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b : ℝ) : T.band a b →ₗ[ℂ] S.band a b :=
  T.bandMap S (levelTrace hMN) (levelTrace_mem_cuspidal hM hN hMN)
    (fun _ _ h => levelTrace_friedrichsGraph hMN h) a b

def frickeBandMap {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    S.band a b →ₗ[ℂ] S.band a b :=
  S.bandMap S (frickeIsometry N hN).toContinuousLinearMap (fricke_mem_cuspidal N hN)
    (fun _ _ h => fricke_friedrichsGraph N hN h) a b

theorem coverBandMap_injective {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b : ℝ) : Function.Injective (S.coverBandMap T hMN a b) :=
  S.bandMap_injective T _ _ _ (levelCover_injective hMN) a b

theorem traceBandMap_coverBandMap {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b : ℝ) (v : S.band a b) :
    S.traceBandMap T hMN a b (S.coverBandMap T hMN a b v) =
      (Nat.card (AsymptoticCongruenceStrip.gamma M ⧸
        (AsymptoticCongruenceStrip.gamma N).subgroupOf (AsymptoticCongruenceStrip.gamma M)) : ℂ) • v := by
  apply Subtype.ext
  apply Subtype.ext
  exact levelTrace_cover hMN (v.val : AutomorphicSpace M)

/-- The finite-band trace has the genuine inner-product adjoint identity. -/
theorem traceBandMap_pairing {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b : ℝ) (v : S.band a b) (w : T.band a b) :
    inner ℂ v (S.traceBandMap T hMN a b w) = inner ℂ (S.coverBandMap T hMN a b v) w :=
  ContinuousLinearMap.adjoint_inner_right (levelCover hMN)
    (v.val : AutomorphicSpace M) (w.val : AutomorphicSpace N)

theorem frickeBandMap_involutive {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) : Function.Involutive (S.frickeBandMap a b) := by
  intro v
  apply Subtype.ext
  apply Subtype.ext
  exact frickeIsometry_involutive N hN (v.val : AutomorphicSpace N)

/-- Both ordinary and Fricke old inclusions preserve a distinct prime's
newform equations on the actual spectral band. Continuity is constructed
from the geometric basis, rather than imposed on the vector. -/
theorem coverBandMap_cross_new (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hc : p.Coprime q)
    (S : CuspEnergySpectrum (q * M) (Nat.mul_pos hq.pos hM))
    (T : CuspEnergySpectrum (p * (q * M)) (Nat.mul_pos hp (Nat.mul_pos hq.pos hM)))
    (a b : ℝ) (v : S.band a b)
    (hv : (v.val : AutomorphicSpace (q * M)) ∈
      newTraceKernel (Nat.mul_pos hq.pos hM) (Nat.dvd_mul_left M q)) :
    ((S.coverBandMap T (Nat.dvd_mul_left (q * M) p) a b v).val :
      AutomorphicSpace (p * (q * M))) ∈
        newTraceKernel (Nat.mul_pos hp (Nat.mul_pos hq.pos hM))
          (show p * M ∣ p * (q * M) from ⟨q, by ring⟩) ∧
    ((T.frickeBandMap a b (S.coverBandMap T (Nat.dvd_mul_left (q * M) p) a b v)).val :
      AutomorphicSpace (p * (q * M))) ∈
        newTraceKernel (Nat.mul_pos hp (Nat.mul_pos hq.pos hM))
          (show p * M ∣ p * (q * M) from ⟨q, by ring⟩) := by
  obtain ⟨f, hf, he⟩ := exists_continuous_window_representative (q * M)
    (Nat.mul_pos hq.pos hM) S.basis S.energy S.energy_nonneg S.graph a b v.val v.property
  have hh := ordinary_cover_cross_new_continuous M p q hM hp hq hc f hf (by rwa [he])
  rw [he] at hh
  exact ⟨hh, newTraceKernel_fricke _ _ _ hh⟩

/-- Restricting the cover to spectral bands loses no old vectors. A
preimage in the matching lower band is constructed by normalized trace. -/
theorem coverBandMap_range_iff {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b : ℝ) (v : T.band a b) :
    v ∈ (S.coverBandMap T hMN a b).range ↔
      (v.val : AutomorphicSpace N) ∈ (levelCover hMN).range := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(x.val : AutomorphicSpace M),
      congrArg (fun y : T.band a b => (y.val : AutomorphicSpace N)) hx⟩
  · rintro ⟨x, hx⟩
    change levelCover hMN x = (v.val : AutomorphicSpace N) at hx
    let d : ℂ := Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M))
    have hd : d ≠ 0 := by
      dsimp [d]
      exact_mod_cast (Nat.card_pos (α := gamma M ⧸ (gamma N).subgroupOf (gamma M))).ne'
    refine ⟨d⁻¹ • S.traceBandMap T hMN a b v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change levelCover hMN (d⁻¹ • levelTrace hMN (v.val : AutomorphicSpace N)) =
      (v.val : AutomorphicSpace N)
    rw [← hx, levelTrace_cover]
    change levelCover hMN (d⁻¹ • (d • x)) = levelCover hMN x
    rw [smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem frickeCoverBandMap_range_iff {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b : ℝ) (v : T.band a b) :
    v ∈ ((T.frickeBandMap a b).comp (S.coverBandMap T hMN a b)).range ↔
      (v.val : AutomorphicSpace N) ∈
        ((frickeIsometry N hN).toContinuousLinearMap.comp (levelCover hMN)).range := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(x.val : AutomorphicSpace M),
      congrArg (fun y : T.band a b => (y.val : AutomorphicSpace N)) hx⟩
  · rintro ⟨x, hx⟩
    have hcover : T.frickeBandMap a b v ∈ (S.coverBandMap T hMN a b).range := by
      apply (S.coverBandMap_range_iff T hMN a b _).mpr
      refine ⟨x, ?_⟩
      change levelCover hMN x = frickeIsometry N hN (v.val : AutomorphicSpace N)
      have hh := congrArg (frickeIsometry N hN) hx
      change frickeIsometry N hN (frickeIsometry N hN (levelCover hMN x)) =
        frickeIsometry N hN (v.val : AutomorphicSpace N) at hh
      rwa [frickeIsometry_involutive N hN _] at hh
    obtain ⟨u, hu⟩ := hcover
    refine ⟨u, ?_⟩
    change T.frickeBandMap a b (S.coverBandMap T hMN a b u) = v
    rw [hu]
    exact T.frickeBandMap_involutive a b v

/-- At a repeated prime with prime intervening group index, the actual
old-band overlap is exactly the two-step lower band. This is a range
identity of the constructed operators, proved from the generated group. -/
theorem repeated_old_band_intersection (L p : ℕ) [NeZero L] [NeZero (p * L)]
    [NeZero (p * (p * L))] (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime)
    (S : CuspEnergySpectrum L hL)
    (T : CuspEnergySpectrum (p * L) (Nat.mul_pos hp.pos hL))
    (V : CuspEnergySpectrum (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)))
    (a b : ℝ) :
    (T.coverBandMap V (Nat.dvd_mul_left (p * L) p) a b).range ⊓
      ((V.frickeBandMap a b).comp (T.coverBandMap V (Nat.dvd_mul_left (p * L) p) a b)).range =
      ((T.coverBandMap V (Nat.dvd_mul_left (p * L) p) a b).comp
        ((T.frickeBandMap a b).comp (S.coverBandMap T (Nat.dvd_mul_left L p) a b))).range := by
  apply le_antisymm
  · intro v hv
    obtain ⟨x, hx⟩ := hv.1
    obtain ⟨f, hf, hfx⟩ := exists_continuous_window_representative (p * L)
      (Nat.mul_pos hp.pos hL) T.basis T.energy T.energy_nonneg T.graph a b x.val x.property
    let F := levelCoverRepresentative (Nat.dvd_mul_left (p * L) p) f
    have hFv : AutomorphicL2.denseEmbedding _ _ F = (v.val : AutomorphicSpace (p * (p * L))) := by
      rw [← levelCover_apply, hfx]
      exact congrArg (fun y : V.band a b => (y.val : AutomorphicSpace (p * (p * L)))) hx
    have hF : Continuous F.val := levelCoverRepresentative_continuous _ f hf
    have hD := continuous_repeated_old_invariant L p hL hp hr F hF (by
      rw [hFv]
      exact ⟨(T.coverBandMap_range_iff V _ a b v).mp hv.1,
        (T.frickeCoverBandMap_range_iff V _ a b v).mp hv.2⟩)
    have hxold : x ∈ ((T.frickeBandMap a b).comp
        (S.coverBandMap T (Nat.dvd_mul_left L p) a b)).range := by
      apply (S.frickeCoverBandMap_range_iff T _ a b x).mpr
      rw [← hfx]
      apply (continuous_fricke_cover_range_iff (Nat.mul_pos hp.pos hL)
        (Nat.dvd_mul_left L p) f hf).mpr
      rw [frickeOldLevel_eq_dilationLevel L p hL hp.pos]
      simpa only [F, levelCoverRepresentative_coe] using hD
    obtain ⟨u, hu⟩ := hxold
    refine ⟨u, ?_⟩
    change T.coverBandMap V _ a b (((T.frickeBandMap a b).comp
      (S.coverBandMap T _ a b)) u) = v
    rw [hu]
    exact hx
  · rintro v ⟨u, rfl⟩
    let x := T.frickeBandMap a b (S.coverBandMap T (Nat.dvd_mul_left L p) a b u)
    constructor
    · exact ⟨x, rfl⟩
    · apply (T.frickeCoverBandMap_range_iff V _ a b _).mpr
      obtain ⟨f, hf, hfx⟩ := exists_continuous_window_representative (p * L)
        (Nat.mul_pos hp.pos hL) T.basis T.energy T.energy_nonneg T.graph a b x.val x.property
      have hD := continuous_fricke_old_invariant (Nat.mul_pos hp.pos hL)
        (Nat.dvd_mul_left L p) f hf (by
          rw [hfx]
          exact ⟨(u.val : AutomorphicSpace L), rfl⟩)
      rw [frickeOldLevel_eq_dilationLevel L p hL hp.pos] at hD
      let F := levelCoverRepresentative (Nat.dvd_mul_left (p * L) p) f
      have hF : Continuous F.val := levelCoverRepresentative_continuous _ f hf
      have hFx : AutomorphicL2.denseEmbedding _ _ F =
          levelCover (Nat.dvd_mul_left (p * L) p) (x.val : AutomorphicSpace (p * L)) := by
        rw [← levelCover_apply, hfx]
      change levelCover (Nat.dvd_mul_left (p * L) p) (x.val : AutomorphicSpace (p * L)) ∈ _
      rw [← hFx]
      apply (continuous_fricke_cover_range_iff (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))
        (Nat.dvd_mul_left (p * L) p) F hF).mpr
      rw [frickeOldLevel_eq_dilationLevel (p * L) p (Nat.mul_pos hp.pos hL) hp.pos]
      simpa only [F, levelCoverRepresentative_coe] using
        (dilationLevel_mono hp.pos (Nat.dvd_mul_left L p)).trans hD

/-- Exact dimension of the proved repeated-prime overlap. -/
theorem repeated_old_band_overlap_finrank (L p : ℕ) [NeZero L] [NeZero (p * L)]
    [NeZero (p * (p * L))] (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime)
    (S : CuspEnergySpectrum L hL)
    (T : CuspEnergySpectrum (p * L) (Nat.mul_pos hp.pos hL))
    (V : CuspEnergySpectrum (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)))
    (a b : ℝ) :
    Module.finrank ℂ ↥((T.coverBandMap V (Nat.dvd_mul_left (p * L) p) a b).range ⊓
      ((V.frickeBandMap a b).comp (T.coverBandMap V (Nat.dvd_mul_left (p * L) p) a b)).range) =
      Module.finrank ℂ (S.band a b) := by
  let := S.band_finiteDimensional a b
  rw [repeated_old_band_intersection L p hL hp hr S T V a b]
  apply LinearMap.finrank_range_of_inj
  exact (T.coverBandMap_injective V (Nat.dvd_mul_left (p * L) p) a b).comp
    ((T.frickeBandMap_involutive a b).injective.comp
      (S.coverBandMap_injective T (Nat.dvd_mul_left L p) a b))

/-- In particular the repeated overlap at 2 is proved at every positive
lower level, without retaining an index or decomposition assumption. -/
theorem repeated_two_old_band_overlap_finrank (L : ℕ) [NeZero L] [NeZero (2 * L)]
    [NeZero (2 * (2 * L))] (hL : 0 < L)
    (S : CuspEnergySpectrum L hL)
    (T : CuspEnergySpectrum (2 * L) (Nat.mul_pos (by decide) hL))
    (V : CuspEnergySpectrum (2 * (2 * L)) (Nat.mul_pos (by decide) (Nat.mul_pos (by decide) hL)))
    (a b : ℝ) :
    Module.finrank ℂ ↥((T.coverBandMap V (Nat.dvd_mul_left (2 * L) 2) a b).range ⊓
      ((V.frickeBandMap a b).comp (T.coverBandMap V (Nat.dvd_mul_left (2 * L) 2) a b)).range) =
      Module.finrank ℂ (S.band a b) :=
  repeated_old_band_overlap_finrank L 2 hL Nat.prime_two (two_level_relIndex_prime L hL) S T V a b

/-- At a simply ramified prime, the two actual lower-level band images
are disjoint. Their preimages have been constructed on the same interval. -/
theorem simple_old_band_disjoint (M p : ℕ) [NeZero M] [NeZero (p * M)]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM)) (a b : ℝ) :
    Disjoint (S.coverBandMap T (Nat.dvd_mul_left M p) a b).range
      ((T.frickeBandMap a b).comp (S.coverBandMap T (Nat.dvd_mul_left M p) a b)).range := by
  rw [disjoint_iff_inf_le]
  intro v hv
  change v = 0
  apply simple_old_window_intersection_zero M p hM hp hcp
    T.basis T.energy T.energy_nonneg T.graph a b v
  constructor
  · obtain ⟨x, hx⟩ := hv.1
    refine ⟨(x.val : AutomorphicSpace M), ?_⟩
    exact congrArg (fun w : T.band a b => (w.val : AutomorphicSpace (p * M))) hx
  · obtain ⟨x, hx⟩ := hv.2
    refine ⟨(x.val : AutomorphicSpace M), ?_⟩
    exact congrArg (fun w : T.band a b => (w.val : AutomorphicSpace (p * M))) hx

/-- The already constructed geometric reflection projection on a band. -/
def bandParity {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) : S.band a b →ₗ[ℂ] S.band a b :=
  cuspWindowParity N hN S.basis S.energy S.energy_nonneg S.graph a b σ

abbrev parityBand {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) : Submodule ℂ (S.band a b) :=
  (S.bandParity a b σ).range

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance

local instance {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance

theorem bandMap_parity {M N : ℕ} [NeZero M] [NeZero N] {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (U : AutomorphicSpace M →L[ℂ] AutomorphicSpace N)
    (hc : ∀ x, x ∈ localCuspidalSpace M hM → U x ∈ localCuspidalSpace N hN)
    (hg : ∀ x y, FriedrichsGraph M x y → FriedrichsGraph N (U x) (U y))
    (hr : ∀ v, U (reflectionIsometry M v) = reflectionIsometry N (U v))
    (a b σ : ℝ) (v : S.band a b) :
    S.bandMap T U hc hg a b (S.bandParity a b σ v) =
      T.bandParity a b σ (S.bandMap T U hc hg a b v) := by
  apply Subtype.ext
  apply Subtype.ext
  change U (parityProjection M σ (v.val : AutomorphicSpace M)) =
    parityProjection N σ (U (v.val : AutomorphicSpace M))
  simp only [parityProjection_apply, map_smul, map_add, hr]

def parityBandMap {M N : ℕ} [NeZero M] [NeZero N] {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (U : AutomorphicSpace M →L[ℂ] AutomorphicSpace N)
    (hc : ∀ x, x ∈ localCuspidalSpace M hM → U x ∈ localCuspidalSpace N hN)
    (hg : ∀ x y, FriedrichsGraph M x y → FriedrichsGraph N (U x) (U y))
    (hr : ∀ v, U (reflectionIsometry M v) = reflectionIsometry N (U v)) (a b σ : ℝ) :
    S.parityBand a b σ →ₗ[ℂ] T.parityBand a b σ :=
  (S.bandMap T U hc hg a b).restrict (by
    rintro v ⟨w, rfl⟩
    exact ⟨S.bandMap T U hc hg a b w, (S.bandMap_parity T U hc hg hr a b σ w).symm⟩)

theorem parityBandMap_injective {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (U : AutomorphicSpace M →L[ℂ] AutomorphicSpace N)
    (hc : ∀ x, x ∈ localCuspidalSpace M hM → U x ∈ localCuspidalSpace N hN)
    (hg : ∀ x y, FriedrichsGraph M x y → FriedrichsGraph N (U x) (U y))
    (hr : ∀ v, U (reflectionIsometry M v) = reflectionIsometry N (U v))
    (hU : Function.Injective U) (a b σ : ℝ) :
    Function.Injective (S.parityBandMap T U hc hg hr a b σ) := by
  intro x y he
  apply Subtype.ext
  exact S.bandMap_injective T U hc hg hU a b (congrArg Subtype.val he)

def coverParityBandMap {M N : ℕ} [NeZero M] [NeZero N] {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b σ : ℝ) : S.parityBand a b σ →ₗ[ℂ] T.parityBand a b σ :=
  S.parityBandMap T (levelCover hMN)
    (fun v hv => (levelCover_mem_cuspidal_iff hM hN hMN v).mpr hv)
    (fun _ _ h => levelCover_friedrichsGraph hMN h)
    (fun v => (levelCover_reflection hMN v).symm) a b σ

def traceParityBandMap {M N : ℕ} [NeZero M] [NeZero N] {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b σ : ℝ) : T.parityBand a b σ →ₗ[ℂ] S.parityBand a b σ :=
  T.parityBandMap S (levelTrace hMN) (levelTrace_mem_cuspidal hM hN hMN)
    (fun _ _ h => levelTrace_friedrichsGraph hMN h) (levelTrace_reflection hMN) a b σ

def frickeParityBandMap {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) : S.parityBand a b σ →ₗ[ℂ] S.parityBand a b σ :=
  S.parityBandMap S (frickeIsometry N hN).toContinuousLinearMap (fricke_mem_cuspidal N hN)
    (fun _ _ h => fricke_friedrichsGraph N hN h) (frickeIsometry_reflection N hN) a b σ

theorem coverParityBandMap_injective {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b σ : ℝ) : Function.Injective (S.coverParityBandMap T hMN a b σ) :=
  S.parityBandMap_injective T _ _ _ _ (levelCover_injective hMN) a b σ

theorem frickeParityBandMap_involutive {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) : Function.Involutive (S.frickeParityBandMap a b σ) := by
  intro v
  apply Subtype.ext
  exact S.frickeBandMap_involutive a b v.val

theorem coverBandMap_parity {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b σ : ℝ) (v : S.band a b) :
    S.coverBandMap T hMN a b (S.bandParity a b σ v) =
      T.bandParity a b σ (S.coverBandMap T hMN a b v) :=
  S.bandMap_parity T _ _ _ (fun v => (levelCover_reflection hMN v).symm) a b σ v

theorem frickeBandMap_parity {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (v : S.band a b) :
    S.frickeBandMap a b (S.bandParity a b σ v) =
      S.bandParity a b σ (S.frickeBandMap a b v) :=
  S.bandMap_parity S _ _ _ (frickeIsometry_reflection N hN) a b σ v

/-- The repeated-prime intersection identity retains reflection parity.
Preimages are projected with the actual geometric parity operator. -/
theorem repeated_old_parity_intersection (L p : ℕ) [NeZero L] [NeZero (p * L)]
    [NeZero (p * (p * L))] (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime)
    (S : CuspEnergySpectrum L hL)
    (T : CuspEnergySpectrum (p * L) (Nat.mul_pos hp.pos hL))
    (V : CuspEnergySpectrum (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)))
    (a b σ : ℝ) (hσ : σ ^ 2 = 1) :
    (T.coverParityBandMap V (Nat.dvd_mul_left (p * L) p) a b σ).range ⊓
      ((V.frickeParityBandMap a b σ).comp
        (T.coverParityBandMap V (Nat.dvd_mul_left (p * L) p) a b σ)).range =
      ((T.coverParityBandMap V (Nat.dvd_mul_left (p * L) p) a b σ).comp
        ((T.frickeParityBandMap a b σ).comp
          (S.coverParityBandMap T (Nat.dvd_mul_left L p) a b σ))).range := by
  let C := T.coverBandMap V (Nat.dvd_mul_left (p * L) p) a b
  let D := (V.frickeBandMap a b).comp C
  let E := C.comp ((T.frickeBandMap a b).comp (S.coverBandMap T (Nat.dvd_mul_left L p) a b))
  have hC (x : T.band a b) : C (T.bandParity a b σ x) = V.bandParity a b σ (C x) :=
    T.coverBandMap_parity V _ a b σ x
  have hD (x : T.band a b) : D (T.bandParity a b σ x) = V.bandParity a b σ (D x) := by
    change V.frickeBandMap a b (C (T.bandParity a b σ x)) = _
    rw [hC, frickeBandMap_parity]
    rfl
  have hE (x : S.band a b) : E (S.bandParity a b σ x) = V.bandParity a b σ (E x) := by
    change C (T.frickeBandMap a b (S.coverBandMap T _ a b (S.bandParity a b σ x))) = _
    rw [coverBandMap_parity, frickeBandMap_parity, hC]
    rfl
  have hQ : IsIdempotentElem (V.bandParity a b σ) :=
    cuspWindowParity_idempotent _ _ V.basis V.energy V.energy_nonneg V.graph a b σ hσ
  ext v
  change v ∈ (projectedRangeMap (E := T.band a b) (F := V.band a b)
      (T.bandParity a b σ) (V.bandParity a b σ) C hC).range ∧
      v ∈ (projectedRangeMap (E := T.band a b) (F := V.band a b)
        (T.bandParity a b σ) (V.bandParity a b σ) D hD).range ↔
    v ∈ (projectedRangeMap (E := S.band a b) (F := V.band a b)
      (S.bandParity a b σ) (V.bandParity a b σ) E hE).range
  rw [projectedRangeMap_range_iff _ _ _ _ hQ,
    projectedRangeMap_range_iff _ _ _ _ hQ, projectedRangeMap_range_iff _ _ _ _ hQ]
  change v.val ∈ C.range ⊓ D.range ↔ v.val ∈ E.range
  rw [show C.range ⊓ D.range = E.range from
    repeated_old_band_intersection L p hL hp hr S T V a b]

theorem repeated_old_parity_overlap_finrank (L p : ℕ) [NeZero L] [NeZero (p * L)]
    [NeZero (p * (p * L))] (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime)
    (S : CuspEnergySpectrum L hL)
    (T : CuspEnergySpectrum (p * L) (Nat.mul_pos hp.pos hL))
    (V : CuspEnergySpectrum (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)))
    (a b σ : ℝ) (hσ : σ ^ 2 = 1) :
    Module.finrank ℂ ↥((T.coverParityBandMap V (Nat.dvd_mul_left (p * L) p) a b σ).range ⊓
      ((V.frickeParityBandMap a b σ).comp
        (T.coverParityBandMap V (Nat.dvd_mul_left (p * L) p) a b σ)).range) =
      Module.finrank ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  rw [repeated_old_parity_intersection L p hL hp hr S T V a b σ hσ]
  apply LinearMap.finrank_range_of_inj
  exact (T.coverParityBandMap_injective V (Nat.dvd_mul_left (p * L) p) a b σ).comp
    ((T.frickeParityBandMap_involutive a b σ).injective.comp
      (S.coverParityBandMap_injective T (Nat.dvd_mul_left L p) a b σ))

/-- The simply ramified disjointness retains either reflection parity and
sums over all Fricke signs, exactly as required for the manuscript count. -/
theorem simple_old_parity_disjoint (M p : ℕ) [NeZero M] [NeZero (p * M)]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM)) (a b σ : ℝ) :
    Disjoint (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ).range
      ((T.frickeParityBandMap a b σ).comp
        (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ)).range := by
  apply Submodule.disjoint_def.mpr
  intro v hv hw
  apply Subtype.ext
  apply Submodule.disjoint_def.mp (simple_old_band_disjoint M p hM hp hcp S T a b) v.val
  · obtain ⟨x, hx⟩ := hv
    exact ⟨x.val, congrArg Subtype.val hx⟩
  · obtain ⟨x, hx⟩ := hw
    exact ⟨x.val, congrArg Subtype.val hx⟩

/-- Exact physical dimension of the two old images at a simply ramified
prime, within a fixed reflection parity and the unchanged spectral band. -/
theorem simple_old_parity_finrank (M p : ℕ) [NeZero M] [NeZero (p * M)]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM)) (a b σ : ℝ) :
    Module.finrank ℂ ↥((S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ).range ⊔
      ((T.frickeParityBandMap a b σ).comp
        (S.coverParityBandMap T (Nat.dvd_mul_left M p) a b σ)).range) =
      2 * Module.finrank ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  let := T.band_finiteDimensional a b
  exact disjoint_injective_ranges_finrank _ _
    (S.coverParityBandMap_injective T (Nat.dvd_mul_left M p) a b σ)
    ((T.frickeParityBandMap_involutive a b σ).injective.comp
      (S.coverParityBandMap_injective T (Nat.dvd_mul_left M p) a b σ))
    (simple_old_parity_disjoint M p hM hp hcp S T a b σ)

/-- The two actual trace kernels restricted to the fixed spectral/parity
band. At composite levels this imposes only the specified prime equation. -/
def traceNewParityBand {M N : ℕ} [NeZero M] [NeZero N] {hM : 0 < M} {hN : 0 < N}
    (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b σ : ℝ) : Submodule ℂ (T.parityBand a b σ) :=
  (S.traceParityBandMap T hMN a b σ).ker ⊓
    ((S.traceParityBandMap T hMN a b σ).comp (T.frickeParityBandMap a b σ)).ker

theorem mem_traceNewParityBand {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b σ : ℝ) (v : T.parityBand a b σ) :
    v ∈ S.traceNewParityBand T hMN a b σ ↔
      (v.val.val : AutomorphicSpace N) ∈ newTraceKernel hN hMN := by
  change (_ = 0 ∧ _ = 0) ↔ (levelTrace hMN _ = 0 ∧ levelTrace hMN _ = 0)
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨congrArg (fun x : S.parityBand a b σ => (x.val.val : AutomorphicSpace M)) h₁,
      congrArg (fun x : S.parityBand a b σ => (x.val.val : AutomorphicSpace M)) h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Subtype.ext (Subtype.ext (Subtype.ext h₁)),
      Subtype.ext (Subtype.ext (Subtype.ext h₂))⟩

/-- Adjointness is retained after both spectral and parity restriction. -/
theorem traceNewParityBand_orthogonal {M N : ℕ} [NeZero M] [NeZero N]
    {hM : 0 < M} {hN : 0 < N} (S : CuspEnergySpectrum M hM) (T : CuspEnergySpectrum N hN)
    (hMN : M ∣ N) (a b σ : ℝ) :
    S.traceNewParityBand T hMN a b σ =
      ((S.coverParityBandMap T hMN a b σ).range ⊔
        ((T.frickeParityBandMap a b σ).comp (S.coverParityBandMap T hMN a b σ)).range)ᗮ := by
  apply paired_two_kernel_orthogonal
  · intro x y
    exact S.traceBandMap_pairing T hMN a b x.val y.val
  · intro x y
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (frickeIsometry_selfAdjoint N hN) (x.val.val : AutomorphicSpace N)
        (y.val.val : AutomorphicSpace N)).symm

/-- The exact one-prime new/old recurrence in either reflection parity. -/
theorem simple_traceNewParityBand_finrank (M p : ℕ) [NeZero M] [NeZero (p * M)]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM)) (a b σ : ℝ) :
    Module.finrank ℂ (S.traceNewParityBand T (Nat.dvd_mul_left M p) a b σ) +
      2 * Module.finrank ℂ (S.parityBand a b σ) =
        Module.finrank ℂ (T.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  let := T.band_finiteDimensional a b
  rw [S.traceNewParityBand_orthogonal T (Nat.dvd_mul_left M p) a b σ]
  exact orthogonal_disjoint_injective_ranges_finrank _ _
    (S.coverParityBandMap_injective T (Nat.dvd_mul_left M p) a b σ)
    ((T.frickeParityBandMap_involutive a b σ).injective.comp
      (S.coverParityBandMap_injective T (Nat.dvd_mul_left M p) a b σ))
    (simple_old_parity_disjoint M p hM hp hcp S T a b σ)

/-- At a repeated prime, one copy of the lower band is restored because
it is exactly the intersection of the two old images. -/
theorem repeated_traceNewParityBand_finrank (L p : ℕ) [NeZero L] [NeZero (p * L)]
    [NeZero (p * (p * L))] (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime)
    (S : CuspEnergySpectrum L hL)
    (T : CuspEnergySpectrum (p * L) (Nat.mul_pos hp.pos hL))
    (V : CuspEnergySpectrum (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL)))
    (a b σ : ℝ) (hσ : σ ^ 2 = 1) :
    Module.finrank ℂ (T.traceNewParityBand V (Nat.dvd_mul_left (p * L) p) a b σ) +
      2 * Module.finrank ℂ (T.parityBand a b σ) =
        Module.finrank ℂ (V.parityBand a b σ) + Module.finrank ℂ (S.parityBand a b σ) := by
  let := T.band_finiteDimensional a b
  let := V.band_finiteDimensional a b
  exact paired_new_finrank_of_overlap _ _
    (T.coverParityBandMap_injective V (Nat.dvd_mul_left (p * L) p) a b σ)
    ((V.frickeParityBandMap_involutive a b σ).injective.comp
      (T.coverParityBandMap_injective V (Nat.dvd_mul_left (p * L) p) a b σ))
    _ (T.traceNewParityBand_orthogonal V (Nat.dvd_mul_left (p * L) p) a b σ)
    _ (repeated_old_parity_overlap_finrank L p hL hp hr S T V a b σ hσ)

#print axioms band_finiteDimensional
#print axioms map_mem_band
#print axioms bandMap_injective
#print axioms coverBandMap_injective
#print axioms traceBandMap_coverBandMap
#print axioms traceBandMap_pairing
#print axioms frickeBandMap_involutive
#print axioms coverBandMap_cross_new
#print axioms coverBandMap_range_iff
#print axioms frickeCoverBandMap_range_iff
#print axioms repeated_old_band_intersection
#print axioms repeated_old_band_overlap_finrank
#print axioms repeated_two_old_band_overlap_finrank
#print axioms simple_old_band_disjoint
#print axioms bandMap_parity
#print axioms parityBandMap_injective
#print axioms coverParityBandMap_injective
#print axioms frickeParityBandMap_involutive
#print axioms coverBandMap_parity
#print axioms frickeBandMap_parity
#print axioms repeated_old_parity_intersection
#print axioms repeated_old_parity_overlap_finrank
#print axioms simple_old_parity_disjoint
#print axioms simple_old_parity_finrank
#print axioms mem_traceNewParityBand
#print axioms traceNewParityBand_orthogonal
#print axioms simple_traceNewParityBand_finrank
#print axioms repeated_traceNewParityBand_finrank

end CuspEnergySpectrum

#print axioms geometricCuspSpectrum
#print axioms paired_kernel_eq_range_orthogonal
#print axioms paired_two_kernel_orthogonal
#print axioms disjoint_injective_ranges_finrank
#print axioms orthogonal_injective_ranges_finrank
#print axioms orthogonal_disjoint_injective_ranges_finrank
#print axioms paired_new_finrank_of_overlap
#print axioms projectedRangeMap_range_iff

end QuantitativeNinaMaass
