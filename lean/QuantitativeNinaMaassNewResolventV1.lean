module

public import QuantitativeNinaMaassPartialNewV1
public import QuantitativeNinaMaassHeckeSymmetriesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set QuantitativeMaass QuantitativeArithmeticMaassCuspBand
open scoped InnerProductSpace

/-!
The actual Friedrichs resolvent and global Fricke on finite new-parity
bands. Resolvent eigenvectors acquire their principal spectral parameter
from a nonzero coefficient in the actual energy basis. Thus the interval
condition is proved from membership in the window, not an extra input to
the eventual simultaneous eigenfamily.
-/

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance
local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

theorem resolvent_preserves_graph (N : ℕ) {v w : AutomorphicSpace N}
    (h : FriedrichsGraph N v w) :
    FriedrichsGraph N (friedrichsResolvent N v) (friedrichsResolvent N w) := by
  change friedrichsResolvent N (friedrichsResolvent N v + friedrichsResolvent N w) = _
  rw [← map_add, h]

theorem resolvent_nonzero_eigen_graph (N : ℕ) (v : AutomorphicSpace N)
    (hv : v ≠ 0) (μ : ℂ) (he : friedrichsResolvent N v = μ • v) :
    FriedrichsGraph N v ((μ⁻¹ - 1) • v) := by
  have hμ : μ ≠ 0 := by
    intro hz
    apply hv
    apply friedrichsResolvent_injective N
    rw [he, hz, zero_smul, map_zero]
  change friedrichsResolvent N (v + (μ⁻¹ - 1) • v) = v
  have hs : v + (μ⁻¹ - 1) • v = μ⁻¹ • v := by module
  rw [hs, map_smul, he, smul_smul, inv_mul_cancel₀ hμ, one_smul]

theorem partialNewSpace_resolvent (N : ℕ) [NeZero N] (hN : 0 < N)
    (P : Set ℕ) (v : AutomorphicSpace N) (hv : v ∈ partialNewSpace N hN P) :
    friedrichsResolvent N v ∈ partialNewSpace N hN P := by
  rw [mem_partialNewSpace] at hv ⊢
  intro p hp
  let : NeZero (N / p.val) := ⟨(Nat.div_pos
    (Nat.le_of_dvd hN p.property.2) p.property.1.pos).ne'⟩
  exact newTraceKernel_resolvent hN (Nat.div_dvd_of_dvd p.property.2) v (hv p hp)

namespace CuspEnergySpectrum

theorem resolvent_basis {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (j : S.Index) :
    friedrichsResolvent N (S.basis j : AutomorphicSpace N) =
      (((1 + S.energy j)⁻¹ : ℝ) : ℂ) • (S.basis j : AutomorphicSpace N) := by
  have hc : (1 + (S.energy j : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + S.energy j) ≠ 0 by linarith [S.energy_nonneg j])
  have hg : (1 + (S.energy j : ℂ)) • friedrichsResolvent N (S.basis j) = S.basis j := by
    rw [← map_smul, add_smul, one_smul]
    exact S.graph j
  have hh := congrArg (fun z : AutomorphicSpace N => (1 + (S.energy j : ℂ))⁻¹ • z) hg
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hh
  simpa only [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one] using hh

/-- The proved wave separation forces resolvent commutation on the cusp
space. This avoids assuming any differential regularity of a cusp vector. -/
theorem wave_commuting_cusp_resolvent {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (U : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hc : ∀ v, v ∈ localCuspidalSpace N hN → U v ∈ localCuspidalSpace N hN)
    (hw : ∀ t, Commute U (Wave.shiftedQuotientWave N t)) (v : localCuspidalSpace N hN) :
    friedrichsResolvent N (U v) = U (friedrichsResolvent N v) := by
  have hj (j : S.Index) : friedrichsResolvent N (U (S.basis j)) =
      (((1 + S.energy j)⁻¹ : ℝ) : ℂ) • U (S.basis j) := by
    let u : localCuspidalSpace N hN := ⟨U (S.basis j), hc _ (S.basis j).property⟩
    have he : cuspidalResolvent N hN u = (((1 + S.energy j)⁻¹ : ℝ) : ℂ) • u := by
      apply S.basis.repr.injective
      apply lp.ext
      funext i
      simp only [S.basis.repr_apply_apply]
      change inner ℂ (S.basis i : AutomorphicSpace N) (friedrichsResolvent N (U (S.basis j))) =
        inner ℂ (S.basis i : AutomorphicSpace N)
          ((((1 + S.energy j)⁻¹ : ℝ) : ℂ) • U (S.basis j))
      have hR : inner ℂ (friedrichsResolvent N (S.basis i)) (U (S.basis j)) =
          inner ℂ (S.basis i : AutomorphicSpace N) (friedrichsResolvent N (U (S.basis j))) :=
        ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (friedrichsResolvent_isSelfAdjoint N) _ _
      rw [← hR, S.resolvent_basis,
        inner_smul_left (𝕜 := ℂ) (S.basis i : AutomorphicSpace N) (U (S.basis j)),
        inner_smul_right (𝕜 := ℂ) (S.basis i : AutomorphicSpace N) (U (S.basis j)),
        Complex.conj_ofReal]
      by_cases he : S.energy i = S.energy j
      · rw [he]
      · rw [wave_commuting_energy_coefficient_zero N U hw _ _ _ _
          (S.energy_nonneg i) (S.energy_nonneg j) (S.graph i) (S.graph j) he]
        simp only [mul_zero]
    exact congrArg Subtype.val he
  let F := ((friedrichsResolvent N).comp U).comp (localCuspidalSpace N hN).subtypeL
  let G := (U.comp (friedrichsResolvent N)).comp (localCuspidalSpace N hN).subtypeL
  have he (j : S.Index) : F (S.basis j) = G (S.basis j) := by
    change friedrichsResolvent N (U (S.basis j)) = U (friedrichsResolvent N (S.basis j))
    rw [hj, S.resolvent_basis, map_smul]
  have hF := F.hasSum (S.basis.hasSum_repr v)
  have hG := G.hasSum (S.basis.hasSum_repr v)
  simp only [map_smul, he] at hF
  simp only [map_smul] at hG
  exact hF.unique hG

theorem cusp_resolvent_reflection {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (v : localCuspidalSpace N hN) :
    friedrichsResolvent N (reflectionIsometry N v) =
      reflectionIsometry N (friedrichsResolvent N v) :=
  S.wave_commuting_cusp_resolvent (reflectionIsometry N).toContinuousLinearMap
    (reflectionIsometry_mem_localCuspidalSpace N hN) (reflectionIsometry_wave_commute N) v

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

def resolventBandMap {N : ℕ} {hN : 0 < N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    S.band a b →ₗ[ℂ] S.band a b :=
  S.bandMap S (friedrichsResolvent N) (resolvent_mem_localCuspidalSpace N hN)
    (fun _ _ h => resolvent_preserves_graph N h) a b

theorem resolventBandMap_parity {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (v : S.band a b) :
    S.resolventBandMap a b (S.bandParity a b σ v) =
      S.bandParity a b σ (S.resolventBandMap a b v) := by
  apply Subtype.ext
  apply Subtype.ext
  change friedrichsResolvent N (parityProjection N σ (v.val : AutomorphicSpace N)) =
    parityProjection N σ (friedrichsResolvent N v.val)
  simp only [parityProjection_apply, map_smul, map_add, S.cusp_resolvent_reflection]

def resolventParityBandMap {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    S.parityBand a b σ →ₗ[ℂ] S.parityBand a b σ :=
  (S.resolventBandMap a b).restrict (by
    rintro v ⟨w, rfl⟩
    exact ⟨S.resolventBandMap a b w, (S.resolventBandMap_parity a b σ w).symm⟩)

def partialNewResolvent {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    S.partialParityBand a b σ P →ₗ[ℂ] S.partialParityBand a b σ P :=
  (S.resolventParityBandMap a b σ).restrict (by
    intro v hv
    exact partialNewSpace_resolvent N hN P (v.val.val : AutomorphicSpace N) hv)

theorem partialNewResolvent_actual {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ)
    (v : S.partialParityBand a b σ P) :
    ((S.partialNewResolvent a b σ P v).val.val.val : AutomorphicSpace N) =
      friedrichsResolvent N (v.val.val.val : AutomorphicSpace N) := rfl

theorem partialNewResolvent_injective {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    Function.Injective (S.partialNewResolvent a b σ P) := by
  intro v w he
  have hh := friedrichsResolvent_injective N
    (congrArg (fun x : S.partialParityBand a b σ P => (x.val.val.val : AutomorphicSpace N)) he)
  exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext hh)))

theorem partialNewResolvent_symmetric {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    (S.partialNewResolvent a b σ P).IsSymmetric := by
  intro v w
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (friedrichsResolvent_isSelfAdjoint N)
      (v.val.val.val : AutomorphicSpace N) (w.val.val.val : AutomorphicSpace N)

def partialNewFricke {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    S.partialParityBand a b σ P →ₗ[ℂ] S.partialParityBand a b σ P :=
  (S.frickeParityBandMap a b σ).restrict (by
    intro v hv
    exact fricke_mem_partialNewSpace N hN P (v.val.val : AutomorphicSpace N) hv)

theorem partialNewFricke_symmetric {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    (S.partialNewFricke a b σ P).IsSymmetric := by
  intro v w
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (frickeIsometry_selfAdjoint N hN)
      (v.val.val.val : AutomorphicSpace N) (w.val.val.val : AutomorphicSpace N)

theorem partialNewFricke_involutive {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    Function.Involutive (S.partialNewFricke a b σ P) := by
  intro v
  exact Subtype.ext (Subtype.ext (Subtype.ext
    (Subtype.ext (frickeIsometry_involutive N hN (v.val.val.val : AutomorphicSpace N)))))

theorem partialNewResolvent_fricke_commute {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ) :
    Commute (S.partialNewResolvent a b σ P) (S.partialNewFricke a b σ P) := by
  apply LinearMap.ext
  intro v
  exact Subtype.ext (Subtype.ext (Subtype.ext
    (Subtype.ext (fricke_resolvent N hN (v.val.val.val : AutomorphicSpace N)))))

/-- Membership in the literal spectral span forces all coefficients off
the requested principal interval to vanish. -/
theorem band_coefficient_zero {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) (v : localCuspidalSpace N hN)
    (hv : v ∈ S.band a b) (i : S.Index) (hi : i ∉ principalWindowIndices S.energy a b) :
    S.basis.repr v i = 0 := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [S.basis.repr_apply_apply, orthonormal_iff_ite.mp S.basis.orthonormal]
    exact ite_eq_right (by intro h; exact hi (h ▸ j.property))
  | zero => simp only [map_zero, lp.coeFn_zero, Pi.zero_apply]
  | add x y _ _ hx hy => simp only [map_add, lp.coeFn_add, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hx, mul_zero]

/-- A nonzero graph eigenvector in this actual band has its parameter in
the same interval, regardless of multiplicities of the energy basis. -/
theorem band_graph_eigen_parameter {N : ℕ} {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b : ℝ) (v : localCuspidalSpace N hN)
    (hv : v ∈ S.band a b) (hv0 : v ≠ 0) (ell : ℂ)
    (he : FriedrichsGraph N (v : AutomorphicSpace N) (ell • (v : AutomorphicSpace N))) :
    ∃ r : ℝ, 0 ≤ r ∧ r ∈ Icc a b ∧ ((1 / 4 + r ^ 2 : ℝ) : ℂ) = ell := by
  have hex : ∃ i, S.basis.repr v i ≠ 0 := by
    by_contra! h
    apply hv0
    apply S.basis.repr.injective
    apply lp.ext
    funext i
    simpa only [map_zero, lp.coeFn_zero, Pi.zero_apply] using h i
  obtain ⟨i, hi⟩ := hex
  have hwin : i ∈ principalWindowIndices S.energy a b := by
    by_contra h
    exact hi (S.band_coefficient_zero a b v hv i h)
  have hei : (S.energy i : ℂ) = ell := by
    have h := friedrichsGraph_symmetric N (S.graph i) he
    rw [inner_smul_left (𝕜 := ℂ) (S.basis i : AutomorphicSpace N) (v : AutomorphicSpace N),
      inner_smul_right (𝕜 := ℂ) (S.basis i : AutomorphicSpace N) (v : AutomorphicSpace N),
      Complex.conj_ofReal] at h
    apply mul_right_cancel₀ _ h
    rw [S.basis.repr_apply_apply] at hi
    exact hi
  refine ⟨Real.sqrt (S.energy i - 1 / 4), Real.sqrt_nonneg _, hwin.2, ?_⟩
  rw [Real.sq_sqrt (sub_nonneg.mpr hwin.1)]
  convert hei using 2
  ring

theorem partialNewResolvent_eigen_parameter {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) (P : Set ℕ)
    (v : S.partialParityBand a b σ P) (hv : v ≠ 0) (μ : ℂ)
    (he : S.partialNewResolvent a b σ P v = μ • v) :
    ∃ r : ℝ, 0 ≤ r ∧ r ∈ Icc a b ∧
      FriedrichsGraph N (v.val.val.val : AutomorphicSpace N)
        (((1 / 4 + r ^ 2 : ℝ) : ℂ) • (v.val.val.val : AutomorphicSpace N)) := by
  let x : AutomorphicSpace N := v.val.val.val
  have hx0 : x ≠ 0 := by
    intro hz
    exact hv (Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext hz))))
  have hx : friedrichsResolvent N x = μ • x :=
    congrArg (fun w : S.partialParityBand a b σ P =>
      (w.val.val.val : AutomorphicSpace N)) he
  have hg : FriedrichsGraph N x ((μ⁻¹ - 1) • x) := resolvent_nonzero_eigen_graph N x hx0 μ hx
  obtain ⟨r, hr, hwin, hell⟩ := S.band_graph_eigen_parameter a b v.val.val.val
    v.val.val.property (by
      intro hz
      exact hv (Subtype.ext (Subtype.ext (Subtype.ext hz)))) (μ⁻¹ - 1) hg
  exact ⟨r, hr, hwin, by rw [hell]; exact hg⟩

#print axioms resolvent_basis
#print axioms wave_commuting_cusp_resolvent
#print axioms cusp_resolvent_reflection
#print axioms resolventBandMap_parity
#print axioms partialNewResolvent_actual
#print axioms partialNewResolvent_injective
#print axioms partialNewResolvent_symmetric
#print axioms partialNewFricke_symmetric
#print axioms partialNewFricke_involutive
#print axioms partialNewResolvent_fricke_commute
#print axioms band_coefficient_zero
#print axioms band_graph_eigen_parameter
#print axioms partialNewResolvent_eigen_parameter

end CuspEnergySpectrum

#print axioms resolvent_preserves_graph
#print axioms resolvent_nonzero_eigen_graph
#print axioms partialNewSpace_resolvent

end QuantitativeNinaMaass
