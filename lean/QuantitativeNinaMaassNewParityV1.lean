module

public import QuantitativeNinaMaassOldTraceV1
public import QuantitativeNinaMaassOldBandsV1
public import QuantitativeMaassParityWindowDimensionV1
public import QuantitativeMaassParityShortWeylV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter QuantitativeMaass
open AsymptoticClassicalPetersson
open scoped InnerProductSpace Topology

/-!
Actual finite new spectral bands and their two reflection parities. Newness
means the physical trace equations from OldTraceV1, inside the constructed
cuspidal spectral band. The projections below are restrictions of the existing
geometric parity projection, not replacement counting models.

The one-prime trace-new asymptotics below follow from actual old-image
dimensions. At levels with several prime factors they do not yet identify
the simultaneous new count. No coefficient-sequence lower bound is asserted.
-/

namespace QuantitativeNinaMaass

local instance (N : ℕ) (hN : 0 < N) : NormedAddCommGroup (localCuspidalSpace N hN) :=
  inferInstance

local instance (N : ℕ) (hN : 0 < N) : InnerProductSpace ℂ (localCuspidalSpace N hN) :=
  inferInstance

theorem newSpace_closed (N : ℕ) [NeZero N] (hN : 0 < N) :
    IsClosed (newSpace N hN : Set (AutomorphicSpace N)) := by
  rw [newSpace_eq_oldSpace_orthogonal]
  exact (oldSpace N hN).isClosed_orthogonal

/-- Restricting to either geometric reflection parity preserves newness. -/
theorem newSpace_parityProjection (N : ℕ) [NeZero N] (hN : 0 < N)
    (σ : ℝ) (v : AutomorphicSpace N) (hv : v ∈ newSpace N hN) :
    parityProjection N σ v ∈ newSpace N hN := by
  rw [parityProjection_apply]
  exact (newSpace N hN).smul_mem _ ((newSpace N hN).add_mem hv
    ((newSpace N hN).smul_mem _ (newSpace_reflection N hN v hv)))

local instance {κ : Type*} (N : ℕ) (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ) (a b : ℝ) :
    NormedAddCommGroup (cuspPrincipalWindowSpace N hN basis e a b) := inferInstance

local instance {κ : Type*} (N : ℕ) (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ) (a b : ℝ) :
    InnerProductSpace ℂ (cuspPrincipalWindowSpace N hN basis e a b) := inferInstance

/-- Physical trace-new vectors inside an actual finite cusp spectral band. -/
def newWindowSpace {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (a b : ℝ) : Submodule ℂ (cuspPrincipalWindowSpace N hN basis e a b) :=
  (newSpace N hN).comap ((localCuspidalSpace N hN).subtype.comp
    (cuspPrincipalWindowSpace N hN basis e a b).subtype)

local instance {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ) (a b : ℝ) :
    NormedAddCommGroup (newWindowSpace N hN basis e a b) := inferInstance

local instance {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ) (a b : ℝ) :
    InnerProductSpace ℂ (newWindowSpace N hN basis e a b) := inferInstance

theorem newWindowSpace_finiteDimensional {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
      ((e j : ℂ) • (basis j : AutomorphicSpace N))) (a b : ℝ) :
    FiniteDimensional ℂ (newWindowSpace N hN basis e a b) := by
  let := cuspPrincipalWindowSpace_finiteDimensional N hN basis e henergy hgraph a b
  infer_instance

def newWindowParity {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
      ((e j : ℂ) • (basis j : AutomorphicSpace N))) (a b σ : ℝ) :
    newWindowSpace N hN basis e a b →ₗ[ℂ] newWindowSpace N hN basis e a b :=
  (cuspWindowParity N hN basis e henergy hgraph a b σ).restrict (by
    intro x hx
    change parityProjection N σ (x.val : AutomorphicSpace N) ∈ newSpace N hN
    exact newSpace_parityProjection N hN σ (x.val : AutomorphicSpace N) hx)

theorem newWindowParity_idempotent {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
      ((e j : ℂ) • (basis j : AutomorphicSpace N))) (a b σ : ℝ) (hσ : σ^2 = 1) :
    IsIdempotentElem (newWindowParity N hN basis e henergy hgraph a b σ) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact parityProjection_idempotent N σ hσ (x.val.val : AutomorphicSpace N)

theorem newWindowParity_symmetric {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
      ((e j : ℂ) • (basis j : AutomorphicSpace N))) (a b σ : ℝ) :
    (newWindowParity N hN basis e henergy hgraph a b σ).IsSymmetric := by
  intro x y
  change inner ℂ (parityProjection N σ (x.val.val : AutomorphicSpace N))
      (y.val.val : AutomorphicSpace N) =
    inner ℂ (x.val.val : AutomorphicSpace N)
      (parityProjection N σ (y.val.val : AutomorphicSpace N))
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (parityProjection_selfAdjoint N σ) _ _

/-- The new spectral count with a fixed reflection eigenvalue, summing over
all Fricke and ramified signs. No sign-sector asymptotic is built in. -/
def newParityCount {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
      ((e j : ℂ) • (basis j : AutomorphicSpace N))) (a b σ : ℝ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (newWindowParity N hN basis e henergy hgraph a b σ))

/-- Exact finite-dimensional parity splitting in the physical new spectral band. -/
theorem newParityCount_add {κ : Type*} (N : ℕ) [NeZero N] (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
      ((e j : ℂ) • (basis j : AutomorphicSpace N))) (a b σ : ℝ) (hσ : σ^2 = 1) :
    newParityCount N hN basis e henergy hgraph a b σ +
      newParityCount N hN basis e henergy hgraph a b (-σ) =
      Module.finrank ℂ (newWindowSpace N hN basis e a b) := by
  let := newWindowSpace_finiteDimensional N hN basis e henergy hgraph a b
  exact finite_complementary_projection_finrank
    (newWindowParity N hN basis e henergy hgraph a b σ)
    (newWindowParity N hN basis e henergy hgraph a b (-σ))
    (newWindowParity_idempotent N hN basis e henergy hgraph a b σ hσ)
    (newWindowParity_idempotent N hN basis e henergy hgraph a b (-σ)
      (by simpa only [neg_sq] using hσ)) (by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change parityProjection N σ (x.val.val : AutomorphicSpace N) +
      parityProjection N (-σ) (x.val.val : AutomorphicSpace N) =
      (x.val.val : AutomorphicSpace N)
    simp only [parityProjection_apply, Complex.ofReal_neg]
    module)

/-- At a prime power the single prime trace condition is all of physical
newness. No decomposition or spectral multiplicity is used here. -/
theorem newSpace_prime_power (p k : ℕ) (hp : p.Prime) :
    let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    newSpace (p ^ (k + 1)) (pow_pos hp.pos _) =
      newTraceKernel (pow_pos hp.pos (k + 1))
        (show p ^ k ∣ p ^ (k + 1) from ⟨p, pow_succ p k⟩) := by
  let : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdiv : p ^ (k + 1) / p = p ^ k := by
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  have hpN : p ∣ p ^ (k + 1) := dvd_pow_self p (Nat.succ_ne_zero k)
  ext v
  simp only [newSpace, Submodule.mem_iInf]
  constructor
  · intro hv
    have hh := hv ⟨p, hp, hpN⟩
    simpa only [hdiv] using hh
  · intro hv q
    have hq : q.val = p := (Nat.prime_dvd_prime_iff_eq q.property.1 hp).mp
      (q.property.1.dvd_of_dvd_pow q.property.2)
    simpa only [hq, hdiv] using hv

namespace CuspEnergySpectrum

/-- The checked full cusp parity law, expressed using the actual spectral
bundle and the original slowly shrinking interval. -/
theorem parityBand_short_weyl {N : ℕ} [NeZero N] {hN : 0 < N}
    (S : CuspEnergySpectrum N hN) (σ : ℝ) (hσ : σ ^ 2 = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t => (Module.finrank ℂ (S.parityBand t (t + ε t) σ) : ℝ) / (t * ε t))
      atTop (𝓝 ((quotientMeasure N).real univ / (4 * Real.pi))) :=
  cuspParityWindow_short_interval_weyl N hN S.basis S.energy S.energy_nonneg S.graph
    σ hσ ε hε hproduct

/-- Removing the actual two old images at a simply ramified prime gives
the sharp one-prime trace-new leading constant, with parity preserved. -/
theorem simple_traceNewParityBand_short_weyl (M p : ℕ) [NeZero M] [NeZero (p * M)]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (S : CuspEnergySpectrum M hM)
    (T : CuspEnergySpectrum (p * M) (Nat.mul_pos hp.pos hM))
    (σ : ℝ) (hσ : σ ^ 2 = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (Module.finrank ℂ (S.traceNewParityBand T (Nat.dvd_mul_left M p) t (t + ε t) σ) : ℝ) /
        (t * ε t)) atTop
      (𝓝 (((quotientMeasure (p * M)).real univ - 2 * (quotientMeasure M).real univ) /
        (4 * Real.pi))) := by
  have hhigh := T.parityBand_short_weyl σ hσ ε hε hproduct
  have hlow := S.parityBand_short_weyl σ hσ ε hε hproduct
  have hlimit := hhigh.sub (hlow.const_mul 2)
  convert hlimit using 1
  · funext t
    have hd :
        (Module.finrank ℂ (S.traceNewParityBand T (Nat.dvd_mul_left M p) t (t + ε t) σ) : ℝ) +
          2 * (Module.finrank ℂ (S.parityBand t (t + ε t) σ) : ℝ) =
            (Module.finrank ℂ (T.parityBand t (t + ε t) σ) : ℝ) := by
      exact_mod_cast simple_traceNewParityBand_finrank M p hM hp hcp S T t (t + ε t) σ
    rw [← mul_div_assoc, ← sub_div]
    congr 1
    linarith
  · congr 1
    ring

/-- At repeated 2-levels, the exact lower-band overlap supplies the third
term in the sharp parity coefficient. The group-index condition is discharged. -/
theorem repeated_two_traceNewParityBand_short_weyl (L : ℕ) [NeZero L]
    (hL : 0 < L)
    (S : CuspEnergySpectrum L hL)
    (T : CuspEnergySpectrum (2 * L) (Nat.mul_pos (by decide) hL))
    (V : CuspEnergySpectrum (2 * (2 * L)) (Nat.mul_pos (by decide) (Nat.mul_pos (by decide) hL)))
    (σ : ℝ) (hσ : σ ^ 2 = 1) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop, 0 < ε t ∧ ε t ≤ 1)
    (hproduct : Tendsto (fun t => ε t * slowScale t) atTop atTop) :
    Tendsto (fun t =>
      (Module.finrank ℂ (T.traceNewParityBand V (Nat.dvd_mul_left (2 * L) 2)
        t (t + ε t) σ) : ℝ) / (t * ε t)) atTop
      (𝓝 (((quotientMeasure (2 * (2 * L))).real univ -
        2 * (quotientMeasure (2 * L)).real univ + (quotientMeasure L).real univ) /
          (4 * Real.pi))) := by
  have hhigh := V.parityBand_short_weyl σ hσ ε hε hproduct
  have hmid := T.parityBand_short_weyl σ hσ ε hε hproduct
  have hlow := S.parityBand_short_weyl σ hσ ε hε hproduct
  have hlimit := (hhigh.sub (hmid.const_mul 2)).add hlow
  convert hlimit using 1
  · funext t
    have hd :
        (Module.finrank ℂ (T.traceNewParityBand V (Nat.dvd_mul_left (2 * L) 2)
          t (t + ε t) σ) : ℝ) +
            2 * (Module.finrank ℂ (T.parityBand t (t + ε t) σ) : ℝ) =
              (Module.finrank ℂ (V.parityBand t (t + ε t) σ) : ℝ) +
                (Module.finrank ℂ (S.parityBand t (t + ε t) σ) : ℝ) := by
      exact_mod_cast repeated_traceNewParityBand_finrank L 2 hL Nat.prime_two
        (two_level_relIndex_prime L hL) S T V t (t + ε t) σ hσ
    rw [← mul_div_assoc, ← sub_div, ← add_div]
    congr 1
    linarith
  · congr 1
    ring

#print axioms parityBand_short_weyl
#print axioms simple_traceNewParityBand_short_weyl
#print axioms repeated_two_traceNewParityBand_short_weyl

end CuspEnergySpectrum

#print axioms newSpace_closed
#print axioms newSpace_parityProjection
#print axioms newWindowSpace_finiteDimensional
#print axioms newWindowParity_idempotent
#print axioms newWindowParity_symmetric
#print axioms newParityCount_add
#print axioms newSpace_prime_power

end QuantitativeNinaMaass
