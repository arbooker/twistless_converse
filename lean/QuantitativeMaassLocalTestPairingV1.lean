module

public import QuantitativeMaassLocalRestrictionV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

theorem localSeedMemLp (K : Set ℍ) (u : SmoothUpperSeed) :
    MemLp (upperFunction u.toFun) 2 (volume.restrict K) :=
  ((upperFunction_continuous u.smooth).memLp_of_hasCompactSupport u.compact).restrict K

def localSeedVector (K : Set ℍ) (u : SmoothUpperSeed) : Lp ℂ 2 (volume.restrict K) :=
  (localSeedMemLp K u).toLp (upperFunction u.toFun)

/-- Unfolding identifies compact local L2 tests with the literal Poincare
test vector. This equality holds on the whole Hilbert completion. -/
theorem quotientRestriction_pairing (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (hKm : MeasurableSet K) (u : SmoothUpperSeed)
    (hs : tsupport (upperFunction u.toFun)⊆K) (f : AutomorphicSpace N) :
    inner ℂ (localSeedVector K u) (quotientRestriction N K hK hKm f)=
      inner ℂ (poincareSeedVector N u) f := by
  have he : (fun f : AutomorphicSpace N =>
      inner ℂ (localSeedVector K u) (quotientRestriction N K hK hKm f))=
      fun f => inner ℂ (poincareSeedVector N u) f := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (by fun_prop) (by fun_prop)
    funext g
    dsimp only [Function.comp_apply]
    rw [quotientRestriction_representative]
    have hl : inner ℂ (localSeedVector K u) ((representativeLocalMemLp N K hK hKm g).toLp g.val)=
        ∫ Z in K, star (upperFunction u.toFun Z)*g.val Z := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(localSeedMemLp K u).coeFn_toLp,
        (representativeLocalMemLp N K hK hKm g).coeFn_toLp] with Z hu hg
      change inner ℂ ((localSeedMemLp K u).toLp (upperFunction u.toFun) Z)
        ((representativeLocalMemLp N K hK hKm g).toLp g.val Z)=_
      rw [hu,hg]
      simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]
    have hr : inner ℂ (poincareSeedVector N u)
        (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) g)=
        ∫ Z, star (poincareSum (G := gamma N) (upperFunction u.toFun) Z)*g.val Z
          ∂quotientMeasure N := by
      change inner ℂ (poincareSeedVector N u).val (g.property.2.2.toLp g.val)=_
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [poincareSeedVector_coeFn N u,g.property.2.2.coeFn_toLp] with Z hu hg
      rw [hu,hg]
      simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]
    rw [hl,hr,congruence_poincare_pairing_left N g.val g.property.1
      g.property.2.1 g.property.2.2 (upperFunction u.toFun) (upperFunction_continuous u.smooth) u.compact]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro Z hZ
    have hu : upperFunction u.toFun Z=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hZ (hs h))
    rw [hu,star_zero,zero_mul]
  exact congrFun he f

theorem quotientRestriction_test_integral (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (hKm : MeasurableSet K) (u : SmoothUpperSeed)
    (hs : tsupport (upperFunction u.toFun)⊆K) (f : AutomorphicSpace N) :
    (∫ Z in K, star (upperFunction u.toFun Z)*(quotientRestriction N K hK hKm f) Z)=
      inner ℂ (poincareSeedVector N u) f := by
  rw [← quotientRestriction_pairing N K hK hKm u hs f,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(localSeedMemLp K u).coeFn_toLp] with Z hu
  change star (upperFunction u.toFun Z)*(quotientRestriction N K hK hKm f) Z=
    inner ℂ ((localSeedMemLp K u).toLp (upperFunction u.toFun) Z) _
  rw [hu]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

#print axioms quotientRestriction_pairing
#print axioms quotientRestriction_test_integral

end QuantitativeMaass
