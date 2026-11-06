module

public import QuantitativeArithmeticSmallLevelTwentyTwoHeckeV1
public import QuantitativeArithmeticEntireQuotientV1
public import SmallLevelTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Complex SmallLevelAdditive SmallLevelTaylor Filter Set
open scoped Topology

/-- The even quadratic additive combination, equal to the Gauss-factor
multiple of the chi5 twist in its original convergence half-plane. -/
def quadraticCombination (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  evenOne k f s-evenTwo k f s

def denominator (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  heckeScalar m f s+1

def numerator (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  (1-heckeScalar m f s)*ramanujanEntire 22 (2*m) f 5 s+
    2*evenTenthEntire m f s

theorem denominator_entire (m : ℕ) (f : ℕ → ℂ) : Differentiable ℂ (denominator m f) := by
  unfold denominator heckeScalar
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop

theorem denominator_nonzero (m : ℕ) (f : ℕ → ℂ) : ∃ s : ℂ, denominator m f s≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw 0
  have h1 := hw 1
  norm_num [denominator,heckeScalar,Complex.cpow_neg,Complex.cpow_natCast] at h0 h1
  have hbad : (1:ℂ)=0 := by
    linear_combination 2*h1-h0
  norm_num at hbad

theorem original_numerator_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) : Differentiable ℂ (numerator m f) := by
  have he := (original_tenth_continuation m hm hf).1
  have hr : Differentiable ℂ (ramanujanEntire 22 (2*m) f 5) := by
    intro s
    exact ((original_ramanujan_entire (by decide : 0<22) (by omega) hf (by decide : 0<5)).1 s).differentiableAt
  have hc : Differentiable ℂ (fun s => 1-heckeScalar m f s) := by
    unfold heckeScalar
    simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
    fun_prop
  exact (hc.mul hr).add (he.const_mul 2)

/-- Actual original-input numerator identity, before any quotient or
meromorphic continuation. No restriction on the complex Hecke eigenvalue. -/
theorem original_quotient_identity (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      numerator m f s=denominator m f s*quadraticCombination (2*m) f s := by
  obtain ⟨Bc,hc⟩ := (original_tenth_continuation m hm hf).2
  obtain ⟨Bh,hh⟩ := original_even_hecke m hm hf
  obtain ⟨Br,hr⟩ := (original_ramanujan_entire (by decide : 0<22) (by omega) hf (by decide : 0<5)).2
  refine ⟨max Bc (max Bh Br),fun s hs => ?_⟩
  have hcs := lt_of_le_of_lt (le_max_left Bc (max Bh Br)) hs
  have hhs : Bh<s.re := lt_of_le_of_lt ((le_max_left Bh Br).trans (le_max_right Bc _)) hs
  have hrs : Br<s.re := lt_of_le_of_lt ((le_max_right Bh Br).trans (le_max_right Bc _)) hs
  have hb : evenTenthEntire m f s=tenthSum (2*m) f s := hc s hcs
  unfold numerator
  rw [hb,hr s hrs,ramanujan_five]
  unfold denominator quadraticCombination
  linear_combination -2*(hh s hhs)

/-- The original even quadratic combination modulo5 has a global
normal-form meromorphic continuation. Its only possible poles lie on the
explicit Hecke2 denominator. Pole removal is not claimed here. -/
theorem original_quadratic_continuation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ → ℂ), (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=quadraticCombination (2*m) f s) ∧
      (∀ s, denominator m f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator m f s)) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_quotient_identity m hm hf
  have hinit (z : ℂ) (hz : max B H<z.re) : AnalyticAt ℂ (quadraticCombination (2*m) f) z := by
    have hs := lt_of_le_of_lt (le_max_left B H) hz
    exact ((hB (1/5) z hs).1.add (hB (-1/5) z hs).1).sub
      ((hB (2/5) z hs).1.add (hB (-2/5) z hs).1)
  obtain ⟨G,hG,hagree,hpole,hgerm⟩ := QuantitativeArithmeticEntireQuotient.continuation
    (numerator m f) (denominator m f) (quadraticCombination (2*m) f) (max B H)
    (fun z => (original_numerator_entire m hm hf).analyticAt z)
    (fun z => (denominator_entire m f).analyticAt z)
    (denominator_nonzero m f) hinit
    (fun z hz => hH z (lt_of_le_of_lt (le_max_right _ _) hz))
  exact ⟨max B H,G,hG,hagree,hpole,hgerm⟩

#print axioms denominator_nonzero
#print axioms original_quotient_identity
#print axioms original_quadratic_continuation
end QuantitativeArithmeticSmallLevelTwentyTwo
