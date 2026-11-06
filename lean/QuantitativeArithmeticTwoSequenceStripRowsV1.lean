module
public import QuantitativeArithmeticMellinStripBoundV1
public import QuantitativeArithmeticTwoSequenceMellinRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticMellinStrip
open Complex Set
/-- Uniform boundedness on every compact vertical substrip of a half-plane. -/
def BoundedSubstrips (b : ℝ) (F : ℂ → ℂ) : Prop :=
  ∀ l u : ℝ,b<l → b<u → ∃ C : ℝ,0≤C ∧
    ∀ s : ℂ,l≤s.re → s.re≤u → ‖F s‖≤C

theorem BoundedSubstrips.mono {a b : ℝ} {F : ℂ → ℂ}
    (h : BoundedSubstrips a F) (hab : a≤b) : BoundedSubstrips b F :=
  fun l u hl hu => h l u (hab.trans_lt hl) (hab.trans_lt hu)
end QuantitativeArithmeticMellinStrip

namespace QuantitativeArithmeticTwoSequenceTaylor
open SmallLevelTaylor Complex Filter Asymptotics Set MeasureTheory
open FinitenessFourierConstruction FinitenessPolynomialSeries QuantitativeArithmeticMellinStrip
open scoped Topology

/-- Uniform vertical bounds for the actual untruncated Taylor remainder. -/
theorem two_error_strip_bound {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) {a b : ℕ → ℂ}
    (ha : PolynomialBound a) (ha0 : a 0=0) (hb : PolynomialBound b) (hb0 : b 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ,0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier b (-1/((L:ℂ)*z))) :
    ∃ K : ℕ,∀ M : ℕ,BoundedSubstrips ((K:ℝ)-(M:ℝ))
      (mellin (twoError k a b L r χ M)) := by
  obtain ⟨K,hK⟩ := two_error_small hL hr k a hb hb0 χ hF
  refine ⟨K,?_⟩
  intro M l u hl hu
  have hzero : twoError k a b L r χ M=O[𝓝[>] 0]
      (fun y : ℝ => y^(-((K:ℝ)-(M:ℝ)))) := by
    rw [show -((K:ℝ)-(M:ℝ))=(M:ℝ)-(K:ℝ) by ring]
    exact hK M
  have hconv (v : ℝ) (hv : (K:ℝ)-(M:ℝ)<v) :
      MellinConvergent (twoError k a b L r χ M) (v:ℂ) := by
    apply mellinConvergent_of_isBigO_rpow (b := (K:ℝ)-(M:ℝ))
      (two_error_local k ha hb hL hr χ M)
      (two_error_rapid k ha ha0 hb hb0 hL hr χ M (-(v+1)))
      (by simp only [Complex.ofReal_re]; linarith)
      hzero
    exact hv
  exact bounded_strip _ l u (hconv l hl) (hconv u hu)

/-- The same exact original Taylor identities now retain both analyticity
and vertical strip bounds of their actual remainders. -/
theorem two_taylor_bounded_rows {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) {a b : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0)
    (hb : PolynomialBound b) (hb0 : b 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ,0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier b (-1/((L:ℂ)*z))) :
    ∃ B : ℝ,∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (twoError k a b L r χ M)) {s : ℂ | B-(M:ℝ)<s.re} ∧
      BoundedSubstrips (B-(M:ℝ)) (mellin (twoError k a b L r χ M)) ∧
      ∀ s : ℂ,B<s.re →
        SmallLevelAdditive.transform a r s-
          (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*
            (∑ n∈Finset.range M,mellinTaylorTerm k b (-1/(L*r)) (L*r^2) r n s)=
          mellin (twoError k a b L r χ M) s := by
  obtain ⟨B,hB⟩ := two_taylor_mellin_rows hL hr k ha ha0 hb hb0 χ hF
  obtain ⟨K,hK⟩ := two_error_strip_bound hL hr k ha ha0 hb hb0 χ hF
  refine ⟨max B (K:ℝ),?_⟩
  intro M
  refine ⟨?_,(hK M).mono (sub_le_sub_right (le_max_right _ _) _),?_⟩
  · intro s hs
    apply (hB M).1 s
    change max B (K:ℝ)-(M:ℝ)<s.re at hs
    change B-(M:ℝ)<s.re
    linarith [le_max_left B (K:ℝ)]
  · intro s hs
    exact (hB M).2 s ((le_max_left _ _).trans_lt hs)
#print axioms two_error_strip_bound
#print axioms two_taylor_bounded_rows
end QuantitativeArithmeticTwoSequenceTaylor
