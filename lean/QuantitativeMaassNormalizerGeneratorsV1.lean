module

public import QuantitativeMaassNormalizerWordCoverV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticIntegralSubgroup AsymptoticClassicalPetersson
open AsymptoticFreshMatrices
open scoped MatrixGroups ENNReal

namespace QuantitativeMaass

/-- The fixed geometric generators needed for the admissible cusp cover. -/
inductive admissibleNormalizerGenerator (N : ℕ) (hN : 0<N) :
    AsymptoticRationalGroup.Group → Prop
  | fricke : admissibleNormalizerGenerator N hN (frickeLabel N hN)
  | half (h4 : 4∣N) : admissibleNormalizerGenerator N hN (translationLabel (1/2))
  | atkin (D Q : ℕ) (hQ : 0<Q) (A B : ℤ) (hAB : (Q:ℤ)*A+(D:ℤ)*B=1)
      (hQD : Q*D=N) : admissibleNormalizerGenerator N hN (exactAtkinLabel D Q hQ A B hAB)

def admissibleNormalizerGroup (N : ℕ) (hN : 0<N) : Subgroup AsymptoticRationalGroup.Group :=
  Subgroup.closure {g | admissibleNormalizerGenerator N hN g}

/-- Both the normalizer family and its height bound are chosen before
any function or eigenvalue is introduced. -/
theorem admissible_generator_height_cover (N : ℕ) (hN : GridAdmissibleGap.Admissible N) :
    ∃ g : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → AsymptoticRationalGroup.Group,
      (∀ q,g q∈admissibleNormalizerGroup N hN.1) ∧
      (∀ q,∀ a∈gamma N,g q*a*(g q)⁻¹∈gamma N) ∧
      (∀ q,∀ a∈gamma N,(g q)⁻¹*a*g q∈gamma N) ∧
      ∃ Y : ℝ,0<Y ∧ ∀ z : ℍ,∃ q,∃ a : gamma N,Y≤(a.val • (g q • z)).im := by
  apply admissible_normalizer_height_cover_subgroup N hN (admissibleNormalizerGroup N hN.1)
  · intro h4
    exact Subgroup.subset_closure (admissibleNormalizerGenerator.half h4)
  · exact Subgroup.subset_closure admissibleNormalizerGenerator.fricke
  · intro D Q hQ A B hAB hQD
    exact Subgroup.subset_closure (admissibleNormalizerGenerator.atkin D Q hQ A B hAB hQD)

/-- Modulus-one equations for the elementary generators imply the lower
weighted metric estimate with a constant independent of the function. -/
theorem admissible_generator_energy_lower (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    ∃ c : ℝ,0<c ∧ ∀ f : ℍ → ℂ,Measurable f →
      (∀ a : gamma N,∀ z,f (a.val • z)=f z) →
      (∀ g,admissibleNormalizerGenerator N hN.1 g → ∀ z,‖f (g • z)‖=‖f z‖) →
      ENNReal.ofReal c*(∫⁻ z,ENNReal.ofReal (‖f z‖^2) ∂quotientMeasure N) ≤
        (Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ≥0∞)*
          ∫⁻ z,ENNReal.ofReal (‖(AsymptoticCompactBranch.cap ε v z:ℂ)*f z‖^2)
            ∂quotientMeasure 0 := by
  classical
  let : NeZero N := ⟨hN.1.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨g,hg,hc,hci,Y,hY,hcover⟩ := admissible_generator_height_cover N hN
  refine ⟨heightWeightFloor ε v Y,heightWeightFloor_pos hε hY v,?_⟩
  intro f hf hinv hgen
  have hS : admissibleNormalizerGroup N hN.1 ≤ modulusStabilizer f := by
    rw [admissibleNormalizerGroup,Subgroup.closure_le]
    intro a ha
    exact hgen a ha
  have hm : ∀ q z,‖f (g q • z)‖=‖f z‖ := fun q => hS (hg q)
  simpa only [Nat.card_eq_fintype_card] using
    weighted_quotient_energy_lower_of_normalizers N hε hY hv g hc hci hcover f hf hinv hm

#print axioms admissible_generator_height_cover
#print axioms admissible_generator_energy_lower

end QuantitativeMaass
