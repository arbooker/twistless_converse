module

public import QuantitativeMaassFrickeHalfV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix UpperHalfPlane AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticIntegralSubgroup
open scoped MatrixGroups

namespace QuantitativeMaass

theorem admissible_cusp_reduction_subgroup (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (S : Subgroup AsymptoticRationalGroup.Group)
    (hT : 4∣N → translationLabel (1/2)∈S)
    (hL : ∀ L : ℕ,0<L → 4*L=N → integralLabel (lowerSL (2*L) 1)∈S)
    (a : SL(2,ℤ)) :
    ∃ g : AsymptoticRationalGroup.Group,g∈S ∧
      (∀ b∈gamma N,g*b*g⁻¹∈gamma N) ∧ (∀ b∈gamma N,g⁻¹*b*g∈gamma N) ∧
      ∃ a' : SL(2,ℤ),fullDyadicDenominator N (a' 1 0).natAbs ∧
      ∃ d : ℕ,∃ hd : 0<d,g*integralLabel a=integralLabel a'*dilationLabel d hd := by
  by_cases hfull : fullDyadicDenominator N (a 1 0).natAbs
  · refine ⟨1,S.one_mem,?_,?_,a,hfull,1,by decide,?_⟩
    · intro b hb; simpa using hb
    · intro b hb; simpa using hb
    · rw [dilationLabel_one,one_mul,mul_one]
  have hc2 : (2:ℤ)∣a 1 0 := by
    by_contra h
    exact hfull (fullDyadicDenominator_of_odd N (a 1 0) h)
  have hN4 : 4∣N := by
    by_contra h
    exact hfull (fullDyadicDenominator_of_level N h (a 1 0))
  by_cases hc4 : (4:ℤ)∣a 1 0
  · have hN8 : 8∣N := by
      by_contra h
      exact hfull (fullDyadicDenominator_of_four N h (a 1 0) hc4)
    have hc8 : ¬(8:ℤ)∣a 1 0 := by
      intro h
      exact hfull (fullDyadicDenominator_of_eight N (a 1 0) h)
    obtain ⟨M,rfl⟩ := hN8
    have h4 : 4*(2*M)=8*M := by omega
    have h2 : 2*(2*M)=4*M := by omega
    refine ⟨integralLabel (lowerSL (4*M) 1),?_,?_,?_,lowerSL (4*M) 1*a,?_,1,by decide,?_⟩
    · have hp : 0<2*M := by have := hN.1; omega
      simpa only [h2] using hL (2*M) hp h4
    · intro b hb
      have hb' : b∈gamma (4*(2*M)) := by simpa only [h4] using hb
      simpa only [h4,h2] using lowerHalfLabel_conj_mem (2*M) 1 hb'
    · intro b hb
      have hb' : b∈gamma (4*(2*M)) := by simpa only [h4] using hb
      simpa only [h4,h2] using lowerHalfLabel_inv_conj_mem (2*M) 1 hb'
    · exact fullDyadicDenominator_of_eight (8*M) _ (lowerHalf_cusp_eight M hN.2.1 a hc4 hc8)
    · rw [dilationLabel_one,mul_one,map_mul]
  · obtain ⟨c,u,hc,hu,hco⟩ := halfCuspReduction_exists a hc2 hc4
    refine ⟨translationLabel (1/2),hT hN4,?_,?_,halfCuspReduction a c u hc hu,?_,4,by decide,?_⟩
    · intro b hb
      simpa only [Int.cast_one] using halfTranslation_conj_mem N hN4 1 hb
    · intro b hb
      simpa only [Int.cast_one] using halfTranslation_inv_conj_mem N hN4 1 hb
    · exact fullDyadicDenominator_of_odd N c hco
    · exact halfCuspReduction_label a c u hc hu


#print axioms admissible_cusp_reduction_subgroup

end QuantitativeMaass
