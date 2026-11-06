module

public import AsymptoticFunctionalCalculusApproxV1
public import QuantitativeHolomorphicNewtonTransportV1
public import QuantitativeEulerOldProjectionKernelV1
public import QuantitativeEulerEndpointCutCalculusV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointCutIntertwining
open ContinuousLinearMap Filter Polynomial QuantitativeSpectralCut
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cfc_intertwines (A B S : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hS : B.comp S=S.comp A) (f : ℝ → ℝ) (hf : Continuous f) :
    (cfc f B).comp S=S.comp (cfc f A) := by
  let T : Bool → H →L[ℂ] H := fun b => if b then B else A
  have ht (b : Bool) : IsSelfAdjoint (T b) := by cases b <;> assumption
  have hn (b : Bool) : ‖T b‖≤max ‖A‖ ‖B‖ := by
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  obtain ⟨p,hp⟩ := AsymptoticFunctionalCalculus.exists_polynomial_approximation T ht _ hn f hf
  have ha : Tendsto (fun n => aeval A (p n)) atTop (𝓝 (cfc f A)) := hp false
  have hb : Tendsto (fun n => aeval B (p n)) atTop (𝓝 (cfc f B)) := hp true
  apply ContinuousLinearMap.ext
  intro v
  have hleft := ((ContinuousLinearMap.apply ℂ H (S v)).continuous.tendsto _).comp hb
  have hright := S.continuous.tendsto (cfc f A v) |>.comp
    (((ContinuousLinearMap.apply ℂ H v).continuous.tendsto _).comp ha)
  have he (n : ℕ) : aeval B (p n) (S v)=S (aeval A (p n) v) :=
    congrArg (fun R : H →L[ℂ] H => R v)
      (QuantitativeHolomorphic.real_polynomial_intertwines A B S hS (p n))
  change Tendsto (fun n => aeval B (p n) (S v)) atTop (𝓝 (cfc f B (S v))) at hleft
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Intertwining survives the exact low spectral projection, including threshold eigenvectors. -/
theorem lowAt_projection_intertwines (A B S : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hS : B.comp S=S.comp A) (a : ℝ) :
    S.comp (lowAt A a).starProjection=(lowAt B a).starProjection.comp S := by
  let f := fun r : ℝ => (r-a)⁺
  have hf : Continuous f := by unfold f; fun_prop
  have hi := cfc_intertwines A B S hA hB hS f hf
  have hpa := QuantitativeEulerEndpointCutCalculus.shifted_positivePart A hA a
  have hpb := QuantitativeEulerEndpointCutCalculus.shifted_positivePart B hB a
  have he : S.comp (positivePart (A-a • 1))=(positivePart (B-a • 1)).comp S := by
    rw [hpa,hpb]
    exact hi.symm
  apply ContinuousLinearMap.ext
  intro v
  exact QuantitativeEulerOldProjectionBlock.kernel_intertwine S
    (positivePart (A-a • 1)) (positivePart (B-a • 1))
    (IsSelfAdjoint.of_nonneg (CFC.posPart_nonneg _))
    (IsSelfAdjoint.of_nonneg (CFC.posPart_nonneg _)) he v

theorem highAt_projection_intertwines (A B S : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hS : B.comp S=S.comp A) (a : ℝ) :
    S.comp (highAt A a).starProjection=(highAt B a).starProjection.comp S := by
  apply ContinuousLinearMap.ext
  intro v
  have hl := congrArg (fun R : H →L[ℂ] H => R v)
    (lowAt_projection_intertwines A B S hA hB hS a)
  change S ((lowAt A a)ᗮ.starProjection v)=(lowAt B a)ᗮ.starProjection (S v)
  rw [Submodule.starProjection_orthogonal_val,Submodule.starProjection_orthogonal_val,map_sub]
  exact congrArg (fun w => S v-w) hl

#print axioms cfc_intertwines
#print axioms lowAt_projection_intertwines
#print axioms highAt_projection_intertwines
end QuantitativeEulerEndpointCutIntertwining
