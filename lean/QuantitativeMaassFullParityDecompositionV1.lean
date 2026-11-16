module

public import QuantitativeMaassFullParityOrthogonalV1
public import QuantitativeMaassCanonicalParityDecompositionV1
public import QuantitativeMaassNormalizerParityBandV1
public import QuantitativeMaassLVParityComparisonV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

open Set AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNinaMaass

namespace QuantitativeMaass

local instance (ε : ℝ) : NormedAddCommGroup (AsymptoticCylinderTerminal.Space ε) := inferInstance
local instance (ε : ℝ) : InnerProductSpace ℂ (AsymptoticCylinderTerminal.Space ε) := inferInstance
local instance (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    NormedAddCommGroup (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) :
    InnerProductSpace ℂ (completedNewSignSpace N hN χ) := inferInstance
local instance (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ) :
    NormedAddCommGroup (completedNewSignParitySpace N hN χ η) := inferInstance
local instance (N : ℕ) (hN : 0<N) [NeZero N]
    (χ : admissibleGeneratorIndex N hN→ℂ) (η : ℝ) :
    InnerProductSpace ℂ (completedNewSignParitySpace N hN χ η) := inferInstance

/-- The full canonical terminal range is the orthogonal sum of its two
parities, in the exact terminal metric used for original Euler counting. -/
theorem completedSectorFullTerminal_parity_projection_sum {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N] (e : Sector N)
    (η : ℝ) (hη : η^2=1) :
    embeddingGramProjection
      (V := completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e))
      (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
      (completedNewSignFullTerminalEmbedding A hN.1 P (sectorCharacter N hN.1 e) e)=
    embeddingGramProjection
      (V := completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) η)
      (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
      (completedNewSignParityFullTerminalEmbedding A hN.1 P (sectorCharacter N hN.1 e) e η)+
    embeddingGramProjection
      (V := completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) (-η))
      (H := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
      (completedNewSignParityFullTerminalEmbedding A hN.1 P (sectorCharacter N hN.1 e) e (-η)) := by
  let χ := sectorCharacter N hN.1 e
  let K := completedNewSignFullTerminalEmbedding A hN.1 P χ e
  let Kp := completedNewSignParityFullTerminalEmbedding A hN.1 P χ e η
  let Km := completedNewSignParityFullTerminalEmbedding A hN.1 P χ e (-η)
  obtain ⟨a,ha,hl⟩ := completedNewSignFullTerminalEmbedding_lower A hN P
  have hK (x : completedNewSignSpace N hN.1 χ) : a*‖x‖^2≤‖K x‖^2 :=
    hl χ e (sectorCharacter_norm N hN.1 e)
      (sectorCharacter_coherent N hN.1 e).1 (sectorCharacter_coherent N hN.1 e).2 x
  have hp (x : completedNewSignParitySpace N hN.1 χ η) : a*‖x‖^2≤‖Kp x‖^2 :=
    hK (completedNewSignParityInclusion N hN.1 χ η x)
  have hm (x : completedNewSignParitySpace N hN.1 χ (-η)) : a*‖x‖^2≤‖Km x‖^2 :=
    hK (completedNewSignParityInclusion N hN.1 χ (-η) x)
  have hcK : IsClosed (K.range : Set (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)) :=
    (lower_energy_injective_closed
      (H := completedNewSignSpace N hN.1 χ)
      (K := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) K ha hK).2
  have hcP : IsClosed (Kp.range : Set (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)) :=
    (lower_energy_injective_closed
      (H := completedNewSignParitySpace N hN.1 χ η)
      (K := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) Kp ha hp).2
  have hcM : IsClosed (Km.range : Set (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)) :=
    (lower_energy_injective_closed
      (H := completedNewSignParitySpace N hN.1 χ (-η))
      (K := AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε) Km ha hm).2
  let : CompleteSpace K.range := hcK.completeSpace_coe
  let : CompleteSpace Kp.range := hcP.completeSpace_coe
  let : CompleteSpace Km.range := hcM.completeSpace_coe
  have hs : Kp.range≤K.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨completedNewSignParityInclusion N hN.1 χ η x,rfl⟩
  have ht : Km.range≤K.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨completedNewSignParityInclusion N hN.1 χ (-η) x,rfl⟩
  have ho : ∀ x∈Kp.range,∀ y∈Km.range,inner ℂ x y=0 := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    exact completedParityFullTerminal_opposite_inner_zero A hN.1 P χ e η hη
      (sectorCharacter_coherent N hN.1 e).1 (sectorCharacter_coherent N hN.1 e).2 x y
  have hsplit : ∀ x∈K.range,∃ y∈Kp.range,∃ z∈Km.range,x=y+z := by
    rintro _ ⟨x,rfl⟩
    let xp : completedNewSignParitySpace N hN.1 χ η :=
      ⟨parityProjection N η x.val,completedSectorNewSign_parity N hN e η x.val x.property,
        (mem_completedParitySpace N η _).mpr (parityProjection_idempotent N η hη x.val)⟩
    let xm : completedNewSignParitySpace N hN.1 χ (-η) :=
      ⟨parityProjection N (-η) x.val,completedSectorNewSign_parity N hN e (-η) x.val x.property,
        (mem_completedParitySpace N (-η) _).mpr
          (parityProjection_idempotent N (-η) (by simpa only [neg_sq] using hη) x.val)⟩
    refine ⟨Kp xp,⟨xp,rfl⟩,Km xm,⟨xm,rfl⟩,?_⟩
    change K x=K (completedNewSignParityInclusion N hN.1 χ η xp)+
      K (completedNewSignParityInclusion N hN.1 χ (-η) xm)
    rw [←map_add]
    apply congrArg K
    apply Subtype.ext
    exact (parityProjection_add_neg N η x.val).symm
  have hh := projection_add_of_orthogonal_decomposition K.range Kp.range Km.range hs ht ho hsplit
  rw [embedding_projection_gram_formula K ha hK,embedding_projection_gram_formula Kp ha hp,
    embedding_projection_gram_formula Km ha hm] at hh
  exact hh

#print axioms completedSectorFullTerminal_parity_projection_sum

end QuantitativeMaass
