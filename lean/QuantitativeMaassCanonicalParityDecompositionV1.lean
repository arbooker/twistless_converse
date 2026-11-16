module

public import QuantitativeMaassTerminalParityOrthogonalV1
public import QuantitativeMaassNormalizerParityBandV1
public import QuantitativeMaassLVParityComparisonV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

open Set AsymptoticClassicalPetersson AsymptoticSectorSigns QuantitativeNinaMaass

namespace QuantitativeMaass

local instance (ε : ℝ) : NormedAddCommGroup (terminalNonzeroModes ε) := inferInstance
local instance (ε : ℝ) : InnerProductSpace ℂ (terminalNonzeroModes ε) := inferInstance
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

theorem completedSectorNewSign_reflection (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) (e : Sector N) (x : AutomorphicSpace N)
    (hx : x∈completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e)) :
    reflectionIsometry N x∈completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e) := by
  rw [←completedCountingSectorSpace_eq_newSign N hN e] at hx ⊢
  rw [completedCountingSectorSpace_mem] at hx ⊢
  refine ⟨⟨reflectionIsometry_mem_localCuspidalSpace N hN.1 x hx.1.1,
    newSpace_reflection N hN.1 x hx.1.2⟩,?_⟩
  intro i
  have hr := sectorNormalizerGroup_reflection N hN.1 i x
  change (quotientNormalizerPullback N (sectorNormalizerGroup N hN.1 i)).toContinuousLinearMap
      (reflectionIsometry N x)=
    reflectionIsometry N ((quotientNormalizerPullback N (sectorNormalizerGroup N hN.1 i)).toContinuousLinearMap x) at hr
  rw [sectorNormalizerGroup_action] at hr
  rw [hr,hx.2 i,map_smul]

theorem completedSectorNewSign_parity (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) (e : Sector N) (η : ℝ)
    (x : AutomorphicSpace N) (hx : x∈completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e)) :
    parityProjection N η x∈completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e) := by
  rw [parityProjection_apply]
  exact (completedNewSignSpace N hN.1 _).smul_mem _
    ((completedNewSignSpace N hN.1 _).add_mem hx
      ((completedNewSignSpace N hN.1 _).smul_mem _ (completedSectorNewSign_reflection N hN e x hx)))

/-- Orthogonal summands give the actual full projection, not just a bound
on its range. -/
theorem projection_add_of_orthogonal_decomposition {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W S T : Submodule ℂ H) [CompleteSpace W] [CompleteSpace S] [CompleteSpace T]
    (hS : S≤W) (hT : T≤W) (hort : ∀ x∈S,∀ y∈T,inner ℂ x y=0)
    (hsplit : ∀ x∈W,∃ y∈S,∃ z∈T,x=y+z) :
    W.starProjection=S.starProjection+T.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact W.add_mem (hS (S.starProjection_apply_mem x)) (hT (T.starProjection_apply_mem x))
  · intro w hw
    obtain ⟨y,hy,z,hz,rfl⟩ := hsplit w hw
    have h1 := S.starProjection_inner_eq_zero x y hy
    have h2 := T.starProjection_inner_eq_zero x z hz
    have h3 := hort (S.starProjection x) (S.starProjection_apply_mem x) z hz
    have h4 : inner ℂ (T.starProjection x) y=0 :=
      inner_eq_zero_symm.mp (hort y hy (T.starProjection x) (T.starProjection_apply_mem x))
    change inner ℂ (x-(S.starProjection x+T.starProjection x)) (y+z)=0
    simp only [inner_sub_left,inner_add_left,inner_add_right,h3,h4,zero_add,add_zero] at h1 h2 ⊢
    linear_combination h1+h2

/-- The full canonical terminal range is the orthogonal sum of its two
parities, in the exact terminal metric used for original Euler counting. -/
theorem completedSectorTerminal_parity_projection_sum {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : GridAdmissibleGap.Admissible N)
    (P : FinitenessGlobalHeight.Parameters A) [NeZero N] (e : Sector N)
    (η : ℝ) (hη : η^2=1) :
    embeddingGramProjection
      (V := completedNewSignSpace N hN.1 (sectorCharacter N hN.1 e))
      (H := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)
      (completedNewSignTerminalEmbedding A hN.1 P (sectorCharacter N hN.1 e) e)=
    embeddingGramProjection
      (V := completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) η)
      (H := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)
      (completedNewSignParityTerminalEmbedding A hN.1 P (sectorCharacter N hN.1 e) e η)+
    embeddingGramProjection
      (V := completedNewSignParitySpace N hN.1 (sectorCharacter N hN.1 e) (-η))
      (H := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)
      (completedNewSignParityTerminalEmbedding A hN.1 P (sectorCharacter N hN.1 e) e (-η)) := by
  let χ := sectorCharacter N hN.1 e
  let K := completedNewSignTerminalEmbedding A hN.1 P χ e
  let Kp := completedNewSignParityTerminalEmbedding A hN.1 P χ e η
  let Km := completedNewSignParityTerminalEmbedding A hN.1 P χ e (-η)
  obtain ⟨a,ha,hl⟩ := completedNewSignTerminalEmbedding_lower A hN P
  have hK (x : completedNewSignSpace N hN.1 χ) : a*‖x‖^2≤‖K x‖^2 :=
    hl χ e (sectorCharacter_norm N hN.1 e)
      (sectorCharacter_coherent N hN.1 e).1 (sectorCharacter_coherent N hN.1 e).2 x
  have hp (x : completedNewSignParitySpace N hN.1 χ η) : a*‖x‖^2≤‖Kp x‖^2 :=
    hK (completedNewSignParityInclusion N hN.1 χ η x)
  have hm (x : completedNewSignParitySpace N hN.1 χ (-η)) : a*‖x‖^2≤‖Km x‖^2 :=
    hK (completedNewSignParityInclusion N hN.1 χ (-η) x)
  have hcK : IsClosed (K.range : Set (terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)) :=
    (lower_energy_injective_closed
      (H := completedNewSignSpace N hN.1 χ)
      (K := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε) K ha hK).2
  have hcP : IsClosed (Kp.range : Set (terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)) :=
    (lower_energy_injective_closed
      (H := completedNewSignParitySpace N hN.1 χ η)
      (K := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε) Kp ha hp).2
  have hcM : IsClosed (Km.range : Set (terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε)) :=
    (lower_energy_injective_closed
      (H := completedNewSignParitySpace N hN.1 χ (-η))
      (K := terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε) Km ha hm).2
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
    exact completedParityTerminal_opposite_inner_zero A hN.1 P χ e η hη
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

#print axioms completedSectorNewSign_reflection
#print axioms completedSectorNewSign_parity
#print axioms projection_add_of_orthogonal_decomposition
#print axioms completedSectorTerminal_parity_projection_sum

end QuantitativeMaass
