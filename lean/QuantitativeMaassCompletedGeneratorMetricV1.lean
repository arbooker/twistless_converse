module

public import QuantitativeMaassNormalizerFamilyEnergyV1
public import QuantitativeMaassGeneratorCompletionV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticCongruenceLabels AsymptoticFreshMatrices AsymptoticIntegralSubgroup
open scoped MatrixGroups

namespace QuantitativeMaass

theorem admissibleNormalizerGroup_le_normalizer (N : ℕ) (hN : 0<N) :
    admissibleNormalizerGroup N hN≤(quotientNormalizerGroup N) := by
  rw [admissibleNormalizerGroup,Subgroup.closure_le]
  intro g hg
  apply normalizer_mem_of_conjugations
  · cases hg with
    | fricke => exact fun _ ha => fricke_conj_mem N hN ha
    | half h4 =>
      intro a ha
      simpa only [Int.cast_one] using halfTranslation_conj_mem N h4 1 ha
    | atkin D Q hQ A B hAB hQD =>
      have hD : 0<D := by
        apply Nat.pos_of_ne_zero
        intro hz
        have hzero : N=0 := by simpa only [hz,mul_zero] using hQD.symm
        exact hN.ne' hzero
      simpa only [hQD] using (exactAtkinLabel_normalizes D Q hD hQ A B hAB).1
  · cases hg with
    | fricke =>
      intro a ha
      simpa only [frickeLabel_inv] using fricke_conj_mem N hN ha
    | half h4 =>
      intro a ha
      simpa only [Int.cast_one] using halfTranslation_inv_conj_mem N h4 1 ha
    | atkin D Q hQ A B hAB hQD =>
      have hD : 0<D := by
        apply Nat.pos_of_ne_zero
        intro hz
        have hzero : N=0 := by simpa only [hz,mul_zero] using hQD.symm
        exact hN.ne' hzero
      simpa only [hQD] using (exactAtkinLabel_normalizes D Q hD hQ A B hAB).2

def admissibleGeneratorLift (N : ℕ) (hN : 0<N) (i : admissibleGeneratorIndex N hN) :
    (quotientNormalizerGroup N) :=
  ⟨i.val,admissibleNormalizerGroup_le_normalizer N hN (Subgroup.subset_closure i.property)⟩

/-- Simultaneous generator eigenspaces defined by actual bounded
operators on the completed quotient space, not by a density assumption. -/
def completedGeneratorSpace (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) : Submodule ℂ (AutomorphicSpace N) where
  carrier := {x | ∀ i,quotientNormalizerPullback N (admissibleGeneratorLift N hN i) x=χ i • x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; rw [map_add,hx,hy,smul_add]
  smul_mem' := by intro c x hx i; rw [map_smul,hx,smul_comm]

theorem completedGeneratorSpace_closed (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    IsClosed (completedGeneratorSpace N hN χ : Set (AutomorphicSpace N)) := by
  change IsClosed {x | ∀ i,quotientNormalizerPullback N (admissibleGeneratorLift N hN i) x=χ i • x}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_eq
    (quotientNormalizerPullback N (admissibleGeneratorLift N hN i)).continuous
    (by fun_prop))

instance completedGeneratorSpace_complete (N : ℕ) (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) : CompleteSpace (completedGeneratorSpace N hN χ) :=
  (completedGeneratorSpace_closed N hN χ).completeSpace_coe

/-- The uniform metric lower bound holds on the actual completed
operator eigenspaces, with no assumption about dense eigen-representatives. -/
theorem completedGeneratorSpace_energy_lower (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    ∃ a : ℝ,0<a ∧ ∀ χ : admissibleGeneratorIndex N hN.1 → ℂ,(∀ i,‖χ i‖=1) →
      ∀ x : completedGeneratorSpace N hN.1 χ,
        a*‖x‖^2≤‖weightedQuotientEmbedding N hε hv x.val‖^2 := by
  classical
  let : NeZero N := ⟨hN.1.ne'⟩
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨g,hg,hc,hci,Y,hY,hcover⟩ := admissible_generator_height_cover N hN
  let g' (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : (quotientNormalizerGroup N) :=
    ⟨g q,normalizer_mem_of_conjugations N (g q) (hc q) (hci q)⟩
  let m := Fintype.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  refine ⟨heightWeightFloor ε v Y/((m:ℝ)+1),
    div_pos (heightWeightFloor_pos hε hY v) (by positivity),?_⟩
  intro χ hχ x
  have hsub : admissibleNormalizerGroup N hN.1≤
      (normalizerEigenStabilizer N x.val).map (quotientNormalizerGroup N).subtype := by
    rw [admissibleNormalizerGroup,Subgroup.closure_le]
    intro a ha
    refine ⟨admissibleGeneratorLift N hN.1 ⟨a,ha⟩,?_,rfl⟩
    exact ⟨χ ⟨a,ha⟩,hχ ⟨a,ha⟩,x.property ⟨a,ha⟩⟩
  have hn (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      ‖weightedQuotientEmbedding N hε hv (quotientNormalizerPullback N (g' q)⁻¹ x.val)‖^2=
        ‖weightedQuotientEmbedding N hε hv x.val‖^2 := by
    obtain ⟨a,ha,he⟩ := hsub (hg q)
    have heq : a=g' q := Subtype.ext he
    have hi := (normalizerEigenStabilizer N x.val).inv_mem (heq ▸ ha)
    obtain ⟨c,hc',he'⟩ := hi
    rw [he',map_smul,norm_smul,hc',one_mul]
  have hl := normalizer_family_completed_lower N hε hY hv g' hcover x.val
  simp only [hn,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hl
  change heightWeightFloor ε v Y*‖x‖^2≤(m:ℝ)*‖weightedQuotientEmbedding N hε hv x.val‖^2 at hl
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0<(m:ℝ)+1)).mpr
  nlinarith [sq_nonneg ‖weightedQuotientEmbedding N hε hv x.val‖]

def completedGeneratorWeightedEmbedding (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN → ℂ) :
    completedGeneratorSpace N hN χ →L[ℂ] Lp ℂ 2 (quotientMeasure 0) :=
  (weightedQuotientEmbedding N hε hv).comp (completedGeneratorSpace N hN χ).subtypeL

theorem completedGeneratorWeightedEmbedding_closed (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (χ : admissibleGeneratorIndex N hN.1 → ℂ) (hχ : ∀ i,‖χ i‖=1) :
    Function.Injective (completedGeneratorWeightedEmbedding N hN.1 hε hv χ) ∧
      IsClosed (Set.range (completedGeneratorWeightedEmbedding N hN.1 hε hv χ)) := by
  obtain ⟨a,ha,hl⟩ := completedGeneratorSpace_energy_lower N hN hε hv
  apply lower_energy_injective_closed
    (H := completedGeneratorSpace N hN.1 χ) (K := Lp ℂ 2 (quotientMeasure 0))
    (completedGeneratorWeightedEmbedding N hN.1 hε hv χ) ha
  intro x
  exact hl χ hχ x

#print axioms admissibleNormalizerGroup_le_normalizer
#print axioms completedGeneratorSpace_closed
#print axioms completedGeneratorSpace_energy_lower
#print axioms completedGeneratorWeightedEmbedding_closed

end QuantitativeMaass
