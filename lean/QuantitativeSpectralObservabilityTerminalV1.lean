module

public import QuantitativeSpectralObservabilityEnergyV1
public import QuantitativeSpectralWordDefectV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set
open AsymptoticHyperbolicArea AsymptoticOrbitDiagonal
open QuantitativeSpectralObservabilityDecoded QuantitativeSpectralWordDefect
open scoped MatrixGroups BigOperators lp

theorem terminal_energy_split (ε H : ℝ) (x : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    ‖corner (terminal ε) x v‖^2 ≤
      ‖corner (terminalBand ε H) x v‖^2+‖corner (terminal H) x v‖^2 := by
  have hn (f : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
      HasSum (fun g => ‖f g‖^2) (‖f‖^2) := by
    simpa using lp.hasSum_norm (p:=2) (by norm_num) f
  have hr := (hn (corner (terminalBand ε H) x v)).add (hn (corner (terminal H) x v))
  have hp (g : AsymptoticRationalGroup.Group) :
      ‖corner (terminal ε) x v g‖^2 ≤
        ‖corner (terminalBand ε H) x v g‖^2+‖corner (terminal H) x v g‖^2 := by
    classical
    by_cases hg : g • x∈terminal ε
    · by_cases hh : (g • x).im≤H
      · have hb : g • x∈terminalBand ε H := ⟨hg,hh⟩
        simp only [corner_apply,ite_eq_left hg,ite_eq_left hb]
        nlinarith [sq_nonneg ‖corner (terminal H) x v g‖,
          sq_nonneg ‖corner (terminalBand ε H) x v g‖]
      · have ht : g • x∈terminal H := ⟨hg.1,lt_of_not_ge hh⟩
        simp only [corner_apply,ite_eq_left hg,ite_eq_left ht]
        nlinarith [sq_nonneg ‖corner (terminal H) x v g‖,
          sq_nonneg ‖corner (terminalBand ε H) x v g‖]
    · simp only [corner_apply,ite_eq_right hg,norm_zero,zero_pow (by decide : 2≠0)]
      positivity
  have hh := (hn (corner (terminal ε) x v)).summable.tsum_le_tsum hp hr.summable
  rwa [(hn (corner (terminal ε) x v)).tsum_eq,hr.tsum_eq] at hh

/-- One compact set contains every intermediate point in the fixed
reducing words; it is explicitly constructed from the terminal rectangle. -/
def wordRegion (W : Finset (List SL(2,ℤ))) (ε H : ℝ) : Set ℍ :=
  ⋃ l : W, region l.val (terminalRectangle ε H)

theorem wordRegion_compact (W : Finset (List SL(2,ℤ))) {ε : ℝ}
    (hε : 0<ε) (H : ℝ) : IsCompact (wordRegion W ε H) := by
  apply isCompact_iUnion
  intro l
  exact region_compact l.val (terminalRectangle_compact hε H)

/-- Actual norm observability by a fixed finite family of congruence
words, the compact sampler, and the terminal tail. The word family is
chosen once, independently of H, t, x and the vector. -/
theorem exists_terminal_word_energy (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ W : Finset (List SL(2,ℤ)),
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ (H : ℝ), ε⁻¹≤H → ∀ (t : ℕ) (x : ℍ)
        (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),
        ‖corner (terminal ε) x v‖^2 ≤
          2 * ∑ l : W, (‖sampling N hN H hε t x v‖^2+
            ‖AsymptoticCongruenceDefect.operator l.val.prod
              (terminalRectangle_compact hε H) hε t x v‖^2)+
          ‖corner (terminal H) x v‖^2 := by
  obtain ⟨W,hW,hw⟩ := finite_terminal_words_retained N S hS hε
  refine ⟨W,hW,?_⟩
  intro H hH t x v
  exact (terminal_energy_split ε H x v).trans
    (add_le_add (terminalBand_energy N hN hε H t W
      (fun z hz => hw H hH z hz.1 hz.2) x v) le_rfl)

/-- Replacing word defects by literal generator observations on the
explicit common region. D bounds only individual generators and their
inverses, not the desired observability conclusion. -/
theorem terminal_generator_energy (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ)) {ε : ℝ} (hε : 0<ε) (H : ℝ) (t : ℕ)
    (W : Finset (List SL(2,ℤ)))
    (hletters : ∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S)
    (hW : ∀ z∈terminalBand ε H, ∃ l∈W,
      AsymptoticCongruenceLabels.integralLabel l.prod • z∈wideCompactCover N H)
    (x : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) (D : ℝ)
    (hgen : ∀ a : SL(2,ℤ), a∈S ∨ a⁻¹∈S →
      ‖AsymptoticCongruenceDefect.operator a (wordRegion_compact W hε H) hε t x v‖≤D) :
    ‖corner (terminal ε) x v‖^2 ≤
      2 * ∑ l : W, (‖sampling N hN H hε t x v‖^2+
        (cost l.val (terminalRectangle_compact hε H) hε t*D)^2)+
      ‖corner (terminal H) x v‖^2 := by
  apply (terminal_energy_split ε H x v).trans
  apply add_le_add _ le_rfl
  apply (terminalBand_energy N hN hε H t W hW x v).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro l _
  apply add_le_add le_rfl
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply word_norm_of_generator_bound l.val (terminalRectangle_compact hε H)
    (wordRegion_compact W hε H)
    (subset_iUnion (fun l : W => region l.val (terminalRectangle ε H)) l) hε t x v D
  intro a ha
  exact hgen a (hletters l.val l.property a ha)

#print axioms exists_terminal_word_energy
#print axioms terminal_generator_energy

end QuantitativeSpectralObservability
