module

public import QuantitativeSpectralObservabilityTerminalV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set
open AsymptoticHyperbolicArea AsymptoticOrbitDiagonal
open QuantitativeSpectralObservabilityDecoded QuantitativeSpectralWordDefect
open scoped MatrixGroups BigOperators lp

/-- The sum of norms of the actual generators and inverse generators,
observed on the explicitly constructed common compact set. -/
def generatorResidual (S : Finset SL(2,ℤ)) {u : Set ℍ} (hu : IsCompact u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) : ℝ :=
  ∑ a : S, (‖AsymptoticCongruenceDefect.operator a.val hu hε t x v‖+
    ‖AsymptoticCongruenceDefect.operator a.val⁻¹ hu hε t x v‖)

theorem generator_le_residual (S : Finset SL(2,ℤ)) {u : Set ℍ} (hu : IsCompact u)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) (a : SL(2,ℤ))
    (ha : a∈S ∨ a⁻¹∈S) :
    ‖AsymptoticCongruenceDefect.operator a hu hε t x v‖≤
      generatorResidual S hu hε t x v := by
  classical
  have hb (b : S) :
      ‖AsymptoticCongruenceDefect.operator b.val hu hε t x v‖+
        ‖AsymptoticCongruenceDefect.operator b.val⁻¹ hu hε t x v‖≤
          generatorResidual S hu hε t x v := by
    unfold generatorResidual
    exact Finset.single_le_sum
      (f := fun j : S => ‖AsymptoticCongruenceDefect.operator j.val hu hε t x v‖+
        ‖AsymptoticCongruenceDefect.operator j.val⁻¹ hu hε t x v‖)
      (fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ b)
  rcases ha with ha | ha
  · have hh := hb ⟨a,ha⟩
    dsimp only at hh
    linarith [norm_nonneg (AsymptoticCongruenceDefect.operator a⁻¹ hu hε t x v)]
  · have hh := hb ⟨a⁻¹,ha⟩
    simp only [inv_inv] at hh
    linarith [norm_nonneg (AsymptoticCongruenceDefect.operator a⁻¹ hu hε t x v)]

/-- Concrete terminal norm observability: no approximate-invariance or
norm-observability hypothesis occurs. All residuals on the right are
literal compact observations of the fixed finite generating set. -/
theorem exists_terminal_generator_observability (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ W : Finset (List SL(2,ℤ)),
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ (H : ℝ), ε⁻¹≤H → ∀ (t : ℕ) (x : ℍ)
        (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),
        ‖corner (terminal ε) x v‖^2 ≤
          2 * ∑ l : W, (‖sampling N hN H hε t x v‖^2+
            (cost l.val (terminalRectangle_compact hε H) hε t*
              generatorResidual S (wordRegion_compact W hε H) hε t x v)^2)+
          ‖corner (terminal H) x v‖^2 := by
  obtain ⟨W,hW,hw⟩ := finite_terminal_words_retained N S hS hε
  refine ⟨W,hW,?_⟩
  intro H hH t x v
  exact terminal_generator_energy N hN S hε H t W hW
    (fun z hz => hw H hH z hz.1 hz.2) x v
    (generatorResidual S (wordRegion_compact W hε H) hε t x v)
    (generator_le_residual S (wordRegion_compact W hε H) hε t x v)

#print axioms generator_le_residual
#print axioms exists_terminal_generator_observability

end QuantitativeSpectralObservability
