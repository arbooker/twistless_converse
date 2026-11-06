module

public import QuantitativeArithmeticSmallLevelCircBridgeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane FinitenessOriginalInput SmallLevelOriginal
open scoped ModularForm

theorem primeTrace_zero (N : ℕ) (hN : 0<N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p∣N}) : primeTrace N hN k p 0 = 0 := by
  simpa only [zero_smul] using primeTrace_smul N hN k p 0 0

theorem primeTrace_add (N : ℕ) (hN : 0<N) (k : ℤ)
    (p : {p : ℕ // p.Prime ∧ p∣N}) (F G : ModularForm (level N) k) :
    primeTrace N hN k p (F+G) = primeTrace N hN k p F + primeTrace N hN k p G := by
  classical
  unfold primeTrace
  ext z
  simp only [ModularForm.coe_trace, Finset.sum_apply, FunLike.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h r => simp [SlashInvariantForm.quotientFunc_mk]

/-- The actual trace-defined modular subspace in the paper. The witness G
is the unique modular form whose underlying function is F|W_N. -/
def space (N : ℕ) (hN : 0<N) (k : ℕ) :
    Submodule ℂ (ModularForm (level N) (k : ℤ)) where
  carrier := {F | ∃ G : ModularForm (level N) (k : ℤ),
    (G : ℍ → ℂ) = (F : ℍ → ℂ) ∣[(k : ℤ)] SmallLevelNormalized.fricke N hN ∧
    IsZeroAtImInfty (F : ℍ → ℂ) ∧ IsZeroAtImInfty (G : ℍ → ℂ) ∧
    ∀ p : {p : ℕ // p.Prime ∧ p∣N},
      primeTrace N hN (k : ℤ) p F = 0 ∧ primeTrace N hN (k : ℤ) p G = 0}
  zero_mem' := by
    refine ⟨0, ?_, ?_, ?_, ?_⟩
    · simp only [FunLike.coe_zero, SlashAction.zero_slash]
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · intro p
      exact ⟨primeTrace_zero N hN _ p, primeTrace_zero N hN _ p⟩
  add_mem' := by
    intro F H hF hH
    obtain ⟨G,hG,hF0,hG0,hFG⟩ := hF
    obtain ⟨J,hJ,hH0,hJ0,hHJ⟩ := hH
    refine ⟨G+J, ?_, ?_, ?_, ?_⟩
    · simp only [FunLike.coe_add, SlashAction.add_slash, hG, hJ]
    · change IsZeroAtImInfty ((F : ℍ → ℂ)+(H : ℍ → ℂ))
      exact hF0.add hH0
    · change IsZeroAtImInfty ((G : ℍ → ℂ)+(J : ℍ → ℂ))
      exact hG0.add hJ0
    · intro p
      constructor
      · rw [primeTrace_add, (hFG p).1, (hHJ p).1, add_zero]
      · rw [primeTrace_add, (hFG p).2, (hHJ p).2, add_zero]
  smul_mem' := by
    intro c F hF
    obtain ⟨G,hG,hF0,hG0,hFG⟩ := hF
    refine ⟨c • G, ?_, ?_, ?_, ?_⟩
    · simp only [FunLike.coe_smul, SmallLevelNormalized.det_one_smul _
        (SmallLevelNormalized.fricke_det N hN), hG]
    · change Filter.Tendsto (fun z => c * F z) atImInfty (nhds 0)
      simpa only [mul_zero] using hF0.const_mul c
    · change Filter.Tendsto (fun z => c * G z) atImInfty (nhds 0)
      simpa only [mul_zero] using hG0.const_mul c
    · intro p
      constructor
      · rw [primeTrace_smul, (hFG p).1, smul_zero]
      · rw [primeTrace_smul, (hFG p).2, smul_zero]

theorem isCirc_iff_mem {N k : ℕ} {hN : 0<N} {f : ℕ → ℂ} :
    IsCirc N hN k f ↔ ∃ F : space N hN k, (F.val : ℍ → ℂ) = fourierFunction k f := by
  constructor
  · rintro ⟨F,G,hF,hG,hF0,hG0,ht⟩
    exact ⟨⟨F,G,hG,hF0,hG0,ht⟩,hF⟩
  · rintro ⟨⟨F,G,hG,hF0,hG0,ht⟩,hF⟩
    exact ⟨F,G,hF,hG,hF0,hG0,ht⟩

/-- Every already-proved modular solution now gives an element of the
literal modular subspace whose finrank occurs in the desired count. -/
theorem original_modular_mem_space {N k : ℕ} (hN : 0<N) (hk : 0<k)
    (heven : Even k) {f : ℕ → ℂ} (hf : IsSolution N k f) (hmod : IsModular N k f) :
    ∃ F : space N hN k, (F.val : ℍ → ℂ) = fourierFunction k f :=
  isCirc_iff_mem.mp (original_modular_isCirc_even hN hk heven hf hmod)

#print axioms primeTrace_add
#print axioms space
#print axioms isCirc_iff_mem
#print axioms original_modular_mem_space
end QuantitativeArithmeticSmallLevelCirc
