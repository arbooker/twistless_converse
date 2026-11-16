module

public import QuantitativeArithmeticMixedLabelDetectionV1

@[expose] public section

namespace SpanningCriterionLabelDetection

open GridLabelDetection GridTriangularDetection QuantitativeArithmeticMixedLabelDetection

theorem mixed_label_detect_above {K : Type*} [AddCommMonoid K] {G : ℕ} (hG : 0 < G)
    (good : Fin G → Prop) [DecidablePred good] (p : Fin G → ℕ)
    (hp : ∀ a, 2 < labelOrder a → ¬ good a → (p a).Prime)
    (hpG : ∀ a, 2 < labelOrder a → ¬ good a → p a ∣ G)
    (hpa : ∀ a, 2 < labelOrder a → ¬ good a → ¬ p a ∣ labelOrder a)
    (f : Fin G → K)
    (hgood : ∀ a, 2 < labelOrder a → good a → ∑ z ∈ labelHit a, f z = 0)
    (hbad : ∀ a, 2 < labelOrder a → ¬ good a → ∑ z ∈ primeHit (p a) a, f z = 0) : ∀ a, 2 < labelOrder a → f a = 0 := by
  classical
  apply triangular_detect_above labelOrder 2 (fun a => if good a then labelHit a else primeHit (p a) a)
  · intro a hahi
    split_ifs
    · exact (mem_labelHit a a).mpr (Nat.ModEq.refl _)
    · exact (mem_primeHit a a).mpr (Nat.ModEq.refl _)
  · intro a hahi z hz hne
    by_cases ha : good a
    · simp only [ite_eq_left ha] at hz
      exact labelHit_strict hG a z hz hne
    · simp only [ite_eq_right ha] at hz
      exact primeHit_strict hG (hp a hahi ha) (hpG a hahi ha) a z (hpa a hahi ha) hz hne
  · intro a hahi
    by_cases ha : good a
    · simpa only [ite_eq_left ha] using hgood a hahi ha
    · simpa only [ite_eq_right ha] using hbad a hahi ha

theorem mixed_label_detect {K : Type*} [AddCommMonoid K] {G : ℕ} (hG : 0 < G)
    (good : Fin G → Prop) [DecidablePred good] (p : Fin G → ℕ)
    (hp : ∀ a, 2 < labelOrder a → ¬ good a → (p a).Prime)
    (hpG : ∀ a, 2 < labelOrder a → ¬ good a → p a ∣ G)
    (hpa : ∀ a, 2 < labelOrder a → ¬ good a → ¬ p a ∣ labelOrder a)
    (f : Fin G → K)
    (hgood : ∀ a, 2 < labelOrder a → good a → ∑ z ∈ labelHit a, f z = 0)
    (hbad : ∀ a, 2 < labelOrder a → ¬ good a → ∑ z ∈ primeHit (p a) a, f z = 0)
    (hzero : f ⟨0,hG⟩ = 0)
    (hpair : ∀ a : Fin G, 2*a.val = G → f ⟨0,hG⟩ + f a = 0) : f = 0 := by
  funext a
  change f a = 0
  by_cases ha : 2 < labelOrder a
  · exact mixed_label_detect_above hG good p hp hpG hpa f hgood hbad a ha
  · rcases small_order hG a (by omega) with hz | hh
    · have he : a = ⟨0,hG⟩ := Fin.ext hz
      simpa only [he] using hzero
    · simpa only [hzero, zero_add] using hpair a hh

#print axioms mixed_label_detect

end SpanningCriterionLabelDetection
