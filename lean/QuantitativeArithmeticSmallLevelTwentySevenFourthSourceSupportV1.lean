module
public import QuantitativeArithmeticSmallLevelTwentySevenFourthFormalLinearityV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open FinitenessRamanujanSum

/-- Finite coordinate support required by the four-layer packing. The legacy
constructor is deliberately excluded; the selected 340 rows use explicit specs. -/
def Supported (r : Source) : Prop :=
  match r with
  | .old _ => False
  | .matrix u _ _ _ => u.left < 607 ∧ u.right < 607
  | .ramanujan u _ _ _ => ∀ a ∈ residues u.q, u.left a < 607 ∧ u.right a < 607
  | .hecke u _ => (∀ a : Fin u.p, u.sample a < 607) ∧ u.first < 607 ∧ u.second < 607
  | .entire p _ => ∀ t ∈ p, t.2.1 < 607

instance supportedDecidable (r : Source) : Decidable (Supported r) := by
  cases r <;> unfold Supported <;> infer_instance

private theorem sample_congr (q : ℕ) (a : ℕ → ℕ)
    (ha : ∀ t ∈ residues q, a t < 607) (v u : ℕ → ℂ)
    (h : ∀ j, j < 607 → v j=u j) : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval q a v=QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval q a u := by
  unfold QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval
  apply Finset.sum_congr rfl
  intro t ht
  exact h (a t) (ha t ht)

private theorem eval_congr (x y z w a b c : ℂ) (p : QuantitativeArithmeticSevenLaurentRows.Poly)
    (hp : ∀ t ∈ p, t.2.1 < 607) (v u : ℕ → ℂ)
    (h : ∀ j, j < 607 → v j=u j) :
    QuantitativeArithmeticSevenLaurentRows.eval x y z w a b c v p=
      QuantitativeArithmeticSevenLaurentRows.eval x y z w a b c u p := by
  unfold QuantitativeArithmeticSevenLaurentRows.eval
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [h t.2.1 (hp t ht)]

theorem formalRow_congr (r : Source) (hr : Supported r)
    (ε : ℚ) (x y z w a b c : ℂ) (v u : ℕ → ℂ)
    (h : ∀ j, j < 607 → v j=u j) :
    formalRow r ε x y z w a b c v=formalRow r ε x y z w a b c u := by
  cases r with
  | old t => exact False.elim hr
  | matrix t ht obs ho =>
    simp only [formalRow,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,h t.left hr.1,h t.right hr.2]
  | ramanujan t ht obs ho =>
    have hl := sample_congr t.q t.left (fun a ha => (hr a ha).1) v u h
    have hright := sample_congr t.q t.right (fun a ha => (hr a ha).2) v u h
    simp only [formalRow,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,hl,hright]
  | hecke t ht =>
    have hs : (∑ a : Fin t.p, v (t.sample a))=∑ a : Fin t.p, u (t.sample a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact h _ (hr.1 a)
    simp only [formalRow,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,hs,h t.first hr.2.1,h t.second hr.2.2]
  | entire p hp => exact eval_congr x y z w a b c p hr v u h

theorem formalHigher_congr (r : Source) (hr : Supported r)
    (ε : ℚ) (x y z w : ℂ) (n : ℕ) (v u : ℕ → ℂ)
    (h : ∀ j, j < 607 → v j=u j) :
    formalHigher r ε x y z w n v=formalHigher r ε x y z w n u := by
  cases r with
  | old t => exact False.elim hr
  | matrix t ht obs ho => simp only [formalHigher,matrixHigher,h t.right hr.2]
  | ramanujan t ht obs ho =>
    have hs := sample_congr t.q t.right (fun a ha => (hr a ha).2) v u h
    simp only [formalHigher,ramanujanHigher,hs]
  | hecke t ht => rfl
  | entire p hp => rfl

#print axioms formalRow_congr
#print axioms formalHigher_congr
end QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
