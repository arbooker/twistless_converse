module

public import QuantitativeMaassGeneratorInvolutionsV1
public import QuantitativeMaassExactAtkinChoiceV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticCongruenceLabels AsymptoticFreshMatrices

namespace QuantitativeMaass

/-- The exact-divisor parameter of an elementary Atkin generator. -/
def generatorAtDivisor (N : ℕ) (hN : 0<N) (Q : ℕ) (i : admissibleGeneratorIndex N hN) : Prop :=
  ∃ (D : ℕ) (hQ : 0<Q) (A B : ℤ) (hAB : (Q:ℤ)*A+(D:ℤ)*B=1),
    Q*D=N ∧ i.val=exactAtkinLabel D Q hQ A B hAB

theorem generatorAtDivisor_action_eq (N : ℕ) (hN : 0<N) (Q : ℕ)
    (i j : admissibleGeneratorIndex N hN) (hi : generatorAtDivisor N hN Q i)
    (hj : generatorAtDivisor N hN Q j) :
    quotientNormalizerPullback N (admissibleGeneratorLift N hN i)=
      quotientNormalizerPullback N (admissibleGeneratorLift N hN j) := by
  obtain ⟨D,hQ,A,B,hAB,hND,hi⟩ := hi
  obtain ⟨D',hQ',A',B',hAB',hND',hj⟩ := hj
  have hd : D'=D := Nat.eq_of_mul_eq_mul_left hQ (hND'.trans hND.symm)
  subst D'
  obtain ⟨a,ha⟩ := exactAtkin_choice_mod_gamma D Q hQ A' B' A B hAB' hAB
  let aN : gamma N := ⟨a.val,by simpa only [hND] using a.property⟩
  ext x : 1
  apply quotientNormalizerPullback_left_gamma N _ _ aN
  change i.val=a.val*j.val
  rw [hi,hj]
  exact ha.symm

/-- A fixed finite list of actual elementary generator actions. The
choice at each divisor only selects a representative of a proved unique action. -/
def finiteGeneratorFamily (N : ℕ) (hN : 0<N) :
    Option (Option (Fin (N+1))) → admissibleGeneratorIndex N hN := by
  classical
  intro j
  exact match j with
  | none => ⟨frickeLabel N hN,admissibleNormalizerGenerator.fricke⟩
  | some none => if h4 : 4∣N then
      ⟨AsymptoticIntegralSubgroup.translationLabel (1/2),admissibleNormalizerGenerator.half h4⟩
    else ⟨frickeLabel N hN,admissibleNormalizerGenerator.fricke⟩
  | some (some q) => if h : ∃ i,generatorAtDivisor N hN q.val i then Classical.choose h
    else ⟨frickeLabel N hN,admissibleNormalizerGenerator.fricke⟩

/-- All elementary actions, despite their infinitely many matrix
representatives, occur in the finite divisor family. -/
theorem finiteGeneratorFamily_covers (N : ℕ) (hN : 0<N) (i : admissibleGeneratorIndex N hN) :
    ∃ j : Option (Option (Fin (N+1))),
      quotientNormalizerPullback N (admissibleGeneratorLift N hN i)=
        quotientNormalizerPullback N (admissibleGeneratorLift N hN (finiteGeneratorFamily N hN j)) := by
  obtain ⟨g,hg⟩ := i
  cases hg with
  | fricke => exact ⟨none,rfl⟩
  | half h4 =>
    refine ⟨some none,?_⟩
    simp only [finiteGeneratorFamily,dite_eq_left h4]
  | atkin D Q hQ A B hAB hND =>
    have hd : Q∣N := ⟨D,hND.symm⟩
    let q : Fin (N+1) := ⟨Q,Nat.lt_succ_of_le (Nat.le_of_dvd hN hd)⟩
    let i : admissibleGeneratorIndex N hN :=
      ⟨exactAtkinLabel D Q hQ A B hAB,admissibleNormalizerGenerator.atkin D Q hQ A B hAB hND⟩
    have hi : generatorAtDivisor N hN q.val i := ⟨D,hQ,A,B,hAB,hND,rfl⟩
    have hex : ∃ j,generatorAtDivisor N hN q.val j := ⟨i,hi⟩
    refine ⟨some (some q),?_⟩
    change quotientNormalizerPullback N (admissibleGeneratorLift N hN i)=_
    rw [finiteGeneratorFamily,dite_eq_left hex]
    exact generatorAtDivisor_action_eq N hN q.val i (Classical.choose hex) hi (Classical.choose_spec hex)

theorem admissibleGenerator_actions_finite (N : ℕ) (hN : 0<N) :
    (Set.range (fun i : admissibleGeneratorIndex N hN =>
      quotientNormalizerPullback N (admissibleGeneratorLift N hN i))).Finite := by
  apply (Set.finite_range (fun j : Option (Option (Fin (N+1))) =>
    quotientNormalizerPullback N (admissibleGeneratorLift N hN (finiteGeneratorFamily N hN j)))).subset
  rintro _ ⟨i,rfl⟩
  obtain ⟨j,hj⟩ := finiteGeneratorFamily_covers N hN i
  exact ⟨j,hj.symm⟩

#print axioms generatorAtDivisor_action_eq
#print axioms finiteGeneratorFamily_covers
#print axioms admissibleGenerator_actions_finite

end QuantitativeMaass
