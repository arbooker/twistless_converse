module
public import SmallLevelTwentySixGermSourcesTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixJetSignFlip
open SmallLevelTwentySixGermSources

/-- The only rows sensitive to the ramified13 sign are the corresponding
Ramanujan rows and Hecke13 rows. The latter are absent in the selected system. -/
def independent : GridSource → Prop
  | .taylor i => ¬13∣gridTaylorQ i
  | .hecke i => gridHeckeP i≠13
  | _ => True

theorem jet_independent (n : ℕ) (X Y Z W η σ₂ c d a b : ℂ)
    (v : ℕ→Fin 780→ℂ) (i : GridSource) (hi : independent i) :
    laurentJetRow n X Y Z W η σ₂ c a b v i=
      laurentJetRow n X Y Z W η σ₂ d a b v i := by
  cases i <;>
    simp_all only [independent,laurentJetRow,laurentRows,laurentSlopeRows,
      laurentHecke,primeEigenvalue,ite_false]

theorem selected_hecke_independent (i : Fin 96) : gridHeckeP i≠13 := by
  have h : ∀ j : Fin 96,gridHeckeP j≠13 := by decide +kernel
  exact h i

/-- Changing the ramified13 sign reverses every right-hand Taylor layer.
Adding the two rows therefore leaves twice the untransformed top layer.
This identity works at all Taylor orders and does not compare pole orders. -/
theorem jet_taylor_flip (n : ℕ) (X Y Z W η σ₂ a b : ℂ)
    (v : ℕ→Fin 780→ℂ) (i : Fin 53) (hi : 13∣gridTaylorQ i) :
    laurentJetRow n X Y Z W η σ₂ 1 a b v (.taylor i)+
      laurentJetRow n X Y Z W η σ₂ (-1) a b v (.taylor i)=
        2*gridSample (gridTaylorQ i) (gridTaylorT i) (v n) := by
  have hl :
      laurentRows (X/2^n) (Y/3^n) (Z/13^n) (W/5^n) η σ₂ 1 a b (v n) (.taylor i)+
      laurentRows (X/2^n) (Y/3^n) (Z/13^n) (W/5^n) η σ₂ (-1) a b (v n) (.taylor i)=
        2*gridSample (gridTaylorQ i) (gridTaylorT i) (v n) := by
    simp only [laurentRows,hi,↓reduceIte]
    ring
  have hs :
      (∑ h∈Finset.range n,laurentSlopeRows (n-h) (X/2^n) (Y/3^n) (Z/13^n) (W/5^n)
        η σ₂ 1 (v h) (.taylor i)/((n-h).factorial:ℂ))+
      (∑ h∈Finset.range n,laurentSlopeRows (n-h) (X/2^n) (Y/3^n) (Z/13^n) (W/5^n)
        η σ₂ (-1) (v h) (.taylor i)/((n-h).factorial:ℂ))=0 := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro h hh
    simp only [laurentSlopeRows,hi,↓reduceIte]
    ring
  unfold laurentJetRow
  linear_combination hl-hs

#print axioms jet_independent
#print axioms selected_hecke_independent
#print axioms jet_taylor_flip
end QuantitativeArithmeticSmallLevelTwentySixJetSignFlip
