module

public import QuantitativeSpectralObservabilityPolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open Matrix UpperHalfPlane Set
open AsymptoticHyperbolicArea AsymptoticOrbitDiagonal
open QuantitativeSpectralObservabilityDecoded QuantitativeSpectralWordDefect
open QuantitativeHolomorphic
open scoped MatrixGroups BigOperators lp

private theorem single_le_total {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, 0≤f i) (i : I) : f i≤∑ j,f j := by
  classical
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

/-- A single finite arithmetic constant bounds every suffix matrix in
the reducing family. It is independent of every analytic cutoff. -/
theorem finite_word_matrix_bound (W : Finset (List SL(2,ℤ))) :
    ∃ B : ℝ, 1≤B ∧ ∀ l∈W, ∀ k : ℕ, MatrixEntryBound (l.drop k).prod.val B := by
  classical
  let A (l : W) (k : Fin (l.val.length+1)) (i j : Fin 2) : ℝ :=
    |(((l.val.drop k.val).prod) i j:ℝ)|
  let B := 1+∑ l : W, ∑ k : Fin (l.val.length+1), ∑ i : Fin 2, ∑ j : Fin 2, A l k i j
  have hs : 0≤∑ l : W, ∑ k : Fin (l.val.length+1), ∑ i : Fin 2, ∑ j : Fin 2, A l k i j := by
    dsimp [A]
    positivity
  have hB : 1≤B := by dsimp only [B]; linarith
  refine ⟨B,hB,?_⟩
  intro l hl k i j
  by_cases hk : k<l.length+1
  · let w : W := ⟨l,hl⟩
    let n : Fin (w.val.length+1) := ⟨k,hk⟩
    change A w n i j≤B
    calc
      _ ≤ ∑ b : Fin 2, A w n i b := single_le_total (fun b : Fin 2 => A w n i b) (fun _ => abs_nonneg _) j
      _ ≤ ∑ a : Fin 2, ∑ b : Fin 2, A w n a b :=
        single_le_total (fun a : Fin 2 => ∑ b : Fin 2, A w n a b)
          (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) i
      _ ≤ ∑ m : Fin (w.val.length+1), ∑ a : Fin 2, ∑ b : Fin 2, A w m a b :=
        single_le_total (fun m : Fin (w.val.length+1) => ∑ a : Fin 2, ∑ b : Fin 2, A w m a b)
          (fun _ => by dsimp [A]; positivity) n
      _ ≤ ∑ v : W, ∑ m : Fin (v.val.length+1), ∑ a : Fin 2, ∑ b : Fin 2, A v m a b :=
        single_le_total (fun v : W => ∑ m : Fin (v.val.length+1), ∑ a : Fin 2, ∑ b : Fin 2, A v m a b)
          (fun _ => by dsimp [A]; positivity) w
      _ ≤ B := by dsimp only [B]; linarith
  · have hd : l.drop k=[] := List.drop_eq_nil_iff.mpr (by omega)
    rw [hd,List.prod_nil]
    fin_cases i <;> fin_cases j <;> norm_num at * <;> linarith

/-- The terminal observability constant is polynomial in the cutoff H
for every fixed cap exponent t. Both the finite words and their matrix
bound are chosen before H, t, x and the input vector. -/
theorem exists_polynomial_terminal_observability (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ (H : ℝ), ε⁻¹≤H → ∀ (t : ℕ) (x : ℍ)
        (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),
        ‖corner (terminal ε) x v‖^2 ≤
          2 * ∑ l : W, (‖sampling N hN H hε t x v‖^2+
            (l.val.length*transportPolynomial B H t*
              generatorResidual S (wordRegion_compact W hε H) hε t x v)^2)+
          ‖corner (terminal H) x v‖^2 := by
  obtain ⟨W,hW,hw⟩ := finite_terminal_words_retained N S hS hε
  obtain ⟨B,hB,hmat⟩ := finite_word_matrix_bound W
  refine ⟨W,B,hB,hW,?_⟩
  intro H hH t x v
  apply (terminal_energy_split ε H x v).trans
  apply add_le_add _ le_rfl
  apply (terminalBand_energy N hN hε H t W
    (fun z hz => hw H hH z hz.1 hz.2) x v).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro l _
  apply add_le_add le_rfl
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply word_norm_polynomial l.val hB (hmat l.val l.property) hε t
    (wordRegion_compact W hε H)
    (subset_iUnion (fun l : W => region l.val (terminalRectangle ε H)) l)
  intro a ha
  exact generator_le_residual S (wordRegion_compact W hε H) hε t x v a
    (hW l.val l.property a ha)

#print axioms finite_word_matrix_bound
#print axioms exists_polynomial_terminal_observability

end QuantitativeSpectralObservability
