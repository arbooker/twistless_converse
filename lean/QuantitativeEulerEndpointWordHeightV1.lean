module

public import QuantitativeEulerEndpointGeneratorCheckV1
public import QuantitativeEulerDiamondGeneratorWordsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode AsymptoticCongruenceLabels
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

/-- Both possible suffixes after normalizing a signed generator letter.
The height is fixed before choosing any fresh prime or analytic cutoff. -/
def wordTransportHeight (L : List (SL(2,ℤ) × SL(2,ℤ))) (β : SL(2,ℤ)) : ℝ :=
  1+∑ i : Fin L.length,
    (fixedMatrixHeight ((L.get i).2*β).val+
      fixedMatrixHeight ((L.get i).1*((L.get i).2*β)).val)

theorem wordTransportHeight_one_le (L : List (SL(2,ℤ) × SL(2,ℤ))) (β : SL(2,ℤ)) :
    1≤wordTransportHeight L β := by
  have h := Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset (Fin L.length))) =>
    add_nonneg (fixedMatrixHeight_nonneg ((L.get i).2*β).val)
      (fixedMatrixHeight_nonneg ((L.get i).1*((L.get i).2*β)).val))
  unfold wordTransportHeight
  linarith

theorem wordTransportHeight_bounds (L : List (SL(2,ℤ) × SL(2,ℤ))) (β : SL(2,ℤ))
    (i : Fin L.length) :
    MatrixEntryBound ((L.get i).2*β).val (wordTransportHeight L β) ∧
    MatrixEntryBound ((L.get i).1*((L.get i).2*β)).val (wordTransportHeight L β) := by
  have hsum := Finset.single_le_sum
    (fun j (_ : j∈(Finset.univ : Finset (Fin L.length))) =>
      add_nonneg (fixedMatrixHeight_nonneg ((L.get j).2*β).val)
        (fixedMatrixHeight_nonneg ((L.get j).1*((L.get j).2*β)).val)) (Finset.mem_univ i)
  have hleft := fixedMatrixHeight_nonneg ((L.get i).2*β).val
  have hright := fixedMatrixHeight_nonneg ((L.get i).1*((L.get i).2*β)).val
  constructor
  · apply entry_bound_mono (fixedMatrixHeight_bounds _)
    unfold wordTransportHeight
    linarith
  · apply entry_bound_mono (fixedMatrixHeight_bounds _)
    unfold wordTransportHeight
    linarith

theorem inverse_letter_identity (γ β : SL(2,ℤ)) :
    (symbol (integralLabel γ)-1)*symbol (integralLabel β)=
      -((symbol (integralLabel γ⁻¹)-1)*symbol (integralLabel (γ*β))) := by
  have hi : symbol (integralLabel γ⁻¹)*symbol (integralLabel γ)=1 := by
    rw [←symbol.map_mul,←integralLabel.map_mul,inv_mul_cancel,map_one,map_one]
  rw [integralLabel.map_mul,symbol.map_mul,sub_mul,sub_mul,one_mul,one_mul,←mul_assoc,hi,one_mul]
  abel

theorem inverse_letter_norm (γ β : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x ((symbol (integralLabel γ)-1)*symbol (integralLabel β)) v‖=
    ‖compactAction hs hε t x
      ((symbol (integralLabel γ⁻¹)-1)*symbol (integralLabel (γ*β))) v‖ := by
  rw [inverse_letter_identity,map_neg,_root_.neg_apply,norm_neg]

theorem finite_sum_squared_bound {ι : Type*} [Fintype ι] (u : ι → Space) (K : ℝ)
    (h : ∀ i, ‖u i‖^2≤K) : ‖∑ i,u i‖^2≤(Fintype.card ι : ℝ)^2*K := by
  have hn := (sq_le_sq₀ (norm_nonneg (∑ i,u i))
    (Finset.sum_nonneg (fun i _ => norm_nonneg (u i)))).2 (norm_sum_le _ _)
  have hc : (∑ i,‖u i‖)^2≤(Fintype.card ι : ℝ)*(∑ i,‖u i‖^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ)) (fun i => ‖u i‖)
  have hs : (∑ i,‖u i‖^2)≤(Fintype.card ι : ℝ)*K := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι)) => h i)
  exact (hn.trans hc).trans ((mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)).trans_eq (by ring))

#print axioms wordTransportHeight_bounds
#print axioms inverse_letter_identity
#print axioms inverse_letter_norm
#print axioms finite_sum_squared_bound
end QuantitativeEulerEndpointPrepared
