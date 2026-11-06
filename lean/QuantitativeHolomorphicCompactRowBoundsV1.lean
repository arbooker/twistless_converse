module

public import QuantitativeHolomorphicCompactFamilyBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane AsymptoticFiniteBranch AsymptoticCompactObservationCount
open AsymptoticRegularObservationRows AsymptoticSectorSigns

theorem compactFamily_uniform_unit_bounds {ι : Type*} [Fintype ι]
    (b : ι → AsymptoticRegularBranchFamily.Branch) :
    ∃ B : ℝ, 1≤B ∧ ∀ (c : ι → ℂ) (_hc : ∀ i, ‖c i‖≤1)
      {s : Set UpperHalfPlane} (hs : IsCompact s) {Y H ε : ℝ} (_hY : 0<Y) (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_hhi : ∀ z∈s, z.im≤H) (t : ℕ),
      ∃ E : Expression,
        (∀ m, holomorphicSum E m = holomorphicSum (compactFamilyExpression b c hs hε t) m) ∧
        (∀ z, regularSum E z = regularSum (compactFamilyExpression b c hs hε t) z) ∧
        E.length = Fintype.card ι * (2*integerCompactCutoff B Y H+1) ∧
        expressionBound E ≤ (Fintype.card ι:ℝ) *
          (2*(integerCompactCutoff B Y H:ℝ)+1)*(integerCompactDistortion B H)^t ∧
        ExpressionMatrixBound E (4*(1+(integerCompactCutoff B Y H:ℝ))*B) := by
  obtain ⟨B,hB,h⟩ := compactFamily_uniform_integer_bounds b
  refine ⟨B,hB,?_⟩
  intro c hc s hs Y H ε hY hε hre hlo hhi t
  obtain ⟨E,hp,hr,hl,hm,hE⟩ := h c hs hY hε hre hlo hhi t
  refine ⟨E,hp,hr,hl,?_,hE⟩
  rw [hm]
  have hc' : (∑ i, ‖c i‖) ≤ (Fintype.card ι:ℝ) := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hc i)
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hc' (by positivity)
  · unfold integerCompactDistortion
    positivity

def rowBranchCount {N : ℕ} (r : Row N) : ℕ :=
  match r with
  | .twist q _ => Fintype.card (AsymptoticCertificateBranches.residues q ⊕ AsymptoticCertificateBranches.residues q)
  | .ramified p _ _ => Fintype.card (Fin p ⊕ Unit)

/-- Literal twist and ramified counting rows now have exact common-branch
replacements with explicit mass, length and matrix height. The single fixed
matrix constant is independent of sector, weight and every region cutoff. -/
theorem rowExpression_uniform_integer_bounds {N : ℕ} (hN : 0<N) (r : Row N) :
    ∃ B : ℝ, 1≤B ∧ ∀ (e : Sector N)
      {s : Set UpperHalfPlane} (hs : IsCompact s) {Y H ε : ℝ} (_hY : 0<Y) (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_hhi : ∀ z∈s, z.im≤H) (t : ℕ),
      ∃ E : Expression,
        (∀ m, holomorphicSum E m = holomorphicSum (rowExpression hN r e hs hε t) m) ∧
        (∀ z, regularSum E z = regularSum (rowExpression hN r e hs hε t) z) ∧
        E.length = rowBranchCount r * (2*integerCompactCutoff B Y H+1) ∧
        expressionBound E ≤ (rowBranchCount r:ℝ) *
          (2*(integerCompactCutoff B Y H:ℝ)+1)*(integerCompactDistortion B H)^t ∧
        ExpressionMatrixBound E (4*(1+(integerCompactCutoff B Y H:ℝ))*B) := by
  cases r with
  | twist q hq =>
    obtain ⟨B,hB,h⟩ := compactFamily_uniform_unit_bounds (twistBranches N q hN hq)
    refine ⟨B,hB,?_⟩
    intro e s hs Y H ε hY hε hre hlo hhi t
    apply h (Sum.elim (fun _ => 1) (fun _ => -multiplier e q)) _ hs hY hε hre hlo hhi t
    intro i
    cases i <;> simp [multiplier_norm]
  | ramified p hp hpN =>
    obtain ⟨B,hB,h⟩ := compactFamily_uniform_unit_bounds (ramifiedBranches p hp.pos)
    refine ⟨B,hB,?_⟩
    intro e s hs Y H ε hY hε hre hlo hhi t
    apply h (Sum.elim (fun _ => 1) (fun _ => -AsymptoticCylinderRamified.eigenvalue e p)) _ hs hY hε hre hlo hhi t
    intro i
    cases i
    · simp
    · simpa only [Sum.elim_inr,norm_neg] using AsymptoticCylinderRamified.eigenvalue_norm_le e p

#print axioms compactFamily_uniform_unit_bounds
#print axioms rowExpression_uniform_integer_bounds

end QuantitativeHolomorphic
