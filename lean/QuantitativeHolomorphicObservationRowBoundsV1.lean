module

public import QuantitativeHolomorphicObservationMatricesV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane MeasureTheory AsymptoticRationalFreeness
open AsymptoticCompactBranch AsymptoticFiniteBranch AsymptoticRationalBranches
open AsymptoticRegularObservationRows AsymptoticCompactObservationCount AsymptoticSectorSigns

variable {ι : Type*} [Fintype ι]

theorem compactFamily_integer_bounds_of_representatives (b : ι → AsymptoticRegularBranchFamily.Branch)
    (B : ℝ) (hB : 1≤B)
    (hrep : ∀ i, ∃ M, IntegerAction (AsymptoticRationalBranches.ofMatrix (b i).matrix (b i).positive) M ∧ MatrixEntryBound M B) :
    ∀ (c : ι → ℂ) {s : Set UpperHalfPlane} (hs : IsCompact s)
      {Y H ε : ℝ} (_hY : 0<Y) (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_hhi : ∀ z∈s, z.im≤H) (t : ℕ),
      ∃ E : Expression,
        (∀ m, holomorphicSum E m = holomorphicSum (compactFamilyExpression b c hs hε t) m) ∧
        (∀ z, regularSum E z = regularSum (compactFamilyExpression b c hs hε t) z) ∧
        E.length = Fintype.card ι * (2*integerCompactCutoff B Y H+1) ∧
        expressionBound E = (∑ i, ‖c i‖) *
          (2*(integerCompactCutoff B Y H:ℝ)+1)*(integerCompactDistortion B H)^t ∧
        ExpressionMatrixBound E (4*(1+(integerCompactCutoff B Y H:ℝ))*B) := by
  choose M hM hb using hrep
  intro c s hs Y H ε hY hε hre hlo hhi t
  let D := fun i => integerCompactData (b i).matrix (b i).positive (hM i)
    (zero_le_one.trans hB) (hb i) hY hε hre hlo hhi t
  let E := compactFamilyDataExpression b c hs hε t D
  have he := fun i => integerCompactExpression_bounds (b i).matrix (b i).positive (hM i)
    (zero_le_one.trans hB) (hb i) hY hε hs.measurableSet hre hlo hhi t
  refine ⟨E, fun m => compactFamilyDataExpression_physical b c hs hε t m D,
    fun z => compactFamilyDataExpression_regular b c hs hε t D z, ?_, ?_, ?_⟩
  · dsimp only [E, compactFamilyDataExpression, D]
    simp only [length_sumExpressions, scaleExpression, List.length_map, (he _).1]
    simp
  · dsimp only [E, compactFamilyDataExpression, D]
    simp only [expressionBound_sumExpressions, expressionBound_scale, (he _).2.1]
    rw [← Finset.sum_mul]
    ring
  · apply expressionMatrixBound_sum
    intro i _
    exact (he i).2.2.scale (c i)

theorem compactFamily_unit_bounds_of_representatives {ι : Type*} [Fintype ι]
    (b : ι → AsymptoticRegularBranchFamily.Branch)
    (B : ℝ) (hB : 1≤B)
    (hrep : ∀ i, ∃ M, IntegerAction (ofMatrix (b i).matrix (b i).positive) M ∧ MatrixEntryBound M B) :
    ∀ (c : ι → ℂ) (_hc : ∀ i, ‖c i‖≤1)
      {s : Set UpperHalfPlane} (hs : IsCompact s) {Y H ε : ℝ} (_hY : 0<Y) (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_hhi : ∀ z∈s, z.im≤H) (t : ℕ),
      ∃ E : Expression,
        (∀ m, holomorphicSum E m = holomorphicSum (compactFamilyExpression b c hs hε t) m) ∧
        (∀ z, regularSum E z = regularSum (compactFamilyExpression b c hs hε t) z) ∧
        E.length = Fintype.card ι * (2*integerCompactCutoff B Y H+1) ∧
        expressionBound E ≤ (Fintype.card ι:ℝ) *
          (2*(integerCompactCutoff B Y H:ℝ)+1)*(integerCompactDistortion B H)^t ∧
        ExpressionMatrixBound E (4*(1+(integerCompactCutoff B Y H:ℝ))*B) := by
  have h := compactFamily_integer_bounds_of_representatives b B hB hrep
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


 theorem twistBranches_integer_representatives (N q : ℕ) (hN : 0<N) (hq : 0<q) :
    ∀ i, ∃ M, IntegerAction (ofMatrix (twistBranches N q hN hq i).matrix
      (twistBranches N q hN hq i).positive) M ∧ MatrixEntryBound M (N*q^3:ℕ) := by
  have hqB : q≤N*q^3 := by
    have hq1 : 1≤q := hq
    have hN1 : 1≤N := hN
    nlinarith [Nat.pow_le_pow_right hq1 (show 1≤3 by omega)]
  intro i
  cases i with
  | inl a =>
    have ha : a.val≤q := (Finset.mem_range.mp (Finset.mem_filter.mp a.property).1).le
    refine ⟨translationIntegerMatrix q a.val, translation_integer_action q a.val hq,?_⟩
    intro i j
    exact (translation_integer_bound q a.val ha i j).trans (Nat.cast_le.mpr hqB)
  | inr a =>
    have ha : a.val≤q := (Finset.mem_range.mp (Finset.mem_filter.mp a.property).1).le
    exact ⟨reflectedIntegerMatrix N q a.val,reflected_integer_action N q a.val hN hq,
      reflected_integer_bound N q a.val hN hq ha⟩

theorem ramifiedBranches_integer_representatives (p : ℕ) (hp : 0<p) :
    ∀ i, ∃ M, IntegerAction (ofMatrix (ramifiedBranches p hp i).matrix
      (ramifiedBranches p hp i).positive) M ∧ MatrixEntryBound M p := by
  intro i
  cases i with
  | inl a => exact ⟨ramifiedIntegerMatrix p a.val,ramified_integer_action p a.val hp,
      ramified_integer_bound p a.val hp a.isLt.le⟩
  | inr a =>
    refine ⟨translationIntegerMatrix 1 0,?_,?_⟩
    · simpa only [ramifiedBranches,Sum.elim_inr,Nat.cast_zero,zero_div] using
        translation_integer_action 1 0 (by omega)
    · intro i j
      exact (translation_integer_bound 1 0 (by omega) i j).trans (Nat.cast_le.mpr hp)

def rowArithmeticHeight {N : ℕ} (r : Row N) : ℝ :=
  match r with
  | .twist q _ => (N*q^3:ℕ)
  | .ramified p _ _ => p

theorem rowArithmeticHeight_one_le {N : ℕ} (hN : 0<N) (r : Row N) :
    1≤rowArithmeticHeight r := by
  cases r with
  | twist q hq =>
    change (1:ℝ)≤((N*q^3:ℕ):ℝ)
    exact_mod_cast (show 1≤N*q^3 from Nat.mul_pos hN (pow_pos hq 3))
  | ramified p hp _ =>
    change (1:ℝ)≤(p:ℝ)
    exact_mod_cast hp.pos

/-- Literal row replacement with modulus-polynomial matrix heights, uniform
as the observation family grows. -/
theorem rowExpression_explicit_integer_bounds {N : ℕ} (hN : 0<N) (r : Row N) :
    ∀ (e : Sector N)
      {s : Set UpperHalfPlane} (hs : IsCompact s) {Y H ε : ℝ} (_hY : 0<Y) (hε : 0<ε)
      (_hre : ∀ z∈s, |z.re|≤1) (_hlo : ∀ z∈s, Y≤z.im) (_hhi : ∀ z∈s, z.im≤H) (t : ℕ),
      ∃ E : Expression,
        (∀ m, holomorphicSum E m = holomorphicSum (rowExpression hN r e hs hε t) m) ∧
        (∀ z, regularSum E z = regularSum (rowExpression hN r e hs hε t) z) ∧
        E.length = rowBranchCount r * (2*integerCompactCutoff (rowArithmeticHeight r) Y H+1) ∧
        expressionBound E ≤ (rowBranchCount r:ℝ) *
          (2*(integerCompactCutoff (rowArithmeticHeight r) Y H:ℝ)+1)*
          (integerCompactDistortion (rowArithmeticHeight r) H)^t ∧
        ExpressionMatrixBound E (4*(1+(integerCompactCutoff (rowArithmeticHeight r) Y H:ℝ))*rowArithmeticHeight r) := by
  have hB := rowArithmeticHeight_one_le hN r
  cases r with
  | twist q hq =>
    have h := compactFamily_unit_bounds_of_representatives (twistBranches N q hN hq)
      _ hB (twistBranches_integer_representatives N q hN hq)
    intro e s hs Y H ε hY hε hre hlo hhi t
    apply h (Sum.elim (fun _ => 1) (fun _ => -multiplier e q)) _ hs hY hε hre hlo hhi t
    intro i
    cases i <;> simp [multiplier_norm]
  | ramified p hp hpN =>
    have h := compactFamily_unit_bounds_of_representatives (ramifiedBranches p hp.pos)
      _ hB (ramifiedBranches_integer_representatives p hp.pos)
    intro e s hs Y H ε hY hε hre hlo hhi t
    apply h (Sum.elim (fun _ => 1) (fun _ => -AsymptoticCylinderRamified.eigenvalue e p)) _ hs hY hε hre hlo hhi t
    intro i
    cases i
    · simp
    · simpa only [Sum.elim_inr,norm_neg] using AsymptoticCylinderRamified.eigenvalue_norm_le e p

#print axioms rowExpression_explicit_integer_bounds

end QuantitativeHolomorphic
