module
public import AsymptoticClassicalBadHeckeLowerV1
public import AsymptoticClassicalNewCuspKernelV1
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane ConjAct
open scoped ModularForm Pointwise

/-- The coset trace is independent of the presentation of its target group. -/
theorem trace_target_congr {G H J : Subgroup (GL (Fin 2) ℝ)}
    [G.IsFiniteRelIndex H] [G.IsFiniteRelIndex J] (k : ℤ) (h : H = J)
    (f : CuspForm G k) : (CuspForm.trace H f : ℍ → ℂ) = (CuspForm.trace J f : ℍ → ℂ) := by
  subst J
  rfl

/-- At a repeated prime the U_p trace at level p*M equals a restriction
of the trace to level M. -/
theorem upperTrace_repeated_lower (M p : ℕ) [NeZero M] (hp : p.Prime) (hpM : p ∣ M)
    (k : ℤ) (f : CuspForm (level (p * M)) k) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
    (upperTrace (p * M) p hp.pos k f : ℍ → ℂ) =
      (arithmeticTrace (upperDilationLevel (p * M) p hp.pos) (level M) k
        (CuspForm.translate f (upperDilationReal p hp.pos)) : ℍ → ℂ) := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
  dsimp only
  rw [upperTrace_bad_slash (p * M) p hp (Nat.dvd_mul_right p M),
    upperTrace_coset_sum (p * M) M p hp.pos (upperLowerCosetEquiv M p hp hpM)
      (upperLowerCosetEquiv_mk M p hp hpM)]

/-- The second old-trace equation annihilates U_p at a repeated prime. -/
theorem upperTrace_repeated_zero_of_trace (M p : ℕ) [NeZero M] (hp : p.Prime)
    (hpM : p ∣ M) (k : ℤ) (f : CuspForm (level (p * M)) k)
    (hf : let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (dilationLevel M p hp.pos) k f = 0) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p hp.pos k f = 0 := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
  dsimp only
  let G := level (p * M)
  let H := dilationLevel M p hp.pos
  let g := upperDilationReal p hp.pos
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  let := conjugate_finiteRelIndex G H g
  let : (upperDilationLevel (p * M) p hp.pos).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := upperDilationLevel (p * M) p hp.pos)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let : (toConjAct g⁻¹ • G).IsFiniteRelIndex (level M) :=
    inferInstanceAs ((upperDilationLevel (p * M) p hp.pos).IsFiniteRelIndex (level M))
  have hzero : (CuspForm.trace H f : ℍ → ℂ) = 0 := by
    exact congrArg (fun h : CuspForm H k => (h : ℍ → ℂ)) hf
  have ht := trace_translate G H g k f
  rw [hzero, SlashAction.zero_slash] at ht
  apply DFunLike.coe_injective
  rw [upperTrace_repeated_lower M p hp hpM k f]
  change (CuspForm.trace (level M) (CuspForm.translate f g) : ℍ → ℂ) = 0
  rw [← trace_target_congr k (upper_translate_dilationLevel M p hp.pos)
    (CuspForm.translate f g)]
  exact ht

/-- Genuine new cusp forms have zero U_p at every square divisor of the level. -/
theorem upperTrace_repeated_new_zero (M p : ℕ) [NeZero M] (hp : p.Prime)
    (hpM : p ∣ M) (k : ℤ) (f : CuspForm (level (p * M)) k)
    (hf : f ∈ newSpace (p * M) (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero (NeZero.ne M))) k) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p hp.pos k f = 0 := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
  dsimp only
  let hM := Nat.pos_of_ne_zero (NeZero.ne M)
  let hN := Nat.mul_pos hp.pos hM
  let q : {q : ℕ // q.Prime ∧ q ∣ p * M} := ⟨p, hp, Nat.dvd_mul_right p M⟩
  let : NeZero ((p * M) / p) := ⟨by rw [Nat.mul_div_cancel_left M hp.pos]; exact NeZero.ne M⟩
  have hdiv : (p * M) / p = M := Nat.mul_div_cancel_left M hp.pos
  have hg : frickeOldLevel (p * M) ((p * M) / p) hN = dilationLevel M p hp.pos := by
    rw [hdiv]
    exact frickeOldLevel_eq_dilationLevel M p hM hp.pos
  have ht := (prime_trace_eq_zero (p * M) hN k q f hf).2
  apply upperTrace_repeated_zero_of_trace M p hp hpM k f
  let : (level (p * M)).IsFiniteRelIndex (frickeOldLevel (p * M) ((p * M) / p) hN) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable
        (𝒢 := frickeOldLevel (p * M) ((p * M) / p) hN)).symm).1
  let : (level (p * M)).IsFiniteRelIndex (dilationLevel M p hp.pos) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := dilationLevel M p hp.pos)).symm).1
  apply DFunLike.coe_injective
  change (CuspForm.trace (dilationLevel M p hp.pos) f : ℍ → ℂ) = 0
  rw [← trace_target_congr k hg f]
  exact congrArg (fun h : CuspForm (frickeOldLevel (p * M) ((p * M) / p) hN) k => (h : ℍ → ℂ)) ht

#print axioms trace_target_congr
#print axioms upperTrace_repeated_lower
#print axioms upperTrace_repeated_zero_of_trace
#print axioms upperTrace_repeated_new_zero
end AsymptoticClassicalCusp
