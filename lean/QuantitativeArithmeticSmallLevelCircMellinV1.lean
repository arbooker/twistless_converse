module

public import QuantitativeArithmeticSmallLevelCircCoefficientsV1
public import AsymptoticClassicalLSeriesOrderV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane Matrix Complex Filter Asymptotics Set ConjAct
open scoped ModularForm Pointwise

/-- Vanishing after normalized W_N implies vanishing after S, since
W_N differs from S by an upper triangular matrix. No other cusp is used. -/
theorem slashS_zero_of_fricke {N : ℕ} (hN : 0<N) (k : ℤ)
    (F : ℍ → ℂ)
    (hF : IsZeroAtImInfty (F ∣[k] SmallLevelNormalized.fricke N hN)) :
    IsZeroAtImInfty (F ∣[k] (ModularGroup.S : GL (Fin 2) ℝ)) := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  let D : GL (Fin 2) ℝ := SmallLevelNormalized.matrix
    (Real.sqrt N)⁻¹ 0 0 (Real.sqrt N) (by simp [hs])
  have hD : D 1 0 = 0 := rfl
  have hWD : SmallLevelNormalized.fricke N hN * D =
      (ModularGroup.S : GL (Fin 2) ℝ) := by
    apply Units.ext
    have hS : (ModularGroup.S : GL (Fin 2) ℝ).val = !![(0 : ℝ), -1; 1, 0] := by
      change (ModularGroup.S.val.map (fun z : ℤ => (z : ℝ))) = _
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [ModularGroup.S, Matrix.map_apply]
    rw [hS]
    change !![0, -1/Real.sqrt N; Real.sqrt N, 0] *
      !![(Real.sqrt N)⁻¹, 0; 0, Real.sqrt N] = !![(0 : ℝ), -1; 1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
  have h := hF.slash k hD
  rwa [← SlashAction.slash_mul, hWD] at h

theorem space_zero_at_infty {N k : ℕ} {hN : 0<N} (F : space N hN k) :
    IsZeroAtImInfty (F.val : ℍ → ℂ) := by
  obtain ⟨G,hG,hF0,hG0,ht⟩ := F.property
  exact hF0

theorem space_zero_slashS {N k : ℕ} {hN : 0<N} (F : space N hN k) :
    IsZeroAtImInfty ((F.val : ℍ → ℂ) ∣[(k : ℤ)] (ModularGroup.S : GL (Fin 2) ℝ)) := by
  obtain ⟨G,hG,hF0,hG0,ht⟩ := F.property
  apply slashS_zero_of_fricke hN (k : ℤ) F.val
  rw [← hG]
  exact hG0

/-- The full modular weak functional-equation pair is strong on M_k^circ.
This includes forms noncuspidal at the other cusps. -/
theorem space_strongPair {N k : ℕ} [NeZero N] {hN : 0<N} (hk : 0<k)
    (F : space N hN k) :
    IsStrongFEPair (ModularForm.weakFEPair (by exact_mod_cast hk : (0 : ℤ)<k) F.val) where
  hf₀ := (space_zero_at_infty F).valueAtInfty_eq_zero
  hg₀ := (space_zero_slashS F).valueAtInfty_eq_zero

/-- Every modular form vanishing at infinity has an exponential bound
on the positive imaginary ray. No all-cusp condition is required. -/
theorem modular_axis_exponential_bound {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (F : ModularForm Γ k) (hF : IsZeroAtImInfty (F : ℍ → ℂ)) :
    ∃ C c : ℝ, 0≤C ∧ 0<c ∧ ∀ t : ℝ, 1≤t →
      ‖F (ofComplex (Complex.I*t))‖ ≤ C*Real.exp (-c*t) := by
  obtain ⟨c,hc,ho⟩ := ModularFormClass.exp_decay_sub_atImInfty' F
  rw [hF.valueAtInfty_eq_zero] at ho
  simp only [sub_zero] at ho
  have ha : (fun t : ℝ => F (ofComplex (Complex.I*t)))
      =O[atTop] (fun t : ℝ => Real.exp (-c*t)) := by
    apply (ho.comp_tendsto AsymptoticClassicalLSeries.axis_tendsto).congr'
      (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [Function.comp_apply, ofComplex_apply_of_im_pos, ht, ← coe_im]
  have hcts : ContinuousOn (fun t : ℝ => F (ofComplex (Complex.I*t))) (Ici 1) :=
    F.holo'.continuous.comp_continuousOn
      (continuousOn_ofComplex_I_mul.mono (fun t ht => lt_of_lt_of_le zero_lt_one ht))
  obtain ⟨C,hC,hbound⟩ := AsymptoticClassicalLSeries.exponential_bound_on_Ici hcts ha
  exact ⟨C,c,hC,hc,hbound⟩

/-- Entire continuation of the full trace-new Mellin transform. -/
theorem space_lambda_differentiable {N k : ℕ} [NeZero N] {hN : 0<N} (hk : 0<k)
    (F : space N hN k) :
    Differentiable ℂ (ModularForm.Λ (by exact_mod_cast hk : (0 : ℤ)<k) F.val) :=
  (space_strongPair hk F).differentiable_Λ

/-- The same Mellin transform has finite order, by exponential decay of
exactly its two functional-equation tails. -/
theorem space_lambda_finiteOrder {N k : ℕ} [NeZero N] {hN : 0<N} (hk : 0<k)
    (F : space N hN k) :
    FinitenessFiniteOrder.Bound (ModularForm.Λ (by exact_mod_cast hk : (0 : ℤ)<k) F.val) := by
  let ΓS := toConjAct (ModularGroup.S : GL (Fin 2) ℝ)⁻¹ • level N
  let : ΓS.IsArithmetic := by
    convert Subgroup.IsArithmetic.conj (level N) ↑(ModularGroup.S⁻¹)
    simp only [ModularGroup.S_inv, ← map_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]
  let G : ModularForm ΓS (k : ℤ) := ModularForm.translate F.val (ModularGroup.S : GL (Fin 2) ℝ)
  obtain ⟨Cf,cf,hCf,hcf,hf⟩ := modular_axis_exponential_bound F.val (space_zero_at_infty F)
  obtain ⟨Cg,cg,hCg,hcg,hg⟩ := modular_axis_exponential_bound G (space_zero_slashS F)
  exact AsymptoticClassicalLSeries.strongPair_finiteOrder
    (ModularForm.weakFEPair (by exact_mod_cast hk : (0 : ℤ)<k) F.val)
    (space_strongPair hk F) hCf hCg hcf hcg hf hg

#print axioms slashS_zero_of_fricke
#print axioms space_strongPair
#print axioms space_lambda_differentiable
#print axioms space_lambda_finiteOrder
end QuantitativeArithmeticSmallLevelCirc
