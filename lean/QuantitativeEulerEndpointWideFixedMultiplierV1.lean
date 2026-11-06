module

public import QuantitativeEulerEndpointFixedMultiplierV1
public import QuantitativeEulerEndpointWideProjectiveGeneratorV1


set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane CongruenceSubgroup QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open AsymptoticCongruenceLabels AsymptoticRegularObservationRows
open AsymptoticRegularCompactBranch (Space)
open AsymptoticObservationStack
open scoped Classical MatrixGroups

/-- Fixed Gamma1 defects followed by any fixed group-ring multiplier are
controlled by the actual fresh-prime stack. Both constants precede the
prime and all analytic cutoffs. Allowing a larger height C permits a finite
family of correction terms to share exactly the same observation region. -/
theorem wide_gamma1_fixed_multiplier_stack_bound {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (γ : SL(2,ℤ)) (hγ : γ∈Gamma1 N) (E : Ring) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (w : ℂ) (_hw : w*w=1)
        {s : Set ℍ} (hs : IsCompact s) {ε W₀ Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
        (_hre : ∀ z∈s, |z.re|≤W₀) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
        (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖compactAction hs hε t x ((symbol (integralLabel γ)-1)*E) v‖^2≤
      K*((wideDistortion L W₀ H)^t)^2*
        (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
          ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
            (wideFreshRegion_compact L W₀ H hY) hε t j x) v‖^2) := by
  obtain ⟨W,hW,hexp⟩ := gamma1_compact_generator_expansion N γ hγ
  let J := ↥E.coeff.support
  let label : (Fin W.length × J) × Bool → AsymptoticRationalGroup.Group := fun p =>
    if p.2 then integralLabel (W.get p.1.1).1*(integralLabel (W.get p.1.1).2*p.1.2.val)
    else integralLabel (W.get p.1.1).2*p.1.2.val
  obtain ⟨B,hB,hmat⟩ := QuantitativeEulerIntegerHeight.finite_family_height label
  let R := coefficientSquareBound E
  have hR : 0≤R := (coefficientSquareBound_pos E).le
  let K := 200*(W.length : ℝ)^2*(Fintype.card J : ℝ)^2*R
  have hK : 0≤K := mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)) hR
  refine ⟨B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hqGood
  have hC : 0≤C := zero_le_one.trans (hB.trans hBC)
  obtain ⟨hqN,hqbound⟩ := wide_good_prime_projective_generator_stack_bound P q hqGood
  refine ⟨hqN,?_⟩
  intro w hw s hs ε W₀ Y H hε hY hre hlo him t x v
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let Q := ((wideDistortion L W₀ H)^t)^2*
    (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (wideFreshRegion_compact L W₀ H hY) hε t x v‖^2+
      ‖stack (fun j => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
        (wideFreshRegion_compact L W₀ H hY) hε t j x) v‖^2)
  have hrow (i : Fin W.length) (g : J) :
      ‖compactAction hs hε t x ((symbol (integralLabel (W.get i).1)-1)*
        symbol (integralLabel (W.get i).2*g.val)) v‖^2≤200*Q := by
    rcases hW (W.get i) (List.get_mem W i) with hpos | hneg
    · obtain ⟨M,hM,hMb⟩ := hmat ((i,g),false)
      change IntegerAction (integralLabel (W.get i).2*g.val) M at hM
      exact (hqbound ⟨_,hpos⟩ _ M C hM hC (entry_bound_mono hMb hBC)
        w hw hs hε hY hre hlo him t x v).trans_eq (mul_assoc _ _ _)
    · obtain ⟨M,hM,hMb⟩ := hmat ((i,g),true)
      change IntegerAction (integralLabel (W.get i).1*(integralLabel (W.get i).2*g.val)) M at hM
      rw [projective_inverse_letter_norm (W.get i).1 (integralLabel (W.get i).2*g.val) hs hε t x v]
      exact (hqbound ⟨_,hneg⟩ _ M C hM hC (entry_bound_mono hMb hBC)
        w hw hs hε hY hre hlo him t x v).trans_eq (mul_assoc _ _ _)
  let u : Fin W.length → J → Space := fun i g => E.coeff g.val •
    compactAction hs hε t x ((symbol (integralLabel (W.get i).1)-1)*
      symbol (integralLabel (W.get i).2*g.val)) v
  have hterm (i : Fin W.length) (g : J) : ‖u i g‖^2≤R*(200*Q) := by
    dsimp only [u]
    rw [norm_smul,mul_pow]
    exact mul_le_mul (coefficientSquareBound_le E g) (hrow i g) (sq_nonneg _) hR
  have hinner (i : Fin W.length) :
      ‖∑ g : J, u i g‖^2≤(Fintype.card J : ℝ)^2*(R*(200*Q)) :=
    finite_sum_squared_bound (u i) _ (hterm i)
  have hsum := finite_sum_squared_bound (fun i : Fin W.length => ∑ g : J, u i g) _ hinner
  rw [hexp E hs hε t x,←List.ofFn_getElem_eq_map,List.sum_ofFn,_root_.sum_apply]
  have he (i : Fin W.length) :
      compactAction hs hε t x
        ((symbol (integralLabel (W.get i).1)-1)*(symbol (integralLabel (W.get i).2)*E)) v=
      ∑ g : J, u i g := by
    rw [compact_word_multiplier_expand,_root_.sum_apply]
    rfl
  change ‖∑ i : Fin W.length, compactAction hs hε t x
    ((symbol (integralLabel (W.get i).1)-1)*(symbol (integralLabel (W.get i).2)*E)) v‖^2≤_
  simp_rw [he]
  simp only [Fintype.card_fin] at hsum
  exact hsum.trans_eq (by dsimp only [K,Q]; ring)

#print axioms wide_gamma1_fixed_multiplier_stack_bound
end QuantitativeEulerEndpointPrepared
