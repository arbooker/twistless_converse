module

public import QuantitativeEulerEndpointGamma0WordsV1
public import QuantitativeSpectralObservabilityTerminalV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane CongruenceSubgroup QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators QuantitativeEulerDiamondDecode
open QuantitativeSpectralObservability QuantitativeSpectralObservabilityDecoded
open AsymptoticRegularObservationRows AsymptoticObservationStack
open AsymptoticHyperbolicArea AsymptoticOrbitDiagonal
open AsymptoticRegularCompactBranch (Space)
open scoped Classical MatrixGroups

theorem observed_word_mem_gamma0 (N : ℕ) [NeZero N] (l : List SL(2,ℤ))
    (h : ∀ a∈l, a∈observedGenerators N ∨ a⁻¹∈observedGenerators N) : l.prod∈Gamma0 N := by
  have hm (a : SL(2,ℤ)) (ha : a∈observedGenerators N) : a∈Gamma0 N := by
    rw [←observedGenerators_closure]
    exact Subgroup.subset_closure ha
  induction l with
  | nil => exact (Gamma0 N).one_mem
  | cons a l ih =>
    apply (Gamma0 N).mul_mem
    · rcases h a List.mem_cons_self with ha | ha
      · exact hm a ha
      · simpa only [inv_inv] using (Gamma0 N).inv_mem (hm a⁻¹ ha)
    · exact ih (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- Actual terminal energy is controlled by the compact sampler, original
untwisted/fixed-prime rows, the actual fresh-prime stack and the terminal
tail. Constants are selected at epsilon, BEFORE H,t,q,w,x and the vector.
No quantitative dependence on a varying epsilon is asserted here. -/
theorem terminal_original_fresh_energy {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ ∃ M : ℝ, 0≤M ∧
      ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
      ∃ hqN : ¬q∣N, ∀ (H : ℝ), ε⁻¹≤H → ∀ (w : ℂ), w*w=1 →
      ∀ (t : ℕ) (x : ℍ) (v : Space),
      let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
      ‖corner (terminal ε) x v‖^2≤
        M*‖sampling N (NeZero.pos N) H hε t x v‖^2+
        K*((integerCompactDistortion L H)^t)^2*
          (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hε) hε t x v‖^2+
            ‖fixedPrimeStack N w (freshObservationRegion_compact L H hε) hε t x v‖^2+
            ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
              (freshObservationRegion_compact L H hε) hε t i x) v‖^2)+
        ‖corner (terminal H) x v‖^2 := by
  obtain ⟨W,hW,hw⟩ := exists_terminal_word_energy N (NeZero.pos N) (observedGenerators N)
    (observedGenerators_closure N) hε
  have hprod (l : ↥W) : l.val.prod∈Gamma0 N :=
    observed_word_mem_gamma0 N l.val (hW l.val l.property)
  obtain ⟨B,hB,K,hK,hbound⟩ := gamma0_finite_original_control P
    (fun l : ↥W => l.val.prod) hprod (fun _ => 1)
  let m : ℝ := 2*(Fintype.card ↥W : ℝ)
  have hm : 0≤m := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  refine ⟨B,hB,m*K,mul_nonneg hm hK,m,hm,?_⟩
  intro C hBC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro H hH w hww t x v
  let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
  let Q := K*((integerCompactDistortion L H)^t)^2*
    (‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w (freshObservationRegion_compact L H hε) hε t x v‖^2+
      ‖fixedPrimeStack N w (freshObservationRegion_compact L H hε) hε t x v‖^2+
      ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
        (freshObservationRegion_compact L H hε) hε t i x) v‖^2)
  have hre (z : ℍ) (hz : z∈terminalRectangle ε H) : |z.re|≤1 := by
    rw [abs_of_nonneg hz.1]
    exact hz.2.1
  have hterm (l : ↥W) :
      ‖AsymptoticCongruenceDefect.operator l.val.prod (terminalRectangle_compact hε H) hε t x v‖^2≤Q := by
    obtain ⟨_hqN,hl⟩ := hbound l C hBC q hqGood
    have hh := hl w hww (terminalRectangle_compact hε H) hε hε hre
      (fun z hz => hz.2.2.1) (fun z hz => hz.2.2.2) t x v
    simpa only [map_one,mul_one,compactAction_congruence] using hh
  have hsum := Finset.sum_le_sum (fun l (_ : l∈(Finset.univ : Finset ↥W)) =>
    add_le_add (le_refl (‖sampling N (NeZero.pos N) H hε t x v‖^2)) (hterm l))
  have ht := (hw H hH t x v).trans
    (add_le_add (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ)≤2)) (le_refl _))
  exact ht.trans_eq (by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    dsimp only [m,Q]
    ring)

#print axioms observed_word_mem_gamma0
#print axioms terminal_original_fresh_energy
end QuantitativeEulerEndpointPrepared
