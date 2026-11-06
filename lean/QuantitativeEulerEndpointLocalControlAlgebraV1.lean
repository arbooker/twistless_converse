module

public import QuantitativeEulerEndpointLocalControlV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

variable {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
variable {P : Prepared N excluded threshold} {p : ℕ} {hp : 0<p} {w δ : ℂ}

theorem wide_local_control_mono {A : Ring} {B B' K : ℝ}
    (h : WideLocalControl P p hp w δ A B K) (hB : B≤B') :
    WideLocalControl P p hp w δ A B' K := by
  intro C hC q _ hq
  exact h C (hB.trans hC) q hq

theorem wide_local_control_zero (P : Prepared N excluded threshold) (p : ℕ) (hp : 0<p) (w δ : ℂ) :
    WideLocalControl P p hp w δ 0 1 0 := by
  intro C _hC q hqPrime hqGood
  obtain ⟨_hex,hqN,_ht,_a,_hqa,_hcert⟩ := P.prime_data q Fact.out hqGood
  refine ⟨hqN,?_⟩
  intro s hs ε R Y H hε hY _hre _hlo _him t x v
  simp only [map_zero,_root_.zero_apply,norm_zero,zero_pow (by norm_num : 2≠0),zero_mul,le_refl]

theorem wide_local_control_add {A₁ A₂ : Ring} {B K₁ K₂ : ℝ}
    (h₁ : WideLocalControl P p hp w δ A₁ B K₁)
    (h₂ : WideLocalControl P p hp w δ A₂ B K₂) :
    WideLocalControl P p hp w δ (A₁+A₂) B (2*(K₁+K₂)) := by
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,h₁q⟩ := h₁ C hBC q hqGood
  obtain ⟨_hqN,h₂q⟩ := h₂ C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro s hs ε R Y H hε hY hre hlo him t x v
  have h₁v := h₁q hs hε hY hre hlo him t x v
  have h₂v := h₂q hs hε hY hre hlo him t x v
  rw [map_add,_root_.add_apply]
  exact ((two_vector_squared _ _).trans
    (mul_le_mul_of_nonneg_left (add_le_add h₁v h₂v) (by norm_num : (0 : ℝ)≤2))).trans_eq (by ring)

theorem wide_local_control_smul {A : Ring} {B K : ℝ}
    (h : WideLocalControl P p hp w δ A B K) (c : ℂ) :
    WideLocalControl P p hp w δ (c • A) B (‖c‖^2*K) := by
  intro C hBC q hqPrime hqGood
  obtain ⟨hqN,hqbound⟩ := h C hBC q hqGood
  refine ⟨hqN,?_⟩
  intro s hs ε R Y H hε hY hre hlo him t x v
  rw [map_smul,_root_.smul_apply,norm_smul,mul_pow]
  exact (mul_le_mul_of_nonneg_left (hqbound hs hε hY hre hlo him t x v)
    (sq_nonneg _)).trans_eq (by ring)

/-- Finite algebraic span membership gives actual quantitative compact
control, with all constants chosen before the fresh prime and geometry. -/
theorem wide_local_span_control (P : Prepared N excluded threshold)
    (p : ℕ) (hp : 0<p) (w δ : ℂ) (hw : w*w=1) (A : Ring)
    (hA : A∈localRowSpan N p (NeZero.pos N) hp w δ) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧ WideLocalControl P p hp w δ A B K := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · intro a ha
    obtain ⟨i,rfl⟩ := ha
    exact wide_local_translated_control P p hp w δ hw i
  · exact ⟨1,le_refl _,0,le_refl _,wide_local_control_zero P p hp w δ⟩
  · intro a b _ha _hb ia ib
    obtain ⟨B₁,hB₁,K₁,hK₁,h₁⟩ := ia
    obtain ⟨B₂,_hB₂,K₂,hK₂,h₂⟩ := ib
    exact ⟨max B₁ B₂,hB₁.trans (le_max_left _ _),2*(K₁+K₂),
      mul_nonneg (by norm_num) (add_nonneg hK₁ hK₂),
      wide_local_control_add (wide_local_control_mono h₁ (le_max_left _ _))
        (wide_local_control_mono h₂ (le_max_right _ _))⟩
  · intro c a _ha ia
    obtain ⟨B,hB,K,hK,h⟩ := ia
    exact ⟨B,hB,‖c‖^2*K,mul_nonneg (sq_nonneg _) hK,wide_local_control_smul h c⟩

/-- The actual simple-prime old trace is controlled by original ramified,
Fricke and Euler rows, without any exact invariance/newness premise on v. -/
theorem simpleTraceRow_original_control (M p : ℕ) [Fact p.Prime] [NeZero (p*M)]
    (P : Prepared (p*M) excluded threshold) (hM : 0<M) (hpM : ¬p∣M)
    (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (w δ : ℂ) (hw : w*w=1) (hδ : δ^2=1) :
    ∃ B₀ : ℝ, 1≤B₀ ∧ ∃ K : ℝ, 0≤K ∧
      WideLocalControl P p (Fact.out : p.Prime).pos w δ (simpleTraceRow M p A B hAB) B₀ K := by
  exact wide_local_span_control P p (Fact.out : p.Prime).pos w δ hw _
    (simpleTraceRow_mem_localRowSpan M p hM hpM A B hAB w δ hδ)

#print axioms wide_local_control_zero
#print axioms wide_local_control_add
#print axioms wide_local_control_smul
#print axioms wide_local_span_control
#print axioms simpleTraceRow_original_control
end QuantitativeEulerEndpointPrepared
