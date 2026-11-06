module

public import QuantitativeSpectralFreshStepV1
public import QuantitativeSpectralRegularPacketV1
public import QuantitativeSpectralDeflationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralPacketContraction

open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace AsymptoticObservationStack
open AsymptoticMixing AsymptoticSubgroupSupport QuantitativeSpectralCornerCutRow
open QuantitativeSpectralDeflationChain QuantitativeSpectralRegularPacket
open QuantitativeSpectralFreshStep QuantitativeSpectralDeflation
open scoped lp ENNReal

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem nextSpace_restricted (P : Submodule ℂ H) [CompleteSpace P]
    (B : H →L[ℂ] H) (d : ℝ) : nextSpace P (B.comp P.starProjection) d = nextSpace P B d := by
  have he : restricted P (B.comp P.starProjection) = restricted P B := by
    change (B.comp P.starProjection).comp P.starProjection = B.comp P.starProjection
    rw [comp_assoc, show P.starProjection.comp P.starProjection = P.starProjection from
      P.isIdempotentElem_starProjection]
  simp only [nextSpace, he]
end Hilbert

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ ℓ²(G,ℂ)) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

variable (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (d : ℝ)

/-- The surviving corner is the actual recursive spectral-deflation chain. -/
def packetSpace (n : ℕ) (x : α) : Submodule ℂ ℓ²(G,ℂ) :=
  (chain (U x) (fun i => B i x) d n).toSubmodule
instance packetSpace_complete (n : ℕ) (x : α) : CompleteSpace (packetSpace U B d n x) :=
  closedSubmodule_complete _

local notation "P" => packetSpace U B d

/-- Exponential decay of the excess trace for the constructed packet, with
varying row counts. Every one-step dimension loss is proved from actual fresh
coset separation and norm observability. This theorem still requires the
concrete arithmetic/geometric application to supply those row operators,
sampling maps, and observability inequalities. -/
theorem packet_trace_excess (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).toSubmodule.starProjection g h))
    (hcU : Covariant (fun x => (U x).toSubmodule.starProjection))
    (hmB : ∀ n g h, Measurable (fun x => matrix (B n x) g h))
    (hcB : ∀ n, Covariant (B n)) (MB : ℕ → ℝ) (hMB : ∀ n x, ‖B n x‖ ≤ MB n)
    (hd : 0 < d) (hf : trace μ (fun x => (U x).toSubmodule.starProjection) < ∞)
    (S : ℕ → Subgroup G) (a : ∀ n, ι n → G)
    (ha : ∀ n i j, i ≠ j → a n j * (a n i)⁻¹ ∉ S n)
    (hι : ∀ n, 0 < Fintype.card (ι n))
    (L : ∀ n, α → ι n → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmL : ∀ n i g h, Measurable (fun x => matrix (L n x i) g h))
    (hcL : ∀ n i, Covariant (fun x => L n x i))
    (hL : ∀ n x i, Supported (S n) (L n x i))
    (hLP : ∀ n x i, (L n x i).comp (P n x).starProjection = L n x i)
    (hmix : ∀ n x, normalizedMixed (a n) (L n x) = (B n x).comp (P n x).starProjection)
    (V : ℕ → α → Submodule ℂ ℓ²(G,ℂ)) [∀ n x, CompleteSpace (V n x)]
    (C : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmC : ∀ n g h, Measurable (fun x => matrix (C n x) g h))
    (hcC : ∀ n, Covariant (C n)) (M N K c : ℕ → ℝ)
    (hM : ∀ n x, ‖stack (L n x)‖ ≤ M n) (hN : ∀ n x, ‖C n x‖ ≤ N n)
    (hfV : ∀ n, trace μ (fun x => (V n x).starProjection) < ∞)
    {theta target : ℝ} (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hV : ∀ n, (trace μ (fun x => (V n x).starProjection)).toReal ≤ target)
    (hc : ∀ n, 0 < c n)
    (hscale : ∀ n, d^2 = (c n)^2*theta/(2*(Fintype.card (ι n))))
    (hK : ∀ n, 0 ≤ K n) (hsmall : ∀ n, K n*(c n)^2 < 1)
    (n : ℕ)
    (hobs : ∀ j < n, ∀ x v, v ∈ P j x → ‖v‖^2 ≤ K j*(‖stack (L j x) v‖^2+‖C j x v‖^2))
    (hmap : ∀ j x v, v ∈ P j x → C j x v ∈ V j x) :
    (trace μ (fun x => (P n x).starProjection)).toReal ≤
      target + max 0 ((trace μ (fun x => (U x).toSubmodule.starProjection)).toReal-target) *
        Real.exp (-(∑ i ∈ Finset.range n, (1-theta)/(Fintype.card (ι i)))) := by
  let p := fun j => (trace μ (fun x => (P j x).starProjection)).toReal
  let w := fun j => (1-theta)/(Fintype.card (ι j):ℝ)
  have hw (j : ℕ) : 0 ≤ w j := div_nonneg (sub_nonneg.mpr htheta1) (Nat.cast_nonneg _)
  have hw1 (j : ℕ) : w j ≤ 1 := by
    have hn : (1:ℝ) ≤ Fintype.card (ι j) := by exact_mod_cast hι j
    have hnpos : (0:ℝ) < Fintype.card (ι j) := by exact_mod_cast hι j
    apply (div_le_iff₀ hnpos).mpr
    simpa only [one_mul] using (show 1-theta ≤ (Fintype.card (ι j):ℝ) by linarith)
  have hloss (j : ℕ) (hj : j < n) : w j*(p j-target) ≤ p j-p (j+1) := by
    have hr := projection_regular U B d hmU hcU hmB hcB MB hMB hd j
    have hfin : trace μ (fun x => (P j x).starProjection) < ∞ := by
      apply projection_trace_finite_of_le μ _ (fun x => (U x).toSubmodule) _ hf
      intro x
      exact chain_antitone (U x) (fun i => B i x) d (Nat.zero_le j)
    have hh := observable_fresh_step μ hmp (S j) (a j) (ha j) (hι j) (P j) (V j)
      hr.1 hr.2 (L j) (hmL j) (hcL j) (hL j) (hLP j) (C j) (hmC j) (hcC j)
      (M j) (N j) (hM j) (hN j) hfin (hfV j) (hc j) hd htheta htheta1 (hscale j)
      (hK j) (hsmall j) (hobs j hj) (hmap j)
    have he (x : α) : nextSpace (P j x) (normalizedMixed (a j) (L j x)) d = P (j+1) x := by
      rw [hmix, nextSpace_restricted]
      rfl
    have heP (x : α) : (nextSpace (P j x) (normalizedMixed (a j) (L j x)) d).starProjection =
        (P (j+1) x).starProjection := AsymptoticPolarIsometry.starProjection_congr _ _ (he x)
    simp only [heP] at hh
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left (hV j) (p j)) (hw j)).trans hh
  let p' := fun j => p (min j n)
  let w' := fun j => if j < n then w j else 0
  have hw' (j : ℕ) : w' j ≤ 1 := by
    by_cases hj : j < n
    · simpa only [w', ite_eq_left hj] using hw1 j
    · simp only [w', ite_eq_right hj, zero_le_one]
  have hloss' (j : ℕ) : w' j*(p' j-target) ≤ p' j-p' (j+1) := by
    by_cases hj : j < n
    · simpa only [w', ite_eq_left hj, p', Nat.min_eq_left hj.le,
        Nat.min_eq_left (Nat.succ_le_of_lt hj)] using hloss j hj
    · have hjn : n ≤ j := Nat.le_of_not_gt hj
      simp only [w', ite_eq_right hj, p', Nat.min_eq_right hjn,
        Nat.min_eq_right (hjn.trans (Nat.le_succ j)), zero_mul, sub_self, le_refl]
  have hsum : (∑ i ∈ Finset.range n, w' i) = ∑ i ∈ Finset.range n, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [w', ite_eq_left (Finset.mem_range.mp hi)]
  have hh := trace_le_target_add_exp p' w' target hw' hloss' n
  simpa only [p', Nat.min_self, Nat.zero_min, hsum, p, w, packetSpace, chain] using hh

#print axioms nextSpace_restricted
#print axioms packet_trace_excess

end QuantitativeSpectralPacketContraction
