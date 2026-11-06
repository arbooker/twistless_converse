module

public import QuantitativeSpectralExceptionalStackDetectorV1
public import AsymptoticOrbitRegionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalReducedRows

open UpperHalfPlane ContinuousLinearMap AsymptoticOrbitDiagonal
open AsymptoticRegularBranchFamily QuantitativeSpectralWordDefect
open QuantitativeSpectralObservability
open QuantitativeSpectralExceptionalUnweight (G Space)
open scoped MatrixGroups lp

/-- Difference support removes the upper cutoff including its boundary. -/
theorem difference_source_corners (s u : Set ℍ) (x : ℍ) (f : Space)
    (hf : f∈AsymptoticOrbitRegion.Space (s\u) x) :
    corner s x f=f ∧ corner u x f=0 := by
  have he := (AsymptoticOrbitRegion.mem_space (s\u) x f).mp hf
  have hz : ∀ g : G, g • x∉s\u → f g=0 := by
    intro g hg
    have hh := congrArg (fun v : Space => v g) he
    simpa only [corner_apply,ite_eq_right hg] using hh.symm
  constructor
  · apply lp.ext
    funext g
    rw [corner_apply]
    by_cases hg : g • x∈s
    · rw [ite_eq_left hg]
    · rw [ite_eq_right hg,hz g (fun h => hg h.1)]
  · apply (AsymptoticOrbitRegion.corner_eq_zero_iff u x f).mpr
    intro g hg
    exact hz g (fun h => h.2 hg)

def terminalObservationConstant (S : Finset SL(2,ℤ)) (W : Finset (List SL(2,ℤ))) : ℝ :=
  1+2*∑ l : ↥W, (1+((l.val.length:ℝ)*(2*(S.card:ℝ)))^2)

theorem terminalObservationConstant_ge_one (S : Finset SL(2,ℤ))
    (W : Finset (List SL(2,ℤ))) : 1≤terminalObservationConstant S W := by
  unfold terminalObservationConstant
  have : 0≤∑ l : ↥W, (1+((l.val.length:ℝ)*(2*(S.card:ℝ)))^2) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  linarith

/-- The finite word sum has a fixed coefficient and one explicit polynomial
power; no observation estimate is assumed here. -/
theorem terminal_word_sum_bound (S : Finset SL(2,ℤ)) (W : Finset (List SL(2,ℤ)))
    (B H d a : ℝ) (t : ℕ) :
    2*∑ l : ↥W, (a^2+
      ((l.val.length:ℝ)*transportPolynomial B H t*((2*(S.card:ℝ))*d))^2) ≤
    terminalObservationConstant S W*(1+B^2*(H+3)^2)^(2*t)*(d^2+a^2) := by
  let q := (1+B^2*(H+3)^2)^t
  have hbase : 0≤B^2*(H+3)^2 := by positivity
  have hq : 1≤q := one_le_pow₀ (by linarith)
  have hp : 0≤transportPolynomial B H t := by unfold transportPolynomial; positivity
  have hpq : transportPolynomial B H t≤q := by
    apply pow_le_pow_left₀ (by positivity)
    exact max_le (by linarith) (by linarith)
  have hp2 : (transportPolynomial B H t)^2≤q^2 := pow_le_pow_left₀ hp hpq 2
  have hq2 : 1≤q^2 := by nlinarith
  have hterm (l : ↥W) :
      a^2+((l.val.length:ℝ)*transportPolynomial B H t*((2*(S.card:ℝ))*d))^2 ≤
      (1+((l.val.length:ℝ)*(2*(S.card:ℝ)))^2)*q^2*(d^2+a^2) := by
    let r := ((l.val.length:ℝ)*(2*(S.card:ℝ)))^2
    have hr : 0≤r := sq_nonneg _
    have h1 := mul_le_mul_of_nonneg_right hq2 (sq_nonneg a)
    have h2 := mul_le_mul_of_nonneg_left hp2 (mul_nonneg hr (sq_nonneg d))
    have h3 : 0≤q^2*d^2+r*q^2*a^2 := by positivity
    dsimp only [r] at *
    nlinarith only [h1,h2,h3]
  calc
    _ ≤ 2*∑ l : ↥W, (1+((l.val.length:ℝ)*(2*(S.card:ℝ)))^2)*q^2*(d^2+a^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun l _ => hterm l)) (by norm_num)
    _ = (2*∑ l : ↥W, (1+((l.val.length:ℝ)*(2*(S.card:ℝ)))^2))*q^2*(d^2+a^2) := by
      rw [← Finset.sum_mul,← Finset.sum_mul]; ring
    _ ≤ terminalObservationConstant S W*q^2*(d^2+a^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg q)
      unfold terminalObservationConstant
      linarith
    _ = _ := by simp only [q,← pow_mul,Nat.mul_comm]

variable {J : Type*} [Fintype J] {I K : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, Fintype (K j)]

/-- Concrete polynomial observability on the retained terminal source for
the same enlarged detector used by every retained quotient row. -/
theorem exists_enlarged_source_observability (N : ℕ) (hN : 0<N)
    (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (b : ∀ j, I j → Branch) (w : ∀ j, K j → I j → List SL(2,ℤ)) (c : ∀ j, I j → ℂ)
    (s : ℝ → J → Set ℍ) (hs : ∀ H j, IsCompact (s H j))
    {ε : ℝ} (hε : 0<ε) :
    ∃ (W : Finset (List SL(2,ℤ))) (B : ℝ), 1≤B ∧
      (∀ l∈W, ∀ a∈l, a∈S ∨ a⁻¹∈S) ∧
      ∀ (H : ℝ), max ε⁻¹ 4≤H → ∀ (t : ℕ) (ht : 1≤t) (x : ℍ),
        fundamentalGood N x → ∀ (P : Submodule ℂ Space),
          P≤AsymptoticOrbitRegion.Space
            (AsymptoticHyperbolicArea.terminal ε\AsymptoticHyperbolicArea.terminal H) x →
          ∀ (f : Space), f∈P →
        let hu := enlargedRegion_compact b w (s H) (hs H) (wordRegion_compact W hε H)
        ‖f‖^2 ≤ terminalObservationConstant S W*(1+B^2*(H+3)^2)^(2*t)*
          (‖enlargedDetector (signedGenerators S) b c hu hε t x f‖^2+
           ‖fundamentalSampling N hN H hε ht x f‖^2) := by
  obtain ⟨W,B,hB,hW,hobs⟩ := exists_enlarged_terminal_observability N hN S hS b w c s hs hε
  refine ⟨W,B,hB,hW,?_⟩
  intro H hH t ht x hx P hP f hf
  have hc := difference_source_corners _ _ x f (hP hf)
  have hh := hobs H hH t ht x hx f
  dsimp only at hh ⊢
  rw [hc.1,hc.2,norm_zero,zero_pow (by omega),add_zero] at hh
  rw [enlargedDetector_norm_apply]
  exact hh.trans (terminal_word_sum_bound S W B H _ _ t)

#print axioms difference_source_corners
#print axioms terminal_word_sum_bound
#print axioms exists_enlarged_source_observability

end QuantitativeSpectralExceptionalReducedRows
