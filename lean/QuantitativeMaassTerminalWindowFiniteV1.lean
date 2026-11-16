module

public import QuantitativeMaassTerminalPacketCountV1
public import QuantitativeMaassOriginalWindowPacketV1
public import QuantitativeMaassWindowIdentityTermV1
public import QuantitativeMaassTerminalCountableV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap ContDiff FourierTransform

namespace QuantitativeMaass.EulerHilbert.Nonzero

/-- The actual original Euler window is finite for the explicitly
normalized smoothed interval. No Hilbert-Schmidt or spectral-action
hypothesis remains; the displayed tail inequality concerns only the
chosen scalar smoothing function. -/
theorem originalWindow_finite_smoothed_terminal {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ
      (terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε))
    (σ : ℕ) (t ε : ℝ)
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (δ : ℝ) (hδ : 0<δ) (ht : 0<t-δ) (k : ℕ)
    (htail : (∫ u,|u|^k*K u)/(R*δ)^k<1) :
    (QuantitativeConcreteGoals.maassWindow N σ t ε).Finite := by
  let g := windowTimeSchwartz K hc R hR (t-δ) (t+ε+δ)
  let c : ℂ := ((windowInteriorConstant K R δ k)⁻¹:ℝ)
  let f : SchwartzMap ℝ ℂ := c • g
  have hg : HasCompactSupport (g : ℝ → ℂ) :=
    symmetricWindowTimeTest_compact K hc R (t-δ) (t+ε+δ) hR
  have hge : Function.Even g := symmetricWindowTimeTest_even K he R (t-δ) (t+ε+δ)
  have hgr : ∀ x,star (g x)=g x := symmetricWindowTimeTest_real K he R (t-δ) (t+ε+δ)
  have hfc : HasCompactSupport (f : ℝ → ℂ) := hg.smul_left
  have hfe : Function.Even f := by
    intro x
    change c*g (-x)=c*g x
    rw [hge]
  have hfr : ∀ x,star (f x)=f x := by
    intro x
    change star (c*g x)=c*g x
    rw [star_mul,hgr]
    simp only [c,Complex.star_def,Complex.conj_ofReal,mul_comm]
  let L := windowSupportRadius K hc*R
  have hL : 0≤L := (mul_pos (windowSupportRadius_pos K hc) hR).le
  have hfs : Function.support f⊆Icc (-L) L := by
    intro x hx
    apply windowSupportRadius_support K hc R hR (t-δ) (t+ε+δ)
    intro hz
    apply hx
    change c*g x=0
    change g x=0 at hz
    rw [hz,mul_zero]
  have hcos (r : ℝ) : cosinePacket f r=
      (smoothedWindow K R (Icc (t-δ) (t+ε+δ)∪Icc (-(t+ε+δ)) (-(t-δ))) r /
        windowInteriorConstant K R δ k:ℝ) := by
    have heq : cosinePacket f r=c*cosinePacket g r := by
      unfold cosinePacket
      change (∫ s,c*g s*(Real.cos (s*r):ℂ))=c*∫ s,g s*(Real.cos (s*r):ℂ)
      simp_rw [mul_assoc]
      exact integral_const_mul c _
    have hgcos : cosinePacket g r=
        (smoothedWindow K R (Icc (t-δ) (t+ε+δ)∪Icc (-(t+ε+δ)) (-(t-δ))) r:ℂ) :=
      symmetricWindowTimeTest_cosinePacket K he hc R (t-δ) (t+ε+δ) r hR ht
    rw [heq,hgcos]
    simp only [c,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
    ring
  exact (originalWindow_count_terminal_packet A hN P basis σ t ε f hfc hfe hfr L hL hfs
    (by
      intro r hr
      rw [hcos,Complex.ofReal_re]
      exact originalWindowMajorant_scalar_lower K hK hm R hR t (t+ε) δ r k hδ hr htail)).1

#print axioms originalWindow_finite_smoothed_terminal

/-- Finiteness of the literal original Euler solution set in each compact
positive principal window. The basis, scalar smoothing kernel and its tail
parameters are constructed inside the proof. -/
theorem originalWindow_finite_terminal {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) (σ : ℕ) (t ε : ℝ) (ht : 0<t) :
    (QuantitativeConcreteGoals.maassWindow N σ t ε).Finite := by
  obtain ⟨ι,hι,⟨basis⟩⟩ := exists_countable_terminal_nonzero_basis
    (AsymptoticReconstructedCount.parameters A P).ε
  let : Countable ι := hι
  obtain ⟨K,hK,he,hm,hc⟩ := exists_positive_bandlimited_window_kernel
  let δ := t/2
  have hδ : 0<δ := half_pos ht
  let m := ∫ u,|u| * K u
  have hm0 : 0≤m := integral_nonneg (fun u => mul_nonneg (abs_nonneg _) (hK u))
  let R := (m+1)/δ
  have hR : 0<R := div_pos (by linarith) hδ
  have htail : (∫ u,|u|^1*K u)/(R*δ)^1<1 := by
    simp only [pow_one]
    change m/(R*δ)<1
    have heq : R*δ=m+1 := div_mul_cancel₀ _ hδ.ne'
    rw [heq]
    exact (div_lt_one (by linarith : 0<m+1)).mpr (by linarith)
  exact originalWindow_finite_smoothed_terminal A hN P basis σ t ε K hK hm he hc
    R hR δ hδ (by dsimp [δ]; linarith) 1 htail

#print axioms originalWindow_finite_terminal

/-- Finiteness for every admissible level and positive principal window,
with the spanning certificate and height parameters constructed internally. -/
theorem admissible_originalWindow_finite (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (σ : ℕ) (t ε : ℝ) (ht : 0<t) :
    (QuantitativeConcreteGoals.maassWindow N σ t ε).Finite := by
  obtain ⟨Q,hQ,_,⟨A⟩⟩ := FinitenessCertificate.exists_certificate N hN.1 hN.2.1 hN.2.2
  obtain ⟨P⟩ := FinitenessGlobalHeight.parameters_exist hN.1 hQ A
  exact originalWindow_finite_terminal A hN.1 P σ t ε ht

/-- The eventual-finiteness component of the literal requested Maass
window claim, independent of any asymptotic restriction on window width. -/
theorem admissible_originalWindow_eventually_finite (N : ℕ)
    (hN : GridAdmissibleGap.Admissible N) (σ : ℕ) (ε : ℝ → ℝ) :
    ∀ᶠ t in atTop,(QuantitativeConcreteGoals.maassWindow N σ t (ε t)).Finite := by
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact admissible_originalWindow_finite N hN σ t (ε t) ht

#print axioms admissible_originalWindow_finite
#print axioms admissible_originalWindow_eventually_finite

end QuantitativeMaass.EulerHilbert.Nonzero
