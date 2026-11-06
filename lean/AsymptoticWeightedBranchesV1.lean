module

public import AsymptoticFoldSelectionV1
public import AsymptoticCertificateFEV1
public import AsymptoticCertificateOperatorsV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticWeightedBranches

open UpperHalfPlane Set AsymptoticHyperbolicSlash AsymptoticReconstructionBranch
open AsymptoticFoldedLow AsymptoticFoldSelection AsymptoticCertificateOperators

/-- The capped holomorphic section on the hyperbolic strip. -/
noncomputable def weighted (ε : ℝ) (t m : ℕ) (F : ℂ → ℂ) (z : ℍ) : ℂ :=
  ((min (z.im/ε) 1)^t:ℝ)*(z.im:ℂ)^m*F z

noncomputable def stripSection (ε : ℝ) (t m : ℕ) (F : ℂ → ℂ) : ℍ → ℂ :=
  AsymptoticMassTransport.strip.indicator (weighted ε t m F)

theorem weighted_low {ε : ℝ} (hε : 0<ε) (t m : ℕ) (F : ℂ → ℂ)
    (z : ℍ) (hz : z.im≤ε) :
    weighted ε t m F z=((z.im/ε)^t:ℝ)*(z.im:ℂ)^m*F z := by
  rw [weighted,min_eq_left ((div_le_one hε).mpr hz)]

theorem weighted_high {ε : ℝ} (hε : 0<ε) (t m : ℕ) (F : ℂ → ℂ)
    (z : ℍ) (hz : ε≤z.im) : weighted ε t m F z=(z.im:ℂ)^m*F z := by
  rw [weighted,min_eq_right ((one_le_div hε).mpr hz),one_pow,Complex.ofReal_one,one_mul]

/-- Exact cancellation of the capped weight in a low-to-low branch. -/
theorem low_weight_cancel {ε : ℝ} (hε : 0<ε) (t m : ℕ) (F : ℂ → ℂ)
    (z w : ℍ) (hw : w.im≤ε) :
    ((z.im/w.im)^t:ℝ)*weighted ε t m F w=
      ((z.im/ε)^t:ℝ)*(w.im:ℂ)^m*F w := by
  rw [weighted_low hε t m F w hw]
  have he : (z.im/w.im)^t*(w.im/ε)^t=(z.im/ε)^t := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [← mul_assoc,← mul_assoc,← Complex.ofReal_mul,he]

variable {L : ℝ} (hL : 0<L) (b d : ℝ)

theorem section_fold {ε : ℝ} (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (n : ℤ) (z : ℍ) (hn : n=Int.floor (branch L b d hL.ne' • z).re) :
    stripSection ε t m F (fold hL b d n • z)=weighted ε t m F (branch L b d hL.ne' • z) := by
  rw [stripSection,Set.indicator_of_mem ((fold_mem_strip_iff hL b d n z).mpr hn)]
  rw [weighted,weighted,fold_im hL b d,periodic_fold hL b d F hp]

/-- The two target-height regions account for the entire branch. -/
theorem coefficient_weighted {ε cap : ℝ} (hε : 0<ε)
    (s : Set ℍ) (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (z : ℍ) (hz : z∈s) (hcap : z.im/(branch L b d hL.ne' • z).im≤cap)
    (n : ℤ) (hn : n=Int.floor (branch L b d hL.ne' • z).re) :
    coefficient hL b d s (lowStrip ε) cap t n z*
        phase (fold hL b d n) (2*m) z*stripSection ε t m F (fold hL b d n • z)+
      AsymptoticFoldedTerminal.coefficient hL b d s (highStrip ε) ε t n z*
        phase (fold hL b d n) (2*m) z*stripSection ε t m F (fold hL b d n • z)=
      ((z.im/ε)^t:ℝ)*phase (branch L b d hL.ne') (2*m) z*
        ((branch L b d hL.ne' • z).im:ℂ)^m*F (branch L b d hL.ne' • z:ℍ) := by
  have hstrip := (fold_mem_strip_iff hL b d n z).mpr hn
  have hr : ratio hL b d n z≤cap := by simpa only [ratio,fold_im hL b d] using hcap
  rw [section_fold hL b d t m F hp n z hn,fold_phase hL b d]
  by_cases hw : (branch L b d hL.ne' • z).im<ε
  · have hlow : z∈region hL b d s (lowStrip ε) cap n :=
      ⟨⟨hz,⟨hstrip,by
        change (fold hL b d n • z).im<ε
        simpa only [fold_im hL b d] using hw⟩⟩,hr⟩
    have hhigh : z∉AsymptoticFoldedTerminal.region hL b d s (highStrip ε) n := by
      intro h
      have hh : ε≤(fold hL b d n • z).im := h.2.2
      rw [fold_im hL b d] at hh
      exact (not_le_of_gt hw) hh
    rw [coefficient,Set.indicator_of_mem hlow,AsymptoticFoldedTerminal.coefficient,
      Set.indicator_of_notMem hhigh,zero_mul,zero_mul,add_zero,ratio,fold_im hL b d]
    have he := low_weight_cancel hε t m F z (branch L b d hL.ne' • z) hw.le
    linear_combination phase (branch L b d hL.ne') (2*m) z*he
  · have hhigh : z∈AsymptoticFoldedTerminal.region hL b d s (highStrip ε) n :=
      ⟨hz,⟨hstrip,by
        change ε≤(fold hL b d n • z).im
        simpa only [fold_im hL b d] using le_of_not_gt hw⟩⟩
    have hlow : z∉region hL b d s (lowStrip ε) cap n := by
      intro h
      have hh : (fold hL b d n • z).im<ε := h.1.2.2
      exact hw (by simpa only [fold_im hL b d] using hh)
    rw [coefficient,Set.indicator_of_notMem hlow,zero_mul,zero_mul,zero_add,
      AsymptoticFoldedTerminal.coefficient,Set.indicator_of_mem hhigh,
      weighted_high hε t m F _ (le_of_not_gt hw)]
    ring

/-- Any folded expression containing the strip section has singleton
support in the integer fold variable. -/
theorem fold_series_selected {ε : ℝ} (t m : ℕ) (F : ℂ → ℂ)
    (C : ℤ → ℂ) (z : ℍ) :
    (∑' n : ℤ,C n*stripSection ε t m F (fold hL b d n • z))=
      C (Int.floor (branch L b d hL.ne' • z).re)*
        stripSection ε t m F (fold hL b d (Int.floor (branch L b d hL.ne' • z).re) • z) := by
  classical
  apply tsum_eq_single
  intro n hn
  rw [stripSection,Set.indicator_of_notMem ((fold_mem_strip_iff hL b d n z).not.mpr hn),mul_zero]

noncomputable def lowValue (ε cap : ℝ) (s : Set ℍ) (t m : ℕ) (F : ℂ → ℂ)
    (z : ℍ) : ℂ :=
  ∑' n : ℤ,coefficient hL b d s (lowStrip ε) cap t n z*
    phase (fold hL b d n) (2*m) z*stripSection ε t m F (fold hL b d n • z)

noncomputable def terminalValue (ε : ℝ) (s : Set ℍ) (t m : ℕ) (F : ℂ → ℂ)
    (z : ℍ) : ℂ :=
  ∑' n : ℤ,AsymptoticFoldedTerminal.coefficient hL b d s (highStrip ε) ε t n z*
    phase (fold hL b d n) (2*m) z*stripSection ε t m F (fold hL b d n • z)

/-- Exact substitution in the full, all-integer branch sums. -/
theorem values_eq {ε cap : ℝ} (hε : 0<ε) (s : Set ℍ) (t m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (z : ℍ)
    (hcap : z∈s → z.im/(branch L b d hL.ne' • z).im≤cap) :
    lowValue hL b d ε cap s t m F z+terminalValue hL b d ε s t m F z=
      s.indicator (fun w : ℍ => ((w.im/ε)^t:ℝ)*
        phase (branch L b d hL.ne') (2*m) w*
          ((branch L b d hL.ne' • w).im:ℂ)^m*F (branch L b d hL.ne' • w:ℍ)) z := by
  classical
  rw [lowValue,terminalValue,fold_series_selected hL b d,fold_series_selected hL b d]
  by_cases hz : z∈s
  · rw [Set.indicator_of_mem hz]
    exact coefficient_weighted hL b d hε s t m F hp z hz (hcap hz) _ rfl
  · have hlo (n : ℤ) : z∉region hL b d s (lowStrip ε) cap n := fun h => hz h.1.1
    have hhi (n : ℤ) : z∉AsymptoticFoldedTerminal.region hL b d s (highStrip ε) n := fun h => hz h.1
    rw [Set.indicator_of_notMem hz,coefficient,Set.indicator_of_notMem (hlo _),
      AsymptoticFoldedTerminal.coefficient,Set.indicator_of_notMem (hhi _)]
    ring

#print axioms low_weight_cancel
#print axioms section_fold
#print axioms coefficient_weighted
#print axioms fold_series_selected
#print axioms values_eq

end AsymptoticWeightedBranches
