module

public import QuantitativeMaassOrbitReconstructionFormulaV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane ContinuousLinearMap AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches
open AsymptoticCertificateOperators (lowCell lowStrip highStrip)
open AsymptoticRegularCertificate AsymptoticWeightedBranches
open AsymptoticRegularFoldedLow (Space)
namespace QuantitativeMaass.CountingMetric
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (hN : 0<N) (P : Parameters A)

/-- The terminal branch reads only terminal coordinates. -/
theorem regular_terminalPart_high {t : ℕ} (ht : 2≤t) (z : ℍ) (u : Space) (v : Index A) :
    terminalPart A hN P ht v z (highProjection A P z u)=terminalPart A hN P ht v z u := by
  classical
  apply lp.ext
  funext a
  unfold terminalPart AsymptoticRegularFoldedTerminal.operator
  rw [tsum_apply_coordinate _ (Summable.of_norm
    (AsymptoticRegularFoldedTerminal.term_norm_summable _ _ _ _ _ _ _ _ _ _ ht z)),
    tsum_apply_coordinate _ (Summable.of_norm
    (AsymptoticRegularFoldedTerminal.term_norm_summable _ _ _ _ _ _ _ _ _ _ ht z))]
  apply tsum_congr
  intro n
  simp only [AsymptoticRegularFoldedTerminal.term,AsymptoticOrbitBranch.operator_apply,
    highProjection,AsymptoticOrbitDiagonal.corner_apply]
  by_cases hh : (AsymptoticRationalBranches.fold (levelQ_pos A hN v)
      (inputShiftQ A v) (outputShiftQ A v) n*a) • z∈highStrip P.ε
  · simp only [ite_eq_left hh]
  · have hnot : a • z∉AsymptoticFoldedTerminal.region
        (show (0:ℝ)<levelQ A v by exact_mod_cast levelQ_pos A hN v)
        (inputShiftQ A v:ℝ) (outputShiftQ A v:ℝ) (lowCell A P.ε v) (highStrip P.ε) n := by
      intro h
      apply hh
      rw [mul_smul,AsymptoticRationalBranches.fold_action]
      exact h.2
    simp only [AsymptoticFoldedTerminal.coefficient,Set.indicator_of_notMem hnot,zero_mul]

theorem regular_terminal_high (χ : ℕ→ℂ) {t : ℕ} (ht : 2≤t) (z : ℍ) (u : Space) :
    terminal A hN P χ ht z (highProjection A P z u)=terminal A hN P χ ht z u := by
  simp only [terminal,_root_.sum_apply,_root_.smul_apply,regular_terminalPart_high A hN P ht z u]

/-- The pointwise analytic laws imply the actual regular reconstruction
identity, including the terminal restriction. -/
theorem regular_equation_of_FE (χ : ℕ→ℂ) {t : ℕ} (ht : 2≤t) (z : ℍ) (F : ℂ→ℂ)
    (hp : ∀ w,F (w+1)=F w)
    (hFE : ∀ q : ℕ,q∣Q → ∀ w : ℂ,0<w.im →
      FinitenessAnalyticReconstruction.twist F q w=
        χ q*FinitenessAnalyticReconstruction.twist F q (-1/((Nat.lcm N (q^2):ℂ)*w)))
    (u : Space) (hu : ∀ a,u a=stripSection P.ε t 0 F (a • z)) :
    u=highProjection A P z u+low A hN P χ t z u+
      terminal A hN P χ ht z (highProjection A P z u) := by
  classical
  rw [regular_terminal_high A hN P,add_assoc]
  apply lp.ext
  funext a
  change u a=highProjection A P z u a+(low A hN P χ t z u+terminal A hN P χ ht z u) a
  rw [regular_reconstruction_section A hN P χ ht z F u hu,hu]
  have he := AsymptoticWeightedFE.reconstruct A hN P χ t 0 F hp
    (by simpa only [Nat.mul_zero,pow_zero,div_one] using hFE) (a • z)
  rw [he]
  congr 1
  rw [highProjection,AsymptoticOrbitDiagonal.corner_apply]
  by_cases ha : a • z∈highStrip P.ε
  · rw [Set.indicator_of_mem ha,ite_eq_left ha,hu]
  · rw [Set.indicator_of_notMem ha,ite_eq_right ha]

theorem regular_extension_of_FE (χ : ℕ→ℂ) (z : ℍ) (F : ℂ→ℂ)
    (hp : ∀ w,F (w+1)=F w)
    (hFE : ∀ q : ℕ,q∣Q → ∀ w : ℂ,0<w.im →
      FinitenessAnalyticReconstruction.twist F q w=
        χ q*FinitenessAnalyticReconstruction.twist F q (-1/((Nat.lcm N (q^2):ℂ)*w)))
    (u : Space) (hu : ∀ a,u a=stripSection P.ε (P.s+3) 0 F (a • z))
    (hK : ‖low A hN P χ (P.s+3) z‖<1) :
    AsymptoticRegularReconstruction.extension A hN P χ z
      (AsymptoticOrbitRegion.restrict (highStrip P.ε) z u)=u :=
  AsymptoticRegularReconstruction.extension_unique A hN P χ z hK u
    (regular_equation_of_FE A hN P χ (by omega) z F hp hFE u hu)

#print axioms regular_terminalPart_high
#print axioms regular_terminal_high
#print axioms regular_equation_of_FE
#print axioms regular_extension_of_FE
end QuantitativeMaass.CountingMetric
