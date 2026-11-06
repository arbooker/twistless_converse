module

public import AsymptoticFiniteBranchFoldsV1
public import AsymptoticFiniteBranchSumsV1
public import AsymptoticFiniteCertificateV1
public import AsymptoticRegularFiniteCertificateV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches
open AsymptoticCertificateOperators AsymptoticRegularCertificate

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def lowPartExpression (hN : 0<N) (P : Parameters A) (t : ℕ) (v : Index A)
    (I : Finset ℤ) : Expression :=
  ofFinset I (fun n => lowFold (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) t n)

theorem holomorphicSum_lowPartExpression (hN : 0<N) (P : Parameters A) (t m : ℕ)
    (v : Index A) (I : Finset ℤ) :
    holomorphicSum (lowPartExpression A hN P t v I) m=
      AsymptoticCertificateOperators.finiteLowPart A hN P t m v I := by
  rw [lowPartExpression,holomorphicSum_ofFinset,AsymptoticCertificateOperators.finiteLowPart]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [levelQ_cast,inputShiftQ_cast,outputShiftQ_cast] using
    holomorphic_lowFold (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
      (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
      (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) t m n

theorem regularSum_lowPartExpression (hN : 0<N) (P : Parameters A) (t : ℕ)
    (v : Index A) (I : Finset ℤ) (z : ℍ) :
    regularSum (lowPartExpression A hN P t v I) z=
      AsymptoticRegularCertificate.finiteLowPart A hN P t z v I := by
  rw [lowPartExpression,regularSum_ofFinset,AsymptoticRegularCertificate.finiteLowPart]
  apply Finset.sum_congr rfl
  intro n _
  exact regular_lowFold (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) t n z

noncomputable def terminalPartExpression (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (v : Index A) (I : Finset ℤ) : Expression :=
  ofFinset I (fun n => terminalFold (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht n)

theorem holomorphicSum_terminalPartExpression (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (m : ℕ) (v : Index A) (I : Finset ℤ) :
    holomorphicSum (terminalPartExpression A hN P ht v I) m=
      AsymptoticCertificateOperators.finiteTerminalPart A hN P ht m v I := by
  rw [terminalPartExpression,holomorphicSum_ofFinset,AsymptoticCertificateOperators.finiteTerminalPart]
  apply Finset.sum_congr rfl
  intro n _
  simpa only [levelQ_cast,inputShiftQ_cast,outputShiftQ_cast] using
    holomorphic_terminalFold (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
      (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
      (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
      (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht m n

theorem regularSum_terminalPartExpression (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (v : Index A) (I : Finset ℤ) (z : ℍ) :
    regularSum (terminalPartExpression A hN P ht v I) z=
      AsymptoticRegularCertificate.finiteTerminalPart A hN P ht z v I := by
  rw [terminalPartExpression,regularSum_ofFinset,AsymptoticRegularCertificate.finiteTerminalPart]
  apply Finset.sum_congr rfl
  intro n _
  exact regular_terminalFold (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht n z

noncomputable def lowExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (t : ℕ)
    (I : Finset ℤ) : Expression :=
  sumExpressions Finset.univ (fun v : Index A =>
    scaleExpression (amplitude A χ v) (lowPartExpression A hN P t v I))

noncomputable def terminalExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t)
    (I : Finset ℤ) : Expression :=
  sumExpressions Finset.univ (fun v : Index A =>
    scaleExpression (amplitude A χ v) (terminalPartExpression A hN P ht v I))

theorem holomorphicSum_lowExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (t : ℕ)
    (I : Finset ℤ) (m : ℕ) :
    holomorphicSum (lowExpression A hN P χ t I) m=
      AsymptoticCertificateOperators.finiteLow A hN P χ t I m := by
  rw [lowExpression,holomorphicSum_sumExpressions,AsymptoticCertificateOperators.finiteLow]
  apply Finset.sum_congr rfl
  intro v _
  rw [holomorphicSum_scale,holomorphicSum_lowPartExpression]

theorem regularSum_lowExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (t : ℕ)
    (I : Finset ℤ) (z : ℍ) :
    regularSum (lowExpression A hN P χ t I) z=
      AsymptoticRegularCertificate.finiteLow A hN P χ t I z := by
  rw [lowExpression,regularSum_sumExpressions,AsymptoticRegularCertificate.finiteLow]
  apply Finset.sum_congr rfl
  intro v _
  exact (regularSum_scale _ _ z).trans (congrArg (fun T => amplitude A χ v • T)
    (regularSum_lowPartExpression A hN P t v I z))

theorem holomorphicSum_terminalExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t)
    (I : Finset ℤ) (m : ℕ) :
    holomorphicSum (terminalExpression A hN P χ ht I) m=
      AsymptoticCertificateOperators.finiteTerminal A hN P χ ht I m := by
  rw [terminalExpression,holomorphicSum_sumExpressions,AsymptoticCertificateOperators.finiteTerminal]
  apply Finset.sum_congr rfl
  intro v _
  rw [holomorphicSum_scale,holomorphicSum_terminalPartExpression]

theorem regularSum_terminalExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t)
    (I : Finset ℤ) (z : ℍ) :
    regularSum (terminalExpression A hN P χ ht I) z=
      AsymptoticRegularCertificate.finiteTerminal A hN P χ ht I z := by
  rw [terminalExpression,regularSum_sumExpressions,AsymptoticRegularCertificate.finiteTerminal]
  apply Finset.sum_congr rfl
  intro v _
  exact (regularSum_scale _ _ z).trans (congrArg (fun T => amplitude A χ v • T)
    (regularSum_terminalPartExpression A hN P ht v I z))

#print axioms holomorphicSum_lowPartExpression
#print axioms regularSum_lowPartExpression
#print axioms holomorphicSum_terminalPartExpression
#print axioms regularSum_terminalPartExpression
#print axioms holomorphicSum_lowExpression
#print axioms regularSum_lowExpression
#print axioms holomorphicSum_terminalExpression
#print axioms regularSum_terminalExpression

end AsymptoticFiniteBranch
