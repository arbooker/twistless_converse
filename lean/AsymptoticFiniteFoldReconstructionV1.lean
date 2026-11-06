module

public import AsymptoticFiniteNeumannPerturbationV1
public import AsymptoticFiniteCertificateV1
public import AsymptoticRegularFiniteCertificateV1
public import AsymptoticFiniteReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstruction

open ContinuousLinearMap Filter

variable {G E α ι : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Terminal inclusions and projections preserve uniform approximation,
even when the corner depends on the orbit root. -/
theorem uniform_add_comp {l : Filter ι} (F : ι → α → E →L[ℂ] E) (f : α → E →L[ℂ] E)
    (D U : α → G →L[ℂ] E) (hU : ∀ a,‖U a‖≤1) (hf : TendstoUniformly F f l) :
    TendstoUniformly (fun i a => D a+(F i a).comp (U a))
      (fun a => D a+(f a).comp (U a)) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  apply ((Metric.tendstoUniformly_iff.mp hf) ε hε).mono
  intro i hi a
  rw [dist_eq_norm,add_sub_add_left_eq_sub,← sub_comp]
  apply (opNorm_comp_le _ _).trans_lt
  apply (mul_le_mul_of_nonneg_left (hU a) (norm_nonneg _)).trans_lt
  simpa only [mul_one,dist_eq_norm] using hi a

theorem finiteLow_norm_le_of_half (K : E →L[ℂ] E) (B : G →L[ℂ] E) {C : ℝ}
    (hK : ‖K‖≤1/2) (hB : ‖B‖≤C) (n : ℕ) : ‖finiteLow K B n‖≤2*C := by
  apply (finiteLow_norm_le K B hK (by norm_num) n).trans
  calc
    ‖B‖/(1-(1/2:ℝ))=2*‖B‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by norm_num)

#print axioms finiteLow_norm_le_of_half

#print axioms uniform_add_comp

end AsymptoticReconstruction

namespace AsymptoticGeometricReconstruction

open ContinuousLinearMap Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCertificateOperators AsymptoticHyperbolicSlash

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- A genuine finite branch expression: both depth and integer folds are
finite, and every coefficient and cell rule comes from the certificate. -/
noncomputable def finiteFoldExtension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (m : ℕ) : TerminalSpace A P →L[ℂ] Space :=
  (TerminalSpace A P).subtypeL+
    (AsymptoticReconstruction.finiteLow (finiteLow A hN P χ (P.s+3) I m)
      (finiteTerminal A hN P χ (by omega : 2≤P.s+3) I m) n).comp (TerminalSpace A P).subtypeL

theorem finiteFoldExtension_norm_le (hN : 0<N) (P : Parameters A)
    (hP : P.ρ^(P.s+3-1)*lowConstant A P≤1/2) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    ‖finiteFoldExtension A hN P χ n I m‖≤1+2*terminalConstant A P := by
  have ht := AsymptoticReconstruction.finiteLow_norm_le_of_half
    (finiteLow A hN P χ (P.s+3) I m) (finiteTerminal A hN P χ (by omega : 2≤P.s+3) I m)
    ((finiteLow_norm_le A hN P χ hχ (by omega) I m).trans hP)
    (finiteTerminal_norm_le A hN P χ hχ (by omega) I m) n
  have hc : ‖(AsymptoticReconstruction.finiteLow (finiteLow A hN P χ (P.s+3) I m) (finiteTerminal A hN P χ (by omega : 2≤P.s+3) I m) n).comp
      (TerminalSpace A P).subtypeL‖≤2*terminalConstant A P := by
    apply (opNorm_comp_le _ _).trans
    apply (mul_le_mul_of_nonneg_left (terminal_inclusion_norm_le A P) (norm_nonneg _)).trans
    simpa only [mul_one] using ht
  exact (norm_add_le (TerminalSpace A P).subtypeL
    ((AsymptoticReconstruction.finiteLow (finiteLow A hN P χ (P.s+3) I m) (finiteTerminal A hN P χ (by omega : 2≤P.s+3) I m) n).comp
      (TerminalSpace A P).subtypeL)).trans (add_le_add (terminal_inclusion_norm_le A P) hc)

#print axioms finiteFoldExtension_norm_le

theorem finiteFoldExtension_tendstoUniformly (hN : 0<N) (P : Parameters A)
    (hP : P.ρ^(P.s+3-1)*lowConstant A P≤1) {α : Type*}
    (m : α → ℕ) (χ : α → ℕ → ℂ) (hχ : ∀ a q,q∣Q → ‖χ a q‖=1) (n : ℕ) :
    TendstoUniformly (fun I a => finiteFoldExtension A hN P (χ a) n I (m a))
      (fun a => finiteExtension A hN P (χ a) (m a) n) atTop := by
  have hC : 0≤terminalConstant A P := by unfold terminalConstant; positivity
  have hf := AsymptoticReconstruction.finiteLow_tendstoUniformly_of_approximations
    (fun a => low A hN P (χ a) (P.s+3) (m a))
    (fun a => terminal A hN P (χ a) (by omega : 2≤P.s+3) (m a))
    (fun I a => finiteLow A hN P (χ a) (P.s+3) I (m a))
    (fun I a => finiteTerminal A hN P (χ a) (by omega : 2≤P.s+3) I (m a)) hC
    (fun a => (low_norm_le A hN P (χ a) (hχ a) (by omega) (m a)).trans hP)
    (fun I a => (finiteLow_norm_le A hN P (χ a) (hχ a) (by omega) I (m a)).trans hP)
    (fun a => terminal_norm_le A hN P (χ a) (hχ a) (by omega) (m a))
    (finiteLow_tendstoUniformly A hN P m χ hχ (by omega))
    (finiteTerminal_tendstoUniformly A hN P m χ hχ (by omega)) n
  have hg := AsymptoticReconstruction.uniform_add_comp _ _
    (fun _ : α => (TerminalSpace A P).subtypeL)
    (fun _ : α => (TerminalSpace A P).subtypeL)
    (fun _ => terminal_inclusion_norm_le A P) hf
  simpa only [finiteFoldExtension,finiteExtension,AsymptoticReconstruction.finiteLow,comp_assoc] using hg

#print axioms finiteFoldExtension_tendstoUniformly

end AsymptoticGeometricReconstruction

namespace AsymptoticRegularReconstruction

open UpperHalfPlane ContinuousLinearMap Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (lowConstant terminalConstant)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The regular expression uses the same finite fold set and depth as
the holomorphic expression. -/
noncomputable def finiteFoldFull (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  (1+AsymptoticReconstruction.finiteLow (finiteLow A hN P χ (P.s+3) I z)
    (finiteTerminal A hN P χ (by omega : 2≤P.s+3) I z) n).comp (highProjection A P z)

theorem finiteFoldFull_norm_le (hN : 0<N) (P : Parameters A)
    (hP : P.ρ^(P.s+3-1)*lowConstant A P≤1/2) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    ‖finiteFoldFull A hN P χ n I z‖≤1+2*terminalConstant A P := by
  have ht := AsymptoticReconstruction.finiteLow_norm_le_of_half
    (finiteLow A hN P χ (P.s+3) I z) (finiteTerminal A hN P χ (by omega : 2≤P.s+3) I z)
    ((finiteLow_norm_le A hN P χ hχ (by omega) I z).trans hP)
    (finiteTerminal_norm_le A hN P χ hχ (by omega) I z) n
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (highProjection_norm_le A P z) (norm_nonneg _)).trans
  rw [mul_one]
  exact (norm_add_le _ _).trans (add_le_add norm_id_le ht)

#print axioms finiteFoldFull_norm_le

theorem finiteFoldFull_tendstoUniformly (hN : 0<N) (P : Parameters A)
    (hP : P.ρ^(P.s+3-1)*lowConstant A P≤1) {α : Type*}
    (z : α → ℍ) (χ : α → ℕ → ℂ) (hχ : ∀ a q,q∣Q → ‖χ a q‖=1) (n : ℕ) :
    TendstoUniformly (fun I a => finiteFoldFull A hN P (χ a) n I (z a))
      (fun a => finiteFull A hN P (χ a) n (z a)) atTop := by
  have hC : 0≤terminalConstant A P := by unfold terminalConstant; positivity
  have hf := AsymptoticReconstruction.finiteLow_tendstoUniformly_of_approximations
    (fun a => low A hN P (χ a) (P.s+3) (z a))
    (fun a => terminal A hN P (χ a) (by omega : 2≤P.s+3) (z a))
    (fun I a => finiteLow A hN P (χ a) (P.s+3) I (z a))
    (fun I a => finiteTerminal A hN P (χ a) (by omega : 2≤P.s+3) I (z a)) hC
    (fun a => (low_norm_le A hN P (χ a) (hχ a) (by omega) (z a)).trans hP)
    (fun I a => (finiteLow_norm_le A hN P (χ a) (hχ a) (by omega) I (z a)).trans hP)
    (fun a => terminal_norm_le A hN P (χ a) (hχ a) (by omega) (z a))
    (finiteLow_tendstoUniformly A hN P z χ hχ (by omega))
    (finiteTerminal_tendstoUniformly A hN P z χ hχ (by omega)) n
  have hg := AsymptoticReconstruction.uniform_add_comp _ _
    (fun a => highProjection A P (z a)) (fun a => highProjection A P (z a))
    (fun a => highProjection_norm_le A P (z a)) hf
  simpa only [finiteFoldFull,finiteFull,add_comp,ContinuousLinearMap.one_def,id_comp] using hg

#print axioms finiteFoldFull_tendstoUniformly

end AsymptoticRegularReconstruction
