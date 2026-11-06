module

public import QuantitativeArithmeticRetainedTerminalExtensionV1
public import QuantitativeArithmeticRetainedRegularOperatorsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedExtensionSupport

open UpperHalfPlane MeasureTheory Set Filter ContinuousLinearMap SpanningIntegerRows
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators
open QuantitativeArithmeticRetainedAnalyticReconstruction
open QuantitativeArithmeticRetainedTerminalExtension
open AsymptoticHyperbolicSlash
open AsymptoticCertificateBranches (residues)
open AsymptoticCertificateOperators (highStrip highStrip_measurable)

/-- Source support of the finite affine pullback, for arbitrary input. -/
theorem affine_zero_off_source (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (k : ℕ) (f : Space) :
    ∀ᵐ z ∂volume,z∉s → QuantitativeArithmeticRetainedDilationOperator.folded a b ha hs hr k f z=0 := by
  filter_upwards [QuantitativeArithmeticRetainedDilationOperator.folded_coeFn a b ha hs hr k f]
    with z hz hzs
  rw [hz]
  apply Finset.sum_eq_zero
  intro n _
  have hn : z∉QuantitativeArithmeticRetainedDilationOperator.region a b ha s r n := fun h => hzs h.1
  rw [QuantitativeArithmeticRetainedDilationOperator.coefficient,Set.indicator_of_notMem hn,zero_mul]

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
variable (hS : ∀ p∈S,p.Prime)

theorem high_affine_zero (P : Parameters A) (j : Fin Q) (a b : ℝ) (ha : 0<a)
    {r : Set ℍ} (hr : MeasurableSet r) (k : ℕ) (f : Space) :
    highProjection A P
      (QuantitativeArithmeticRetainedDilationOperator.folded a b ha (cell_measurable P.ε j) hr k f)=0 := by
  apply (AsymptoticRegionL2.projection_eq_zero_iff _ _ _ _).mpr
  filter_upwards [affine_zero_off_source a b ha (cell_measurable P.ε j) hr k f]
    with z hz hhigh
  apply hz
  intro hcell
  exact (not_lt_of_ge (show P.ε≤z.im from hhigh.2)) (show z.im<P.ε from hcell.2)

theorem high_affine_terminal_zero (P : Parameters A) (j : Fin Q) (a b : ℝ) (ha : 0<a)
    {r : Set ℍ} (hr : MeasurableSet r) (β : ℂ) (t k : ℕ) (f : Space) :
    highProjection A P (QuantitativeArithmeticRetainedDilationOperator.terminal
      a b ha (cell_measurable P.ε j) hr P.ε P.epsilon_pos β t k f)=0 := by
  apply (AsymptoticRegionL2.projection_eq_zero_iff _ _ _ _).mpr
  filter_upwards [QuantitativeArithmeticRetainedDilationOperator.terminal_coeFn
    a b ha (cell_measurable P.ε j) hr P.ε P.epsilon_pos β t k f] with z hz hhigh
  rw [hz]
  have hzcell : z∉cell P.ε j := fun hc =>
    (not_lt_of_ge (show P.ε≤z.im from hhigh.2)) (show z.im<P.ε from hc.2)
  have he : (∑ n∈QuantitativeArithmeticRetainedDilationOperator.folds a b,
      QuantitativeArithmeticRetainedDilationOperator.coefficient a b ha (cell P.ε j) r n z *
        f (AsymptoticMobiusFold.fold (QuantitativeArithmeticRetainedDilationOperator.affine a b ha) n • z))=0 := by
    apply Finset.sum_eq_zero
    intro n _
    have hn : z∉QuantitativeArithmeticRetainedDilationOperator.region a b ha (cell P.ε j) r n :=
      fun hh => hzcell hh.1
    rw [QuantitativeArithmeticRetainedDilationOperator.coefficient,Set.indicator_of_notMem hn,zero_mul]
  rw [he,mul_zero]

theorem high_rowLow_zero (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (j : Fin Q) {t : ℕ} (ht : 1≤t) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q) (f : Space) :
    highProjection A P (rowLow A hS hN P χ β j t m i f)=0 := by
  cases i with
  | inl i =>
    have hd (d : residues i.val.1) : highProjection A P
        (AsymptoticFoldedLow.operator (row_level_pos (hQ:=hQ) hN i)
          (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
          (AsymptoticCertificateOperators.lowStrip_measurable P.ε) P.rho_pos.le
          (residue_nonneg _ d) (residue_lt_one _ d).le (fun _ hz => hz.1) t m f)=0 := by
      apply (AsymptoticRegionL2.projection_eq_zero_iff _ _ _ _).mpr
      filter_upwards [AsymptoticFoldedLow.operator_zero_off_source (row_level_pos (hQ:=hQ) hN i)
        (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
        (AsymptoticCertificateOperators.lowStrip_measurable P.ε) P.rho_pos.le
        (residue_nonneg _ d) (residue_lt_one _ d).le (fun _ hz => hz.1) ht m f]
        with z hz hhigh
      apply hz
      intro hc
      exact (not_lt_of_ge (show P.ε≤z.im from hhigh.2)) (show z.im<P.ε from hc.2)
    simp only [rowLow,primitiveLow,_root_.smul_apply,_root_.sum_apply,map_sum,map_smul,
      hd,Finset.sum_const_zero,smul_zero]
  | inr i =>
    simp only [rowLow,QuantitativeArithmeticRetainedDilationOperator.weighted,_root_.smul_apply,
      map_smul,high_affine_zero A P j,smul_zero]

theorem high_rowTerminal_zero (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q) (f : Space) :
    highProjection A P (rowTerminal A hS hN P χ β j ht m i f)=0 := by
  cases i with
  | inl i =>
    have hd (d : residues i.val.1) : highProjection A P
        (AsymptoticFoldedTerminal.operator (row_level_pos (hQ:=hQ) hN i)
          (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
          (highStrip_measurable P.ε) P.epsilon_pos
          (residue_nonneg _ d) (residue_lt_one _ d).le
          (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
          (fun _ hz => hz.1) ht m f)=0 := by
      apply (AsymptoticRegionL2.projection_eq_zero_iff _ _ _ _).mpr
      filter_upwards [AsymptoticFoldedTerminal.operator_zero_off_source (row_level_pos (hQ:=hQ) hN i)
        (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
        (highStrip_measurable P.ε) P.epsilon_pos (residue_nonneg _ d) (residue_lt_one _ d).le
        (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le)
        (fun _ hz => hz.1) ht m f] with z hz hhigh
      apply hz
      intro hc
      exact (not_lt_of_ge (show P.ε≤z.im from hhigh.2)) (show z.im<P.ε from hc.2)
    simp only [rowTerminal,primitiveTerminal,_root_.smul_apply,_root_.sum_apply,map_sum,map_smul,
      hd,Finset.sum_const_zero,smul_zero]
  | inr i => exact high_affine_terminal_zero A P j _ _ _ _ _ _ _ f

theorem high_low_zero (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (m : ℕ) (f : Space) :
    highProjection A P (low A hS hN P χ β t m f)=0 := by
  simp only [low,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    high_rowLow_zero A hS hN P χ β _ ht,smul_zero,Finset.sum_const_zero]

theorem high_terminal_zero (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (f : Space) :
    highProjection A P (terminal A hS hN P χ β ht m f)=0 := by
  simp only [terminal,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    high_rowTerminal_zero A hS hN P χ β _ ht,smul_zero,Finset.sum_const_zero]

/-- The Neumann extension leaves all terminal data unchanged. -/
theorem extension_terminal (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (hK : ‖low A hS hN P χ β t m‖<1)
    (g : TerminalSpace A P) :
    highProjection A P (extension A hS hN P χ β ht m g)=(g:Space) := by
  have he := AsymptoticReconstruction.low_equation (low A hS hN P χ β t m)
    (((ContinuousLinearMap.id ℂ Space)+terminal A hS hN P χ β ht m).comp
      (TerminalSpace A P).subtypeL) hK g
  change extension A hS hN P χ β ht m g=
    low A hS hN P χ β t m (extension A hS hN P χ β ht m g)+
      ((g:Space)+terminal A hS hN P χ β ht m (g:Space)) at he
  rw [he,map_add,high_low_zero A hS hN P χ β (by omega : 1≤t),zero_add,
    map_add,high_terminal_zero,add_zero]
  exact (AsymptoticRegionL2.mem_space _ _ _ _).mp g.property

/-- In particular the extension is bounded below, uniformly in weight. -/
theorem extension_norm_ge (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (hK : ‖low A hS hN P χ β t m‖<1)
    (g : TerminalSpace A P) : ‖g‖≤‖extension A hS hN P χ β ht m g‖ := by
  calc
    ‖g‖=‖highProjection A P (extension A hS hN P χ β ht m g)‖ := by
      rw [extension_terminal A hS hN P χ β ht m hK g]
      rfl
    _ ≤ ‖highProjection A P‖*‖extension A hS hN P χ β ht m g‖ := (highProjection A P).le_opNorm _
    _ ≤ ‖extension A hS hN P χ β ht m g‖ := by
      simpa only [highProjection,one_mul] using mul_le_mul_of_nonneg_right
        (AsymptoticRegionL2.projection_norm_le volume (highStrip P.ε) (highStrip_measurable P.ε))
        (norm_nonneg (extension A hS hN P χ β ht m g))

/-- A common exponent gives a bounded, bounded-below terminal extension
and simultaneous contraction in the regular representation. -/
theorem uniform_extension (hN : 0<N) (P : Parameters A) :
    ∃ s : ℕ,P.s≤s ∧ ∀ χ β : ℕ → ℂ,
      (∀ q,q∣Q → ‖χ q‖=1) → (∀ p∈S,‖β p‖≤1) →
        (∀ z,‖QuantitativeArithmeticRetainedRegularOperators.low A hS hN P χ β (s+3) z‖<1/2) ∧
        ∀ m,‖extension A hS hN P χ β (by omega : 2≤s+3) m‖≤2*(1+terminalConstant A P) ∧
          ∀ g : TerminalSpace A P,
            highProjection A P (extension A hS hN P χ β (by omega : 2≤s+3) m g)=(g:Space) ∧
            ‖g‖≤‖extension A hS hN P χ β (by omega : 2≤s+3) m g‖ := by
  obtain ⟨s,hs,hc⟩ := QuantitativeArithmeticRetainedRegularOperators.common_contraction A hS hN P
  refine ⟨s,hs,fun χ β hχ hβ => ⟨(hc χ β hχ hβ).1,fun m => ?_⟩⟩
  have hK := (hc χ β hχ hβ).2 m
  have hK1 : ‖low A hS hN P χ β (s+3) m‖<1 := lt_trans hK (by norm_num)
  exact ⟨extension_norm_le A hS hN P χ β hχ hβ (by omega) m hK,
    fun g => ⟨extension_terminal A hS hN P χ β (by omega) m hK1 g,
      extension_norm_ge A hS hN P χ β (by omega) m hK1 g⟩⟩

#print axioms uniform_extension

#print axioms high_low_zero
#print axioms high_terminal_zero
#print axioms extension_terminal
#print axioms extension_norm_ge

end QuantitativeArithmeticRetainedExtensionSupport
