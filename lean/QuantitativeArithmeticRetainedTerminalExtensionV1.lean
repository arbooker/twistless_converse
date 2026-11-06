module

public import QuantitativeArithmeticRetainedAnalyticReconstructionV1
public import AsymptoticFoldedSupportV1
public import AsymptoticNeumannReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedTerminalExtension

open UpperHalfPlane MeasureTheory Set Filter ContinuousLinearMap SpanningIntegerRows
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators
open QuantitativeArithmeticRetainedAnalyticReconstruction
open AsymptoticHyperbolicSlash AsymptoticWeightedBranches
open AsymptoticCertificateBranches (residues)
open AsymptoticCertificateOperators (lowStrip highStrip lowStrip_measurable highStrip_measurable)

/-- An affine pullback only sees the stated target region, for arbitrary L2 data. -/
theorem affine_zero_of_target (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (k : ℕ) (f : Space)
    (hf : ∀ᵐ z ∂volume,z∈r → f z=0) :
    QuantitativeArithmeticRetainedDilationOperator.folded a b ha hs hr k f=0 := by
  let g (n : ℤ) := AsymptoticMobiusFold.fold
    (QuantitativeArithmeticRetainedDilationOperator.affine a b ha) n
  have hp : ∀ᵐ z ∂volume,∀ n : ℤ,g n • z∈r → f (g n • z)=0 :=
    ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (g n) (volume : Measure ℍ)).quasiMeasurePreserving.ae hf)
  apply Lp.ext
  filter_upwards [QuantitativeArithmeticRetainedDilationOperator.folded_coeFn a b ha hs hr k f,
    hp,Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hz hp hzero
  rw [hz,hzero]
  apply Finset.sum_eq_zero
  intro n _
  classical
  by_cases hn : z∈QuantitativeArithmeticRetainedDilationOperator.region a b ha s r n
  · rw [hp n hn.2,mul_zero]
  · rw [QuantitativeArithmeticRetainedDilationOperator.coefficient,Set.indicator_of_notMem hn,zero_mul]

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
variable (hS : ∀ p∈S,p.Prime)

/-- Each mixed terminal row depends only on data in the terminal strip. -/
theorem rowTerminal_zero_of_target (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (j : Fin Q) {t : ℕ} (ht : 2≤t) (m : ℕ) (i : AugIndex N (S:Set ℕ) Q)
    (f : Space) (hf : ∀ᵐ z ∂volume,z∈highStrip P.ε → f z=0) :
    rowTerminal A hS hN P χ β j ht m i f=0 := by
  cases i with
  | inl i =>
    have hd (d : residues i.val.1) := AsymptoticFoldedTerminal.operator_eq_zero_of_target
      (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2) ((d.val:ℝ)/i.val.1)
      (cell_measurable P.ε j) (highStrip_measurable P.ε) P.epsilon_pos
      (residue_nonneg _ d) (residue_lt_one _ d).le
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m f hf
    simp only [rowTerminal,primitiveTerminal,_root_.smul_apply,_root_.sum_apply,hd,
      Finset.sum_const_zero,smul_zero]
  | inr i =>
    have hz := affine_zero_of_target (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2)
      (retained_pos hS i.1) (cell_measurable P.ε j) (highStrip_measurable P.ε) (2*m) f hf
    simp only [rowTerminal,QuantitativeArithmeticRetainedDilationOperator.terminal,
      _root_.smul_apply,ContinuousLinearMap.comp_apply,hz,map_zero,smul_zero]

/-- Exact terminal dependence of the entire mixed operator, on all of L2. -/
theorem terminal_high (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (u : Space) :
    terminal A hS hN P χ β ht m u=
      terminal A hS hN P χ β ht m (highProjection A P u) := by
  have hf : ∀ᵐ z ∂volume,z∈highStrip P.ε → (u-highProjection A P u:Space) z=0 := by
    filter_upwards [Lp.coeFn_sub u (highProjection A P u),
      AsymptoticRegionL2.projection_coeFn volume (highStrip P.ε) (highStrip_measurable P.ε) u]
      with z hsub hproj hz
    rw [hsub]
    change u z-highProjection A P u z=0
    have hh : highProjection A P u z=u z := hproj.trans (Set.indicator_of_mem hz _)
    rw [hh,sub_self]
  have he : terminal A hS hN P χ β ht m (u-highProjection A P u)=0 := by
    simp only [terminal,_root_.sum_apply,_root_.smul_apply,
      rowTerminal_zero_of_target A hS hN P χ β _ ht m _ _ hf,smul_zero,Finset.sum_const_zero]
  exact sub_eq_zero.mp (by simpa only [map_sub] using he)

/-- The terminal Hilbert space is the genuine measurable strip restriction. -/
abbrev TerminalSpace (P : Parameters A) :=
  AsymptoticRegionL2.Space volume (highStrip P.ε) (highStrip_measurable P.ε)

/-- Bounded Neumann extension from terminal data, using exactly the mixed rows. -/
def extension (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) : TerminalSpace A P →L[ℂ] Space :=
  AsymptoticReconstruction.low (low A hS hN P χ β t m)
    (((ContinuousLinearMap.id ℂ Space)+terminal A hS hN P χ β ht m).comp
      (TerminalSpace A P).subtypeL)

theorem extension_norm_le (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (hβ : ∀ p∈S,‖β p‖≤1)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (hK : ‖low A hS hN P χ β t m‖<1/2) :
    ‖extension A hS hN P χ β ht m‖≤2*(1+terminalConstant A P) := by
  have hK1 : ‖low A hS hN P χ β t m‖<1 := lt_trans hK (by norm_num)
  have hR := terminal_norm_le A hS hN P χ β hχ hβ ht m
  have hC : 0≤terminalConstant A P := (norm_nonneg _).trans hR
  have hinc : ‖(TerminalSpace A P).subtypeL‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    simp
  have hB : ‖(((ContinuousLinearMap.id ℂ Space)+terminal A hS hN P χ β ht m).comp
      (TerminalSpace A P).subtypeL)‖≤1+terminalConstant A P := by
    apply (opNorm_comp_le _ _).trans
    have hsum : ‖(ContinuousLinearMap.id ℂ Space)+terminal A hS hN P χ β ht m‖≤
        1+terminalConstant A P :=
      (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hR)
    simpa only [mul_one] using mul_le_mul hsum hinc (norm_nonneg (TerminalSpace A P).subtypeL) (by positivity)
  apply (AsymptoticReconstruction.low_norm_le _ _ hK1).trans
  apply (div_le_iff₀ (by linarith : 0<1-‖low A hS hN P χ β t m‖)).mpr
  nlinarith

/-- The extension reproduces every actual L2 section satisfying the original
Ramanujan Fricke and complete-row equations. -/
theorem extension_of_FE (hN : 0<N) (P : Parameters A) (hdiv : ∀ p∈S,p∣Q)
    (χ β : ℕ → ℂ) {t : ℕ} (ht : 2≤t) (m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      FinitenessAnalyticReconstruction.twist F q z=
        χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
          FinitenessAnalyticReconstruction.twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (hcomplete : ∀ p∈S,∀ w : ℂ,0<w.im →
      QuantitativeArithmeticRetainedReconstruction.completeTwist F p w=
        (β p*(p:ℂ)^m)*F ((p:ℂ)*w))
    (u : Space) (hu : u =ᵐ[volume] stripSection P.ε t m F)
    (hK : ‖low A hS hN P χ β t m‖<1) :
    extension A hS hN P χ β ht m
      (AsymptoticRegionL2.restrict volume (highStrip P.ε) (highStrip_measurable P.ε) u)=u := by
  apply (AsymptoticReconstruction.low_unique _ _ hK ?_).symm
  have he := equation_of_FE A hS hN P hdiv χ β ht m F hp hFE hcomplete u hu
  rw [terminal_high A hS hN P χ β ht m u] at he
  change u=low A hS hN P χ β t m u+
    (highProjection A P u+terminal A hS hN P χ β ht m (highProjection A P u))
  calc
    u=_ := he
    _ = _ := by abel

#print axioms affine_zero_of_target
#print axioms rowTerminal_zero_of_target
#print axioms terminal_high
#print axioms extension_norm_le
#print axioms extension_of_FE

end QuantitativeArithmeticRetainedTerminalExtension
