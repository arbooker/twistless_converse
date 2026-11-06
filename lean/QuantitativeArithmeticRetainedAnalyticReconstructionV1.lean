module

public import QuantitativeArithmeticRetainedCertificateFEV1
public import QuantitativeArithmeticRetainedDilationWeightedV1
public import AsymptoticRegionL2V1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedAnalyticReconstruction

open UpperHalfPlane MeasureTheory Set Filter SpanningIntegerRows
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators QuantitativeArithmeticRetainedCertificateFE
open AsymptoticHyperbolicSlash AsymptoticWeightedBranches
open AsymptoticCertificateBranches (residues)
open AsymptoticCertificateOperators (lowStrip highStrip lowStrip_measurable highStrip_measurable)
open QuantitativeArithmeticRetainedDilationOperator (capWeight)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)

/-- The original Fricke branch operators evaluated on the actual capped section. -/
theorem primitive_coeFn (hN : 0<N) (P : Parameters A) (j : Fin Q)
    (i : RowIndex N Q) (hi : Sum.inl i∈(A.coeff j).support)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (u : Space) (hu : u =ᵐ[volume] stripSection P.ε t m F) :
    (primitiveLow A hN P j i t m u+primitiveTerminal A hN P j i ht m u:Space) =ᵐ[volume]
      (cell P.ε j).indicator (fun z : ℍ => capWeight P.ε t z *
        ∑ d : residues i.val.1,phase (primitiveMatrix (hQ:=hQ) hN j i d) (2*m) z *
          ((primitiveMatrix (hQ:=hQ) hN j i d • z).im:ℂ)^m *
          F (primitiveMatrix (hQ:=hQ) hN j i d • z:ℍ)) := by
  classical
  let l (d : residues i.val.1) := AsymptoticFoldedLow.operator
    (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2) ((d.val:ℝ)/i.val.1)
    (cell_measurable P.ε j) (lowStrip_measurable P.ε) P.rho_pos.le
    (residue_nonneg _ d) (residue_lt_one _ d).le (fun _ hz => hz.1) t m
  let r (d : residues i.val.1) := AsymptoticFoldedTerminal.operator
    (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2) ((d.val:ℝ)/i.val.1)
    (cell_measurable P.ε j) (highStrip_measurable P.ε) P.epsilon_pos
    (residue_nonneg _ d) (residue_lt_one _ d).le
    (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m
  have hd (d : residues i.val.1) : (l d u+r d u:Space) =ᵐ[volume]
      (cell P.ε j).indicator (fun z : ℍ => capWeight P.ε t z *
        phase (primitiveMatrix (hQ:=hQ) hN j i d) (2*m) z *
          ((primitiveMatrix (hQ:=hQ) hN j i d • z).im:ℂ)^m *
          F (primitiveMatrix (hQ:=hQ) hN j i d • z:ℍ)) := by
    let g := AsymptoticFoldedLow.fold (row_level_pos (hQ:=hQ) hN i)
      (shift j i.val.2) ((d.val:ℝ)/i.val.1)
    have hf : ∀ᵐ z ∂volume,∀ n : ℤ,u (g n • z)=stripSection P.ε t m F (g n • z) :=
      ae_all_iff.mpr (fun n =>
        (measurePreserving_smul (g n) (volume : Measure ℍ)).quasiMeasurePreserving.ae hu)
    have hl := AsymptoticFoldedLow.operator_coeFn (row_level_pos (hQ:=hQ) hN i)
      (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
      (lowStrip_measurable P.ε) P.rho_pos.le (residue_nonneg _ d) (residue_lt_one _ d).le
      (fun _ hz => hz.1) (by omega : 1≤t) m u
    have hr := AsymptoticFoldedTerminal.operator_coeFn (row_level_pos (hQ:=hQ) hN i)
      (shift j i.val.2) ((d.val:ℝ)/i.val.1) (cell_measurable P.ε j)
      (highStrip_measurable P.ε) P.epsilon_pos (residue_nonneg _ d) (residue_lt_one _ d).le
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m u
    filter_upwards [Lp.coeFn_add (l d u) (r d u),hl,hr,hf] with z ha hl hr hf
    rw [ha]
    change l d u z+r d u z=_
    have hlv : l d u z=lowValue (row_level_pos (hQ:=hQ) hN i)
        (shift j i.val.2) ((d.val:ℝ)/i.val.1) P.ε P.ρ (cell P.ε j) t m F z := by
      apply hl.trans
      apply tsum_congr
      intro n
      rw [hf n]
    have hrv : r d u z=terminalValue (row_level_pos (hQ:=hQ) hN i)
        (shift j i.val.2) ((d.val:ℝ)/i.val.1) P.ε (cell P.ε j) t m F z := by
      apply hr.trans
      apply tsum_congr
      intro n
      rw [hf n]
    rw [hlv,hrv,AsymptoticWeightedBranches.values_eq
      (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2) ((d.val:ℝ)/i.val.1)
      P.epsilon_pos (cell P.ε j) t m F hp z
      (primitive_ascending A hN P j i hi d z)]
    by_cases hz : z∈cell P.ε j
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz]
      rw [capWeight,min_eq_left ((div_le_one P.epsilon_pos).mpr hz.2.le)]
      rfl
    · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]
  have he : primitiveLow A hN P j i t m u+primitiveTerminal A hN P j i ht m u=
      ∑ d : residues i.val.1,(l d u+r d u) := by
    simp only [primitiveLow,primitiveTerminal,_root_.sum_apply,Finset.sum_add_distrib,l,r]
  rw [he]
  apply (Lp.coeFn_finsetSum _ _).trans
  have hv : (cell P.ε j).indicator (fun z : ℍ => capWeight P.ε t z *
      ∑ d : residues i.val.1,phase (primitiveMatrix (hQ:=hQ) hN j i d) (2*m) z *
        ((primitiveMatrix (hQ:=hQ) hN j i d • z).im:ℂ)^m *
        F (primitiveMatrix (hQ:=hQ) hN j i d • z:ℍ))=
      ∑ d : residues i.val.1,(cell P.ε j).indicator (fun z : ℍ => capWeight P.ε t z *
        phase (primitiveMatrix (hQ:=hQ) hN j i d) (2*m) z *
          ((primitiveMatrix (hQ:=hQ) hN j i d • z).im:ℂ)^m *
          F (primitiveMatrix (hQ:=hQ) hN j i d • z:ℍ)) := by
    funext z
    by_cases hz : z∈cell P.ε j
    · simp only [Finset.sum_apply,Set.indicator_of_mem hz,Finset.mul_sum,mul_assoc]
    · simp only [Finset.sum_apply,Set.indicator_of_notMem hz,Finset.sum_const_zero]
  rw [hv]
  exact eventuallyEq_sum (fun d _ => hd d)

variable (hS : ∀ p∈S,p.Prime)

/-- Both kinds of rows act on the same capped periodic section. -/
theorem row_coeFn (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ) (j : Fin Q)
    (i : AugIndex N (S:Set ℕ) Q) (hi : i∈(A.coeff j).support)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (u : Space) (hu : u =ᵐ[volume] stripSection P.ε t m F) :
    (rowLow A hS hN P χ β j t m i u+rowTerminal A hS hN P χ β j ht m i u:Space) =ᵐ[volume]
      (cell P.ε j).indicator (fun z : ℍ => capWeight P.ε t z *
        rowValue (hQ:=hQ) hS hN F χ β m j z i) := by
  cases i with
  | inl i =>
    have he : rowLow A hS hN P χ β j t m (Sum.inl i) u+
        rowTerminal A hS hN P χ β j ht m (Sum.inl i) u=
        χ i.val.1 • (primitiveLow A hN P j i t m u+primitiveTerminal A hN P j i ht m u) := by
      simp only [rowLow,rowTerminal,_root_.smul_apply,smul_add]
    rw [he]
    filter_upwards [Lp.coeFn_smul (χ i.val.1)
      (primitiveLow A hN P j i t m u+primitiveTerminal A hN P j i ht m u),
      primitive_coeFn A hN P j i hi ht m F hp u hu] with z hsm hv
    rw [hsm]
    change χ i.val.1*(primitiveLow A hN P j i t m u+primitiveTerminal A hN P j i ht m u) z=_
    rw [hv]
    by_cases hz : z∈cell P.ε j
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz,rowValue]
      ring
    · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz,mul_zero]
  | inr i =>
    have h := QuantitativeArithmeticRetainedDilationWeighted.operators_coeFn_section
      (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2) (retained_pos hS i.1) P.epsilon_pos
      (cell_measurable P.ε j) (cell_subset_low (hQ:=hQ) P.ε j) (β i.1.val) t m F hp u hu
    simpa only [rowLow,rowTerminal,rowValue,retainedMatrix,mul_assoc] using h

/-- The literal mixed L2 sum agrees almost everywhere with its geometric formula. -/
theorem reconstruction_coeFn (hN : 0<N) (P : Parameters A) (χ β : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (u : Space) (hu : u =ᵐ[volume] stripSection P.ε t m F) :
    (low A hS hN P χ β t m u+terminal A hS hN P χ β ht m u:Space) =ᵐ[volume]
      (fun z : ℍ => ∑ j : Fin Q,(cell P.ε j).indicator (fun w : ℍ => capWeight P.ε t w *
        ∑ i∈(A.coeff j).support,(A.coeff j i:ℂ)*rowValue (hQ:=hQ) hS hN F χ β m j w i) z) := by
  classical
  let v (j : Fin Q) (i : AugIndex N (S:Set ℕ) Q) :=
    rowLow A hS hN P χ β j t m i u+rowTerminal A hS hN P χ β j ht m i u
  have he : low A hS hN P χ β t m u+terminal A hS hN P χ β ht m u=
      ∑ j : Fin Q,∑ i∈(A.coeff j).support,(A.coeff j i:ℂ) • v j i := by
    simp only [low,terminal,_root_.sum_apply,_root_.smul_apply,v,smul_add,Finset.sum_add_distrib]
  rw [he]
  apply (Lp.coeFn_finsetSum _ _).trans
  have hs : (fun z : ℍ => ∑ j : Fin Q,(cell P.ε j).indicator (fun w : ℍ => capWeight P.ε t w *
      ∑ i∈(A.coeff j).support,(A.coeff j i:ℂ)*rowValue (hQ:=hQ) hS hN F χ β m j w i) z)=
      ∑ j : Fin Q,(cell P.ε j).indicator (fun w : ℍ => capWeight P.ε t w *
        ∑ i∈(A.coeff j).support,(A.coeff j i:ℂ)*rowValue (hQ:=hQ) hS hN F χ β m j w i) := by
    funext z
    simp only [Finset.sum_apply]
  rw [hs]
  apply eventuallyEq_sum
  intro j _
  apply (Lp.coeFn_finsetSum _ _).trans
  have hv : (cell P.ε j).indicator (fun w : ℍ => capWeight P.ε t w *
      ∑ i∈(A.coeff j).support,(A.coeff j i:ℂ)*rowValue (hQ:=hQ) hS hN F χ β m j w i)=
      ∑ i∈(A.coeff j).support,(fun z : ℍ => (A.coeff j i:ℂ)*
        (cell P.ε j).indicator (fun w : ℍ => capWeight P.ε t w *
          rowValue (hQ:=hQ) hS hN F χ β m j w i) z) := by
    funext z
    by_cases hz : z∈cell P.ε j
    · simp only [Finset.sum_apply,Set.indicator_of_mem hz,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [Finset.sum_apply,Set.indicator_of_notMem hz,mul_zero,Finset.sum_const_zero]
  change _ =ᵐ[volume] (cell P.ε j).indicator _
  rw [hv]
  apply eventuallyEq_sum
  intro i hi
  filter_upwards [Lp.coeFn_smul (A.coeff j i:ℂ) (v j i),
    row_coeFn A hS hN P χ β j i hi ht m F hp u hu] with z hsm hr
  rw [hsm]
  change (A.coeff j i:ℂ)*(v j i z)=_
  rw [show v j i z=_ from hr]

/-- Restriction to the fixed terminal strip in the actual ambient Hilbert space. -/
def highProjection (P : Parameters A) : Space →L[ℂ] Space :=
  AsymptoticRegionL2.projection volume (highStrip P.ε) (highStrip_measurable P.ε)

/-- Direct substitution of the original functional equations into the mixed
Hilbert-space operators; there is no abstract reconstruction hypothesis. -/
theorem equation_of_FE (hN : 0<N) (P : Parameters A) (hdiv : ∀ p∈S,p∣Q)
    (χ β : ℕ → ℂ) {t : ℕ} (ht : 2≤t) (m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      FinitenessAnalyticReconstruction.twist F q z=
        χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
          FinitenessAnalyticReconstruction.twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (hcomplete : ∀ p∈S,∀ w : ℂ,0<w.im →
      QuantitativeArithmeticRetainedReconstruction.completeTwist F p w=
        (β p*(p:ℂ)^m)*F ((p:ℂ)*w))
    (u : Space) (hu : u =ᵐ[volume] stripSection P.ε t m F) :
    u=highProjection A P u+low A hS hN P χ β t m u+terminal A hS hN P χ β ht m u := by
  rw [add_assoc]
  apply Lp.ext
  filter_upwards [hu,reconstruction_coeFn A hS hN P χ β ht m F hp u hu,
    AsymptoticRegionL2.projection_coeFn volume (highStrip P.ε) (highStrip_measurable P.ε) u,
    Lp.coeFn_add (highProjection A P u)
      (low A hS hN P χ β t m u+terminal A hS hN P χ β ht m u)] with z hu hr hh ha
  rw [ha]
  change u z=highProjection A P u z+(low A hS hN P χ β t m u+terminal A hS hN P χ β ht m u:Space) z
  rw [hr,reconstruct_low A hS hN hdiv F hp χ β m t P.ε hFE hcomplete z,hu]
  rw [show highProjection A P u z=_ from hh]
  classical
  by_cases hz : z∈lowStrip P.ε
  · have hh : z∉highStrip P.ε := fun h =>
      (not_lt_of_ge (show P.ε≤z.im from h.2)) (show z.im<P.ε from hz.2)
    rw [Set.indicator_of_notMem hh,Set.indicator_of_mem hz,zero_add,
      stripSection,Set.indicator_of_mem hz.1]
  · rw [Set.indicator_of_notMem hz,add_zero]
    by_cases hs : z∈AsymptoticMassTransport.strip
    · have hh : z∈highStrip P.ε := ⟨hs,show P.ε≤z.im from le_of_not_gt (fun h => hz ⟨hs,h⟩)⟩
      rw [Set.indicator_of_mem hh,hu]
    · have hh : z∉highStrip P.ε := fun h => hs h.1
      rw [Set.indicator_of_notMem hh,stripSection,Set.indicator_of_notMem hs]

#print axioms equation_of_FE
#print axioms primitive_coeFn
#print axioms row_coeFn
#print axioms reconstruction_coeFn

end QuantitativeArithmeticRetainedAnalyticReconstruction
