module

public import QuantitativeArithmeticRetainedCertificateOperatorsV1
public import AsymptoticWeightedBranchesV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedCertificateFE

open UpperHalfPlane Matrix Set SpanningIntegerRows
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedCertificateOperators
open QuantitativeArithmeticRetainedReconstruction FinitenessAnalyticReconstruction
open AsymptoticReconstructionBranch AsymptoticHyperbolicSlash
open AsymptoticCertificateBranches (residues)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
variable (hS : ∀ p∈S,p.Prime)

def primitiveMatrix (hN : 0<N) (j : Fin Q) (i : RowIndex N Q) (d : residues i.val.1) :
    GL (Fin 2) ℝ :=
  branch (Nat.lcm N (i.val.1^2):ℝ) (shift j i.val.2) ((d.val:ℝ)/i.val.1)
    (row_level_pos (hQ:=hQ) hN i).ne'

def retainedMatrix (j : Fin Q) (p : S) (u : ℤ) : GL (Fin 2) ℝ :=
  QuantitativeArithmeticRetainedDilationOperator.affine
    (p.val:ℝ) ((p.val:ℝ)*shift j u) (retained_pos hS p)

theorem shift_cast (j : Fin Q) (u : ℤ) :
    ((shift j u:ℝ):ℂ)=((u:ℂ)-(j:ℕ))/Q := by simp [shift]

theorem primitive_action (hN : 0<N) (j : Fin Q) (i : RowIndex N Q)
    (d : residues i.val.1) (z : ℍ) :
    ((primitiveMatrix (hQ:=hQ) hN j i d • z:ℍ):ℂ)=
      -1/((Nat.lcm N (i.val.1^2):ℕ)*((z:ℂ)+((i.val.2:ℂ)-(j:ℕ))/Q))+
        (d.val:ℂ)/i.val.1 := by
  rw [primitiveMatrix,branch_action (row_level_pos (hQ:=hQ) hN i),shift_cast]
  push_cast
  rfl

theorem retained_action (j : Fin Q) (p : S) (u : ℤ) (z : ℍ) :
    ((retainedMatrix hS j p u • z:ℍ):ℂ)=
      (p.val:ℂ)*((z:ℂ)+((u:ℂ)-(j:ℕ))/Q) := by
  rw [retainedMatrix,QuantitativeArithmeticRetainedDilationOperator.affine_action]
  push_cast
  rw [shift_cast]
  ring

/-- Normalized values for exactly the branches in the mixed L2 operator. -/
def rowValue (hN : 0<N) (F : ℂ → ℂ) (χ β : ℕ → ℂ) (m : ℕ) (j : Fin Q) (z : ℍ) :
    AugIndex N (S:Set ℕ) Q → ℂ
  | Sum.inl i => χ i.val.1 * ∑ d : residues i.val.1,
      phase (primitiveMatrix (hQ:=hQ) hN j i d) (2*m) z *
        ((primitiveMatrix (hQ:=hQ) hN j i d • z).im:ℂ)^m *
        F (primitiveMatrix (hQ:=hQ) hN j i d • z:ℍ)
  | Sum.inr i => β i.1.val * ((retainedMatrix hS j i.1 i.2 • z).im:ℂ)^m *
      F (retainedMatrix hS j i.1 i.2 • z:ℍ)

theorem normalized_row (hN : 0<N) (F : ℂ → ℂ) (χ β : ℕ → ℂ) (m : ℕ)
    (j : Fin Q) (z : ℍ) (i : AugIndex N (S:Set ℕ) Q) :
    (z.im:ℂ)^m * dilationRow F (2*m) χ (fun p => β p*(p:ℂ)^m) j z i=
      rowValue (hQ:=hQ) hS hN F χ β m j z i := by
  cases i with
  | inl i =>
    simp only [dilationRow,frickeRow,rowValue]
    rw [twist,Finset.mul_sum,Finset.mul_sum,← Finset.sum_attach,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    have hn := AsymptoticReconstructionBranch.normalized_branch
      (row_level_pos (hQ:=hQ) hN i) (shift j i.val.2) ((d.val:ℝ)/i.val.1)
      m (fun w : ℍ => F w) z
    change phase (primitiveMatrix (hQ:=hQ) hN j i d) (2*m) z *
      ((primitiveMatrix (hQ:=hQ) hN j i d • z).im:ℂ)^m *
        F (primitiveMatrix (hQ:=hQ) hN j i d • z:ℍ)=_ at hn
    rw [shift_cast] at hn
    rw [← primitive_action (hQ:=hQ) hN j i d z]
    dsimp only [primitiveMatrix] at hn ⊢
    linear_combination -(χ i.val.1)*hn
  | inr i =>
    simp only [dilationRow,rowValue]
    rw [retained_action hS]
    change (z.im:ℂ)^m*(β i.1.val*(i.1.val:ℂ)^m * F _) =
      β i.1.val*((QuantitativeArithmeticRetainedDilationOperator.affine
        (i.1.val:ℝ) ((i.1.val:ℝ)*shift j i.2) (retained_pos hS i.1) • z).im:ℂ)^m * F _
    rw [QuantitativeArithmeticRetainedDilationOperator.affine_im]
    push_cast
    rw [mul_pow]
    ring

/-- Literal mixed reconstruction after removing half the weight. Only the
original Ramanujan Fricke equations and complete-row equations are used. -/
theorem reconstruct_row (hN : 0<N) (hdiv : ∀ p∈S,p∣Q)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (χ β : ℕ → ℂ) (m : ℕ)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (hcomplete : ∀ p∈S,∀ w : ℂ,0<w.im →
      completeTwist F p w=(β p*(p:ℂ)^m)*F ((p:ℂ)*w))
    (j : Fin Q) (z : ℍ) :
    (z.im:ℂ)^m*F z=∑ i∈(A.coeff j).support,
      (A.coeff j i:ℂ)*rowValue (hQ:=hQ) hS hN F χ β m j z i := by
  rw [reconstruct_FE_dilation A hdiv F hp (2*m) χ _ hFE hcomplete j z z.im_pos,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := normalized_row (hQ:=hQ) hS hN F χ β m j z i
  linear_combination (A.coeff j i:ℂ)*h

/-- The geometric cap for each primitive occurrence is already part of
the mixed strict-height certificate. -/
theorem primitive_ascending (hN : 0<N) (P : Parameters A) (j : Fin Q)
    (i : RowIndex N Q) (hi : Sum.inl i∈(A.coeff j).support)
    (d : residues i.val.1) (z : ℍ) (hz : z∈cell P.ε j) :
    z.im/(primitiveMatrix (hQ:=hQ) hN j i d • z).im≤P.ρ := by
  rw [primitiveMatrix,ratio_forward (row_level_pos (hQ:=hQ) hN i)]
  have h := P.small j i hi z hz.1.1 hz.1.2.le z.im_pos.le hz.2.le
  simpa [FinitenessComplexGeometry.denominator,shift] using h


include hQ in
/-- The mixed source cells still partition the entire low strip. -/
theorem cell_subset_low (ε : ℝ) (j : Fin Q) :
    cell ε j⊆AsymptoticCertificateOperators.lowStrip ε := by
  intro z hz
  have hQR : (0:ℝ)<Q := by exact_mod_cast hQ
  have hj : (j:ℝ)+1≤Q := by exact_mod_cast (show (j:ℕ)+1≤Q by omega)
  refine ⟨⟨?_,?_⟩,hz.2⟩
  · exact (by positivity : (0:ℝ)≤(j:ℝ)/Q).trans hz.1.1
  · exact hz.1.2.trans_le ((div_le_one hQR).mpr hj)

include hQ in
theorem cell_partition (ε : ℝ) (f : ℍ → ℂ) (z : ℍ) :
    (∑ j : Fin Q,(cell ε j).indicator f z)=
      (AsymptoticCertificateOperators.lowStrip ε).indicator f z := by
  classical
  by_cases hz : z∈AsymptoticCertificateOperators.lowStrip ε
  · obtain ⟨j,hj⟩ := AsymptoticCertificateBranches.cell_index_exists hQ z hz.1
    rw [Set.indicator_of_mem hz,Finset.sum_eq_single j]
    · exact Set.indicator_of_mem (show z∈cell ε j from ⟨hj,hz.2⟩) f
    · intro i _ hij
      apply Set.indicator_of_notMem
      intro hi
      exact hij (AsymptoticCertificateBranches.cell_index_unique hQ i j hi.1 hj)
    · simp
  · rw [Set.indicator_of_notMem hz]
    apply Finset.sum_eq_zero
    intro j _
    exact Set.indicator_of_notMem (fun hj => hz (cell_subset_low (hQ:=hQ) ε j hj)) f

/-- Pointwise weighted reconstruction with the literal mixed certificate,
including the actual cell partition used by its Hilbert-space operators. -/
theorem reconstruct_low (hN : 0<N) (hdiv : ∀ p∈S,p∣Q)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (χ β : ℕ → ℂ) (m t : ℕ) (ε : ℝ)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (hcomplete : ∀ p∈S,∀ w : ℂ,0<w.im →
      completeTwist F p w=(β p*(p:ℂ)^m)*F ((p:ℂ)*w)) (z : ℍ) :
    (∑ j : Fin Q,(cell ε j).indicator (fun w : ℍ =>
      QuantitativeArithmeticRetainedDilationOperator.capWeight ε t w *
      ∑ i∈(A.coeff j).support,(A.coeff j i:ℂ)*rowValue (hQ:=hQ) hS hN F χ β m j w i) z)=
      (AsymptoticCertificateOperators.lowStrip ε).indicator
        (AsymptoticWeightedBranches.weighted ε t m F) z := by
  have he (j : Fin Q) : (fun w : ℍ =>
      QuantitativeArithmeticRetainedDilationOperator.capWeight ε t w *
      ∑ i∈(A.coeff j).support,(A.coeff j i:ℂ)*rowValue (hQ:=hQ) hS hN F χ β m j w i)=
      AsymptoticWeightedBranches.weighted ε t m F := by
    funext w
    rw [← reconstruct_row A hS hN hdiv F hp χ β m hFE hcomplete j w]
    simp only [QuantitativeArithmeticRetainedDilationOperator.capWeight,
      AsymptoticWeightedBranches.weighted,mul_assoc]
  simp_rw [he]
  exact cell_partition (hQ:=hQ) ε _ z

#print axioms cell_partition
#print axioms reconstruct_low
#print axioms normalized_row
#print axioms reconstruct_row
#print axioms primitive_ascending

end QuantitativeArithmeticRetainedCertificateFE
