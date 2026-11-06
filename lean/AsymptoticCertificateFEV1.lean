module

public import AsymptoticCertificateBranchesV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCertificateBranches

open UpperHalfPlane FinitenessCertificate FinitenessGlobalHeight
open FinitenessAnalyticReconstruction AsymptoticReconstructionBranch
open AsymptoticHyperbolicSlash

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The half-open cells form a genuine partition of the strip. -/
theorem cell_index_exists (hQ : 0<Q) (z : ℍ) (hz : z∈AsymptoticMassTransport.strip) :
    ∃ j : Fin Q, (j:ℝ)/Q≤z.re ∧ z.re<((j:ℝ)+1)/Q := by
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hx : 0≤(Q:ℝ)*z.re := mul_nonneg hQ'.le hz.1
  let j : ℕ := Nat.floor ((Q:ℝ)*z.re)
  have hj : j<Q := (Nat.floor_lt hx).mpr (by
    have hz1 : z.re<1 := hz.2
    nlinarith)
  refine ⟨⟨j,hj⟩,?_,?_⟩
  · exact (div_le_iff₀ hQ').mpr (by simpa [j,mul_comm] using Nat.floor_le hx)
  · exact (lt_div_iff₀ hQ').mpr (by simpa [j,mul_comm] using Nat.lt_floor_add_one ((Q:ℝ)*z.re))

theorem cell_index_unique (hQ : 0<Q) (i j : Fin Q) {x : ℝ}
    (hi : (i:ℝ)/Q≤x ∧ x<((i:ℝ)+1)/Q)
    (hj : (j:ℝ)/Q≤x ∧ x<((j:ℝ)+1)/Q) : i=j := by
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hi0 := (div_le_iff₀ hQ').mp hi.1
  have hi1 := (lt_div_iff₀ hQ').mp hi.2
  have hj0 := (div_le_iff₀ hQ').mp hj.1
  have hj1 := (lt_div_iff₀ hQ').mp hj.2
  have hij : (i:ℕ)<(j:ℕ)+1 := by exact_mod_cast (show (i:ℝ)<(j:ℝ)+1 by linarith)
  have hji : (j:ℕ)<(i:ℕ)+1 := by exact_mod_cast (show (j:ℝ)<(i:ℝ)+1 by linarith)
  exact Fin.ext (by omega)

theorem matrix_action (hN : 0<N) (v : Index A) (z : ℍ) :
    ((matrix A hN v • z:ℍ):ℂ)=
      -1/((Nat.lcm N ((modulus A v)^2):ℕ)*
        ((z:ℂ)+((v.2.1.val.val.2:ℂ)-(v.1:ℕ))/Q))+
          (v.2.2.val:ℂ)/modulus A v := by
  rw [matrix,branch_action (level_pos A hN v)]
  simp [level,inputShift,outputShift]

/-- Substitution of the literal functional equation in one certificate
row, with each primitive residue represented by its actual Möbius branch. -/
theorem reconstruct_row (hN : 0<N) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (χ : ℕ → ℂ) (m : ℕ)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (j : Fin Q) (z : ℍ) :
    (z.im:ℂ)^m*F z=
      ∑ i : (A.coeff j).support, ∑ a : residues i.val.val.1,
        (scalar A ⟨j,i,a⟩:ℂ)*χ (modulus A ⟨j,i,a⟩)*
          phase (matrix A hN ⟨j,i,a⟩) (2*m) z*
            ((matrix A hN ⟨j,i,a⟩ • z).im:ℂ)^m*F (matrix A hN ⟨j,i,a⟩ • z:ℍ) := by
  classical
  rw [reconstruct_FE A F hp (2*m) χ hFE j z z.im_pos,Finset.mul_sum]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro i _
  rw [twist,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro a _
  have hn := normalized_branch (level_pos A hN ⟨j,i,a⟩)
    (inputShift A ⟨j,i,a⟩) (outputShift A ⟨j,i,a⟩) m (fun w : ℍ => F w) z
  change phase (matrix A hN ⟨j,i,a⟩) (2*m) z*
    ((matrix A hN ⟨j,i,a⟩ • z).im:ℂ)^m*F (matrix A hN ⟨j,i,a⟩ • z:ℍ)=
    (z.im:ℂ)^m/((Real.sqrt (level A ⟨j,i,a⟩):ℂ)*
      ((z:ℂ)+(inputShift A ⟨j,i,a⟩:ℂ)))^(2*m)*F (matrix A hN ⟨j,i,a⟩ • z:ℍ) at hn
  have hb : ((inputShift A ⟨j,i,a⟩:ℝ):ℂ)=((i.val.val.2:ℂ)-(j:ℕ))/Q := by
    simp [inputShift]
  rw [hb] at hn
  have hact := matrix_action A hN ⟨j,i,a⟩ z
  simp only [modulus] at hact
  rw [← hact]
  have he := congrArg (fun w : ℂ => (scalar A ⟨j,i,a⟩:ℂ)*χ (modulus A ⟨j,i,a⟩)*w) hn
  simp only [scalar,level,modulus] at he ⊢
  linear_combination -he

/-- The finite geometric reconstruction is the literal functional
equation on the strip, including the cell indicators used by the L²
operators. This identity has no extra reconstruction hypothesis. -/
theorem reconstruct_strip (hN : 0<N) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (χ : ℕ → ℂ) (m : ℕ)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (z : ℍ) (hz : z∈AsymptoticMassTransport.strip) :
    (z.im:ℂ)^m*F z=
      ∑ v : Index A, (cell A v).indicator (fun w : ℍ =>
        (scalar A v:ℂ)*χ (modulus A v)*phase (matrix A hN v) (2*m) w*
          ((matrix A hN v • w).im:ℂ)^m*F (matrix A hN v • w:ℍ)) z := by
  classical
  obtain ⟨j,hj⟩ := cell_index_exists hQ z hz
  rw [reconstruct_row A hN F hp χ m hFE j z,Fintype.sum_sigma]
  symm
  rw [Finset.sum_eq_single j]
  · rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    rw [Set.indicator_of_mem (show z∈cell A ⟨j,i,a⟩ from hj)]
  · intro j' _ hj'
    rw [Fintype.sum_sigma]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro a _
    apply Set.indicator_of_notMem
    intro hcell
    exact hj' (cell_index_unique hQ j' j hcell hj)
  · simp

#print axioms cell_index_exists
#print axioms cell_index_unique
#print axioms matrix_action
#print axioms reconstruct_row
#print axioms reconstruct_strip

end AsymptoticCertificateBranches
