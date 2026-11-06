module

public import QuantitativeArithmeticSmallLevelCircBoundarySplitV1
public import QuantitativeArithmeticSmallLevelCircModularHeckeTheoryV4
public import QuantitativeArithmeticSmallLevelEisensteinBoundaryPrimeFactorsV1
public import QuantitativeArithmeticSmallLevelEisensteinBoundaryWeightSumV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelEisenstein. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryPrimeTermV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant
open scoped MatrixGroups ModularForm

/-- A prime-determinant integral slash term has one of two cusp factors.
For p=1 mod N, removing its primitive-column gcd does not alter the
residue cusp label. All hypotheses here are literal finite matrix data. -/
theorem prime_integral_boundary
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne] (k : ℤ)
    (N p : ℕ) (hp : p.Prime) (hpN : (p : ZMod N)=1)
    (hΓ : ∀ rho ∈ CongruenceSubgroup.Gamma N, SpecialLinearGroup.mapGL ℝ rho ∈ Γ)
    (F : ModularForm Γ k) (γ : SL(2,ℤ))
    (B : Matrix (Fin 2) (Fin 2) ℤ) (hdet : B.det=p)
    (g : GL (Fin 2) ℝ) (hg : g.val=B.map (Int.castRingHom ℝ))
    (hcol : ∀ i : Fin 2, (B i 0 : ZMod N)=(γ i 0 : ZMod N)) :
    Tendsto ((F : ℍ → ℂ) ∣[k] g) atImInfty
      (nhds ((if (p:ℤ)∣B 0 0 ∧ (p:ℤ)∣B 1 0 then (p:ℂ)^(k-1) else (p:ℂ)⁻¹) *
        cuspBoundary Γ k F γ)) := by
  obtain ⟨U,a,b,d,ha,hd,had,hU,htri⟩ := integral_triangularGL B
    (by rw [hdet]; exact_mod_cast hp.pos) g hg
  have hadp : a*d=p := had.trans hdet
  have ha1 : (a : ZMod N)=1 := by
    rcases prime_positive_factors p hp a d ha hd hadp with ⟨ha',_⟩ | ⟨ha',_⟩
    · simp only [ha',Int.cast_one]
    · simpa only [ha',Int.cast_natCast] using hpN
  have hUcol : ∀ i : Fin 2, (U i 0 : ZMod N)=(γ i 0 : ZMod N) := by
    intro i
    have hh := hcol i
    rw [hU i] at hh
    simpa only [Int.cast_mul,ha1,mul_one] using hh
  have ht := boundary_integral_term Γ k N hΓ F γ U a b d ha hd g htri hUcol
  rw [prime_reduction_factor p hp B U a d ha hd hadp hU k] at ht
  exact ht

#print axioms prime_integral_boundary

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryHeckeTermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant AsymptoticClassicalCusp
open AsymptoticCongruenceLabels
open scoped MatrixGroups ModularForm

theorem level_contains_principal (N : ℕ) (rho : SL(2,ℤ))
    (hrho : rho ∈ CongruenceSubgroup.Gamma N) : SpecialLinearGroup.mapGL ℝ rho ∈ level N := by
  refine ⟨rho,?_,rfl⟩
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hrho).2.2.1

theorem boundaryTranslation_mem_level (N : ℕ) (j : ℤ) :
    SpecialLinearGroup.mapGL ℝ (boundaryTranslation j) ∈ level N := by
  refine ⟨boundaryTranslation j,?_,rfl⟩
  apply CongruenceSubgroup.Gamma0_mem.mpr
  simp [boundaryTranslation]

theorem dilation_cusp_boundary (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hpN : (p : ZMod N)=1) (k : ℤ) (F : ModularForm (level N) k) (γ : SL(2,ℤ)) :
    Tendsto ((F : ℍ → ℂ) ∣[k] (dilationReal p hp.pos * SpecialLinearGroup.mapGL ℝ γ))
      atImInfty (nhds ((if (p:ℤ)∣γ 1 0 then (p:ℂ)^(k-1) else (p:ℂ)⁻¹) *
        cuspBoundary (level N) k F γ)) := by
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![(p:ℤ),0;0,1]*γ.val
  have hdet : B.det=p := by
    change ( _ * γ.val).det = _
    rw [Matrix.det_mul,γ.property,mul_one]
    simp [Matrix.det_fin_two]
  have hg : (dilationReal p hp.pos * SpecialLinearGroup.mapGL ℝ γ).val =
      B.map (Int.castRingHom ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B,dilationReal,dilationGL,GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero,
        SpecialLinearGroup.mapGL,SpecialLinearGroup.map,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  have hcol : ∀ i : Fin 2, (B i 0 : ZMod N)=(γ i 0 : ZMod N) := by
    intro i
    fin_cases i
    · simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hpN]
    · simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hpN]
  have ht := prime_integral_boundary (level N) k N p hp hpN (level_contains_principal N)
    F γ B hdet _ hg hcol
  have hi : ((p:ℤ)∣B 0 0 ∧ (p:ℤ)∣B 1 0) ↔ (p:ℤ)∣γ 1 0 := by
    simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  simpa only [hi] using ht

theorem upper_cusp_boundary (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hpN : (p : ZMod N)=1) (k : ℤ) (F : ModularForm (level N) k) (γ : SL(2,ℤ))
    (j : ℤ) :
    Tendsto ((F : ℍ → ℂ) ∣[k]
      (triangularGL 1 (j:ℝ) p (by norm_num) (by exact_mod_cast hp.pos) *
        SpecialLinearGroup.mapGL ℝ γ)) atImInfty
      (nhds ((if (p:ℤ)∣γ 0 0+j*γ 1 0 then (p:ℂ)^(k-1) else (p:ℂ)⁻¹) *
        cuspBoundary (level N) k F γ)) := by
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![1,j;0,(p:ℤ)]*γ.val
  have hdet : B.det=p := by
    change ( _ * γ.val).det = _
    rw [Matrix.det_mul,γ.property,mul_one]
    simp [Matrix.det_fin_two]
  have hg : (triangularGL 1 (j:ℝ) p (by norm_num) (by exact_mod_cast hp.pos) *
      SpecialLinearGroup.mapGL ℝ γ).val = B.map (Int.castRingHom ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [B,triangularGL,GeneralLinearGroup.mkOfDetNeZero,
        SpecialLinearGroup.mapGL,SpecialLinearGroup.map,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  have hcol : ∀ i : Fin 2, (B i 0 : ZMod N)=((boundaryTranslation j*γ) i 0 : ZMod N) := by
    intro i
    change (B i 0 : ZMod N)=((!![1,j;0,1]*γ.val) i 0 : ZMod N)
    fin_cases i
    · simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hpN]
    · simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hpN]
  have ht := prime_integral_boundary (level N) k N p hp hpN (level_contains_principal N)
    F (boundaryTranslation j*γ) B hdet _ hg hcol
  rw [cuspBoundary_left (level N) k F (boundaryTranslation j) γ
    (boundaryTranslation_mem_level N j)] at ht
  have hi : ((p:ℤ)∣B 0 0 ∧ (p:ℤ)∣B 1 0) ↔ (p:ℤ)∣γ 0 0+j*γ 1 0 := by
    simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  simpa only [hi] using ht

#print axioms dilation_cusp_boundary
#print axioms upper_cusp_boundary

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryDiagonalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix AsymptoticClassicalCusp
open scoped MatrixGroups

theorem boundary_diagonal_det (N q : ℕ) (hc : q.Coprime N) :
    Matrix.det (!![(q:ℤ),-(N:ℤ)*Nat.gcdB q (N*N);(N:ℤ),Nat.gcdA q (N*N)]) = 1 := by
  have hc2 : q.Coprime (N*N) := hc.mul_right hc
  have h := Nat.gcd_eq_gcd_ab q (N*N)
  rw [hc2.gcd_eq_one,Nat.cast_one,Nat.cast_mul] at h
  rw [Matrix.det_fin_two]
  dsimp
  nlinarith

/-- A genuine Gamma0(N) lift of diag(q,q^{-1}) modulo N. -/
def boundaryDiagonal (N q : ℕ) (hc : q.Coprime N) : SL(2,ℤ) :=
  ⟨!![(q:ℤ),-(N:ℤ)*Nat.gcdB q (N*N);(N:ℤ),Nat.gcdA q (N*N)],
    boundary_diagonal_det N q hc⟩

theorem boundaryDiagonal_mem_level (N q : ℕ) (hc : q.Coprime N) :
    SpecialLinearGroup.mapGL ℝ (boundaryDiagonal N q hc) ∈ level N := by
  refine ⟨boundaryDiagonal N q hc, ?_, rfl⟩
  apply CongruenceSubgroup.Gamma0_mem.mpr
  simp [boundaryDiagonal]

theorem boundaryDiagonal_inverse_entry (N q : ℕ) (hc : q.Coprime N) :
    (Nat.gcdA q (N*N) : ZMod N) * (q:ZMod N)=1 := by
  have h := congrArg (Int.castRingHom (ZMod N)) (boundary_diagonal_det N q hc)
  simp only [Matrix.det_fin_two] at h
  simpa [mul_comm] using h

theorem boundaryDiagonal_column (N q : ℕ) (hc : q.Coprime N) (γ : SL(2,ℤ)) :
    ((boundaryDiagonal N q hc * γ) 0 0 : ZMod N) = (q:ZMod N)*(γ 0 0 : ZMod N) ∧
    ((boundaryDiagonal N q hc * γ) 1 0 : ZMod N) =
      (Nat.gcdA q (N*N) : ZMod N)*(γ 1 0 : ZMod N) := by
  change (((!![(q:ℤ),-(N:ℤ)*Nat.gcdB q (N*N);(N:ℤ),Nat.gcdA q (N*N)] * γ.val) 0 0 : ℤ) : ZMod N) = _ ∧ _
  simp [boundaryDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms boundaryDiagonal_mem_level
#print axioms boundaryDiagonal_inverse_entry
#print axioms boundaryDiagonal_column

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryLabelScaleV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix AsymptoticClassicalDiscriminant
open scoped MatrixGroups

/-- A prime-determinant integral matrix with a nondivisible first column
has that exact column in a unimodular matrix. -/
theorem prime_column_completion (q : ℕ) (hq : q.Prime)
    (B : Matrix (Fin 2) (Fin 2) ℤ) (hdet : B.det=q)
    (hnot : ¬ ((q:ℤ)∣B 0 0 ∧ (q:ℤ)∣B 1 0)) :
    ∃ U : SL(2,ℤ), ∀ i : Fin 2, U i 0 = B i 0 := by
  have hpos : 0<B.det := by rw [hdet]; exact_mod_cast hq.pos
  obtain ⟨U,a,b,d,ha,hd,he⟩ := integral_triangular B hpos
  have had : a*d=q := by
    have hh := congrArg Matrix.det he
    rw [Matrix.det_mul,U.property,one_mul,hdet] at hh
    simpa [Matrix.det_fin_two] using hh.symm
  have hcol : ∀ i : Fin 2, B i 0=U i 0*a := by
    intro i
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M i 0) he
    simpa [Matrix.mul_apply,Fin.sum_univ_two] using hh
  have ha1 : a=1 := by
    rcases prime_positive_factors q hq a d ha hd had with ⟨h,_⟩ | ⟨h,_⟩
    · exact h
    · exact False.elim (hnot ((prime_reduction_expanding_iff q hq B U a d ha hd had hcol).mp h))
  exact ⟨U, fun i ↦ by simpa only [ha1,mul_one] using (hcol i).symm⟩

theorem prime_not_both_column (q : ℕ) (hq : q.Prime) (γ : SL(2,ℤ)) :
    ¬ ((q:ℤ)∣γ 0 0 ∧ (q:ℤ)∣γ 1 0) := by
  rintro ⟨h0,h1⟩
  have hh := dvd_sub (dvd_mul_of_dvd_left h0 (γ 1 1))
    (dvd_mul_of_dvd_right h1 (γ 0 1))
  have hd := γ.property
  rw [Matrix.det_fin_two] at hd
  rw [hd] at hh
  have hl := Int.le_of_dvd (by norm_num : (0:ℤ)<1) hh
  have hg : (1:ℤ)<q := by exact_mod_cast hq.one_lt
  omega

/-- The finite set of realized primitive-column labels is stable under
multiplying the top coordinate by any prime coprime to the level. -/
theorem cuspColumn_scale_prime (N q : ℕ) (hq : q.Prime) (hc : q.Coprime N)
    (γ : SL(2,ℤ)) :
    ∃ U : SL(2,ℤ), (U 0 0 : ZMod N)=(q:ZMod N)*(γ 0 0 : ZMod N) ∧
      (U 1 0 : ZMod N)=(γ 1 0 : ZMod N) := by
  by_cases hqdiv : (q:ℤ)∣γ 1 0
  · let B : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;0,(q:ℤ)]*γ.val
    have hdet : B.det=q := by
      change (_*γ.val).det=_
      rw [Matrix.det_mul,γ.property,mul_one]
      simp [Matrix.det_fin_two]
    have hnot : ¬ ((q:ℤ)∣B 0 0 ∧ (q:ℤ)∣B 1 0) := by
      intro hh
      apply prime_not_both_column q hq γ
      exact ⟨by simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using hh.1,hqdiv⟩
    obtain ⟨V,hV⟩ := prime_column_completion q hq B hdet hnot
    refine ⟨boundaryDiagonal N q hc*V,?_,?_⟩
    · rw [(boundaryDiagonal_column N q hc V).1,hV 0]
      simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    · rw [(boundaryDiagonal_column N q hc V).2,hV 1]
      have hb1 : B 1 0 = (q:ℤ)*γ 1 0 := by
        simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
      rw [hb1,Int.cast_mul,Int.cast_natCast,← mul_assoc,
        boundaryDiagonal_inverse_entry N q hc,one_mul]

  · let B : Matrix (Fin 2) (Fin 2) ℤ := !![(q:ℤ),0;0,1]*γ.val
    have hdet : B.det=q := by
      change (_*γ.val).det=_
      rw [Matrix.det_mul,γ.property,mul_one]
      simp [Matrix.det_fin_two]
    have hnot : ¬ ((q:ℤ)∣B 0 0 ∧ (q:ℤ)∣B 1 0) := by
      intro hh
      apply hqdiv
      simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using hh.2
    obtain ⟨U,hU⟩ := prime_column_completion q hq B hdet hnot
    refine ⟨U,?_,?_⟩
    · rw [hU 0]
      simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    · rw [hU 1]
      simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

#print axioms prime_column_completion
#print axioms prime_not_both_column
#print axioms cuspColumn_scale_prime

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryPermutationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix
open scoped MatrixGroups

def boundaryPrimeMap (N q : ℕ) (hq : q.Prime) (hc : q.Coprime N)
    (v : boundaryLabels N) : boundaryLabels N := by
  refine ⟨fun i ↦ if i=0 then (q:ZMod N)*v.val 0 else v.val 1, ?_⟩
  obtain ⟨U,h0,h1⟩ := cuspColumn_scale_prime N q hq hc (boundaryRepresentative N v)
  refine ⟨U,?_⟩
  ext i
  have hv := boundaryRepresentative_column N v
  fin_cases i
  · simpa [cuspColumn,← congrFun hv 0] using h0
  · simpa [cuspColumn,← congrFun hv 1] using h1

@[simp] theorem boundaryPrimeMap_zero (N q : ℕ) (hq : q.Prime) (hc : q.Coprime N)
    (v : boundaryLabels N) : (boundaryPrimeMap N q hq hc v).val 0 = (q:ZMod N)*v.val 0 := by
  simp [boundaryPrimeMap]

@[simp] theorem boundaryPrimeMap_one (N q : ℕ) (hq : q.Prime) (hc : q.Coprime N)
    (v : boundaryLabels N) : (boundaryPrimeMap N q hq hc v).val 1 = v.val 1 := by
  simp [boundaryPrimeMap]

theorem boundaryPrimeMap_injective (N q : ℕ) (hq : q.Prime) (hc : q.Coprime N) :
    Function.Injective (boundaryPrimeMap N q hq hc) := by
  intro v w he
  apply Subtype.ext
  ext i
  have he0 := congrArg (fun t : boundaryLabels N ↦ t.val 0) he
  have he1 := congrArg (fun t : boundaryLabels N ↦ t.val 1) he
  simp only [boundaryPrimeMap_zero] at he0
  simp only [boundaryPrimeMap_one] at he1
  fin_cases i
  · exact (ZMod.unitOfCoprime q hc).isUnit.mul_left_cancel he0
  · exact he1

/-- The actual prime scaling of the finite primitive-column labels. -/
def boundaryPrimePerm (N q : ℕ) [NeZero N] (hq : q.Prime) (hc : q.Coprime N) :
    Equiv.Perm (boundaryLabels N) :=
  Equiv.ofBijective (boundaryPrimeMap N q hq hc)
    ((Finite.injective_iff_bijective).mp (boundaryPrimeMap_injective N q hq hc))

@[simp] theorem boundaryPrimePerm_apply (N q : ℕ) [NeZero N]
    (hq : q.Prime) (hc : q.Coprime N) (v : boundaryLabels N) :
    boundaryPrimePerm N q hq hc v = boundaryPrimeMap N q hq hc v := rfl

theorem boundaryPrimePerm_commute (N p q : ℕ) [NeZero N]
    (hp : p.Prime) (hcp : p.Coprime N) (hq : q.Prime) (hcq : q.Coprime N) :
    Function.Commute (boundaryPrimePerm N p hp hcp) (boundaryPrimePerm N q hq hcq) := by
  intro v
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [mul_left_comm]

#print axioms boundaryPrimeMap_injective
#print axioms boundaryPrimePerm
#print axioms boundaryPrimePerm_commute

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryPrimeValuesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix AsymptoticClassicalCusp
open scoped MatrixGroups

def cuspLabel (N : ℕ) (γ : SL(2,ℤ)) : boundaryLabels N := ⟨cuspColumn N γ,γ,rfl⟩

def primeBoundaryValue (N q : ℕ) [NeZero N] (hq : q.Prime) (hc : q.Coprime N)
    (k : ℤ) (F : ModularForm (level N) k) (γ : SL(2,ℤ)) : ℂ :=
  finiteCuspBoundary (level N) k N F (boundaryPrimePerm N q hq hc (cuspLabel N γ))

def inversePrimeBoundaryValue (N q : ℕ) [NeZero N] (hq : q.Prime) (hc : q.Coprime N)
    (k : ℤ) (F : ModularForm (level N) k) (γ : SL(2,ℤ)) : ℂ :=
  finiteCuspBoundary (level N) k N F ((boundaryPrimePerm N q hq hc).symm (cuspLabel N γ))

theorem boundary_prime_value_of_column (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hc : q.Coprime N) (k : ℤ) (F : ModularForm (level N) k) (γ U : SL(2,ℤ))
    (h0 : (U 0 0 : ZMod N)=(q:ZMod N)*(γ 0 0 : ZMod N))
    (h1 : (U 1 0 : ZMod N)=(γ 1 0 : ZMod N)) :
    cuspBoundary (level N) k F U = primeBoundaryValue N q hq hc k F γ := by
  have he : cuspLabel N U=boundaryPrimePerm N q hq hc (cuspLabel N γ) := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simpa [cuspLabel,cuspColumn] using h0
    · simpa [cuspLabel,cuspColumn] using h1
  rw [← finiteCuspBoundary_recovers (level N) k N (level_contains_principal N) F U]
  exact congrArg (finiteCuspBoundary (level N) k N F) he

theorem boundary_inverse_value_of_column (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hc : q.Coprime N) (k : ℤ) (F : ModularForm (level N) k) (γ U : SL(2,ℤ))
    (h0 : (q:ZMod N)*(U 0 0 : ZMod N)=(γ 0 0 : ZMod N))
    (h1 : (U 1 0 : ZMod N)=(γ 1 0 : ZMod N)) :
    cuspBoundary (level N) k F U = inversePrimeBoundaryValue N q hq hc k F γ := by
  have he : boundaryPrimePerm N q hq hc (cuspLabel N U)=cuspLabel N γ := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simpa [cuspLabel,cuspColumn] using h0
    · simpa [cuspLabel,cuspColumn] using h1
  rw [← finiteCuspBoundary_recovers (level N) k N (level_contains_principal N) F U]
  exact congrArg (finiteCuspBoundary (level N) k N F) ((Equiv.eq_symm_apply (boundaryPrimePerm N q hq hc)).mpr he)

/-- The expanded dilation column has the inverse prime boundary value;
the Gamma0 diagonal lift is essential here. -/
theorem boundary_inverse_value_of_dilation (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hc : q.Coprime N) (k : ℤ) (F : ModularForm (level N) k) (γ U : SL(2,ℤ))
    (h0 : (U 0 0 : ZMod N)=(γ 0 0 : ZMod N))
    (h1 : (q:ZMod N)*(U 1 0 : ZMod N)=(γ 1 0 : ZMod N)) :
    cuspBoundary (level N) k F U = inversePrimeBoundaryValue N q hq hc k F γ := by
  let v := (boundaryPrimePerm N q hq hc).symm (cuspLabel N γ)
  let V := boundaryRepresentative N v
  have hV : cuspColumn N V=v.val := boundaryRepresentative_column N v
  have hv : boundaryPrimePerm N q hq hc v=cuspLabel N γ := (boundaryPrimePerm N q hq hc).apply_symm_apply _
  have hv0 : (q:ZMod N)*(V 0 0 : ZMod N)=(γ 0 0 : ZMod N) := by
    have hh := congrArg (fun t : boundaryLabels N ↦ t.val 0) hv
    simpa only [boundaryPrimePerm_apply,boundaryPrimeMap_zero,cuspLabel,cuspColumn,← congrFun hV 0] using hh
  have hv1 : (V 1 0 : ZMod N)=(γ 1 0 : ZMod N) := by
    have hh := congrArg (fun t : boundaryLabels N ↦ t.val 1) hv
    simpa only [boundaryPrimePerm_apply,boundaryPrimeMap_one,cuspLabel,cuspColumn,← congrFun hV 1] using hh
  have he : cuspBoundary (level N) k F U =
      cuspBoundary (level N) k F (boundaryDiagonal N q hc*V) := by
    apply cuspBoundary_column_congr (level N) k N (level_contains_principal N)
    intro i
    fin_cases i
    · change (U 0 0 : ZMod N)=((boundaryDiagonal N q hc*V) 0 0 : ZMod N)
      rw [(boundaryDiagonal_column N q hc V).1,hv0]
      exact h0
    · change (U 1 0 : ZMod N)=((boundaryDiagonal N q hc*V) 1 0 : ZMod N)
      rw [(boundaryDiagonal_column N q hc V).2,hv1,← h1,← mul_assoc,
        boundaryDiagonal_inverse_entry N q hc,one_mul]
  rw [he,cuspBoundary_left (level N) k F (boundaryDiagonal N q hc) V
    (boundaryDiagonal_mem_level N q hc)]
  rfl

#print axioms boundary_prime_value_of_column
#print axioms boundary_inverse_value_of_column
#print axioms boundary_inverse_value_of_dilation

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryUpperValuesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix AsymptoticClassicalCusp
open scoped MatrixGroups

theorem boundaryTranslation_column (N : ℕ) (t : ℤ) (U : SL(2,ℤ)) :
    ((boundaryTranslation t*U) 0 0 : ZMod N)=(U 0 0 : ZMod N)+(t:ZMod N)*(U 1 0 : ZMod N) ∧
    ((boundaryTranslation t*U) 1 0 : ZMod N)=(U 1 0 : ZMod N) := by
  change (((!![1,t;0,1]*U.val) 0 0 : ℤ) : ZMod N)=_ ∧ _
  simp [boundaryTranslation,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

theorem boundary_prime_value_of_upper (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hc : q.Coprime N) (k : ℤ) (F : ModularForm (level N) k) (γ U : SL(2,ℤ)) (j : ℤ)
    (h0 : (U 0 0 : ZMod N)=(γ 0 0 : ZMod N)+(j:ZMod N)*(γ 1 0 : ZMod N))
    (h1 : (U 1 0 : ZMod N)=(q:ZMod N)*(γ 1 0 : ZMod N)) :
    cuspBoundary (level N) k F U = primeBoundaryValue N q hq hc k F γ := by
  let V := boundaryDiagonal N q hc*U
  let W := boundaryTranslation (-(q:ℤ)*j)*V
  have hV0 : (V 0 0 : ZMod N)=(q:ZMod N)*((γ 0 0 : ZMod N)+(j:ZMod N)*(γ 1 0 : ZMod N)) := by
    rw [(boundaryDiagonal_column N q hc U).1,h0]
  have hV1 : (V 1 0 : ZMod N)=(γ 1 0 : ZMod N) := by
    rw [(boundaryDiagonal_column N q hc U).2,h1,← mul_assoc,
      boundaryDiagonal_inverse_entry N q hc,one_mul]
  have hW0 : (W 0 0 : ZMod N)=(q:ZMod N)*(γ 0 0 : ZMod N) := by
    rw [(boundaryTranslation_column N (-(q:ℤ)*j) V).1,hV0,hV1]
    push_cast
    ring
  have hW1 : (W 1 0 : ZMod N)=(γ 1 0 : ZMod N) := by
    rw [(boundaryTranslation_column N (-(q:ℤ)*j) V).2,hV1]
  have he := boundary_prime_value_of_column N q hq hc k F γ W hW0 hW1
  have ht := cuspBoundary_left (level N) k F (boundaryTranslation (-(q:ℤ)*j)) V
    (boundaryTranslation_mem_level N _)
  have hd := cuspBoundary_left (level N) k F (boundaryDiagonal N q hc) U
    (boundaryDiagonal_mem_level N q hc)
  exact (hd.symm.trans ht.symm).trans he

theorem boundary_inverse_value_of_upper (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hc : q.Coprime N) (k : ℤ) (F : ModularForm (level N) k) (γ U : SL(2,ℤ)) (j : ℤ)
    (h0 : (q:ZMod N)*(U 0 0 : ZMod N)=(γ 0 0 : ZMod N)+(j:ZMod N)*(γ 1 0 : ZMod N))
    (h1 : (U 1 0 : ZMod N)=(γ 1 0 : ZMod N)) :
    cuspBoundary (level N) k F U = inversePrimeBoundaryValue N q hq hc k F γ := by
  let t : ℤ := -j*Nat.gcdA q (N*N)
  let W := boundaryTranslation t*U
  have hW0 : (q:ZMod N)*(W 0 0 : ZMod N)=(γ 0 0 : ZMod N) := by
    rw [(boundaryTranslation_column N t U).1,mul_add,h0,h1]
    have hi := boundaryDiagonal_inverse_entry N q hc
    dsimp [t]
    push_cast
    linear_combination -(j:ZMod N)*(γ 1 0 : ZMod N)*hi
  have hW1 : (W 1 0 : ZMod N)=(γ 1 0 : ZMod N) := by
    rw [(boundaryTranslation_column N t U).2,h1]
  have he := boundary_inverse_value_of_column N q hq hc k F γ W hW0 hW1
  have ht := cuspBoundary_left (level N) k F (boundaryTranslation t) U
    (boundaryTranslation_mem_level N t)
  exact ht.symm.trans he

#print axioms boundary_prime_value_of_upper
#print axioms boundary_inverse_value_of_upper

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryTwoValuesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant
open scoped MatrixGroups ModularForm

/-- Prime-determinant slash limits from the two actual primitive-column
boundary values. The supplied hypotheses are finite column comparisons. -/
theorem prime_integral_two_boundary
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] [Γ.HasDetOne] (k : ℤ)
    (q : ℕ) (hq : q.Prime) (F : ModularForm Γ k)
    (B : Matrix (Fin 2) (Fin 2) ℤ) (hdet : B.det=q)
    (g : GL (Fin 2) ℝ) (hg : g.val=B.map (Int.castRingHom ℝ)) (C D : ℂ)
    (hsmall : ∀ U : SL(2,ℤ), (∀ i : Fin 2, B i 0=U i 0) → cuspBoundary Γ k F U=C)
    (hlarge : ∀ U : SL(2,ℤ), (∀ i : Fin 2, B i 0=U i 0*(q:ℤ)) → cuspBoundary Γ k F U=D) :
    Tendsto ((F : ℍ → ℂ) ∣[k] g) atImInfty
      (nhds (if (q:ℤ)∣B 0 0 ∧ (q:ℤ)∣B 1 0 then (q:ℂ)^(k-1)*D else (q:ℂ)⁻¹*C)) := by
  have hpos : 0<B.det := by rw [hdet]; exact_mod_cast hq.pos
  obtain ⟨U,a,b,d,ha,hd,had,hcol,hg'⟩ := integral_triangularGL B hpos g hg
  rw [hdet] at had
  rw [hg',SlashAction.slash_mul]
  have ht := tendsto_slash_triangular (cuspBoundary_tendsto Γ k F U)
    (a:ℝ) (b:ℝ) (d:ℝ) (by exact_mod_cast ha) (by exact_mod_cast hd) k
  change Tendsto (((F : ℍ → ℂ) ∣[k] U) ∣[k] _) _
    (nhds (triangularFactor (a:ℝ) (d:ℝ) k*cuspBoundary Γ k F U)) at ht
  have hfac := prime_reduction_factor q hq B U a d ha hd had hcol k
  rw [hfac] at ht
  have hi := prime_reduction_expanding_iff q hq B U a d ha hd had hcol
  by_cases hdiv : (q:ℤ)∣B 0 0 ∧ (q:ℤ)∣B 1 0
  · have hap := hi.mpr hdiv
    have hv := hlarge U (by simpa only [hap] using hcol)
    simp only [ite_eq_left hdiv,hv] at ht ⊢
    exact ht
  · have ha1 : a=1 := by
      rcases prime_positive_factors q hq a d ha hd had with ⟨h,_⟩ | ⟨h,_⟩
      · exact h
      · exact False.elim (hdiv (hi.mp h))
    have hv := hsmall U (by simpa only [ha1,mul_one] using hcol)
    simp only [ite_eq_right hdiv,hv] at ht ⊢
    exact ht

#print axioms prime_integral_two_boundary

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryHeckeTwoTermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant AsymptoticClassicalCusp
open AsymptoticCongruenceLabels
open scoped MatrixGroups ModularForm

theorem dilation_cusp_boundary_two (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hc : p.Coprime N) (k : ℤ) (F : ModularForm (level N) k) (γ : SL(2,ℤ)) :
    Tendsto ((F : ℍ → ℂ) ∣[k] (dilationReal p hp.pos * SpecialLinearGroup.mapGL ℝ γ))
      atImInfty (nhds (if (p:ℤ)∣γ 1 0 then (p:ℂ)^(k-1)*inversePrimeBoundaryValue N p hp hc k F γ
        else (p:ℂ)⁻¹*primeBoundaryValue N p hp hc k F γ)) := by
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![(p:ℤ),0;0,1]*γ.val
  have hdet : B.det=p := by
    change ( _ * γ.val).det = _
    rw [Matrix.det_mul,γ.property,mul_one]
    simp [Matrix.det_fin_two]
  have hg : (dilationReal p hp.pos * SpecialLinearGroup.mapGL ℝ γ).val =
      B.map (Int.castRingHom ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B,dilationReal,dilationGL,GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero,
        SpecialLinearGroup.mapGL,SpecialLinearGroup.map,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  have hs : ∀ U : SL(2,ℤ), (∀ i : Fin 2, B i 0=U i 0) →
      cuspBoundary (level N) k F U=primeBoundaryValue N p hp hc k F γ := by
    intro U hU
    apply boundary_prime_value_of_column N p hp hc k F γ U
    · simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod N)) ((by simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using (hU 0).symm : U 0 0=(p:ℤ)*γ 0 0))
    · simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod N)) ((by simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using (hU 1).symm : U 1 0=γ 1 0))
  have hl : ∀ U : SL(2,ℤ), (∀ i : Fin 2, B i 0=U i 0*(p:ℤ)) →
      cuspBoundary (level N) k F U=inversePrimeBoundaryValue N p hp hc k F γ := by
    intro U hU
    apply boundary_inverse_value_of_dilation N p hp hc k F γ U
    · have hh : (p:ℤ)*γ 0 0=(p:ℤ)*U 0 0 := by
        simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,mul_comm] using hU 0
      simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod N)) ((mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p:ℤ)≠0) hh).symm)
    · simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod N)) ((by simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,mul_comm] using (hU 1).symm : (p:ℤ)*U 1 0=γ 1 0))
  have ht := prime_integral_two_boundary (level N) k p hp F B hdet _ hg
    (primeBoundaryValue N p hp hc k F γ) (inversePrimeBoundaryValue N p hp hc k F γ) hs hl
  have hi : ((p:ℤ)∣B 0 0 ∧ (p:ℤ)∣B 1 0) ↔ (p:ℤ)∣γ 1 0 := by
    simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  simpa only [hi] using ht

theorem upper_cusp_boundary_two (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hc : p.Coprime N) (k : ℤ) (F : ModularForm (level N) k) (γ : SL(2,ℤ))
    (j : ℤ) :
    Tendsto ((F : ℍ → ℂ) ∣[k]
      (triangularGL 1 (j:ℝ) p (by norm_num) (by exact_mod_cast hp.pos) *
        SpecialLinearGroup.mapGL ℝ γ)) atImInfty
      (nhds (if (p:ℤ)∣γ 0 0+j*γ 1 0 then (p:ℂ)^(k-1)*inversePrimeBoundaryValue N p hp hc k F γ
        else (p:ℂ)⁻¹*primeBoundaryValue N p hp hc k F γ)) := by
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![1,j;0,(p:ℤ)]*γ.val
  have hdet : B.det=p := by
    change ( _ * γ.val).det = _
    rw [Matrix.det_mul,γ.property,mul_one]
    simp [Matrix.det_fin_two]
  have hg : (triangularGL 1 (j:ℝ) p (by norm_num) (by exact_mod_cast hp.pos) *
      SpecialLinearGroup.mapGL ℝ γ).val = B.map (Int.castRingHom ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [B,triangularGL,GeneralLinearGroup.mkOfDetNeZero,
        SpecialLinearGroup.mapGL,SpecialLinearGroup.map,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  have hs : ∀ U : SL(2,ℤ), (∀ i : Fin 2, B i 0=U i 0) →
      cuspBoundary (level N) k F U=primeBoundaryValue N p hp hc k F γ := by
    intro U hU
    apply boundary_prime_value_of_upper N p hp hc k F γ U j
    · simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod N)) ((by simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using (hU 0).symm : U 0 0=γ 0 0+j*γ 1 0))
    · simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod N)) ((by simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using (hU 1).symm : U 1 0=(p:ℤ)*γ 1 0))
  have hl : ∀ U : SL(2,ℤ), (∀ i : Fin 2, B i 0=U i 0*(p:ℤ)) →
      cuspBoundary (level N) k F U=inversePrimeBoundaryValue N p hp hc k F γ := by
    intro U hU
    apply boundary_inverse_value_of_upper N p hp hc k F γ U j
    · simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod N)) ((by simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,mul_comm] using (hU 0).symm : (p:ℤ)*U 0 0=γ 0 0+j*γ 1 0))
    · have hh : (p:ℤ)*γ 1 0=(p:ℤ)*U 1 0 := by
        simpa [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,mul_comm] using hU 1
      simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod N)) ((mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p:ℤ)≠0) hh).symm)
  have ht := prime_integral_two_boundary (level N) k p hp F B hdet _ hg
    (primeBoundaryValue N p hp hc k F γ) (inversePrimeBoundaryValue N p hp hc k F γ) hs hl
  have hi : ((p:ℤ)∣B 0 0 ∧ (p:ℤ)∣B 1 0) ↔ (p:ℤ)∣γ 0 0+j*γ 1 0 := by
    simp [B,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  simpa only [hi] using ht

#print axioms dilation_cusp_boundary_two
#print axioms upper_cusp_boundary_two

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryHeckeActionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant
open QuantitativeArithmeticSmallLevelCirc
open scoped MatrixGroups ModularForm

theorem goodHecke_two_cusp_limit (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hgood : ¬p∣N) (k : ℤ) (F : ModularForm (level N) k) (γ : SL(2,ℤ)) :
    Tendsto ((ModularHecke.dilationTrace N p hp.pos k F : ℍ → ℂ) ∣[k] γ)
      atImInfty (nhds (primeBoundaryValue N p hp (hp.coprime_iff_not_dvd.mpr hgood) k F γ+
        (p:ℂ)^(k-1)*inversePrimeBoundaryValue N p hp (hp.coprime_iff_not_dvd.mpr hgood) k F γ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hgood
  have hAB : (p:ℤ)*Nat.gcdA p N+(N:ℤ)*Nat.gcdB p N=1 := by
    have hh := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one,Nat.cast_one] at hh
    exact hh.symm
  rw [ModularHecke.dilationTrace_prime_slash N p (NeZero.pos N) hgood
    (Nat.gcdA p N) (Nat.gcdB p N) hAB k F]
  simp only [SlashAction.add_slash,SlashAction.sum_slash,ModularForm.SL_slash,
    ← SlashAction.slash_mul]
  have hd := dilation_cusp_boundary_two N p hp hc k F γ
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin p)) (fun j _ ↦
    upper_cusp_boundary_two N p hp hc k F γ (j.val:ℤ))
  have ht := hd.add hs
  have hweight := integral_hecke_weights p hp γ
    ((p:ℂ)^(k-1)*inversePrimeBoundaryValue N p hp hc k F γ)
    ((p:ℂ)⁻¹*primeBoundaryValue N p hp hc k F γ)
  have hpC : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [← mul_assoc,mul_inv_cancel₀ hpC,one_mul] at hweight
  have hweight := hweight.trans (add_comm _ _)
  rw [hweight] at ht
  convert ht using 1
  ext z
  simp only [Pi.add_apply,Finset.sum_apply,SpecialLinearGroup.mapGL,
    MonoidHom.comp_apply,Int.cast_natCast]
  rfl

/-- Actual good-prime Hecke action on every cusp constant, without an
Eisenstein classification hypothesis. -/
theorem cuspBoundary_goodHecke_two (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hgood : ¬p∣N) (k : ℤ) (F : ModularForm (level N) k) (γ : SL(2,ℤ)) :
    cuspBoundary (level N) k (ModularHecke.dilationTrace N p hp.pos k F) γ =
      primeBoundaryValue N p hp (hp.coprime_iff_not_dvd.mpr hgood) k F γ+
        (p:ℂ)^(k-1)*inversePrimeBoundaryValue N p hp (hp.coprime_iff_not_dvd.mpr hgood) k F γ :=
  (goodHecke_two_cusp_limit N p hp hgood k F γ).limUnder_eq

/-- The finite boundary map intertwines the actual good Hecke operator with
the sum of a finite permutation and its weighted inverse. -/
theorem finiteCuspBoundary_goodHecke (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hgood : ¬p∣N) (k : ℤ) (F : ModularForm (level N) k) (v : boundaryLabels N) :
    finiteCuspBoundary (level N) k N (ModularHecke.dilationTrace N p hp.pos k F) v =
      finiteCuspBoundary (level N) k N F (boundaryPrimePerm N p hp (hp.coprime_iff_not_dvd.mpr hgood) v)+
      (p:ℂ)^(k-1)*finiteCuspBoundary (level N) k N F
        ((boundaryPrimePerm N p hp (hp.coprime_iff_not_dvd.mpr hgood)).symm v) := by
  have h := cuspBoundary_goodHecke_two N p hp hgood k F (boundaryRepresentative N v)
  have hv : cuspLabel N (boundaryRepresentative N v)=v := by
    apply Subtype.ext
    exact boundaryRepresentative_column N v
  simpa only [finiteCuspBoundary,primeBoundaryValue,inversePrimeBoundaryValue,hv,
    LinearMap.coe_mk,AddHom.coe_mk] using h

#print axioms goodHecke_two_cusp_limit
#print axioms cuspBoundary_goodHecke_two
#print axioms finiteCuspBoundary_goodHecke

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundaryHeckeScalarV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open Matrix UpperHalfPlane Filter AsymptoticClassicalDiscriminant
open QuantitativeArithmeticSmallLevelCirc
open scoped MatrixGroups ModularForm

theorem goodHecke_cusp_limit (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hgood : ¬p∣N) (hpN : (p : ZMod N)=1) (k : ℤ)
    (F : ModularForm (level N) k) (γ : SL(2,ℤ)) :
    Tendsto ((ModularHecke.dilationTrace N p hp.pos k F : ℍ → ℂ) ∣[k] γ)
      atImInfty (nhds ((1+(p:ℂ)^(k-1))*cuspBoundary (level N) k F γ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : p.Coprime N := hp.coprime_iff_not_dvd.mpr hgood
  have hAB : (p:ℤ)*Nat.gcdA p N+(N:ℤ)*Nat.gcdB p N=1 := by
    have hh := Nat.gcd_eq_gcd_ab p N
    rw [hc.gcd_eq_one,Nat.cast_one] at hh
    exact hh.symm
  rw [ModularHecke.dilationTrace_prime_slash N p (NeZero.pos N) hgood
    (Nat.gcdA p N) (Nat.gcdB p N) hAB k F]
  simp only [SlashAction.add_slash,SlashAction.sum_slash,ModularForm.SL_slash,
    ← SlashAction.slash_mul]
  have hd := dilation_cusp_boundary N p hp hpN k F γ
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin p)) (fun j _ ↦
    upper_cusp_boundary N p hp hpN k F γ (j.val:ℤ))
  have ht := hd.add hs
  have hweight :
      (if (p:ℤ)∣γ 1 0 then (p:ℂ)^(k-1) else (p:ℂ)⁻¹)*cuspBoundary (level N) k F γ +
      (∑ j : Fin p, (if (p:ℤ)∣γ 0 0+(j.val:ℤ)*γ 1 0 then (p:ℂ)^(k-1) else (p:ℂ)⁻¹)*
        cuspBoundary (level N) k F γ) =
      (1+(p:ℂ)^(k-1))*cuspBoundary (level N) k F γ := by
    rw [← Finset.sum_mul,← add_mul,prime_boundary_weights p hp γ k]
  rw [hweight] at ht
  convert ht using 1
  ext z
  simp only [Pi.add_apply, Finset.sum_apply, SpecialLinearGroup.mapGL,
    MonoidHom.comp_apply, Int.cast_natCast]
  rfl

/-- At p=1 mod N the genuine good Hecke operator acts on all cusp
constants by the single scalar 1+p^(k-1). No Eisenstein classification or
boundary-image surjectivity is used, so this also applies in weight two. -/
theorem cuspBoundary_goodHecke_scalar (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hgood : ¬p∣N) (hpN : (p : ZMod N)=1) (k : ℤ)
    (F : ModularForm (level N) k) (γ : SL(2,ℤ)) :
    cuspBoundary (level N) k (ModularHecke.dilationTrace N p hp.pos k F) γ =
      (1+(p:ℂ)^(k-1))*cuspBoundary (level N) k F γ :=
  (goodHecke_cusp_limit N p hp hgood hpN k F γ).limUnder_eq

theorem goodHecke_boundary_defect_cuspidal (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hgood : ¬p∣N) (hpN : (p : ZMod N)=1) (k : ℤ)
    (F : ModularForm (level N) k) :
    (1+(p:ℂ)^(k-1)) • F - ModularHecke.dilationTrace N p hp.pos k F ∈
      ModularForm.cuspFormSubmodule (level N) k := by
  rw [← cuspBoundary_ker (level N) k,LinearMap.mem_ker]
  ext γ
  simp only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [cuspBoundary_goodHecke_scalar N p hp hgood hpN]
  exact sub_self _

#print axioms goodHecke_cusp_limit
#print axioms cuspBoundary_goodHecke_scalar
#print axioms goodHecke_boundary_defect_cuspidal

end QuantitativeArithmeticSmallLevelEisenstein
end
end

/-! ## QuantitativeArithmeticSmallLevelEisensteinBoundarySplitV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEisenstein

open QuantitativeArithmeticSmallLevelCirc
open QuantitativeArithmeticSmallLevelCirc.CuspSpectral

/-- Canonical cusp/Eisenstein splitting inside the actual trace-new space.
The Eisenstein summand here is defined spectrally, without assuming a
classification of Eisenstein series or boundary surjectivity. -/
theorem circ_boundary_split (N p m : ℕ) [NeZero N]
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hpN : (p : ZMod N) = 1) (hm : 0 < m)
    (F : space N hN (2 * m)) :
    ∃ G : cuspCorner N (2 * m) hN, ∃ E : space N hN (2 * m),
      F.val = CuspForm.toModularFormₗ G.val + E.val ∧
      ModularHecke.dilationTrace N p hp.pos ((2 * m : ℕ) : ℤ) E.val =
        (1 + (p : ℂ)^(2 * m - 1)) • E.val := by
  have hcast : ((2 * m - 1 : ℕ) : ℤ) = ((2 * m : ℕ) : ℤ) - 1 := by
    omega
  have hpow : (p : ℂ)^(((2 * m : ℕ) : ℤ) - 1) = (p : ℂ)^(2 * m - 1) := by
    rw [← hcast, zpow_natCast]
  have hcus := goodHecke_boundary_defect_cuspidal N p hp hgood hpN
    ((2 * m : ℕ) : ℤ) F.val
  rw [hpow] at hcus
  obtain ⟨H, hH⟩ := hcus
  apply split_of_cuspidal_defect N p m hN hp hgood hm F H
  exact hH.symm

#print axioms circ_boundary_split

end QuantitativeArithmeticSmallLevelEisenstein
end
end
