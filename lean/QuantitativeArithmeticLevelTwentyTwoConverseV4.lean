module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import QuantitativeArithmeticPrimePowerTorsionV1
public import QuantitativeArithmeticQuadraticFiveFourierV1
public import QuantitativeArithmeticQuadraticTwistInversionTheoryV4
public import QuantitativeArithmeticQuadraticTwistQuotientOrderV1
public import QuantitativeArithmeticQuadraticTwistReflectionTheoryV4
public import QuantitativeArithmeticRectangularContinuationTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyTwoTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyTwoGridSourceFourierV1
public import QuantitativeArithmeticSmallLevelTwentyTwoHeckeV1
public import QuantitativeArithmeticSmallLevelTwentyTwoPoleLocusV1
public import QuantitativeArithmeticSmallLevelTwentyTwoReflectionLawsV1
public import SmallLevelAdditiveTheoryV4
public import SmallLevelAllowedSimplePoleTailV1
public import SmallLevelContinuationTheoryV4
public import SmallLevelTaylorTheoryV4
public import SmallLevelExchangedFrickePairV1
public import SmallLevelSimplePoleTaylorTheoryV4
public import SmallLevelModularCriterionV1
public import SmallLevelPoleGridTheoryV4
public import SmallLevelRamanujanReflectionOrderV1
public import SmallLevelRegularPoleTailV1
public import SmallLevelRegularTailBlockKernelV1
public import SmallLevelRegularizedShiftBlockV1
public import SmallLevelRegularizedShiftKernelV1
public import SmallLevelSelectedRegularFirstShiftV1
public import SmallLevelTaylorRowCoefficientsV1
public import SmallLevelPrimeRatesTheoryV4
public import SmallLevelTwentyOneKnownWordsTheoryV4
public import SmallLevelTwentyTwoFirstJetAlgebraV1
public import SmallLevelTwentyTwoJetBlockTheoryV4
public import SmallLevelTwentyTwoLaurentTheoryV4
public import SmallLevelTwentyTwoTriangularTheoryV4
public import SmallLevelUniversalFactoredFirstShiftV1
public import SmallLevelUniversalHigherPoleVectorV1
public import SmallLevelUniversalPoleDetectionV1
public import SmallLevelUniversalRegularTailLeadingV1

/-! Consolidated converse argument. Large exact certificates remain
in their own modules; declarations and proof bodies are preserved. -/

/-! ## TwentyTwoGenerators -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

theorem edgeS_checked (g : SL(2,ZMod 22)) :
    rep g*ModularGroup.S*(rep (g*reduction 22 ModularGroup.S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 22 ModularGroup.S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 22 ModularGroup.S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 22)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 22)) :
    rep g*T*(rep (g*reduction 22 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 22 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 22 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 22)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 22)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 22, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 14, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 22) : γ∈K := by
  apply transversal_mem (reduction 22) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hK hZ _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hK hZ _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edgeSRow_checked
#print axioms edgeTRow_checked
#print axioms gamma0_mem

end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoGridSourceTaylor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set
open scoped MatrixGroups ModularForm

def gridSourceSign (δ η : ℂ) (i : Fin 8) : ℂ :=
  if i.val<3 then η else if i.val=3 then 1 else δ

def gridSourceRate (i : Fin 8) (j : ℝ) : ℝ :=
  (((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ))^2/(gridSourceDet i)

def gridSourceDerivative (i : Fin 8) (j : ℝ) : ℝ :=
  ((gridSourceRaw i) 1 0:ℝ)*(((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ))/(gridSourceDet i)

def gridSourcePartner (i : Fin 8) (j : ℝ) : ℝ :=
  (((gridSourceRaw i) 0 0:ℝ)*j+((gridSourceRaw i) 0 1:ℝ))/
    (((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ))

/-- The raw eight-matrix system, with a prescribed original Fricke sign.
The sign can consequently be shared with the Ramanujan Taylor system. -/
theorem grid_source_taylor_of_fricke (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 22 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (i : Fin 8) (j : ℝ)
    (hj : ((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ)≠0) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        original (2*m) f j s-gridSourceSign (root 22 f 2) η i*
          (gridSourceRate i j:ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*(gridSourceDerivative i j:ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            original (2*m) f (gridSourcePartner i j) (s+(n:ℂ))) = error M s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hw:=grid_words_of_fricke m hf hη hW
  have hF:=grid_source_fourier
    (gridWordSign_unit (root_unit hf.toEulerData 2) hη (gridSourceWord i))
    (hw (gridSourceWord i))
  simp only [gridSource_sign] at hF
  have hC : ((gridSourceRaw i) 1 0:ℝ)≠0 := by
    fin_cases i <;> norm_num [gridSourceRaw]
  have hd : ((gridSourceRaw i) 0 0:ℝ)*((gridSourceRaw i) 1 1:ℝ)-
      ((gridSourceRaw i) 0 1:ℝ)*((gridSourceRaw i) 1 0:ℝ)=(gridSourceDet i:ℝ) := by
    have hh:=gridSourceRaw_det i
    rw [det_fin_two] at hh
    exact_mod_cast hh
  have hh:=QuantitativeArithmeticTwoSequenceTaylor.matrix_even_rows
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m)) m
    ((gridSourceRaw i) 0 0) ((gridSourceRaw i) 0 1) ((gridSourceRaw i) 1 0)
    ((gridSourceRaw i) 1 1) j hC (by rw [hd]; exact_mod_cast gridSourceDet_pos i) hj
    (gridSourceSign (root 22 f 2) η i) (by
      intro z hz
      simpa only [hd,Complex.ofReal_natCast,Complex.ofReal_intCast,gridSourceSign] using hF z hz)
  simpa only [hd,gridSourceRate,gridSourceDerivative,gridSourcePartner,original] using hh

/-- Every selected matrix row comes from the original Euler solution;
there is no continuation hypothesis on any additive twist. -/
theorem original_grid_source_taylor (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 22 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ i : Fin 8, ∀ j : ℝ,
      ((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ)≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          original (2*m) f j s-gridSourceSign (root 22 f 2) η i*
            (gridSourceRate i j:ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (Complex.I*(gridSourceDerivative i j:ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              original (2*m) f (gridSourcePartner i j) (s+(n:ℂ))) = error M s := by
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<22) m hf
  exact ⟨η,hη,fun i j hj => grid_source_taylor_of_fricke m hf hη hW i j hj⟩

#print axioms grid_source_taylor_of_fricke
#print axioms original_grid_source_taylor
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoGridGeometry -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix SmallLevelAdditive

def gridGroupSource : Fin 35 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 4
  | 11 => 5
  | 12 => 5
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 3
  | 18 => 3
  | 19 => 5
  | 20 => 6
  | 21 => 6
  | 22 => 6
  | 23 => 6
  | 24 => 6
  | 25 => 6
  | 26 => 6
  | 27 => 6
  | 28 => 7
  | 29 => 7
  | 30 => 7
  | 31 => 7
  | 32 => 7
  | 33 => 7
  | _ => 7

def gridGroupIndex : Fin 35 → Fin 66
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 65
  | 4 => 30
  | 5 => 33
  | 6 => 33
  | 7 => 2
  | 8 => 6
  | 9 => 33
  | 10 => 34
  | 11 => 32
  | 12 => 36
  | 13 => 9
  | 14 => 11
  | 15 => 18
  | 16 => 22
  | 17 => 54
  | 18 => 62
  | 19 => 35
  | 20 => 18
  | 21 => 27
  | 22 => 37
  | 23 => 38
  | 24 => 39
  | 25 => 42
  | 26 => 45
  | 27 => 54
  | 28 => 12
  | 29 => 21
  | 30 => 24
  | 31 => 28
  | 32 => 29
  | 33 => 31
  | _ => 48

def gridGroupPartner : Fin 35 → ℤ
  | 0 => -3
  | 1 => -198
  | 2 => -66
  | 3 => 198
  | 4 => -1
  | 5 => 0
  | 6 => -2
  | 7 => -99
  | 8 => -33
  | 9 => -6
  | 10 => -3
  | 11 => -1
  | 12 => -3
  | 13 => -22
  | 14 => -18
  | 15 => -11
  | 16 => -9
  | 17 => 4
  | 18 => 12
  | 19 => -4
  | 20 => -5
  | 21 => -4
  | 22 => -24
  | 23 => -15
  | 24 => -12
  | 25 => -9
  | 26 => -8
  | 27 => -7
  | 28 => 7
  | 29 => 8
  | 30 => 9
  | 31 => 15
  | 32 => 24
  | 33 => -12
  | _ => 5

def gridGroupTarget : Fin 35 → Fin 66
  | 0 => 63
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 65
  | 5 => 0
  | 6 => 64
  | 7 => 33
  | 8 => 33
  | 9 => 60
  | 10 => 63
  | 11 => 65
  | 12 => 63
  | 13 => 44
  | 14 => 48
  | 15 => 55
  | 16 => 57
  | 17 => 4
  | 18 => 12
  | 19 => 62
  | 20 => 61
  | 21 => 62
  | 22 => 42
  | 23 => 51
  | 24 => 54
  | 25 => 57
  | 26 => 58
  | 27 => 59
  | 28 => 7
  | 29 => 8
  | 30 => 9
  | 31 => 15
  | 32 => 24
  | 33 => 54
  | _ => 5

def gridGroupRate : Fin 35 → ℚ
  | 0 => 22
  | 1 => (1/198)
  | 2 => (1/22)
  | 3 => (1/198)
  | 4 => 18
  | 5 => (1/2)
  | 6 => (99/2)
  | 7 => (2/99)
  | 8 => (2/11)
  | 9 => (11/2)
  | 10 => (2/9)
  | 11 => 2
  | 12 => 2
  | 13 => (9/22)
  | 14 => (11/18)
  | 15 => (18/11)
  | 16 => (22/9)
  | 17 => 9
  | 18 => (1/9)
  | 19 => (1/2)
  | 20 => 18
  | 21 => (9/2)
  | 22 => (1/18)
  | 23 => (2/9)
  | 24 => (1/2)
  | 25 => 2
  | 26 => (9/2)
  | 27 => 18
  | 28 => 18
  | 29 => (9/2)
  | 30 => 2
  | 31 => (2/9)
  | 32 => (1/18)
  | 33 => (1/18)
  | _ => 18

def gridGroupDerivative : Fin 35 → ℚ
  | 0 => 22
  | 1 => (1/3)
  | 2 => 1
  | 3 => (-1/3)
  | 4 => -330
  | 5 => -55
  | 6 => 33
  | 7 => (2/3)
  | 8 => 2
  | 9 => 11
  | 10 => (110/3)
  | 11 => -66
  | 12 => 66
  | 13 => 3
  | 14 => (11/3)
  | 15 => 6
  | 16 => (22/3)
  | 17 => -66
  | 18 => (-22/3)
  | 19 => 33
  | 20 => -66
  | 21 => -33
  | 22 => (11/3)
  | 23 => (22/3)
  | 24 => 11
  | 25 => 22
  | 26 => 33
  | 27 => 66
  | 28 => -66
  | 29 => -33
  | 30 => -22
  | 31 => (-22/3)
  | 32 => (-11/3)
  | 33 => (11/3)
  | _ => 66

theorem gridGroup_geometry (i : Fin 35) :
    ((gridSourceRaw (gridGroupSource i)) 1 0:ℝ)*((gridGroupIndex i:ℕ):ℝ)/66+
      ((gridSourceRaw (gridGroupSource i)) 1 1:ℝ)≠0 ∧
    gridSourcePartner (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/66)=
      (gridGroupPartner i:ℝ)/66 ∧
    gridSourceRate (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/66)=(gridGroupRate i:ℝ) ∧
    gridSourceDerivative (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/66)=(gridGroupDerivative i:ℝ) := by
  fin_cases i <;> norm_num [gridGroupSource,gridGroupIndex,gridGroupPartner,
    gridGroupRate,gridGroupDerivative,gridSourcePartner,gridSourceRate,gridSourceDerivative,
    gridSourceRaw,gridSourceDet]

theorem gridGroup_target_mod (i : Fin 35) :
    gridGroupPartner i%66=((gridGroupTarget i:ℕ):ℤ) := by
  fin_cases i <;> decide

theorem gridGroup_rate_pos (i : Fin 35) : 0<gridGroupRate i := by
  fin_cases i <;> norm_num [gridGroupRate]

theorem gridGroup_partner_transform (k : ℕ) (f : ℕ→ℂ) (i : Fin 35) (s : ℂ) :
    original k f (gridSourcePartner (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/66)) s=
      grid k f 66 ((gridGroupTarget i:ℕ):ℤ) s := by
  rw [(gridGroup_geometry i).2.1]
  change grid k f 66 (gridGroupPartner i) s=_
  rw [← grid_mod k f (by decide : 0<66)]
  norm_num only [Nat.cast_ofNat]
  rw [gridGroup_target_mod]

#print axioms gridGroup_geometry
#print axioms gridGroup_partner_transform
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoGridMatrixRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessNormalizedTwistProduct
open SmallLevelAdditive Complex Set
open scoped MatrixGroups ModularForm

def gridMatrixScalar (m : ℕ) (δ η : ℂ) (i : Fin 35) (n : ℕ) (s : ℂ) : ℂ :=
  gridSourceSign δ η (gridGroupSource i)*(gridGroupRate i:ℂ)^(s-(m:ℂ))*
    (Complex.I*(gridGroupDerivative i:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

/-- The 35 selected matrix rows of the actual closed 66-grid system.
The leading term and every positive shift use the same grid coordinate. -/
theorem grid_matrix_rows_of_fricke (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 22 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (i : Fin 35) :
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        grid (2*m) f 66 ((gridGroupIndex i:ℕ):ℤ) s-
          gridMatrixScalar m (root 22 f 2) η i 0 s*
            grid (2*m) f 66 ((gridGroupTarget i:ℕ):ℤ) s=
        error M s+∑ n∈Finset.range M,gridMatrixScalar m (root 22 f 2) η i (n+1) s*
          grid (2*m) f 66 ((gridGroupTarget i:ℕ):ℤ) (s+((n:ℂ)+1)) := by
  obtain ⟨B,error,hrows⟩:=grid_source_taylor_of_fricke m hf hη hW
    (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/66) (by
      simpa only [mul_div_assoc] using (gridGroup_geometry i).1)
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  refine ⟨?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_one] using (hrows (M+1)).1
  intro s hs
  have hh:=(hrows (M+1)).2 s hs
  simp_rw [gridGroup_partner_transform] at hh
  rw [(gridGroup_geometry i).2.2.1,(gridGroup_geometry i).2.2.2,
    Finset.sum_range_succ'] at hh
  simp only [Complex.ofReal_ratCast,Nat.cast_zero,add_zero,pow_zero,
    Ring.choose_zero_right,one_mul,Nat.cast_add,Nat.cast_one] at hh
  simp only [gridMatrixScalar,Nat.cast_zero,add_zero,pow_zero,
    Ring.choose_zero_right,mul_one,Nat.cast_add,Nat.cast_one]
  rw [mul_add,Finset.mul_sum] at hh
  simp only [← mul_assoc] at hh
  simp only [grid,Int.cast_natCast,Nat.cast_ofNat] at hh ⊢
  linear_combination hh

/-- The chosen 35 matrix rows hold for original solutions, with a single
sign and with no assumptions on any additive continuation. -/
theorem original_grid_matrix_rows (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 22 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ i : Fin 35,
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        grid (2*m) f 66 ((gridGroupIndex i:ℕ):ℤ) s-
          gridMatrixScalar m (root 22 f 2) η i 0 s*
            grid (2*m) f 66 ((gridGroupTarget i:ℕ):ℤ) s=
        error M s+∑ n∈Finset.range M,gridMatrixScalar m (root 22 f 2) η i (n+1) s*
          grid (2*m) f 66 ((gridGroupTarget i:ℕ):ℤ) (s+((n:ℂ)+1)) := by
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<22) m hf
  exact ⟨η,hη,grid_matrix_rows_of_fricke m hf hη hW⟩

#print axioms grid_matrix_rows_of_fricke
#print axioms original_grid_matrix_rows
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoGridAuxiliary -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive

def gridEntireSpecs : Fin 4→ℕ := ![1,3,6,11]

theorem gridEntireSpecs_valid : ∀ i : Fin 4, 0<gridEntireSpecs i ∧ gridEntireSpecs i∣66 := by decide

theorem original_grid_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 k f) :
    (∀ i : Fin 4, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 22 k f (gridEntireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 4, ∀ s : ℂ, B<s.re →
        ramanujanEntire 22 k f (gridEntireSpecs i) s=gridSum k f 66 (gridEntireSpecs i) 0 s := by
  have hh (i : Fin 4):=original_ramanujan_entire (by decide : 0<22) hk hf (gridEntireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
    rw [hb i s (lt_of_le_of_lt hbi hs)]
    have hg:=ramanujanAdditive_grid k f (by decide : 0<66)
      (gridEntireSpecs_valid i).1 (gridEntireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

def gridHeckeTwo (m : ℕ) (f : ℕ→ℂ) (j : ℤ) (s : ℂ) : ℂ :=
  grid (2*m) f 66 j s+grid (2*m) f 66 (j+33) s-
    heckeScalar m f s*grid (2*m) f 66 (2*j) s

def gridHeckeThree (m : ℕ) (f : ℕ→ℂ) (j : ℤ) (s : ℂ) : ℂ :=
  grid (2*m) f 66 j s+grid (2*m) f 66 (j+22) s+grid (2*m) f 66 (j+44) s-
    ((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s)*grid (2*m) f 66 (3*j) s+
    ((3:ℂ)^((m:ℂ)-s))^2*grid (2*m) f 66 (9*j) s

theorem original_grid_hecke_two {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re → gridHeckeTwo m f j s=0 := by
  obtain ⟨B,hB⟩:=original_ramified_row m hm hf
  refine ⟨B,?_⟩
  intro j s hs
  have hh:=hB ((j:ℝ)/66) s hs
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    Nat.cast_one,Nat.cast_ofNat,zero_div,add_zero] at hh
  have h1 : (j:ℝ)/66+1/2=((j+33:ℤ):ℝ)/66 := by push_cast; ring
  have h2 : 2*((j:ℝ)/66)=((2*j:ℤ):ℝ)/66 := by push_cast; ring
  rw [h1,h2] at hh
  exact sub_eq_zero.mpr hh

theorem original_grid_hecke_three {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re → gridHeckeThree m f j s=0 := by
  obtain ⟨B,hB⟩:=normalized_additive_hecke hf (by decide : Nat.Prime 3) (by decide : ¬3∣22)
  refine ⟨B,?_⟩
  intro j s hs
  have hh:=hB ((j:ℝ)/66) s hs
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    Nat.cast_one,Nat.cast_ofNat,zero_div,add_zero] at hh
  have h1 : (j:ℝ)/66+1/3=((j+22:ℤ):ℝ)/66 := by push_cast; ring
  have h2 : (j:ℝ)/66+2/3=((j+44:ℤ):ℝ)/66 := by push_cast; ring
  have h3 : 3*((j:ℝ)/66)=((3*j:ℤ):ℝ)/66 := by push_cast; ring
  have h9 : (9:ℝ)*((j:ℝ)/66)=((9*j:ℤ):ℝ)/66 := by push_cast; ring
  rw [h1,h2,h3,h9] at hh
  exact hh

def gridHeckeSpecs : Fin 16→ℕ×ℤ :=
  ![(2,9),(2,15),(2,16),(2,17),(2,18),(2,5),(2,4),(3,7),
    (3,4),(2,13),(2,26),(2,19),(3,5),(2,7),(2,8),(2,14)]

def gridHeckeRow (m : ℕ) (f : ℕ→ℂ) (i : Fin 16) (s : ℂ) : ℂ :=
  if (gridHeckeSpecs i).1=2 then gridHeckeTwo m f (gridHeckeSpecs i).2 s
  else gridHeckeThree m f (gridHeckeSpecs i).2 s

theorem original_grid_hecke_rows {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ B : ℝ, ∀ i : Fin 16, ∀ s : ℂ, B<s.re → gridHeckeRow m f i s=0 := by
  obtain ⟨B₂,h₂⟩:=original_grid_hecke_two hm hf
  obtain ⟨B₃,h₃⟩:=original_grid_hecke_three hf
  refine ⟨max B₂ B₃,?_⟩
  intro i s hs
  unfold gridHeckeRow
  split
  · exact h₂ _ s (lt_of_le_of_lt (le_max_left _ _) hs)
  · exact h₃ _ s (lt_of_le_of_lt (le_max_right _ _) hs)

#print axioms original_grid_entire_rows
#print axioms original_grid_hecke_two
#print axioms original_grid_hecke_three
#print axioms original_grid_hecke_rows
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoGridCoherentFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct FinitenessRamanujanFourier
open SmallLevelAdditive SmallLevelTaylor Complex Set MeasureTheory
open scoped MatrixGroups ModularForm

/-- Literal coherent physical laws, supplied for every original solution. -/
def GridFrickeLaws (k : ℕ) (f : ℕ→ℂ) (ε : ℂ) : Prop :=
  ∀ q : ℕ, 0<q → ∀ z : ℂ, 0<z.im →
    FinitenessAnalyticReconstruction.twist (fourier (fullCoefficients f k)) q z=
      (root 22 f q*ε*Complex.I^k)/(((Real.sqrt (Nat.lcm 22 (q^2)):ℂ)*z)^k)*
        FinitenessAnalyticReconstruction.twist (fourier (fullCoefficients f k)) q
          (-1/((Nat.lcm 22 (q^2):ℕ)*z))

theorem original_grid_fricke_laws {k : ℕ} {f : ℕ→ℂ} (hf : IsSolution 22 k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ GridFrickeLaws k f ε :=
  FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<22) hf

theorem grid_physical_sign (m : ℕ) {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    ε*Complex.I^(2*m)=1 ∨ ε*Complex.I^(2*m)= -1 := by
  have hi : Complex.I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,Complex.I_sq]
  rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [hi,h]

theorem grid_fricke_of_laws (m : ℕ) {f : ℕ→ℂ} {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      (ε*Complex.I^(2*m)) • SmallLevelOriginal.fourierFunction (2*m) f := by
  have h:=fricke_law 22 (2*m) (by decide)
    (fourier (fullCoefficients f (2*m))) (ε*Complex.I^(2*m)) (by
      intro z hz
      simpa [root,FinitenessAnalyticReconstruction.twist,Finset.sum_range_succ] using hlaw 1 (by decide) z hz)
  change SmallLevelOriginal.fourierFunction (2*m) f=(ε*Complex.I^(2*m)) •
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W) at h
  rcases grid_physical_sign m hε with hc|hc
  · rw [hc] at h ⊢; simpa using h.symm
  · rw [hc] at h ⊢
    simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm

/-- All-order Ramanujan Taylor rows retain the explicitly supplied coherent
sign, so their sign cannot be chosen independently of the matrix rows. -/
theorem grid_twisted_taylor_of_laws (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 22 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (q : ℕ) (hq : 0<q) (r : ℝ) (hr : r≠0) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 22 (q^2)) r (root 22 f q*ε*Complex.I^(2*m)) M))
        {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        transform (fullCoefficients (twisted f q) (2*m)) r s-
          (root 22 f q*ε*Complex.I^(2*m))*
            (((Nat.lcm 22 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-(((2*m:ℕ):ℂ)/2))*
            normalizedTaylorSum (2*m) (fullCoefficients (twisted f q) (2*m))
              (Nat.lcm 22 (q^2)) r M s=
          mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
            (Nat.lcm 22 (q^2)) r (root 22 f q*ε*Complex.I^(2*m)) M) s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hL : 0<Nat.lcm 22 (q^2):=Nat.lcm_pos (by decide) (pow_pos hq _)
  apply normalized_taylor_mellin_rows (by exact_mod_cast hL) hr (2*m) (even_two_mul m)
    (polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) (2*m))
    (fullCoefficients_zero (twisted_zero hf.zero q) (2*m)) (root 22 f q*ε*Complex.I^(2*m))
  intro z hz
  have hreflect : 0<(-1/((Nat.lcm 22 (q^2):ℕ)*z)).im := by
    simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (Nat.lcm 22 (q^2):ℝ)) (by exact_mod_cast hL) hz
  simpa only [Complex.ofReal_natCast,fourier_twisted hf.zero hg q (2*m) hz,
    fourier_twisted hf.zero hg q (2*m) hreflect] using hlaw q hq z hz

theorem grid_ramanujan_taylor_of_laws (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 22 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (q : ℕ) (hq : 0<q) (r : ℝ) (hr : r≠0) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 22 (q^2)) r (root 22 f q*ε*Complex.I^(2*m)) M))
        {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        ramanujanAdditive (2*m) f q r s-
          (root 22 f q*ε*Complex.I^(2*m))*
            (((Nat.lcm 22 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-(((2*m:ℕ):ℂ)/2))*
            ramanujanTaylorSum (2*m) f q (Nat.lcm 22 (q^2)) r M s=
          mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
            (Nat.lcm 22 (q^2)) r (root 22 f q*ε*Complex.I^(2*m)) M) s := by
  obtain ⟨B,hB⟩:=grid_twisted_taylor_of_laws m hf hlaw q hq r hr
  obtain ⟨C,hC⟩:=ramanujan_additive_sum hf q
  refine ⟨max B C,?_⟩
  intro M
  constructor
  · intro s hs
    apply (hB M).1 s
    change max B C-(M:ℝ)<s.re at hs
    change B-(M:ℝ)<s.re
    linarith [le_max_left B C]
  · intro s hs
    have hsB : B<s.re:=lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : C<s.re:=lt_of_le_of_lt (le_max_right _ _) hs
    have hm:=(hB M).2 s hsB
    rw [hC r s hsC] at hm
    have he : normalizedTaylorSum (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 22 (q^2)) r M s=ramanujanTaylorSum (2*m) f q (Nat.lcm 22 (q^2)) r M s := by
      unfold normalizedTaylorSum ramanujanTaylorSum ramanujanAdditive
      apply Finset.sum_congr rfl
      intro n _
      rw [hC _ (s+(n:ℂ)) (by
        simp only [Complex.add_re,Complex.natCast_re]
        exact lt_of_lt_of_le hsC (le_add_of_nonneg_right (Nat.cast_nonneg n)))]
    rw [he] at hm
    exact hm

#print axioms original_grid_fricke_laws
#print axioms grid_fricke_of_laws
#print axioms grid_ramanujan_taylor_of_laws
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoGridRamanujan -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessNormalizedTwistProduct

def gridTaylorSpecs : Fin 11→ℕ×ℤ :=
  ![(3,2),(3,-2),(11,3),(6,-1),(6,1),(3,1),(3,-1),(11,1),(11,-2),(11,2),(11,-1)]
def gridTaylorQ (i : Fin 11) : ℕ := (gridTaylorSpecs i).1
def gridTaylorT (i : Fin 11) : ℤ := (gridTaylorSpecs i).2
def gridTaylorL (i : Fin 11) : ℕ := Nat.lcm 22 ((gridTaylorQ i)^2)
def gridTaylorD (i : Fin 11) : ℤ := (66:ℤ)^2/(gridTaylorL i:ℤ)
def gridTaylorPartner (i : Fin 11) : ℤ := -(gridTaylorD i/gridTaylorT i)

theorem gridTaylorSpecs_valid : ∀ i : Fin 11,
    0<gridTaylorQ i ∧ gridTaylorQ i∣66 ∧ gridTaylorT i≠0 ∧
      (gridTaylorL i:ℤ)*gridTaylorD i=(66:ℤ)^2 ∧ gridTaylorT i∣gridTaylorD i := by decide

def gridTaylorCoefficient (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 11) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar (2*m) (gridTaylorL i) ((gridTaylorT i:ℝ)/66)
    (root 22 f (gridTaylorQ i)*ε*I^(2*m)) n s

def gridTaylorError (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 11) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError (2*m) (fullCoefficients (twisted f (gridTaylorQ i)) (2*m))
    (gridTaylorL i) ((gridTaylorT i:ℝ)/66) (root 22 f (gridTaylorQ i)*ε*I^(2*m)) (M+1)) s

theorem grid_ramanujan_rows_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (i : Fin 11) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  have hv:=gridTaylorSpecs_valid i
  have hr : (gridTaylorT i:ℝ)/66≠0:=div_ne_zero (by exact_mod_cast hv.2.2.1) (by norm_num)
  have hL : 0<gridTaylorL i:=Nat.lcm_pos (by decide) (pow_pos hv.1 _)
  obtain ⟨B,hB⟩:=grid_ramanujan_taylor_of_laws m hf hlaw (gridTaylorQ i) hv.1 _ hr
  refine ⟨B,?_⟩
  intro M
  constructor
  · intro s hs
    unfold gridTaylorError gridTaylorL
    apply (hB (M+1)).1 s
    change B-((M+1:ℕ):ℝ)<s.re
    change B-((M:ℝ)+1)<s.re at hs
    simpa only [Nat.cast_add,Nat.cast_one] using hs
  · intro s hs
    have hm:=(hB (M+1)).2 s hs
    rw [ramanujanTaylorSum_split] at hm
    rw [show Nat.lcm 22 ((gridTaylorQ i)^2)=gridTaylorL i from rfl] at hm
    have htrans:=ramanujanAdditive_grid (2*m) f (by decide : 0<66) hv.1 hv.2.1 (gridTaylorT i) s
    norm_num only [Nat.cast_ofNat] at htrans
    rw [htrans] at hm
    have hp:=fricke_grid_partner (by decide : 0<66) hL hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
    norm_num only [Nat.cast_ofNat] at hp
    rw [hp] at hm
    have hgrid (t : ℤ) (w : ℂ) :
        ramanujanAdditive (2*m) f (gridTaylorQ i) ((t:ℝ)/66) w=
          ∑ j∈FinitenessRamanujanSum.residues (gridTaylorQ i),
            grid (2*m) f 66 (t+(j:ℤ)*(66/gridTaylorQ i:ℕ)) w := by
      simpa only [Nat.cast_ofNat] using
        ramanujanAdditive_grid (2*m) f (by decide : 0<66) hv.1 hv.2.1 t w
    simp_rw [hgrid] at hm
    simp only [Nat.cast_add,Nat.cast_one] at hm
    unfold gridTaylorCoefficient gridTaylorError gridTaylorPartner gridSum
    linear_combination hm

/-- All eleven Ramanujan rows share a half-plane and the specified sign. -/
theorem grid_ramanujan_system_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∀ i : Fin 11, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  choose b hb using grid_ramanujan_rows_of_laws m hf hlaw
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 11) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

#print axioms gridTaylorSpecs_valid
#print axioms grid_ramanujan_rows_of_laws
#print axioms grid_ramanujan_system_of_laws
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoGridAssembly -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Complex Matrix SmallLevelTaylor SmallLevelAdditive FinitenessRamanujanSum
open FinitenessNormalizedTwistProduct

/-- Block order: 35 matrix rows, 11 Ramanujan Taylor rows, four entire
Ramanujan rows, and sixteen exact Hecke rows. -/
def gridAssemble (G : Fin 35→ℂ) (T : Fin 11→ℂ) (R : Fin 4→ℂ) (H : Fin 16→ℂ)
    (i : Fin 66) : ℂ :=
  if hG : i.val<35 then G ⟨i.val,hG⟩
  else if hT : i.val<46 then T ⟨i.val-35,by omega⟩
  else if hR : i.val<50 then R ⟨i.val-46,by omega⟩
  else H ⟨i.val-50,by omega⟩

def gridIndex (t : ℤ) : Fin 66 :=
  ⟨(t%66).toNat,by have h:=Int.emod_lt_of_pos t (by decide : (0:ℤ)<66); omega⟩

def gridSample (q : ℕ) (t : ℤ) (w : Fin 66→ℂ) : ℂ :=
  ∑ j∈residues q,w (gridIndex (t+(j:ℤ)*(66/q:ℕ)))

def gridVector (k : ℕ) (f : ℕ→ℂ) (s : ℂ) : Fin 66→ℂ :=
  fun j => grid k f 66 (j:ℕ) s

theorem gridVector_index (k : ℕ) (f : ℕ→ℂ) (s : ℂ) (t : ℤ) :
    gridVector k f s (gridIndex t)=grid k f 66 t s := by
  unfold gridVector
  have he : ((gridIndex t).val:ℤ)=t%66:=Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [he]
  simpa only [Nat.cast_ofNat] using grid_mod k f (by decide : 0<66) t s

theorem gridSample_grid (k : ℕ) (f : ℕ→ℂ) (q : ℕ) (t : ℤ) (s : ℂ) :
    gridSample q t (gridVector k f s)=gridSum k f 66 q t s := by
  unfold gridSample gridSum
  simp_rw [gridVector_index]

theorem gridSample_add (q : ℕ) (t : ℤ) (w v : Fin 66→ℂ) :
    gridSample q t (w+v)=gridSample q t w+gridSample q t v := by
  simp [gridSample,Finset.sum_add_distrib]

theorem gridSample_smul (q : ℕ) (t : ℤ) (c : ℂ) (w : Fin 66→ℂ) :
    gridSample q t (c • w)=c*gridSample q t w := by
  simp [gridSample,Finset.mul_sum]

def gridGroupLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 66→ℂ) (i : Fin 35) : ℂ :=
  w (gridGroupIndex i)-gridMatrixScalar m (root 22 f 2) (ε*I^(2*m)) i 0 s*w (gridGroupTarget i)

def gridRamanujanLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 66→ℂ) (i : Fin 11) : ℂ :=
  gridSample (gridTaylorQ i) (gridTaylorT i) w-
    gridTaylorCoefficient m f ε i 0 s*gridSample (gridTaylorQ i) (gridTaylorPartner i) w

def gridHeckeLeading (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (w : Fin 66→ℂ) (i : Fin 16) : ℂ :=
  let j:=(gridHeckeSpecs i).2
  if (gridHeckeSpecs i).1=2 then
    w (gridIndex j)+w (gridIndex (j+33))-heckeScalar m f s*w (gridIndex (2*j))
  else w (gridIndex j)+w (gridIndex (j+22))+w (gridIndex (j+44))-
    ((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s)*w (gridIndex (3*j))+
    ((3:ℂ)^((m:ℂ)-s))^2*w (gridIndex (9*j))

def gridLeadingRows (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 66→ℂ) : Fin 66→ℂ :=
  gridAssemble (gridGroupLeading m f ε s w) (gridRamanujanLeading m f ε s w)
    (fun i => gridSample (gridEntireSpecs i) 0 w) (gridHeckeLeading m f s w)

def gridShiftRows (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (w : Fin 66→ℂ) : Fin 66→ℂ :=
  gridAssemble
    (fun i => gridMatrixScalar m (root 22 f 2) (ε*I^(2*m)) i (n+1) s*w (gridGroupTarget i))
    (fun i => gridTaylorCoefficient m f ε i (n+1) s*gridSample (gridTaylorQ i) (gridTaylorPartner i) w) 0 0

def gridLeadingLinear (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : (Fin 66→ℂ) →ₗ[ℂ] (Fin 66→ℂ) where
  toFun:=gridLeadingRows m f ε s
  map_add':=by
    intro w v
    funext i
    simp only [Pi.add_apply]
    unfold gridLeadingRows gridAssemble
    split_ifs <;> simp only [gridGroupLeading,gridRamanujanLeading,gridHeckeLeading,
      gridSample_add,Pi.add_apply]
    all_goals first | (solve | ring) | (split_ifs <;> ring)
  map_smul':=by
    intro c w
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    unfold gridLeadingRows gridAssemble
    split_ifs <;> simp only [gridGroupLeading,gridRamanujanLeading,gridHeckeLeading,
      gridSample_smul,Pi.smul_apply,smul_eq_mul]
    all_goals first | (solve | ring) | (split_ifs <;> ring)

def gridShiftLinear (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : (Fin 66→ℂ) →ₗ[ℂ] (Fin 66→ℂ) where
  toFun:=gridShiftRows m f ε n s
  map_add':=by
    intro w v
    funext i
    simp only [Pi.add_apply]
    unfold gridShiftRows gridAssemble
    split_ifs <;> simp only [gridSample_add,Pi.add_apply,Pi.zero_apply,mul_add,add_zero]
  map_smul':=by
    intro c w
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    unfold gridShiftRows gridAssemble
    split_ifs <;> simp only [gridSample_smul,Pi.smul_apply,Pi.zero_apply,smul_eq_mul,mul_zero] <;> ring

def gridLeadingMatrix (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix (Fin 66) (Fin 66) ℂ :=
  (gridLeadingLinear m f ε s).toMatrix'

def gridShiftMatrix (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 66) (Fin 66) ℂ :=
  (gridShiftLinear m f ε n s).toMatrix'

theorem gridLeadingMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 66→ℂ) :
    gridLeadingMatrix m f ε s *ᵥ w=gridLeadingRows m f ε s w := LinearMap.toMatrix'_mulVec _ _

theorem gridShiftMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (w : Fin 66→ℂ) :
    gridShiftMatrix m f ε n s *ᵥ w=gridShiftRows m f ε n s w := LinearMap.toMatrix'_mulVec _ _

theorem gridLeadingMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i j : Fin 66) :
    gridLeadingMatrix m f ε s i j=gridLeadingRows m f ε s (Pi.single j 1) i := LinearMap.toMatrix'_apply _ _ _

theorem gridShiftMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (i j : Fin 66) :
    gridShiftMatrix m f ε n s i j=gridShiftRows m f ε n s (Pi.single j 1) i := LinearMap.toMatrix'_apply _ _ _

#print axioms gridLeadingMatrix_mulVec
#print axioms gridShiftMatrix_mulVec
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoKernelActions -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

def repCharacter (δ η : ℂ) : Fin 4 → ℂ
  | 0 => 1
  | 1 => δ
  | 2 => η
  | _ => δ*η

def generatorCharacter (δ η : ℂ) : Fin 5 → ℂ
  | 0 => 1
  | 1 => δ
  | 2 => η
  | 3 => δ
  | _ => 1

theorem kernelGenerator_det (j : Fin 5) : (GeneralLinearGroup.det (kernelGenerator j):ℝ)=1 := by
  fin_cases j
  · exact translation_det _
  · exact E_det
  · exact fricke_det 22 (by decide)
  · exact P_det
  · simp [kernelGenerator]

theorem rep_eigen {k : ℤ} (F : ℍ→ℂ) (δ η : ℂ)
    (hE : F ∣[k] E=δ • F) (hW : F ∣[k] W=η • F) (j : Fin 4) :
    F ∣[k] kernelRep j=repCharacter δ η j • F := by
  fin_cases j
  · simp [kernelRep,repCharacter]
  · exact hE
  · exact hW
  · change F ∣[k] (E*W)=(δ*η) • F
    rw [SlashAction.slash_mul,hE,det_one_smul _ (show (GeneralLinearGroup.det W:ℝ)=1 from fricke_det _ _),hW,smul_smul]

theorem generator_eigen {k : ℤ} (F : ℍ→ℂ) (δ η : ℂ)
    (hT : F ∣[k] translation 1=F) (hE : F ∣[k] E=δ • F)
    (hW : F ∣[k] W=η • F) (hP : F ∣[k] P=δ • F)
    (hY : F ∣[k] Y=F) (j : Fin 5) :
    F ∣[k] kernelGenerator j=generatorCharacter δ η j • F := by
  fin_cases j
  · change F ∣[k] translation 1=(1:ℂ) • F
    simpa only [one_smul] using hT
  · exact hE
  · exact hW
  · exact hP
  · change F ∣[k] SpecialLinearGroup.mapGL ℝ Y=(1:ℂ) • F
    rw [one_smul]
    change F ∣[k] SpecialLinearGroup.mapGL ℝ Y=F at hY
    exact hY

theorem character_relation (δ η : ℂ) (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1) (i : Fin 14) :
    repCharacter δ η (sourceIndex i)*generatorCharacter δ η (symbolIndex i)=
      repCharacter δ η (targetIndex i) := by
  rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> fin_cases i <;>
    norm_num [repCharacter,generatorCharacter,sourceIndex,symbolIndex,targetIndex]

/-- Every integral Schreier generator has trivial character. -/
theorem kernel_invariant (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F)
    (hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F)
    (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)
    (hP : F ∣[((2*m:ℕ):ℤ)] P=δ • F)
    (hY : F ∣[((2*m:ℕ):ℤ)] Y=F) (i : Fin 14) :
    F ∣[((2*m:ℕ):ℤ)] kernel i=F := by
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hc : F ∣[k] (if kernelNegative i then (-1:GL (Fin 2) ℝ) else 1)=F := by
    split_ifs
    · exact central_even F m
    · simp only [SlashAction.slash_one]
  have hh : (F ∣[k] SpecialLinearGroup.mapGL ℝ (kernel i)) ∣[k] kernelRep (targetIndex i)=
      F ∣[k] kernelRep (targetIndex i) := by
    rw [← SlashAction.slash_mul,kernel_relation,SlashAction.slash_mul,SlashAction.slash_mul,hc,
      rep_eigen F δ η hE hW,det_one_smul _ (kernelGenerator_det _),
      generator_eigen F δ η hT hE hW hP hY,smul_smul,character_relation δ η hδ hη,
      rep_eigen F δ η hE hW]
  have he:=congrArg (fun G : ℍ→ℂ => G ∣[k] (kernelRep (targetIndex i))⁻¹) hh
  change F ∣[k] SpecialLinearGroup.mapGL ℝ (kernel i)=F
  simpa only [← SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one,SlashAction.slash_one] using he

def FivePair (k : ℕ) (f : ℕ→ℂ) : Prop :=
  let F:=SmallLevelOriginal.fourierFunction k f
  F ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ B5-F=
    -((F ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ A5-F) ∣[(k:ℤ)] translation (4/5))

/-- All integral generators follow from original input and the single
explicit separated denominator-five pair. -/
theorem original_kernel_of_five_pair (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (hfive : FivePair (2*m) f) (i : Fin 14) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  obtain ⟨hY,hP⟩:=original_Y_P_of_five_pair m hm hf hfive
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<22) m hf
  have hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F := by
    have ht : translation 1=SpecialLinearGroup.mapGL ℝ T := by
      apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
        norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
          SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
    rw [ht]
    exact original_T _ _
  exact kernel_invariant m F (FinitenessNormalizedTwistProduct.root 22 f 2) η
    (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2) hη hT
    (original_E_root hf) hW hP hY i

#print axioms kernel_invariant
#print axioms original_kernel_of_five_pair
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoModularCriterion -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm

/-- Every Gamma0(22) transformation follows once the single separated
modulus-five pair is available. -/
theorem gamma_zero_of_five_pair (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (hfive : FivePair (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 22) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K:=slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  change γ∈K
  exact gamma0_mem K (original_kernel_of_five_pair m hm hf hfive)
    (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- The level22 endgame is conditional only on the explicit analytic five-pair
obligation. This theorem does not assert that obligation or pole removal. -/
theorem modular_of_five_pair {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 k f) (hfive : FivePair k f) : IsModular 22 k f := by
  obtain ⟨m,hm⟩:=heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf hfive ⊢
  exact modular_of_transformations (by decide) hf
    (gamma_zero_of_five_pair m (by omega) hf hfive)

#print axioms gamma_zero_of_five_pair
#print axioms modular_of_five_pair
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoReflectionAlgebra -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct Filter Set
open scoped Topology

/-- Writing the ramified scalar using its genuine local root fixes its sign. -/
theorem heckeScalar_eq (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    heckeScalar m f s= -(root 22 f 2)*(2:ℂ)^((m:ℂ)-s) := by
  rw [root_two]
  unfold heckeScalar QuantitativeArithmeticRamifiedFullTrace.multiplier
  simp only [Nat.cast_ofNat,neg_neg]
  rw [sub_eq_add_neg,Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),Complex.cpow_natCast]
  ring

theorem heckeScalar_product (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (s : ℂ) :
    heckeScalar m f s*heckeScalar m f ((2*m:ℕ)-s)=1 := by
  rw [heckeScalar_eq,heckeScalar_eq]
  have hp : (2:ℂ)^((m:ℂ)-s)*(2:ℂ)^((m:ℂ)-((2*m:ℕ)-s))=1 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    rw [show (m:ℂ)-s+((m:ℂ)-((2*m:ℕ)-s))=0 by push_cast; ring,Complex.cpow_zero]
  rcases root_unit hf.toEulerData 2 with h|h <;> rw [h] <;> simpa using hp

theorem heckeScalar_ne_zero (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (s : ℂ) : heckeScalar m f s≠0 :=
  left_ne_zero_of_mul_eq_one (heckeScalar_product m hf s)

theorem denominator_reflection (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (s : ℂ) :
    denominator m f s=heckeScalar m f s*denominator m f ((2*m:ℕ)-s) := by
  unfold denominator
  rw [mul_add,heckeScalar_product m hf s,mul_one,add_comm]

/-- Even powers of the square-root conductor agree with the usual conductor power. -/
theorem sqrt_cpow_even (N m : ℕ) (hN : 0<N) (s : ℂ) :
    (Real.sqrt N:ℂ)^((2*m:ℕ)-2*s)=(N:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hs : (Real.sqrt N:ℂ)*(Real.sqrt N:ℂ)=(N:ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hp:=Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg (N:ℝ)) (Real.sqrt_nonneg (N:ℝ)) ((m:ℂ)-s)
  rw [hs] at hp
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,← hp]

theorem center_conductor_factor (m : ℕ) (s : ℂ) :
    (Real.sqrt 1100:ℂ)^((2*m:ℕ)-2*s)=
      (2:ℂ)^((m:ℂ)-s)*(Real.sqrt 550:ℂ)^((2*m:ℕ)-2*s) := by
  have h1100 : (Real.sqrt 1100:ℂ)^((2*m:ℕ)-2*s)=(1100:ℂ)^((m:ℂ)-s) := by
    simpa only [Nat.cast_ofNat] using sqrt_cpow_even 1100 m (by decide) s
  have h550 : (Real.sqrt 550:ℂ)^((2*m:ℕ)-2*s)=(550:ℂ)^((m:ℂ)-s) := by
    simpa only [Nat.cast_ofNat] using sqrt_cpow_even 550 m (by decide) s
  rw [h1100,h550]
  have h:=Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)≤550) ((m:ℂ)-s)
  norm_num only [Complex.ofReal_ofNat,show (2:ℂ)*550=1100 by norm_num] at h
  exact h

def reflectionMultiplier (m : ℕ) (ε s : ℂ) : ℂ := -ε*(550:ℂ)^((m:ℂ)-s)

theorem reflectionMultiplier_entire (m : ℕ) (ε : ℂ) : Differentiable ℂ (reflectionMultiplier m ε) := by
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (550:ℂ)≠0)]
  fun_prop

theorem reflectionMultiplier_ne_zero (m : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier m ε s≠0 := by
  exact mul_ne_zero (neg_ne_zero.mpr hε) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))

theorem numerator_reflection (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ)
    (hc : ∀ s : ℂ, evenTenthEntire m f s=(root 22 f 2*ε)*(Real.sqrt 1100:ℂ)^((2*m:ℕ)-2*s)*
      evenTenthEntire m f ((2*m:ℕ)-s))
    (hr : ∀ s : ℂ, ramanujanEntire 22 (2*m) f 5 s=
      ε*(Real.sqrt 550:ℂ)^((2*m:ℕ)-2*s)*ramanujanEntire 22 (2*m) f 5 ((2*m:ℕ)-s))
    (s : ℂ) : numerator m f s=heckeScalar m f s*reflectionMultiplier m ε s*
      numerator m f ((2*m:ℕ)-s) := by
  have ht:=heckeScalar_product m hf s
  have hs : root 22 f 2*(2:ℂ)^((m:ℂ)-s)= -heckeScalar m f s := by rw [heckeScalar_eq]; ring
  unfold numerator reflectionMultiplier
  have h550 : (Real.sqrt 550:ℂ)^((2*m:ℕ)-2*s)=(550:ℂ)^((m:ℂ)-s) := by
    simpa only [Nat.cast_ofNat] using sqrt_cpow_even 550 m (by decide) s
  rw [hr s,hc s,center_conductor_factor,h550]
  calc
    _ = (1-heckeScalar m f s)*ε*(550:ℂ)^((m:ℂ)-s)*ramanujanEntire 22 (2*m) f 5 ((2*m:ℕ)-s)+
        2*(root 22 f 2*(2:ℂ)^((m:ℂ)-s))*ε*(550:ℂ)^((m:ℂ)-s)*evenTenthEntire m f ((2*m:ℕ)-s) := by ring
    _ = _ := by rw [hs]; linear_combination -(ε*(550:ℂ)^((m:ℂ)-s)*ramanujanEntire 22 (2*m) f 5 ((2*m:ℕ)-s))*ht

theorem raw_quotient_reflection (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ)
    (hN : ∀ s : ℂ, numerator m f s=heckeScalar m f s*reflectionMultiplier m ε s*
      numerator m f ((2*m:ℕ)-s)) (s : ℂ) :
    numerator m f s/denominator m f s=reflectionMultiplier m ε s*
      (numerator m f ((2*m:ℕ)-s)/denominator m f ((2*m:ℕ)-s)) := by
  rw [hN s,denominator_reflection m hf s,mul_assoc,
    mul_div_mul_left _ _ (heckeScalar_ne_zero m hf s)]
  ring

#print axioms heckeScalar_product
#print axioms numerator_reflection
#print axioms raw_quotient_reflection
end QuantitativeArithmeticSmallLevelTwentyTwo
end
end

/-! ## TwentyTwoKernelCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoLaurent
open Complex

theorem kernel_case0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (-1) X Y Z a w=0) :
    ∀ j, w j=pole0 X Y Z a j*w 44 := by
  intro j
  fin_cases j
  · exact coordinate0_0 X Y Z a hX hY hZ w hw
  · exact coordinate0_1 X Y Z a hX hY hZ w hw
  · exact coordinate0_2 X Y Z a hX hY hZ w hw
  · exact coordinate0_3 X Y Z a hX hY hZ w hw
  · exact coordinate0_4 X Y Z a hX hY hZ w hw
  · exact coordinate0_5 X Y Z a hX hY hZ w hw
  · exact coordinate0_6 X Y Z a hX hY hZ w hw
  · exact coordinate0_7 X Y Z a hX hY hZ w hw
  · exact coordinate0_8 X Y Z a hX hY hZ w hw
  · exact coordinate0_9 X Y Z a hX hY hZ w hw
  · exact coordinate0_10 X Y Z a hX hY hZ w hw
  · exact coordinate0_11 X Y Z a hX hY hZ w hw
  · exact coordinate0_12 X Y Z a hX hY hZ w hw
  · exact coordinate0_13 X Y Z a hX hY hZ w hw
  · exact coordinate0_14 X Y Z a hX hY hZ w hw
  · exact coordinate0_15 X Y Z a hX hY hZ w hw
  · exact coordinate0_16 X Y Z a hX hY hZ w hw
  · exact coordinate0_17 X Y Z a hX hY hZ w hw
  · exact coordinate0_18 X Y Z a hX hY hZ w hw
  · exact coordinate0_19 X Y Z a hX hY hZ w hw
  · exact coordinate0_20 X Y Z a hX hY hZ w hw
  · exact coordinate0_21 X Y Z a hX hY hZ w hw
  · exact coordinate0_22 X Y Z a hX hY hZ w hw
  · exact coordinate0_23 X Y Z a hX hY hZ w hw
  · exact coordinate0_24 X Y Z a hX hY hZ w hw
  · exact coordinate0_25 X Y Z a hX hY hZ w hw
  · exact coordinate0_26 X Y Z a hX hY hZ w hw
  · exact coordinate0_27 X Y Z a hX hY hZ w hw
  · exact coordinate0_28 X Y Z a hX hY hZ w hw
  · exact coordinate0_29 X Y Z a hX hY hZ w hw
  · exact coordinate0_30 X Y Z a hX hY hZ w hw
  · exact coordinate0_31 X Y Z a hX hY hZ w hw
  · exact coordinate0_32 X Y Z a hX hY hZ w hw
  · exact coordinate0_33 X Y Z a hX hY hZ w hw
  · exact coordinate0_34 X Y Z a hX hY hZ w hw
  · exact coordinate0_35 X Y Z a hX hY hZ w hw
  · exact coordinate0_36 X Y Z a hX hY hZ w hw
  · exact coordinate0_37 X Y Z a hX hY hZ w hw
  · exact coordinate0_38 X Y Z a hX hY hZ w hw
  · exact coordinate0_39 X Y Z a hX hY hZ w hw
  · exact coordinate0_40 X Y Z a hX hY hZ w hw
  · exact coordinate0_41 X Y Z a hX hY hZ w hw
  · exact coordinate0_42 X Y Z a hX hY hZ w hw
  · exact coordinate0_43 X Y Z a hX hY hZ w hw
  · change w 44 = 1 * w 44
    exact (one_mul _).symm
  · exact coordinate0_45 X Y Z a hX hY hZ w hw
  · exact coordinate0_46 X Y Z a hX hY hZ w hw
  · exact coordinate0_47 X Y Z a hX hY hZ w hw
  · exact coordinate0_48 X Y Z a hX hY hZ w hw
  · exact coordinate0_49 X Y Z a hX hY hZ w hw
  · exact coordinate0_50 X Y Z a hX hY hZ w hw
  · exact coordinate0_51 X Y Z a hX hY hZ w hw
  · exact coordinate0_52 X Y Z a hX hY hZ w hw
  · exact coordinate0_53 X Y Z a hX hY hZ w hw
  · exact coordinate0_54 X Y Z a hX hY hZ w hw
  · exact coordinate0_55 X Y Z a hX hY hZ w hw
  · exact coordinate0_56 X Y Z a hX hY hZ w hw
  · exact coordinate0_57 X Y Z a hX hY hZ w hw
  · exact coordinate0_58 X Y Z a hX hY hZ w hw
  · exact coordinate0_59 X Y Z a hX hY hZ w hw
  · exact coordinate0_60 X Y Z a hX hY hZ w hw
  · exact coordinate0_61 X Y Z a hX hY hZ w hw
  · exact coordinate0_62 X Y Z a hX hY hZ w hw
  · exact coordinate0_63 X Y Z a hX hY hZ w hw
  · exact coordinate0_64 X Y Z a hX hY hZ w hw
  · exact coordinate0_65 X Y Z a hX hY hZ w hw

#print axioms kernel_case0

theorem kernel_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ∀ j,w j=pole1 X Y Z a j*w 44 :=
  SmallLevelTwentyTwoTriangular.kernel_case1 X Y Z a hX hY hZ w hw

#print axioms kernel_case1

theorem kernel_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole2 X Y Z a j*w 44 :=
  SmallLevelTwentyTwoTriangular.kernel_case2 X Y Z a hX hY hZ w hw

#print axioms kernel_case2

theorem kernel_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ∀ j,w j=pole3 X Y Z a j*w 44 :=
  SmallLevelTwentyTwoTriangular.kernel_case3 X Y Z a hX hY hZ w hw

#print axioms kernel_case3

theorem kernel_case4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole4 X Y Z a j*w 44 :=
  SmallLevelTwentyTwoTriangular.kernel_case4 X Y Z a hX hY hZ w hw

#print axioms kernel_case4

theorem kernel_case5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    ∀ j,w j=pole5 X Y Z a j*w 44 :=
  SmallLevelTwentyTwoTriangular.kernel_case5 X Y Z a hX hY hZ w hw

#print axioms kernel_case5

theorem kernel_case6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole6 X Y Z a j*w 44 :=
  SmallLevelTwentyTwoTriangular.kernel_case6 X Y Z a hX hY hZ w hw

#print axioms kernel_case6

theorem kernel_case7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ∀ j,w j=pole7 X Y Z a j*w 44 :=
  SmallLevelTwentyTwoTriangular.kernel_case7 X Y Z a hX hY hZ w hw

#print axioms kernel_case7

end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoSyzygyDataCaseFamilyV4 -/
section
@[expose] public noncomputable section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

def first0Indices : Fin 19→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,24,25,30,46,47,48,49,66]
def first0Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![((1)/(X*Z)),(1*Y^2),((1)/(X)),(((-2))/(Z) + (1*X)/(Z)),((1)/(X) + (-1)),((1)/(Z)),((1)/(X)),(1),((1*Y^2)/(Z)),((1)/(X)),((1*Y^2)/(X*Z)),((-1)),((1)/(X)),((1)/(X)),(((-4))/(X*Z) + (1)/(Z)),(((-1)*Y^2)/(X*Z)),(((-1)*Y^2)/(Z)),(((-1))/(X)),(1)]


def second0Indices : Fin 27→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,20,23,25,30,31,34,38,39,46,47,48,49,51,54,55,67]
def second0Coeff (X Y Z _a : ℂ) : Fin 27→ℂ := ![(((-1))/(X*Z) + (1)/(Y^2*Z)),((-1)*Y^2 + 1*X),(((-1))/(X) + (1)/(Y^2)),((2)/(Z)),(((-1))/(X)),(((-1))/(Z)),(((-1))/(X) + (1)/(Y^2)),((-1)),(((-1))/(Z) + ((-1)*Y^2)/(Z) + (1*X^2)/(Z)),(((-1))/(X*Y^2) + ((-1))/(X) + (1*X)/(Y^2)),(((-1)*Y^2)/(X*Z)),((1)/(X*Y^2)),((-1)),(((-1))/(X)),(((-1))/(X)),((-1)),((1)/(X*Y^2)),(((-1))/(X)),(((-1))/(X)),((6)/(X*Z) + ((-2))/(Y^2*Z)),((1)/(X*Z) + (1*Y^2)/(X*Z)),((1)/(Z) + (1*Y^2)/(Z) + ((-1)*X^2)/(Z)),((1)/(X)),(((-1)*X)/(Y^2)),(((-1)*X)/(Y^2)),(1),(1)]


end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

def first1Indices : Fin 19→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,24,25,30,46,47,48,49,66]
def first1Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![((1)/(X*Z)),(1*Y^2),((1)/(X)),(((-2))/(Z) + (1*X)/(Z)),((1)/(X) + (-1)),((1)/(Z)),((1)/(X)),(1),((1*Y^2)/(Z)),((1)/(X)),((1*Y^2)/(X*Z)),((-1)),((1)/(X)),((1)/(X)),(((-4))/(X*Z) + (1)/(Z)),(((-1)*Y^2)/(X*Z)),(((-1)*Y^2)/(Z)),(((-1))/(X)),(1)]


def second1Indices : Fin 27→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,20,23,25,30,31,34,38,39,46,47,48,49,51,54,55,67]
def second1Coeff (X Y Z _a : ℂ) : Fin 27→ℂ := ![(((-1))/(X*Z) + (1)/(Y^2*Z)),((-1)*Y^2 + 1*X),(((-1))/(X) + (1)/(Y^2)),((2)/(Z)),(((-1))/(X)),(((-1))/(Z)),(((-1))/(X) + (1)/(Y^2)),((-1)),(((-1))/(Z) + ((-1)*Y^2)/(Z) + (1*X^2)/(Z)),(((-1))/(X*Y^2) + ((-1))/(X) + (1*X)/(Y^2)),(((-1)*Y^2)/(X*Z)),((1)/(X*Y^2)),((-1)),(((-1))/(X)),(((-1))/(X)),((-1)),((1)/(X*Y^2)),(((-1))/(X)),(((-1))/(X)),((6)/(X*Z) + ((-2))/(Y^2*Z)),((1)/(X*Z) + (1*Y^2)/(X*Z)),((1)/(Z) + (1*Y^2)/(Z) + ((-1)*X^2)/(Z)),((1)/(X)),(((-1)*X)/(Y^2)),(((-1)*X)/(Y^2)),(1),(1)]


end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

def first2Indices : Fin 19→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,24,25,30,46,47,48,49,66]
def first2Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![((1)/(X*Z)),(1*Y^2),(((-1))/(X)),((2)/(Z) + (1*X)/(Z)),(((-1))/(X) + (-1)),(((-1))/(Z)),(((-1))/(X)),(1),(((-1)*Y^2)/(Z)),(((-1))/(X)),((1*Y^2)/(X*Z)),((-1)),(((-1))/(X)),(((-1))/(X)),(((-4))/(X*Z) + ((-1))/(Z)),(((-1)*Y^2)/(X*Z)),((1*Y^2)/(Z)),((1)/(X)),(1)]


def second2Indices : Fin 27→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,20,23,25,30,31,34,38,39,46,47,48,49,51,54,55,67]
def second2Coeff (X Y Z _a : ℂ) : Fin 27→ℂ := ![(((-1))/(X*Z) + ((-1))/(Y^2*Z)),((-1)*Y^2 + (-1)*X),((1)/(X) + (1)/(Y^2)),(((-2))/(Z)),((1)/(X)),((1)/(Z)),((1)/(X) + (1)/(Y^2)),((-1)),((1)/(Z) + (1*Y^2)/(Z) + ((-1)*X^2)/(Z)),((1)/(X*Y^2) + (1)/(X) + ((-1)*X)/(Y^2)),(((-1)*Y^2)/(X*Z)),(((-1))/(X*Y^2)),((-1)),((1)/(X)),((1)/(X)),((-1)),(((-1))/(X*Y^2)),((1)/(X)),((1)/(X)),((6)/(X*Z) + (2)/(Y^2*Z)),((1)/(X*Z) + (1*Y^2)/(X*Z)),(((-1))/(Z) + ((-1)*Y^2)/(Z) + (1*X^2)/(Z)),(((-1))/(X)),((1*X)/(Y^2)),((1*X)/(Y^2)),(1),(1)]


end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

def first3Indices : Fin 19→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,24,25,30,46,47,48,49,66]
def first3Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![((1)/(X*Z)),(1*Y^2),(((-1))/(X)),((2)/(Z) + (1*X)/(Z)),(((-1))/(X) + (-1)),(((-1))/(Z)),(((-1))/(X)),(1),(((-1)*Y^2)/(Z)),(((-1))/(X)),((1*Y^2)/(X*Z)),((-1)),(((-1))/(X)),(((-1))/(X)),(((-4))/(X*Z) + ((-1))/(Z)),(((-1)*Y^2)/(X*Z)),((1*Y^2)/(Z)),((1)/(X)),(1)]


def second3Indices : Fin 27→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,20,23,25,30,31,34,38,39,46,47,48,49,51,54,55,67]
def second3Coeff (X Y Z _a : ℂ) : Fin 27→ℂ := ![(((-1))/(X*Z) + ((-1))/(Y^2*Z)),((-1)*Y^2 + (-1)*X),((1)/(X) + (1)/(Y^2)),(((-2))/(Z)),((1)/(X)),((1)/(Z)),((1)/(X) + (1)/(Y^2)),((-1)),((1)/(Z) + (1*Y^2)/(Z) + ((-1)*X^2)/(Z)),((1)/(X*Y^2) + (1)/(X) + ((-1)*X)/(Y^2)),(((-1)*Y^2)/(X*Z)),(((-1))/(X*Y^2)),((-1)),((1)/(X)),((1)/(X)),((-1)),(((-1))/(X*Y^2)),((1)/(X)),((1)/(X)),((6)/(X*Z) + (2)/(Y^2*Z)),((1)/(X*Z) + (1*Y^2)/(X*Z)),(((-1))/(Z) + ((-1)*Y^2)/(Z) + (1*X^2)/(Z)),(((-1))/(X)),((1*X)/(Y^2)),((1*X)/(Y^2)),(1),(1)]


end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

def first4Indices : Fin 19→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,24,25,30,46,47,48,49,66]
def first4Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![(((-1))/(X*Z)),(1*Y^2),((1)/(X)),((2)/(Z) + ((-1)*X)/(Z)),((1)/(X) + (-1)),(((-1))/(Z)),((1)/(X)),(1),(((-1)*Y^2)/(Z)),((1)/(X)),(((-1)*Y^2)/(X*Z)),((-1)),((1)/(X)),((1)/(X)),((4)/(X*Z) + ((-1))/(Z)),((1*Y^2)/(X*Z)),((1*Y^2)/(Z)),(((-1))/(X)),(1)]


def second4Indices : Fin 27→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,20,23,25,30,31,34,38,39,46,47,48,49,51,54,55,67]
def second4Coeff (X Y Z _a : ℂ) : Fin 27→ℂ := ![((1)/(X*Z) + ((-1))/(Y^2*Z)),((-1)*Y^2 + 1*X),(((-1))/(X) + (1)/(Y^2)),(((-2))/(Z)),(((-1))/(X)),((1)/(Z)),(((-1))/(X) + (1)/(Y^2)),((-1)),((1)/(Z) + (1*Y^2)/(Z) + ((-1)*X^2)/(Z)),(((-1))/(X*Y^2) + ((-1))/(X) + (1*X)/(Y^2)),((1*Y^2)/(X*Z)),((1)/(X*Y^2)),((-1)),(((-1))/(X)),(((-1))/(X)),((-1)),((1)/(X*Y^2)),(((-1))/(X)),(((-1))/(X)),(((-6))/(X*Z) + (2)/(Y^2*Z)),(((-1))/(X*Z) + ((-1)*Y^2)/(X*Z)),(((-1))/(Z) + ((-1)*Y^2)/(Z) + (1*X^2)/(Z)),((1)/(X)),(((-1)*X)/(Y^2)),(((-1)*X)/(Y^2)),(1),(1)]


end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

def first5Indices : Fin 19→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,24,25,30,46,47,48,49,66]
def first5Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![(((-1))/(X*Z)),(1*Y^2),((1)/(X)),((2)/(Z) + ((-1)*X)/(Z)),((1)/(X) + (-1)),(((-1))/(Z)),((1)/(X)),(1),(((-1)*Y^2)/(Z)),((1)/(X)),(((-1)*Y^2)/(X*Z)),((-1)),((1)/(X)),((1)/(X)),((4)/(X*Z) + ((-1))/(Z)),((1*Y^2)/(X*Z)),((1*Y^2)/(Z)),(((-1))/(X)),(1)]


def second5Indices : Fin 27→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,20,23,25,30,31,34,38,39,46,47,48,49,51,54,55,67]
def second5Coeff (X Y Z _a : ℂ) : Fin 27→ℂ := ![((1)/(X*Z) + ((-1))/(Y^2*Z)),((-1)*Y^2 + 1*X),(((-1))/(X) + (1)/(Y^2)),(((-2))/(Z)),(((-1))/(X)),((1)/(Z)),(((-1))/(X) + (1)/(Y^2)),((-1)),((1)/(Z) + (1*Y^2)/(Z) + ((-1)*X^2)/(Z)),(((-1))/(X*Y^2) + ((-1))/(X) + (1*X)/(Y^2)),((1*Y^2)/(X*Z)),((1)/(X*Y^2)),((-1)),(((-1))/(X)),(((-1))/(X)),((-1)),((1)/(X*Y^2)),(((-1))/(X)),(((-1))/(X)),(((-6))/(X*Z) + (2)/(Y^2*Z)),(((-1))/(X*Z) + ((-1)*Y^2)/(X*Z)),(((-1))/(Z) + ((-1)*Y^2)/(Z) + (1*X^2)/(Z)),((1)/(X)),(((-1)*X)/(Y^2)),(((-1)*X)/(Y^2)),(1),(1)]


end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

def first6Indices : Fin 19→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,24,25,30,46,47,48,49,66]
def first6Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![(((-1))/(X*Z)),(1*Y^2),(((-1))/(X)),(((-2))/(Z) + ((-1)*X)/(Z)),(((-1))/(X) + (-1)),((1)/(Z)),(((-1))/(X)),(1),((1*Y^2)/(Z)),(((-1))/(X)),(((-1)*Y^2)/(X*Z)),((-1)),(((-1))/(X)),(((-1))/(X)),((4)/(X*Z) + (1)/(Z)),((1*Y^2)/(X*Z)),(((-1)*Y^2)/(Z)),((1)/(X)),(1)]


def second6Indices : Fin 27→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,20,23,25,30,31,34,38,39,46,47,48,49,51,54,55,67]
def second6Coeff (X Y Z _a : ℂ) : Fin 27→ℂ := ![((1)/(X*Z) + (1)/(Y^2*Z)),((-1)*Y^2 + (-1)*X),((1)/(X) + (1)/(Y^2)),((2)/(Z)),((1)/(X)),(((-1))/(Z)),((1)/(X) + (1)/(Y^2)),((-1)),(((-1))/(Z) + ((-1)*Y^2)/(Z) + (1*X^2)/(Z)),((1)/(X*Y^2) + (1)/(X) + ((-1)*X)/(Y^2)),((1*Y^2)/(X*Z)),(((-1))/(X*Y^2)),((-1)),((1)/(X)),((1)/(X)),((-1)),(((-1))/(X*Y^2)),((1)/(X)),((1)/(X)),(((-6))/(X*Z) + ((-2))/(Y^2*Z)),(((-1))/(X*Z) + ((-1)*Y^2)/(X*Z)),((1)/(Z) + (1*Y^2)/(Z) + ((-1)*X^2)/(Z)),(((-1))/(X)),((1*X)/(Y^2)),((1*X)/(Y^2)),(1),(1)]


end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

def first7Indices : Fin 19→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,24,25,30,46,47,48,49,66]
def first7Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![(((-1))/(X*Z)),(1*Y^2),(((-1))/(X)),(((-2))/(Z) + ((-1)*X)/(Z)),(((-1))/(X) + (-1)),((1)/(Z)),(((-1))/(X)),(1),((1*Y^2)/(Z)),(((-1))/(X)),(((-1)*Y^2)/(X*Z)),((-1)),(((-1))/(X)),(((-1))/(X)),((4)/(X*Z) + (1)/(Z)),((1*Y^2)/(X*Z)),(((-1)*Y^2)/(Z)),((1)/(X)),(1)]


def second7Indices : Fin 27→Fin 68 := ![0,3,4,5,8,9,12,13,14,15,16,20,23,25,30,31,34,38,39,46,47,48,49,51,54,55,67]
def second7Coeff (X Y Z _a : ℂ) : Fin 27→ℂ := ![((1)/(X*Z) + (1)/(Y^2*Z)),((-1)*Y^2 + (-1)*X),((1)/(X) + (1)/(Y^2)),((2)/(Z)),((1)/(X)),(((-1))/(Z)),((1)/(X) + (1)/(Y^2)),((-1)),(((-1))/(Z) + ((-1)*Y^2)/(Z) + (1*X^2)/(Z)),((1)/(X*Y^2) + (1)/(X) + ((-1)*X)/(Y^2)),((1*Y^2)/(X*Z)),(((-1))/(X*Y^2)),((-1)),((1)/(X)),((1)/(X)),((-1)),(((-1))/(X*Y^2)),((1)/(X)),((1)/(X)),(((-6))/(X*Z) + ((-2))/(Y^2*Z)),(((-1))/(X*Z) + ((-1)*Y^2)/(X*Z)),((1)/(Z) + (1*Y^2)/(Z) + ((-1)*X^2)/(Z)),(((-1))/(X)),((1*X)/(Y^2)),((1*X)/(Y^2)),(1),(1)]


end SmallLevelTwentyTwoLaurent
end
end
end

/-! ## TwentyTwoSyzygyCaseIndexFamilySeriesV4 -/
section
@[expose] public noncomputable section
section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first0_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, first0Coeff X Y Z a i*leadingRows (-1) (-1) (-1) X Y Z a w (first0Indices i))=0 := by
  simp only [first0Coeff,first0Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first0_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first0_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (-1) X Y Z a w=0) :
    (∑ i, first0Coeff (X/2) (Y/3) (Z/11) a i*firstRows (-1) (-1) (-1) X Y Z a w (first0Indices i))=
      (((-22))/(3*X*Z))*SmallLevelTwentyTwoFirstJet.first (-1) X Y*w 44 := by
  have hk := kernel_case0 X Y Z a hX hY hZ w hw
  simp only [first0Coeff,first0Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole0,SmallLevelTwentyTwoFirstJet.first]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first0_projection
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second0_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, second0Coeff X Y Z a i*leadingRows (-1) (-1) (-1) X Y Z a w (second0Indices i))=0 := by
  simp only [second0Coeff,second0Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second0_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second0_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (-1) X Y Z a w=0) :
    (∑ i, second0Coeff (X/2) (Y/3) (Z/11) a i*firstRows (-1) (-1) (-1) X Y Z a w (second0Indices i))=
      (((-11))/(3*X*Z))*SmallLevelTwentyTwoFirstJet.second (-1) X Y*w 44 := by
  have hk := kernel_case0 X Y Z a hX hY hZ w hw
  simp only [second0Coeff,second0Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole0,SmallLevelTwentyTwoFirstJet.second]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second0_projection
end SmallLevelTwentyTwoLaurent
end
end

section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first1_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, first1Coeff X Y Z a i*leadingRows (-1) (-1) (1) X Y Z a w (first1Indices i))=0 := by
  simp only [first1Coeff,first1Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first1_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first1_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (∑ i, first1Coeff (X/2) (Y/3) (Z/11) a i*firstRows (-1) (-1) (1) X Y Z a w (first1Indices i))=
      (((-22))/(3*X*Z))*SmallLevelTwentyTwoFirstJet.first (-1) X Y*w 44 := by
  have hk := kernel_case1 X Y Z a hX hY hZ w hw
  simp only [first1Coeff,first1Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole1,SmallLevelTwentyTwoFirstJet.first]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first1_projection
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second1_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, second1Coeff X Y Z a i*leadingRows (-1) (-1) (1) X Y Z a w (second1Indices i))=0 := by
  simp only [second1Coeff,second1Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second1_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second1_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (∑ i, second1Coeff (X/2) (Y/3) (Z/11) a i*firstRows (-1) (-1) (1) X Y Z a w (second1Indices i))=
      (((-11))/(3*X*Z))*SmallLevelTwentyTwoFirstJet.second (-1) X Y*w 44 := by
  have hk := kernel_case1 X Y Z a hX hY hZ w hw
  simp only [second1Coeff,second1Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole1,SmallLevelTwentyTwoFirstJet.second]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second1_projection
end SmallLevelTwentyTwoLaurent
end
end

section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first2_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, first2Coeff X Y Z a i*leadingRows (-1) (1) (-1) X Y Z a w (first2Indices i))=0 := by
  simp only [first2Coeff,first2Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first2_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first2_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (∑ i, first2Coeff (X/2) (Y/3) (Z/11) a i*firstRows (-1) (1) (-1) X Y Z a w (first2Indices i))=
      ((22)/(3*X*Z))*SmallLevelTwentyTwoFirstJet.first (1) X Y*w 44 := by
  have hk := kernel_case2 X Y Z a hX hY hZ w hw
  simp only [first2Coeff,first2Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole2,SmallLevelTwentyTwoFirstJet.first]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first2_projection
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second2_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, second2Coeff X Y Z a i*leadingRows (-1) (1) (-1) X Y Z a w (second2Indices i))=0 := by
  simp only [second2Coeff,second2Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second2_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second2_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (∑ i, second2Coeff (X/2) (Y/3) (Z/11) a i*firstRows (-1) (1) (-1) X Y Z a w (second2Indices i))=
      ((11)/(3*X*Z))*SmallLevelTwentyTwoFirstJet.second (1) X Y*w 44 := by
  have hk := kernel_case2 X Y Z a hX hY hZ w hw
  simp only [second2Coeff,second2Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole2,SmallLevelTwentyTwoFirstJet.second]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second2_projection
end SmallLevelTwentyTwoLaurent
end
end

section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first3_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, first3Coeff X Y Z a i*leadingRows (-1) (1) (1) X Y Z a w (first3Indices i))=0 := by
  simp only [first3Coeff,first3Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first3_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first3_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (∑ i, first3Coeff (X/2) (Y/3) (Z/11) a i*firstRows (-1) (1) (1) X Y Z a w (first3Indices i))=
      ((22)/(3*X*Z))*SmallLevelTwentyTwoFirstJet.first (1) X Y*w 44 := by
  have hk := kernel_case3 X Y Z a hX hY hZ w hw
  simp only [first3Coeff,first3Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole3,SmallLevelTwentyTwoFirstJet.first]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first3_projection
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second3_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, second3Coeff X Y Z a i*leadingRows (-1) (1) (1) X Y Z a w (second3Indices i))=0 := by
  simp only [second3Coeff,second3Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second3_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second3_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (∑ i, second3Coeff (X/2) (Y/3) (Z/11) a i*firstRows (-1) (1) (1) X Y Z a w (second3Indices i))=
      ((11)/(3*X*Z))*SmallLevelTwentyTwoFirstJet.second (1) X Y*w 44 := by
  have hk := kernel_case3 X Y Z a hX hY hZ w hw
  simp only [second3Coeff,second3Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole3,SmallLevelTwentyTwoFirstJet.second]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second3_projection
end SmallLevelTwentyTwoLaurent
end
end

section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first4_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, first4Coeff X Y Z a i*leadingRows (1) (-1) (-1) X Y Z a w (first4Indices i))=0 := by
  simp only [first4Coeff,first4Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first4_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first4_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (∑ i, first4Coeff (X/2) (Y/3) (Z/11) a i*firstRows (1) (-1) (-1) X Y Z a w (first4Indices i))=
      ((22)/(3*X*Z))*SmallLevelTwentyTwoFirstJet.first (-1) X Y*w 44 := by
  have hk := kernel_case4 X Y Z a hX hY hZ w hw
  simp only [first4Coeff,first4Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole4,SmallLevelTwentyTwoFirstJet.first]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first4_projection
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second4_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, second4Coeff X Y Z a i*leadingRows (1) (-1) (-1) X Y Z a w (second4Indices i))=0 := by
  simp only [second4Coeff,second4Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second4_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second4_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (∑ i, second4Coeff (X/2) (Y/3) (Z/11) a i*firstRows (1) (-1) (-1) X Y Z a w (second4Indices i))=
      ((11)/(3*X*Z))*SmallLevelTwentyTwoFirstJet.second (-1) X Y*w 44 := by
  have hk := kernel_case4 X Y Z a hX hY hZ w hw
  simp only [second4Coeff,second4Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole4,SmallLevelTwentyTwoFirstJet.second]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second4_projection
end SmallLevelTwentyTwoLaurent
end
end

section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first5_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, first5Coeff X Y Z a i*leadingRows (1) (-1) (1) X Y Z a w (first5Indices i))=0 := by
  simp only [first5Coeff,first5Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first5_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first5_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (∑ i, first5Coeff (X/2) (Y/3) (Z/11) a i*firstRows (1) (-1) (1) X Y Z a w (first5Indices i))=
      ((22)/(3*X*Z))*SmallLevelTwentyTwoFirstJet.first (-1) X Y*w 44 := by
  have hk := kernel_case5 X Y Z a hX hY hZ w hw
  simp only [first5Coeff,first5Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole5,SmallLevelTwentyTwoFirstJet.first]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first5_projection
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second5_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, second5Coeff X Y Z a i*leadingRows (1) (-1) (1) X Y Z a w (second5Indices i))=0 := by
  simp only [second5Coeff,second5Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second5_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second5_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (∑ i, second5Coeff (X/2) (Y/3) (Z/11) a i*firstRows (1) (-1) (1) X Y Z a w (second5Indices i))=
      ((11)/(3*X*Z))*SmallLevelTwentyTwoFirstJet.second (-1) X Y*w 44 := by
  have hk := kernel_case5 X Y Z a hX hY hZ w hw
  simp only [second5Coeff,second5Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole5,SmallLevelTwentyTwoFirstJet.second]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second5_projection
end SmallLevelTwentyTwoLaurent
end
end

section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first6_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, first6Coeff X Y Z a i*leadingRows (1) (1) (-1) X Y Z a w (first6Indices i))=0 := by
  simp only [first6Coeff,first6Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first6_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first6_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (∑ i, first6Coeff (X/2) (Y/3) (Z/11) a i*firstRows (1) (1) (-1) X Y Z a w (first6Indices i))=
      (((-22))/(3*X*Z))*SmallLevelTwentyTwoFirstJet.first (1) X Y*w 44 := by
  have hk := kernel_case6 X Y Z a hX hY hZ w hw
  simp only [first6Coeff,first6Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole6,SmallLevelTwentyTwoFirstJet.first]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first6_projection
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second6_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, second6Coeff X Y Z a i*leadingRows (1) (1) (-1) X Y Z a w (second6Indices i))=0 := by
  simp only [second6Coeff,second6Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second6_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second6_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (∑ i, second6Coeff (X/2) (Y/3) (Z/11) a i*firstRows (1) (1) (-1) X Y Z a w (second6Indices i))=
      (((-11))/(3*X*Z))*SmallLevelTwentyTwoFirstJet.second (1) X Y*w 44 := by
  have hk := kernel_case6 X Y Z a hX hY hZ w hw
  simp only [second6Coeff,second6Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole6,SmallLevelTwentyTwoFirstJet.second]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second6_projection
end SmallLevelTwentyTwoLaurent
end
end

section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first7_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, first7Coeff X Y Z a i*leadingRows (1) (1) (1) X Y Z a w (first7Indices i))=0 := by
  simp only [first7Coeff,first7Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first7_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem first7_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (∑ i, first7Coeff (X/2) (Y/3) (Z/11) a i*firstRows (1) (1) (1) X Y Z a w (first7Indices i))=
      (((-22))/(3*X*Z))*SmallLevelTwentyTwoFirstJet.first (1) X Y*w 44 := by
  have hk := kernel_case7 X Y Z a hX hY hZ w hw
  simp only [first7Coeff,first7Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole7,SmallLevelTwentyTwoFirstJet.first]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms first7_projection
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second7_syzygy (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) : (∑ i, second7Coeff X Y Z a i*leadingRows (1) (1) (1) X Y Z a w (second7Indices i))=0 := by
  simp only [second7Coeff,second7Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second7_syzygy
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem second7_projection (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (∑ i, second7Coeff (X/2) (Y/3) (Z/11) a i*firstRows (1) (1) (1) X Y Z a w (second7Indices i))=
      (((-11))/(3*X*Z))*SmallLevelTwentyTwoFirstJet.second (1) X Y*w 44 := by
  have hk := kernel_case7 X Y Z a hX hY hZ w hw
  simp only [second7Coeff,second7Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65]
  norm_num [pole7,SmallLevelTwentyTwoFirstJet.second]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms second7_projection
end SmallLevelTwentyTwoLaurent
end
end
end
end

/-! ## TwentyTwoSyzygyUseCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoLaurent
open Complex SmallLevelPrimeRates

theorem first0_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => first0Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [first0Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem first0_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (-1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,first0Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (-1) (-1) (-1) X Y Z a w (first0Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.first (-1) X Y=0 := by
  have hp:=(first0_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((-22:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms first0_analytic
#print axioms first0_necessary

theorem second0_analytic (m : ℕ) (a z : ℂ) (i : Fin 27) :
    AnalyticAt ℂ (fun s => second0Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [second0Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem second0_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (-1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,second0Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (-1) (-1) (-1) X Y Z a w (second0Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.second (-1) X Y=0 := by
  have hp:=(second0_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((-11:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms second0_analytic
#print axioms second0_necessary

theorem first1_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => first1Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [first1Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem first1_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,first1Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (-1) (-1) (1) X Y Z a w (first1Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.first (-1) X Y=0 := by
  have hp:=(first1_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((-22:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms first1_analytic
#print axioms first1_necessary

theorem second1_analytic (m : ℕ) (a z : ℂ) (i : Fin 27) :
    AnalyticAt ℂ (fun s => second1Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [second1Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem second1_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,second1Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (-1) (-1) (1) X Y Z a w (second1Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.second (-1) X Y=0 := by
  have hp:=(second1_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((-11:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms second1_analytic
#print axioms second1_necessary

theorem first2_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => first2Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [first2Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem first2_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,first2Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (-1) (1) (-1) X Y Z a w (first2Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.first (1) X Y=0 := by
  have hp:=(first2_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((22:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms first2_analytic
#print axioms first2_necessary

theorem second2_analytic (m : ℕ) (a z : ℂ) (i : Fin 27) :
    AnalyticAt ℂ (fun s => second2Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [second2Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem second2_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,second2Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (-1) (1) (-1) X Y Z a w (second2Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.second (1) X Y=0 := by
  have hp:=(second2_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((11:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms second2_analytic
#print axioms second2_necessary

theorem first3_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => first3Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [first3Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem first3_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,first3Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (-1) (1) (1) X Y Z a w (first3Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.first (1) X Y=0 := by
  have hp:=(first3_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((22:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms first3_analytic
#print axioms first3_necessary

theorem second3_analytic (m : ℕ) (a z : ℂ) (i : Fin 27) :
    AnalyticAt ℂ (fun s => second3Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [second3Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem second3_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,second3Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (-1) (1) (1) X Y Z a w (second3Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.second (1) X Y=0 := by
  have hp:=(second3_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((11:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms second3_analytic
#print axioms second3_necessary

theorem first4_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => first4Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [first4Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem first4_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,first4Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (1) (-1) (-1) X Y Z a w (first4Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.first (-1) X Y=0 := by
  have hp:=(first4_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((22:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms first4_analytic
#print axioms first4_necessary

theorem second4_analytic (m : ℕ) (a z : ℂ) (i : Fin 27) :
    AnalyticAt ℂ (fun s => second4Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [second4Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem second4_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,second4Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (1) (-1) (-1) X Y Z a w (second4Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.second (-1) X Y=0 := by
  have hp:=(second4_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((11:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms second4_analytic
#print axioms second4_necessary

theorem first5_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => first5Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [first5Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem first5_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,first5Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (1) (-1) (1) X Y Z a w (first5Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.first (-1) X Y=0 := by
  have hp:=(first5_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((22:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms first5_analytic
#print axioms first5_necessary

theorem second5_analytic (m : ℕ) (a z : ℂ) (i : Fin 27) :
    AnalyticAt ℂ (fun s => second5Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [second5Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem second5_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,second5Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (1) (-1) (1) X Y Z a w (second5Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.second (-1) X Y=0 := by
  have hp:=(second5_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((11:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms second5_analytic
#print axioms second5_necessary

theorem first6_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => first6Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [first6Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem first6_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,first6Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (1) (1) (-1) X Y Z a w (first6Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.first (1) X Y=0 := by
  have hp:=(first6_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((-22:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms first6_analytic
#print axioms first6_necessary

theorem second6_analytic (m : ℕ) (a z : ℂ) (i : Fin 27) :
    AnalyticAt ℂ (fun s => second6Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [second6Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem second6_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,second6Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (1) (1) (-1) X Y Z a w (second6Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.second (1) X Y=0 := by
  have hp:=(second6_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((-11:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms second6_analytic
#print axioms second6_necessary

theorem first7_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => first7Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [first7Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem first7_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,first7Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (1) (1) (1) X Y Z a w (first7Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.first (1) X Y=0 := by
  have hp:=(first7_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((-22:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms first7_analytic
#print axioms first7_necessary

theorem second7_analytic (m : ℕ) (a z : ℂ) (i : Fin 27) :
    AnalyticAt ℂ (fun s => second7Coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [second7Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem second7_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) (h44 : w 44≠0)
    (hfirst : (∑ i,second7Coeff (X/2) (Y/3) (Z/11) a i*
      firstRows (1) (1) (1) X Y Z a w (second7Indices i))=0) :
    SmallLevelTwentyTwoFirstJet.second (1) X Y=0 := by
  have hp:=(second7_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  have hc : ((-11:ℂ)/(3*X*Z))≠0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (by norm_num) hX) hZ)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right h44)).resolve_left hc

#print axioms second7_analytic
#print axioms second7_necessary

end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoResidual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoLaurent
open Complex

def residual (η u X Y Z a : ℂ) : ℂ :=
  η*((1)/(X*Z) + ((-1)*Y*a)/(X*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^3*a)/(Y*Z)) + η*u*(((-1))/(Y^2*Z) + ((-1)*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z))

theorem residual_some_point (η u a : ℂ) (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) :
    residual η u (1/2) (1/3) (1/11) a≠0 ∨ residual η u (1/4) (1/9) (1/121) a≠0 := by
  by_contra h
  push Not at h
  obtain ⟨ha,hb⟩:=h
  rcases hη with rfl|rfl <;> rcases hu with rfl|rfl
  · norm_num [residual] at ha hb
    have he : (1:ℂ)=0 := by
      linear_combination (211356/198133265)*ha + (-204768/2179465915)*hb
    norm_num at he
  · norm_num [residual] at ha hb
    have he : (1:ℂ)=0 := by
      linear_combination (-204/103765)*ha + (12384/87888955)*hb
    norm_num at he
  · norm_num [residual] at ha hb
    have he : (1:ℂ)=0 := by
      linear_combination (-211356/198133265)*ha + (204768/2179465915)*hb
    norm_num at he
  · norm_num [residual] at ha hb
    have he : (1:ℂ)=0 := by
      linear_combination (204/103765)*ha + (-12384/87888955)*hb
    norm_num at he

#print axioms residual_some_point
end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoResidualCaseFamilyV4 -/
section
@[expose] public noncomputable section
section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_case0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (-1) X Y Z a w=0) :
    residual (-1) (-1) X Y Z a*w 44=0 := by
  have hk := kernel_case0 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (57:Fin 66)
  change leadingRows (-1) (-1) (-1) X Y Z a w (57:Fin 68)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65] at hr
  norm_num [pole0] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (-1) (-1) X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (-1) X Y Z a w=0) : w=0 := by
  have h44 : w 44=0 := (mul_eq_zero.mp (residual_case0 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case0 X Y Z a hX hY hZ w hw j

#print axioms residual_case0
#print axioms kernel_zero_case0
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    residual (-1) (-1) X Y Z a*w 44=0 := by
  have hk := kernel_case1 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (57:Fin 66)
  change leadingRows (-1) (-1) (1) X Y Z a w (57:Fin 68)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65] at hr
  norm_num [pole1] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (-1) (-1) X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) : w=0 := by
  have h44 : w 44=0 := (mul_eq_zero.mp (residual_case1 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case1 X Y Z a hX hY hZ w hw j

#print axioms residual_case1
#print axioms kernel_zero_case1
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    residual (-1) (1) X Y Z a*w 44=0 := by
  have hk := kernel_case2 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (57:Fin 66)
  change leadingRows (-1) (1) (-1) X Y Z a w (57:Fin 68)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65] at hr
  norm_num [pole2] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (-1) (1) X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) : w=0 := by
  have h44 : w 44=0 := (mul_eq_zero.mp (residual_case2 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case2 X Y Z a hX hY hZ w hw j

#print axioms residual_case2
#print axioms kernel_zero_case2
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    residual (-1) (1) X Y Z a*w 44=0 := by
  have hk := kernel_case3 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (57:Fin 66)
  change leadingRows (-1) (1) (1) X Y Z a w (57:Fin 68)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65] at hr
  norm_num [pole3] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (-1) (1) X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) : w=0 := by
  have h44 : w 44=0 := (mul_eq_zero.mp (residual_case3 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case3 X Y Z a hX hY hZ w hw j

#print axioms residual_case3
#print axioms kernel_zero_case3
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_case4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    residual (1) (-1) X Y Z a*w 44=0 := by
  have hk := kernel_case4 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (57:Fin 66)
  change leadingRows (1) (-1) (-1) X Y Z a w (57:Fin 68)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65] at hr
  norm_num [pole4] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (1) (-1) X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) : w=0 := by
  have h44 : w 44=0 := (mul_eq_zero.mp (residual_case4 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case4 X Y Z a hX hY hZ w hw j

#print axioms residual_case4
#print axioms kernel_zero_case4
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_case5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    residual (1) (-1) X Y Z a*w 44=0 := by
  have hk := kernel_case5 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (57:Fin 66)
  change leadingRows (1) (-1) (1) X Y Z a w (57:Fin 68)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65] at hr
  norm_num [pole5] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (1) (-1) X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) : w=0 := by
  have h44 : w 44=0 := (mul_eq_zero.mp (residual_case5 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case5 X Y Z a hX hY hZ w hw j

#print axioms residual_case5
#print axioms kernel_zero_case5
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_case6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    residual (1) (1) X Y Z a*w 44=0 := by
  have hk := kernel_case6 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (57:Fin 66)
  change leadingRows (1) (1) (-1) X Y Z a w (57:Fin 68)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65] at hr
  norm_num [pole6] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (1) (1) X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) : w=0 := by
  have h44 : w 44=0 := (mul_eq_zero.mp (residual_case6 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case6 X Y Z a hX hY hZ w hw j

#print axioms residual_case6
#print axioms kernel_zero_case6
end SmallLevelTwentyTwoLaurent
end

section
-- These generated finite-row proofs share a simplifier list across coordinates.
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000

namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_case7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    residual (1) (1) X Y Z a*w 44=0 := by
  have hk := kernel_case7 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (57:Fin 66)
  change leadingRows (1) (1) (1) X Y Z a w (57:Fin 68)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65] at hr
  norm_num [pole7] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (1) (1) X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) : w=0 := by
  have h44 : w 44=0 := (mul_eq_zero.mp (residual_case7 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case7 X Y Z a hX hY hZ w hw j

#print axioms residual_case7
#print axioms kernel_zero_case7
end SmallLevelTwentyTwoLaurent
end
end
end

/-! ## TwentyTwoKernelCertificates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoLaurent
open Complex

theorem core_kernel_zero (η u v X Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hd : residual η u X Y Z a≠0)
    (w : Fin 66→ℂ) (hw : coreRows η u v X Y Z a w=0) : w=0 := by
  rcases hη with rfl|rfl <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · exact kernel_zero_case7 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case6 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case5 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case4 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case3 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case2 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case1 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case0 X Y Z a hX hY hZ hd w hw

theorem core_kernel_coordinate_ne_zero (η u v X Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows η u v X Y Z a w=0) (hw0 : w≠0) : w 44≠0 := by
  intro h44
  apply hw0
  rcases hη with rfl|rfl <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · funext j
    simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case7 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case6 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case5 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case4 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case3 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case2 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case1 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h44,mul_zero,Pi.zero_apply] using kernel_case0 X Y Z a hX hY hZ w hw j

theorem core_residual_zero (η u v X Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows η u v X Y Z a w=0) (hw0 : w≠0) :
    residual η u X Y Z a=0 := by
  by_contra hd
  exact hw0 (core_kernel_zero η u v X Y Z a hη hu hv hX hY hZ hd w hw)

#print axioms core_kernel_zero
#print axioms core_kernel_coordinate_ne_zero
#print axioms core_residual_zero
end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoFirstJetPhysical -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoFirstJet
open Complex

/-- On the actual exponential curve, the two first-jet equations force
h=1 and the negative ramified-two sign. No eigenvalue is divided by. -/
theorem physical (h u : ℂ) (hu : u=1 ∨ u= -1)
    (h1 : first u ((2:ℂ)^h) ((3:ℂ)^h)=0)
    (h2 : second u ((2:ℂ)^h) ((3:ℂ)^h)=0) : h=1 ∧ u= -1 := by
  have hx : (2:ℂ)^h≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rcases alternatives u _ _ hu hx h1 h2 with ⟨hx,hy⟩|⟨hx,hy⟩
  · have hp2 : ((2:ℂ)^(h-1))^(2:ℕ)=1 := by
      rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0),Complex.cpow_one,hx]
      rcases hu with rfl|rfl <;> norm_num
    have hp3 : ((3:ℂ)^(h-1))^(2:ℕ)=1 := by
      rw [Complex.cpow_sub _ _ (by norm_num : (3:ℂ)≠0),Complex.cpow_one,div_pow,hy]
      norm_num
    have hh := QuantitativeArithmeticPrimePowerTorsion.distinct_primes_cpow_torsion
      (by decide : Nat.Prime 2) (by decide : Nat.Prime 3) (by decide : (2:ℕ)≠3)
      (h-1) 2 2 (by decide) (by decide) hp2 hp3
    have he : h=1 := sub_eq_zero.mp hh
    refine ⟨he,?_⟩
    rw [he,Complex.cpow_one] at hx
    linear_combination hx/2
  · have hn : ‖(2:ℂ)^h‖=1 := by rw [hx]; rcases hu with rfl|rfl <;> norm_num
    have hr : h.re=0 := by
      apply (Real.rpow_right_inj (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)).mp
      have hn2 := Complex.norm_natCast_cpow_of_pos (by decide : 0<2) h
      norm_num only [Nat.cast_ofNat] at hn2
      rw [hn2] at hn
      simpa only [Real.rpow_zero] using hn
    have hn3 : ‖(3:ℂ)^h‖=1 := by
      have hn3 := Complex.norm_natCast_cpow_of_pos (by decide : 0<3) h
      norm_num only [Nat.cast_ofNat] at hn3
      rw [hn3,hr,Real.rpow_zero]
    have hh := congrArg norm hy
    rw [norm_pow,hn3] at hh
    norm_num at hh

#print axioms physical
end SmallLevelTwentyTwoFirstJet
end
end

/-! ## TwentyTwoFirstJetUse -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoLaurent
open Complex SmallLevelPrimeRates

/-- The finite collection of verified left syzygies forces the two scalar
first-jet equations for every root-sign choice. -/
theorem firstJet_equations (m : ℕ) (η u v a x : ℂ)
    (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (w : Fin 66→ℂ)
    (hw : coreRows η u v (parameter 2 m x) (parameter 3 m x) (parameter 11 m x) a w=0)
    (hw0 : w≠0)
    (hselected : ∀ (r : ℕ) (rows : Fin r→Fin 68) (coeff : ℂ→ℂ→ℂ→Fin r→ℂ),
      (∀ z i, AnalyticAt ℂ
        (fun s => coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) i) z) →
      (∀ X Y Z : ℂ, X≠0 → Y≠0 → Z≠0 → ∀ q : Fin 66→ℂ,
        ∑ i,coeff X Y Z i*leadingRows η u v X Y Z a q (rows i)=0) →
      ∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3) (parameter 11 m x/11) i*
        firstRows η u v (parameter 2 m x) (parameter 3 m x) (parameter 11 m x) a w (rows i)=0) :
    SmallLevelTwentyTwoFirstJet.first u (parameter 2 m x) (parameter 3 m x)=0 ∧
    SmallLevelTwentyTwoFirstJet.second u (parameter 2 m x) (parameter 3 m x)=0 := by
  have hX:=parameter_ne_zero 2 m (by decide) x
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=parameter_ne_zero 11 m (by decide) x
  have h44:=core_kernel_coordinate_ne_zero η u v _ _ _ a hη hu hv hX hY hZ w hw hw0
  rcases hη with rfl|rfl <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · constructor
    · apply first7_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ first7Indices (fun X Y Z => first7Coeff X Y Z a)
      · exact first7_analytic m a
      · intro X Y Z hX hY hZ q
        exact first7_syzygy X Y Z a hX hY hZ q
    · apply second7_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ second7Indices (fun X Y Z => second7Coeff X Y Z a)
      · exact second7_analytic m a
      · intro X Y Z hX hY hZ q
        exact second7_syzygy X Y Z a hX hY hZ q
  · constructor
    · apply first6_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ first6Indices (fun X Y Z => first6Coeff X Y Z a)
      · exact first6_analytic m a
      · intro X Y Z hX hY hZ q
        exact first6_syzygy X Y Z a hX hY hZ q
    · apply second6_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ second6Indices (fun X Y Z => second6Coeff X Y Z a)
      · exact second6_analytic m a
      · intro X Y Z hX hY hZ q
        exact second6_syzygy X Y Z a hX hY hZ q
  · constructor
    · apply first5_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ first5Indices (fun X Y Z => first5Coeff X Y Z a)
      · exact first5_analytic m a
      · intro X Y Z hX hY hZ q
        exact first5_syzygy X Y Z a hX hY hZ q
    · apply second5_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ second5Indices (fun X Y Z => second5Coeff X Y Z a)
      · exact second5_analytic m a
      · intro X Y Z hX hY hZ q
        exact second5_syzygy X Y Z a hX hY hZ q
  · constructor
    · apply first4_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ first4Indices (fun X Y Z => first4Coeff X Y Z a)
      · exact first4_analytic m a
      · intro X Y Z hX hY hZ q
        exact first4_syzygy X Y Z a hX hY hZ q
    · apply second4_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ second4Indices (fun X Y Z => second4Coeff X Y Z a)
      · exact second4_analytic m a
      · intro X Y Z hX hY hZ q
        exact second4_syzygy X Y Z a hX hY hZ q
  · constructor
    · apply first3_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ first3Indices (fun X Y Z => first3Coeff X Y Z a)
      · exact first3_analytic m a
      · intro X Y Z hX hY hZ q
        exact first3_syzygy X Y Z a hX hY hZ q
    · apply second3_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ second3Indices (fun X Y Z => second3Coeff X Y Z a)
      · exact second3_analytic m a
      · intro X Y Z hX hY hZ q
        exact second3_syzygy X Y Z a hX hY hZ q
  · constructor
    · apply first2_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ first2Indices (fun X Y Z => first2Coeff X Y Z a)
      · exact first2_analytic m a
      · intro X Y Z hX hY hZ q
        exact first2_syzygy X Y Z a hX hY hZ q
    · apply second2_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ second2Indices (fun X Y Z => second2Coeff X Y Z a)
      · exact second2_analytic m a
      · intro X Y Z hX hY hZ q
        exact second2_syzygy X Y Z a hX hY hZ q
  · constructor
    · apply first1_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ first1Indices (fun X Y Z => first1Coeff X Y Z a)
      · exact first1_analytic m a
      · intro X Y Z hX hY hZ q
        exact first1_syzygy X Y Z a hX hY hZ q
    · apply second1_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ second1Indices (fun X Y Z => second1Coeff X Y Z a)
      · exact second1_analytic m a
      · intro X Y Z hX hY hZ q
        exact second1_syzygy X Y Z a hX hY hZ q
  · constructor
    · apply first0_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ first0Indices (fun X Y Z => first0Coeff X Y Z a)
      · exact first0_analytic m a
      · intro X Y Z hX hY hZ q
        exact first0_syzygy X Y Z a hX hY hZ q
    · apply second0_necessary _ _ _ a hX hY hZ w hw h44
      apply hselected _ second0Indices (fun X Y Z => second0Coeff X Y Z a)
      · exact second0_analytic m a
      · intro X Y Z hX hY hZ q
        exact second0_syzygy X Y Z a hX hY hZ q

#print axioms firstJet_equations
end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoResidualCandidate -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoLaurent
open Complex

theorem residual_candidate (η a : ℂ) (hη : η=1 ∨ η= -1)
    (hr : residual η (-1) 2 3 11 a=0) : a= -7/3 := by
  rcases hη with rfl|rfl
  · norm_num [residual] at hr
    linear_combination (-22/7)*hr
  · norm_num [residual] at hr
    linear_combination (22/7)*hr

#print axioms residual_candidate
end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoPhysicalCandidate -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoLaurent
open Complex SmallLevelPrimeRates

theorem physical_candidate (m : ℕ) (η u v a x : ℂ)
    (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (w : Fin 66→ℂ)
    (hw : coreRows η u v (parameter 2 m x) (parameter 3 m x) (parameter 11 m x) a w=0)
    (hw0 : w≠0)
    (h1 : SmallLevelTwentyTwoFirstJet.first u (parameter 2 m x) (parameter 3 m x)=0)
    (h2 : SmallLevelTwentyTwoFirstJet.second u (parameter 2 m x) (parameter 3 m x)=0) :
    x=(m:ℂ)+1 ∧ u= -1 ∧ a= -7/3 := by
  have h1' : SmallLevelTwentyTwoFirstJet.first u ((2:ℂ)^(x-(m:ℂ)))
      ((3:ℂ)^(x-(m:ℂ)))=0 := by simpa only [parameter,Nat.cast_ofNat] using h1
  have h2' : SmallLevelTwentyTwoFirstJet.second u ((2:ℂ)^(x-(m:ℂ)))
      ((3:ℂ)^(x-(m:ℂ)))=0 := by simpa only [parameter,Nat.cast_ofNat] using h2
  obtain ⟨hx,hu'⟩:=SmallLevelTwentyTwoFirstJet.physical (x-(m:ℂ)) u hu h1' h2'
  have he : x=(m:ℂ)+1 := by linear_combination hx
  refine ⟨he,hu',?_⟩
  have hr:=core_residual_zero η u v _ _ _ a hη hu hv
    (parameter_ne_zero 2 m (by decide) x) (parameter_ne_zero 3 m (by decide) x)
    (parameter_ne_zero 11 m (by decide) x) w hw hw0
  have hp (p : ℕ) : parameter p m x=(p:ℂ) := by
    simp only [parameter,hx,Complex.cpow_one]
  rw [hu',hp 2,hp 3,hp 11] at hr
  exact residual_candidate η a hη hr

#print axioms physical_candidate
end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoMatrixSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Set Matrix SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelTwentyTwo

def errorVector (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (E : Fin 35→ℕ→ℂ→ℂ)
    (M : ℕ) (s : ℂ) : Fin 66→ℂ :=
  gridAssemble (fun i => E i M s) (fun i => gridTaylorError m f ε i M s)
    (fun i => ramanujanEntire 22 (2*m) f (gridEntireSpecs i) s) 0

theorem hecke_grid (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (i : Fin 16) :
    gridHeckeLeading m f s (gridVector (2*m) f s) i=gridHeckeRow m f i s := by
  unfold gridHeckeLeading gridHeckeRow
  split_ifs <;> simp only [gridVector_index,gridHeckeTwo,gridHeckeThree]

theorem coherent_matrix_system {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∃ E : Fin 35→ℕ→ℂ→ℂ,
      (∀ i : Fin 66, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 66, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => errorVector m f ε E M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        gridLeadingMatrix m f ε s *ᵥ gridVector (2*m) f s=
          errorVector m f ε E M s+
            ∑ n∈Finset.range M, gridShiftMatrix m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  choose b E hG using grid_matrix_rows_of_fricke m hf (grid_physical_sign m hε)
    (grid_fricke_of_laws m hε hlaw)
  let BG : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbG (i : Fin 35) : b i≤BG:=Finset.le_sup' b (Finset.mem_univ i)
  obtain ⟨BT,hT⟩:=grid_ramanujan_system_of_laws m hf hlaw
  obtain ⟨hRE,BR,hR⟩:=original_grid_entire_rows (by omega : 0<2*m) hf
  obtain ⟨BH,hH⟩:=original_grid_hecke_rows hm hf
  obtain ⟨BF,hF⟩:=SmallLevelAdditive.original_common_halfplane hf
  let B : ℝ:=max BG (max (max BT BR) (max BH BF))
  have hBG : BG≤B:=le_max_left _ _
  have hBT : BT≤B:=(le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hBR : BR≤B:=(le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hBH : BH≤B:=(le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBF : BF≤B:=(le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨B,E,?_,?_,?_⟩
  · intro i s hs
    exact (hF (((i:ℕ):ℝ)/66) s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have hg (j : Fin 35) : AnalyticAt ℂ (E j M) s := by
      apply (hG j M).1 s
      change b j-((M:ℝ)+1)<s.re
      linarith [hbG j]
    have ht (j : Fin 11) : AnalyticAt ℂ (gridTaylorError m f ε j M) s := by
      apply (hT j M).1 s
      change BT-((M:ℝ)+1)<s.re
      linarith
    unfold errorVector gridAssemble
    split_ifs
    · exact hg _
    · exact ht _
    · exact hRE _ s
    · exact analyticAt_const
  · intro M s hs
    have hg (j : Fin 35):=(hG j M).2 s (lt_of_le_of_lt ((hbG j).trans hBG) hs)
    have ht (j : Fin 11):=(hT j M).2 s (lt_of_le_of_lt hBT hs)
    rw [gridLeadingMatrix_mulVec]
    simp_rw [gridShiftMatrix_mulVec]
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    unfold gridLeadingRows gridShiftRows errorVector gridAssemble
    split_ifs
    · simpa only [gridGroupLeading,gridVector] using hg ⟨i.val,by assumption⟩
    · simpa only [gridRamanujanLeading,gridSample_grid] using ht ⟨i.val-35,by omega⟩
    · simp only [Pi.zero_apply,Finset.sum_const_zero,add_zero,gridSample_grid]
      exact (hR _ s (lt_of_le_of_lt hBR hs)).symm
    · simp only [Pi.zero_apply,Finset.sum_const_zero,add_zero,hecke_grid]
      exact hH _ s (lt_of_le_of_lt hBH hs)

#print axioms hecke_grid
#print axioms coherent_matrix_system
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoMatrixAnalytic -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex SmallLevelTaylor QuantitativeArithmeticSmallLevelTwentyTwo

theorem matrixScalar_analytic (m : ℕ) (δ η : ℂ) (i : Fin 35) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (gridMatrixScalar m δ η i n) s := by
  have hn : (gridGroupRate i:ℂ)≠0 := by
    fin_cases i <;> norm_num [gridGroupRate]
  have hp : AnalyticAt ℂ (fun z : ℂ => (gridGroupRate i:ℂ)^(z-(m:ℂ))) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  exact ((analyticAt_const.mul hp).mul analyticAt_const).mul (binomial_shift_analytic (2*m) n s)

theorem taylorCoefficient_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 11) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (gridTaylorCoefficient m f ε i n) s := by
  have hv:=gridTaylorSpecs_valid i
  have hr : (gridTaylorT i:ℝ)/66≠0 := div_ne_zero (by exact_mod_cast hv.2.2.1) (by norm_num)
  have hL : (0:ℝ)<gridTaylorL i := by
    exact_mod_cast (Nat.lcm_pos (by decide : 0<22) (pow_pos hv.1 2))
  exact taylorRowScalar_analytic (2*m) hL hr _ n s

theorem heckeScalar_analytic (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    AnalyticAt ℂ (heckeScalar m f) s := by
  unfold heckeScalar
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop

theorem leadingMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i j : Fin 66) :
    AnalyticAt ℂ (fun z => gridLeadingMatrix m f ε z i j) x := by
  simp_rw [gridLeadingMatrix_apply]
  unfold gridLeadingRows gridAssemble
  split_ifs
  · exact analyticAt_const.sub ((matrixScalar_analytic m _ _ _ 0 x).mul analyticAt_const)
  · exact analyticAt_const.sub ((taylorCoefficient_analytic m f ε _ 0 x).mul analyticAt_const)
  · exact analyticAt_const
  · unfold gridHeckeLeading
    split_ifs
    · exact (analyticAt_const.add analyticAt_const).sub
        ((heckeScalar_analytic m f x).mul analyticAt_const)
    · have hp : AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^((m:ℂ)-z)) x := by
        simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
        fun_prop
      exact (((analyticAt_const.add analyticAt_const).add analyticAt_const).sub
        ((analyticAt_const.mul hp).mul analyticAt_const)).add
        ((hp.pow 2).mul analyticAt_const)

theorem shiftMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ) (i j : Fin 66) :
    AnalyticAt ℂ (fun z => gridShiftMatrix m f ε n z i j) x := by
  simp_rw [gridShiftMatrix_apply]
  unfold gridShiftRows gridAssemble
  split_ifs
  · exact (matrixScalar_analytic m _ _ _ (n+1) x).mul analyticAt_const
  · exact (taylorCoefficient_analytic m f ε _ (n+1) x).mul analyticAt_const
  · exact analyticAt_const
  · exact analyticAt_const

#print axioms leadingMatrix_analytic
#print axioms shiftMatrix_analytic
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoExtendedSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix QuantitativeArithmeticSmallLevelTwentyTwo

def extraHeckeIndex (i : Fin 68) : ℤ := if i.val=66 then 6 else 28

def extraHeckeRow (j : ℤ) (a : ℂ) (q : Fin 66) : ℂ :=
  (if q=gridIndex j then 1 else 0)+(if q=gridIndex (j+33) then 1 else 0)-
    a*(if q=gridIndex (2*j) then 1 else 0)

theorem extraHeckeRow_mul (j : ℤ) (a : ℂ) (w : Fin 66→ℂ) :
    (∑ q,extraHeckeRow j a q*w q)=w (gridIndex j)+w (gridIndex (j+33))-a*w (gridIndex (2*j)) := by
  simp [extraHeckeRow,add_mul,sub_mul,Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

def extendedLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix (Fin 68) (Fin 66) ℂ :=
  fun i j => if hi : i.val<66 then gridLeadingMatrix m f ε s ⟨i.val,hi⟩ j
    else extraHeckeRow (extraHeckeIndex i) (heckeScalar m f s) j

def extendedShift (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 68) (Fin 66) ℂ :=
  fun i j => if hi : i.val<66 then gridShiftMatrix m f ε n s ⟨i.val,hi⟩ j else 0

def extendedError (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (E : Fin 35→ℕ→ℂ→ℂ)
    (n : ℕ) (s : ℂ) (i : Fin 68) : ℂ :=
  if hi : i.val<66 then errorVector m f ε E n s ⟨i.val,hi⟩ else 0

theorem extendedLeading_analytic (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i : Fin 68) (j : Fin 66) :
    AnalyticAt ℂ (fun z => extendedLeading m f ε z i j) x := by
  unfold extendedLeading
  split_ifs
  · exact leadingMatrix_analytic m f ε x _ j
  · unfold extraHeckeRow
    exact (analyticAt_const.add analyticAt_const).sub
      ((heckeScalar_analytic m f x).mul analyticAt_const)

theorem extendedShift_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ)
    (i : Fin 68) (j : Fin 66) : AnalyticAt ℂ (fun z => extendedShift m f ε n z i j) x := by
  unfold extendedShift
  split_ifs
  · exact shiftMatrix_analytic m f ε n x _ j
  · exact analyticAt_const

/-- The actual original system with both additional Hecke-two rows. -/
theorem extended_matrix_system {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∃ E : Fin 35→ℕ→ℂ→ℂ,
      (∀ i : Fin 66, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 68, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => extendedError m f ε E M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        extendedLeading m f ε s *ᵥ gridVector (2*m) f s=
          extendedError m f ε E M s+
            ∑ n∈Finset.range M, extendedShift m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  obtain ⟨B,E,hF,hH,hrow⟩:=coherent_matrix_system hm hf hε hlaw
  obtain ⟨C,hC⟩:=original_grid_hecke_two hm hf
  refine ⟨max B C,E,fun i s hs => hF i s (lt_of_le_of_lt (le_max_left _ _) hs),?_,?_⟩
  · intro M i s hs
    unfold extendedError
    split_ifs
    · apply hH M _ s
      linarith [le_max_left B C]
    · exact analyticAt_const
  · intro M s hs
    have hsB : B<s.re:=lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : C<s.re:=lt_of_le_of_lt (le_max_right _ _) hs
    funext i
    simp only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply]
    by_cases hi : i.val<66
    · simp only [extendedLeading,extendedShift,extendedError,dite_eq_left hi]
      simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using
        congrFun (hrow M s hsB) ⟨i.val,hi⟩
    · simp only [extendedLeading,extendedShift,extendedError,dite_eq_right hi,
        zero_mul,Finset.sum_const_zero,zero_add]
      rw [extraHeckeRow_mul]
      simp only [gridVector_index]
      exact hC (extraHeckeIndex i) s hsC

#print axioms extraHeckeRow_mul
#print axioms extendedLeading_analytic
#print axioms extended_matrix_system
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoParameters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoParameters
open Complex FinitenessNormalizedTwistProduct QuantitativeArithmeticSmallLevelTwentyTwo

def sigmaTwo (f : ℕ→ℂ) : ℂ := (Real.sqrt 2:ℂ)*f 2
def sigmaEleven (f : ℕ→ℂ) : ℂ := (Real.sqrt 11:ℂ)*f 11
def phase (m : ℕ) (ε : ℂ) : ℂ := ε*I^(2*m)

theorem root_two (f : ℕ→ℂ) : root 22 f 2= -sigmaTwo f := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign,sigmaTwo]
  ring

theorem root_three (f : ℕ→ℂ) : root 22 f 3=1 := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign]

theorem root_six (f : ℕ→ℂ) : root 22 f 6= -sigmaTwo f := by
  have hp : Nat.primeFactors 6=({2,3}:Finset ℕ) := by
    rw [show (6:ℕ)=2*3 by decide,Nat.primeFactors_mul (by decide : (2:ℕ)≠0) (by decide : (3:ℕ)≠0),
      (by decide : Nat.Prime 2).primeFactors,(by decide : Nat.Prime 3).primeFactors]
    simp
  norm_num [root,hp,FinitenessNormalizedTwistLocal.sign,sigmaTwo]
  ring

theorem root_eleven (f : ℕ→ℂ) : root 22 f 11= -sigmaEleven f := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign,sigmaEleven]
  ring

theorem sigmaTwo_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 22 f) :
    sigmaTwo f=1 ∨ sigmaTwo f= -1 := by
  have h:=root_unit hf 2
  rw [root_two] at h
  rcases h with h|h
  · right; linear_combination -h
  · left; linear_combination -h

theorem sigmaEleven_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 22 f) :
    sigmaEleven f=1 ∨ sigmaEleven f= -1 := by
  have h:=root_unit hf 11
  rw [root_eleven] at h
  rcases h with h|h
  · right; linear_combination -h
  · left; linear_combination -h

theorem phase_sign (m : ℕ) {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    phase m ε=1 ∨ phase m ε= -1 := by
  have hi : I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,I_sq]
  unfold phase
  rw [hi]
  rcases neg_one_pow_eq_or ℂ m with h|h <;> rw [h] <;>
    rcases hε with rfl|rfl <;> norm_num

#print axioms sigmaTwo_sign
#print axioms sigmaEleven_sign
#print axioms phase_sign
end SmallLevelTwentyTwoParameters
end
end

/-! ## TwentyTwoRates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoParameters
open Complex SmallLevelPrimeRates QuantitativeArithmeticSmallLevelTwentyTwo

def groupPowers : Fin 35→ℤ×ℤ×ℤ
  | 0 => (1, 0, 1)
  | 1 => (-1, -2, -1)
  | 2 => (-1, 0, -1)
  | 3 => (-1, -2, -1)
  | 4 => (1, 2, 0)
  | 5 => (-1, 0, 0)
  | 6 => (-1, 2, 1)
  | 7 => (1, -2, -1)
  | 8 => (1, 0, -1)
  | 9 => (-1, 0, 1)
  | 10 => (1, -2, 0)
  | 11 => (1, 0, 0)
  | 12 => (1, 0, 0)
  | 13 => (-1, 2, -1)
  | 14 => (-1, -2, 1)
  | 15 => (1, 2, -1)
  | 16 => (1, -2, 1)
  | 17 => (0, 2, 0)
  | 18 => (0, -2, 0)
  | 19 => (-1, 0, 0)
  | 20 => (1, 2, 0)
  | 21 => (-1, 2, 0)
  | 22 => (-1, -2, 0)
  | 23 => (1, -2, 0)
  | 24 => (-1, 0, 0)
  | 25 => (1, 0, 0)
  | 26 => (-1, 2, 0)
  | 27 => (1, 2, 0)
  | 28 => (1, 2, 0)
  | 29 => (-1, 2, 0)
  | 30 => (1, 0, 0)
  | 31 => (1, -2, 0)
  | 32 => (-1, -2, 0)
  | 33 => (-1, -2, 0)
  | _ => (1, 2, 0)

def taylorPowers : Fin 11→ℤ×ℤ×ℤ
  | 0 => (1, 0, -1)
  | 1 => (1, 0, -1)
  | 2 => (-1, 0, 0)
  | 3 => (0, 0, -1)
  | 4 => (0, 0, -1)
  | 5 => (-1, 0, -1)
  | 6 => (-1, 0, -1)
  | 7 => (-1, -2, 0)
  | 8 => (1, -2, 0)
  | 9 => (1, -2, 0)
  | _ => (-1, -2, 0)

def taylorRate (i : Fin 11) : ℚ := (gridTaylorL i:ℚ)*((gridTaylorT i:ℚ)/66)^2

theorem groupRate_factor (i : Fin 35) :
    gridGroupRate i=(2:ℚ)^(groupPowers i).1*(3:ℚ)^(groupPowers i).2.1*(11:ℚ)^(groupPowers i).2.2 := by
  fin_cases i <;> norm_num [gridGroupRate,groupPowers]

theorem taylorRate_factor (i : Fin 11) :
    taylorRate i=(2:ℚ)^(taylorPowers i).1*(3:ℚ)^(taylorPowers i).2.1*(11:ℚ)^(taylorPowers i).2.2 := by
  fin_cases i <;> norm_num [taylorRate,gridTaylorL,gridTaylorQ,gridTaylorT,gridTaylorSpecs,taylorPowers]

theorem groupRate_complex (i : Fin 35) (h : ℂ) :
    (gridGroupRate i:ℂ)^h=monomial (groupPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((11:ℂ)^h) :=
  rational_power 2 3 11 (by decide) (by decide) (by decide) _ _ (groupRate_factor i) h

theorem taylorRate_complex (i : Fin 11) (h : ℂ) :
    (taylorRate i:ℂ)^h=monomial (taylorPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((11:ℂ)^h) :=
  rational_power 2 3 11 (by decide) (by decide) (by decide) _ _ (taylorRate_factor i) h

theorem heckeScalar_parameter (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    heckeScalar m f s=sigmaTwo f/parameter 2 m s := by
  have hh : (2:ℂ)^((m:ℂ)-s)=(2:ℂ)^(m:ℕ)*(2:ℂ)^(-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ (by norm_num),Complex.cpow_natCast]
  have hi : (2:ℂ)^((m:ℂ)-s)=(parameter 2 m s)⁻¹ := by
    unfold parameter
    norm_num only [Nat.cast_ofNat]
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
  unfold heckeScalar QuantitativeArithmeticRamifiedFullTrace.multiplier sigmaTwo
  norm_num only [Nat.cast_ofNat]
  rw [div_eq_mul_inv,← hi,hh]
  ring

theorem matrixScalar_leading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 35) :
    gridMatrixScalar m (FinitenessNormalizedTwistProduct.root 22 f 2) (phase m ε) i 0 s=
      gridSourceSign (-sigmaTwo f) (phase m ε) (gridGroupSource i)*
        monomial (groupPowers i) (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) := by
  simp only [gridMatrixScalar,pow_zero,Ring.choose_zero_right,mul_one,root_two]
  rw [groupRate_complex]
  rfl

theorem taylorScalar_leading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 11) :
    gridTaylorCoefficient m f ε i 0 s=
      (FinitenessNormalizedTwistProduct.root 22 f (gridTaylorQ i))*phase m ε*
        monomial (taylorPowers i) (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) := by
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  have hb : (((gridTaylorL i:ℝ)*((gridTaylorT i:ℝ)/66)^2:ℝ):ℂ)=(taylorRate i:ℂ) := by
    simp [taylorRate]
  unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar
  simp only [pow_zero,Ring.choose_zero_right,mul_one,hm]
  rw [hb,taylorRate_complex]
  unfold phase parameter
  ring

#print axioms groupRate_complex
#print axioms taylorRate_complex
#print axioms heckeScalar_parameter
#print axioms matrixScalar_leading
#print axioms taylorScalar_leading
end SmallLevelTwentyTwoParameters
end
end

/-! ## TwentyTwoLeadingComparison -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
-- A common finite-case normalization list is used for three different row types.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoParameters
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSmallLevelTwentyTwo
open SmallLevelTwentyTwoLaurent FinitenessRamanujanSum

theorem negative_parameter (p m : ℕ) (s : ℂ) :
    (p:ℂ)^((m:ℂ)-s)=1/parameter p m s := by
  unfold parameter
  rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg,one_div]

/-- The algebraic core is the literal selected 66-row Mellin system. -/
theorem coreRows_actual (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 66→ℂ) :
    gridLeadingRows m f ε s w=
      coreRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) ((Real.sqrt 3:ℂ)*f 3) w := by
  have hX:=parameter_ne_zero 2 m (by decide) s
  have hY:=parameter_ne_zero 3 m (by decide) s
  have hZ:=parameter_ne_zero 11 m (by decide) s
  have he : ε*I^(2*m)=phase m ε:=rfl
  have hn3 := negative_parameter 3 m s
  norm_num only [Nat.cast_ofNat] at hn3
  funext i
  fin_cases i <;>
    norm_num [gridLeadingRows,gridAssemble,gridGroupLeading,gridRamanujanLeading,
      gridHeckeLeading,coreRows,leadingRows,he,matrixScalar_leading,taylorScalar_leading,
      heckeScalar_parameter,hn3,negative_parameter,gridGroupSource,gridGroupIndex,gridGroupTarget,
      gridSourceSign,groupPowers,taylorPowers,monomial,gridSample,gridIndex,
      gridTaylorQ,gridTaylorT,gridTaylorL,gridTaylorD,gridTaylorPartner,gridTaylorSpecs,
      gridHeckeSpecs,gridEntireSpecs,residues,Finset.sum_filter,Finset.sum_range_succ,
      root_three,root_six,root_eleven] <;>
    (try field_simp [hX,hY,hZ]) <;> (try simp) <;> ring

#print axioms coreRows_actual
end SmallLevelTwentyTwoParameters
end
end

/-! ## TwentyTwoTaylorFactors -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoParameters
open Complex SmallLevelPrimeRates QuantitativeArithmeticSmallLevelTwentyTwo

def taylorDerivative (i : Fin 11) : ℚ := (gridTaylorL i:ℚ)*(gridTaylorT i:ℚ)/66

theorem matrixScalar_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 35) (n : ℕ) (s : ℂ) :
    gridMatrixScalar m (FinitenessNormalizedTwistProduct.root 22 f 2) (phase m ε) i n s=
      (gridSourceSign (-sigmaTwo f) (phase m ε) (gridGroupSource i)*
        monomial (groupPowers i) (parameter 2 m s) (parameter 3 m s) (parameter 11 m s))*
      I^n*(gridGroupDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  rw [gridMatrixScalar,root_two,groupRate_complex,mul_pow]
  norm_num only [parameter,Nat.cast_ofNat]
  ring

theorem taylorScalar_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 11) (n : ℕ) (s : ℂ) :
    gridTaylorCoefficient m f ε i n s=
      (FinitenessNormalizedTwistProduct.root 22 f (gridTaylorQ i)*phase m ε*
        monomial (taylorPowers i) (parameter 2 m s) (parameter 3 m s) (parameter 11 m s))*
      I^n*(taylorDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  have hc : gridTaylorCoefficient m f ε i n s=
      gridTaylorCoefficient m f ε i 0 s*
        I^n*(taylorDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
    unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar taylorDerivative
    simp only [pow_zero,Ring.choose_zero_right,mul_one,Rat.cast_div,Rat.cast_mul,
      Rat.cast_natCast,Rat.cast_intCast,Rat.cast_ofNat,Complex.ofReal_div,
      Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_ofNat,mul_pow,div_pow]
    ring
  rw [hc,taylorScalar_leading]

#print axioms matrixScalar_factor
#print axioms taylorScalar_factor
end SmallLevelTwentyTwoParameters
end
end

/-! ## TwentyTwoExtendedComparison -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix SmallLevelPrimeRates SmallLevelTwentyTwoParameters
open QuantitativeArithmeticSmallLevelTwentyTwo SmallLevelTwentyTwoLaurent
open FinitenessRamanujanSum

theorem extendedLeading_mul (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 66→ℂ) (i : Fin 68) :
    (extendedLeading m f ε s *ᵥ w) i=
      if hi : i.val<66 then gridLeadingRows m f ε s w ⟨i.val,hi⟩
      else w (gridIndex (extraHeckeIndex i))+w (gridIndex (extraHeckeIndex i+33))-
        heckeScalar m f s*w (gridIndex (2*extraHeckeIndex i)) := by
  by_cases hi : i.val<66
  · simp only [Matrix.mulVec,dotProduct,extendedLeading,dite_eq_left hi]
    simpa only [Matrix.mulVec,dotProduct] using
      congrFun (gridLeadingMatrix_mulVec m f ε s w) ⟨i.val,hi⟩
  · simp only [Matrix.mulVec,dotProduct,extendedLeading,dite_eq_right hi]
    exact extraHeckeRow_mul _ _ _

theorem extendedShift_mul (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 66→ℂ) (i : Fin 68) :
    (extendedShift m f ε n s *ᵥ w) i=
      if hi : i.val<66 then gridShiftRows m f ε n s w ⟨i.val,hi⟩ else 0 := by
  by_cases hi : i.val<66
  · simp only [Matrix.mulVec,dotProduct,extendedShift,dite_eq_left hi]
    simpa only [Matrix.mulVec,dotProduct] using
      congrFun (gridShiftMatrix_mulVec m f ε n s w) ⟨i.val,hi⟩
  · simp only [Matrix.mulVec,dotProduct,extendedShift,dite_eq_right hi,zero_mul,Finset.sum_const_zero]

theorem extendedLeading_actual (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 66→ℂ) :
    extendedLeading m f ε s *ᵥ w=leadingRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
      (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) ((Real.sqrt 3:ℂ)*f 3) w := by
  funext i
  rw [extendedLeading_mul]
  by_cases hi : i.val<66
  · rw [dite_eq_left hi,coreRows_actual]
    rfl
  · have he : i=66 ∨ i=67 := by
      have hil:=i.isLt
      have hval : i.val=66 ∨ i.val=67:=by omega
      rcases hval with h|h
      · left; apply Fin.ext; exact h
      · right; apply Fin.ext; exact h
    rcases he with rfl|rfl <;>
      norm_num [extraHeckeIndex,gridIndex,leadingRows,heckeScalar_parameter] <;> ring

theorem extendedShift_actual (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 66→ℂ) (i : Fin 68) :
    (extendedShift m f ε n s *ᵥ w) i=
      (I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1))*
      positiveTaylorRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) n w i := by
  have hX:=parameter_ne_zero 2 m (by decide) s
  have hY:=parameter_ne_zero 3 m (by decide) s
  have hZ:=parameter_ne_zero 11 m (by decide) s
  have he : ε*I^(2*m)=phase m ε:=rfl
  rw [extendedShift_mul]
  fin_cases i <;>
    norm_num [gridShiftRows,gridAssemble,matrixScalar_factor,taylorScalar_factor,he,
      positiveTaylorRows,gridGroupTarget,gridGroupSource,gridGroupDerivative,
      gridSourceSign,groupPowers,taylorPowers,taylorDerivative,monomial,
      gridTaylorQ,gridTaylorT,gridTaylorL,gridTaylorD,gridTaylorPartner,gridTaylorSpecs,
      gridSample,gridIndex,residues,Finset.sum_filter,Finset.sum_range_succ,
      root_three,root_six,root_eleven,pow_succ] <;>
    (try field_simp [hX,hY,hZ]) <;> (try simp) <;> ring <;> simp

#print axioms extendedLeading_actual
#print axioms extendedShift_actual
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoFirstShiftComparison -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix SmallLevelPrimeRates SmallLevelTwentyTwoParameters SmallLevelTwentyTwoLaurent

theorem firstRows_positive (η u v X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) :
    positiveTaylorRows η u v (X/2) (Y/3) (Z/11) 0 w=firstRows η u v X Y Z a w := by
  funext i
  fin_cases i <;> norm_num [positiveTaylorRows,firstRows] <;> (try field_simp [hX,hY,hZ]) <;> ring <;> simp

theorem firstShift_actual (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (w : Fin 66→ℂ) (i : Fin 68) :
    (∑ j,extendedShift m f ε 0 (x-1) i j*w j)=
      (I*(x-((2*m:ℕ):ℂ)))*firstRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
        (parameter 2 m x) (parameter 3 m x) (parameter 11 m x) ((Real.sqrt 3:ℂ)*f 3) w i := by
  have h:=extendedShift_actual m f ε 0 (x-1) w i
  have he : x-1+((0+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=x-((2*m:ℕ):ℂ) := by norm_num
  rw [he] at h
  simp only [zero_add,pow_one,Ring.choose_one_right,
    parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 11 m (by decide),Nat.cast_ofNat] at h
  rw [firstRows_positive _ _ _ _ _ _ ((Real.sqrt 3:ℂ)*f 3)
    (parameter_ne_zero 2 m (by decide) x) (parameter_ne_zero 3 m (by decide) x)
    (parameter_ne_zero 11 m (by decide) x)] at h
  exact h

#print axioms firstRows_positive
#print axioms firstShift_actual
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoSelectedFirstShift -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyTwoParameters
open SmallLevelTwentyTwoLaurent QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- Translate an analytic selected left syzygy of the literal Mellin rows
into its polynomial first-shift equation, away from the weight. -/
theorem selected_regular_polynomial_first_shift {ρ : Type*} [Fintype ρ]
    (rows : ρ→Fin 68) (η u v a : ℂ)
    (coeff : ℂ→ℂ→ℂ→ρ→ℂ)
    (hsyz : ∀ X Y Z : ℂ, X≠0 → Y≠0 → Z≠0 → ∀ w : Fin 66→ℂ,
      ∑ i,coeff X Y Z i*leadingRows η u v X Y Z a w (rows i)=0)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phase m ε=η) (hu : sigmaTwo f=u) (hv : sigmaEleven f=v)
    (ha : (Real.sqrt 3:ℂ)*f 3=a)
    (hcoeff : ∀ z i, AnalyticAt ℂ
      (fun s => coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) i) z)
    (B : ℝ) (G : ℂ→Fin 66→ℂ) (H : ℕ→ℂ→Fin 68→ℂ)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ b∈Finset.range n,
          ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j))
    (x : ℂ) (hx : x≠((2*m:ℕ):ℂ)) (w : Fin 66→ℂ) (hw : IsLeadingVector G x w)
    (htail : ∀ b : ℕ, 1≤b → ∀ i j, ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-1) ∧
      (fun z => extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-1)] R) :
    ∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3) (parameter 11 m x/11) i*
      firstRows η u v (parameter 2 m x) (parameter 3 m x) (parameter 11 m x) a w (rows i)=0 := by
  classical
  let K : ℂ→ρ→ℂ:=fun z => coeff (parameter 2 m z) (parameter 3 m z) (parameter 11 m z)
  have hKA (z : ℂ) (w : Fin 66→ℂ) :
      ∑ i,K z i*(∑ j,extendedLeading m f ε z (rows i) j*w j)=0 := by
    have he (i : Fin 68) : (∑ j,extendedLeading m f ε z i j*w j)=
        leadingRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
          (parameter 2 m z) (parameter 3 m z) (parameter 11 m z) ((Real.sqrt 3:ℂ)*f 3) w i :=
      congrFun (extendedLeading_actual m f ε z w) i
    simp only [he,hη,hu,hv,ha,K]
    exact hsyz _ _ _ (parameter_ne_zero 2 m (by decide) z)
      (parameter_ne_zero 3 m (by decide) z) (parameter_ne_zero 11 m (by decide) z) w
  have hh:=SmallLevelFiniteShift.selected_regular_first_shift rows B G
    (extendedLeading m f ε) (extendedShift m f ε) H
    (extendedShift_analytic m f ε) hH hrow x w hw htail K hcoeff hKA
  simp only [firstShift_actual,hη,hu,hv,ha,K,
    parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 11 m (by decide),Nat.cast_ofNat] at hh
  have he : (∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3) (parameter 11 m x/11) i*
      ((I*(x-((2*m:ℕ):ℂ)))*firstRows η u v (parameter 2 m x) (parameter 3 m x)
        (parameter 11 m x) a w (rows i)))=
      (I*(x-((2*m:ℕ):ℂ)))*(∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3)
        (parameter 11 m x/11) i*firstRows η u v (parameter 2 m x) (parameter 3 m x)
          (parameter 11 m x) a w (rows i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero I_ne_zero (sub_ne_zero.mpr hx))

#print axioms selected_regular_polynomial_first_shift
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoCandidateFromRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyTwoParameters
open SmallLevelTwentyTwoLaurent QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem candidate_of_regular_tails {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (B : ℝ) (G : ℂ→Fin 66→ℂ) (H : ℕ→ℂ→Fin 68→ℂ)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ b∈Finset.range n,
          ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j))
    (x : ℂ) (hx : x≠((2*m:ℕ):ℂ)) (w : Fin 66→ℂ) (hw : IsLeadingVector G x w)
    (htail : ∀ d b : ℕ, d≤b → ∀ i j, ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-d) ∧
      (fun z => extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-d)] R) :
    x=(m:ℂ)+1 ∧ sigmaTwo f= -1 ∧ (Real.sqrt 3:ℂ)*f 3= -7/3 := by
  have hη:=phase_sign m hε
  have hu:=sigmaTwo_sign hf.toEulerData
  have hv:=sigmaEleven_sign hf.toEulerData
  have hlead:=hw.regular_tail_leading B G (extendedLeading m f ε) (extendedShift m f ε)
    H x w (extendedLeading_analytic m f ε x) hH
    (fun b i j => by simpa only [Nat.cast_zero,sub_zero] using htail 0 b (Nat.zero_le b) i j) hrow
  rw [extendedLeading_actual] at hlead
  have hcore : coreRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
      (parameter 2 m x) (parameter 3 m x) (parameter 11 m x) ((Real.sqrt 3:ℂ)*f 3) w=0 := by
    funext i
    exact congrFun hlead ⟨i.val,by omega⟩
  have hjet:=firstJet_equations m (phase m ε) (sigmaTwo f) (sigmaEleven f)
    ((Real.sqrt 3:ℂ)*f 3) x hη hu hv w hcore hw.1
    (fun r rows coeff hcoeff hsyz => selected_regular_polynomial_first_shift
      rows _ _ _ _ coeff hsyz m f ε rfl rfl rfl rfl hcoeff B G H hH hrow x hx w hw
      (fun b hb i j => by simpa only [Nat.cast_one] using htail 1 b hb i j))
  exact physical_candidate m _ _ _ _ x hη hu hv w hcore hw.1 hjet.1 hjet.2

#print axioms candidate_of_regular_tails
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoChiFiveFromPartners -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoPartners
open Complex Filter Set SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelTwentyTwo SmallLevelSimplePoleTaylor
open FinitenessOriginalFourier FinitenessFourierConstruction
open scoped Topology

/-- Conditional analytic endgame: only the two old-grid partners at
±5/22 need be analytic away from the weight, with at most a simple weight pole. -/
theorem quadratic_entire_of_simple_partners {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ)
    (hlaw : GridFrickeLaws (2*m) f ε)
    (BG : ℝ) (Gp Gn : ℂ→ℂ)
    (hGp : ∀ s, MeromorphicAt Gp s) (hGn : ∀ s, MeromorphicAt Gn s)
    (hGpa : ∀ s, s≠((2*m:ℕ):ℂ) → AnalyticAt ℂ Gp s)
    (hGna : ∀ s, s≠((2*m:ℕ):ℂ) → AnalyticAt ℂ Gn s)
    (hGpo : (-1:WithTop ℤ)≤meromorphicOrderAt Gp ((2*m:ℕ):ℂ))
    (hGno : (-1:WithTop ℤ)≤meromorphicOrderAt Gn ((2*m:ℕ):ℂ))
    (hGpF : ∀ s, BG<s.re → Gp s=original (2*m) f (-5/22) s)
    (hGnF : ∀ s, BG<s.re → Gn s=original (2*m) f (5/22) s)
    (BQ : ℝ) (Q : ℂ→ℂ) (hQ : ∀ s, MeromorphicNFAt Q s)
    (hQF : ∀ s, BQ<s.re → Q s=quadraticCombination (2*m) f s)
    (hQD : ∀ s, denominator m f s≠0 → AnalyticAt ℂ Q s) :
    ∀ s, AnalyticAt ℂ Q s := by
  obtain ⟨τ,_hτ,hgrowth⟩:=hf.growth
  have hfr : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*I^(2*m))/(((Real.sqrt 22:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((22:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have ha:=polynomial_bound hf.zero hgrowth (2*m)
  have ha0:=fullCoefficients_zero hf.zero (2*m)
  obtain ⟨Bp,Hp,hHp,hHpF,hHpR⟩:=partner_models (by norm_num : (0:ℝ)<22)
    (by norm_num : (1/5:ℝ)≠0) (2*m) (even_two_mul m) ha ha0 (ε*I^(2*m)) hfr
    BG Gp hGp hGpa hGpo (by
      intro s hs
      simpa only [original,show -(1:ℝ)/(22*(1/5))= -5/22 by norm_num] using hGpF s hs)
  obtain ⟨Bn,Hn,hHn,hHnF,hHnR⟩:=partner_models (by norm_num : (0:ℝ)<22)
    (by norm_num : (-1/5:ℝ)≠0) (2*m) (even_two_mul m) ha ha0 (ε*I^(2*m)) hfr
    BG Gn hGn hGna hGno (by
      intro s hs
      simpa only [original,show -(1:ℝ)/(22*(-1/5))=5/22 by norm_num] using hGnF s hs)
  obtain ⟨hRE,BR,hRF⟩:=original_ramanujan_entire (by decide : 0<22) (by omega : 0<2*m)
    hf (by decide : 0<5)
  let B : ℝ:=max (max Bp Bn) BR
  have hpB : Bp≤B:=(le_max_left _ _).trans (le_max_left _ _)
  have hnB : Bn≤B:=(le_max_right _ _).trans (le_max_left _ _)
  have hrB : BR≤B:=le_max_right _ _
  let H : ℕ→ℂ→ℂ := fun M s => 2*(Hp M s+Hn M s)-ramanujanEntire 22 (2*m) f 5 s
  intro x
  by_cases hd : denominator m f x=0
  · have hxre:=denominator_zero_re m hf hd
    have hxk : x≠((2*m:ℕ):ℂ) := by
      intro he
      rw [he] at hxre
      norm_num at hxre
      have hm' : (0:ℝ)<m := by exact_mod_cast hm
      linarith
    apply analyticAt_of_halfplane_germs (quadraticCombination (2*m) f) Q BQ B H x hQ hQF
    · intro M s hs
      have hp : Bp-(M:ℝ)<s.re := by linarith
      have hn : Bn-(M:ℝ)<s.re := by linarith
      exact ((MeromorphicAt.const (2:ℂ) s).mul ((hHp M s hp).add (hHn M s hn))).sub
        ((hRE s).meromorphicAt)
    · intro M s hs
      dsimp only [H]
      rw [hHpF M s (lt_of_le_of_lt hpB hs),hHnF M s (lt_of_le_of_lt hnB hs),
        hRF s (lt_of_le_of_lt hrB hs),ramanujan_five]
      unfold quadraticCombination evenOne
      change 2*(original (2*m) f (1/5) s+original (2*m) f (-1/5) s)-
        (original (2*m) f (1/5) s+original (2*m) f (-1/5) s+evenTwo (2*m) f s)=_
      ring
    · intro M hs
      have hp : Bp-(M:ℝ)<x.re := by linarith
      have hn : Bn-(M:ℝ)<x.re := by linarith
      obtain ⟨Rp,hRp,hep⟩:=hHpR M x hp hxk
      obtain ⟨Rn,hRn,hen⟩:=hHnR M x hn hxk
      refine ⟨fun s => 2*(Rp s+Rn s)-ramanujanEntire 22 (2*m) f 5 s,
        (analyticAt_const.mul (hRp.add hRn)).sub (hRE x),?_⟩
      filter_upwards [hep,hen] with s hsp hsn
      dsimp only [H]
      rw [hsp,hsn]
  · exact hQD x hd

#print axioms quadratic_entire_of_simple_partners
end SmallLevelTwentyTwoPartners
end
end

/-! ## TwentyTwoCoherentReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoCoherentReflection
open QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct FinitenessRamanujanFourier FinitenessAllLevelAxisDecay
open QuantitativeArithmeticTranslatedFricke FinitenessPolynomialSeries SmallLevelAdditive
open Complex MeasureTheory
open scoped MatrixGroups ModularForm

theorem scaled_reflections_of_laws (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : IsSolution 22 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
      (∀ s : ℂ, tenthMellin m f s=(root 22 f 2*ε)*tenthMellin m f ((2*m:ℕ)-s)) ∧
      (∀ s : ℂ, mellin (axis 550 (fullCoefficients (twisted f 5) (2*m))) s=
        ε*mellin (axis 550 (fullCoefficients (twisted f 5) (2*m))) ((2*m:ℕ)-s)) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  let χ : ℂ := ε*Complex.I^(2*m)
  let δ : ℂ := root 22 f 2
  have hδ : δ=1 ∨ δ= -1 := root_unit hf.toEulerData 2
  have hχ : χ=1 ∨ χ= -1 := by
    have hi : Complex.I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,Complex.I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [χ,hi,h]
  have hfr : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      χ/(((Real.sqrt 22:ℂ)*z)^(2*m))*fourier (fullCoefficients f (2*m)) (-1/((22:ℂ)*z)) := by
    intro z hz
    simpa [χ,root,FinitenessAnalyticReconstruction.twist,Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      χ • SmallLevelOriginal.fourierFunction (2*m) f := by
    have h:=fricke_law 22 (2*m) (by decide) (fourier (fullCoefficients f (2*m))) χ hfr
    change SmallLevelOriginal.fourierFunction (2*m) f=
      χ • (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W) at h
    rcases hχ with hc|hc
    · rw [hc] at h ⊢; simpa using h.symm
    · rw [hc] at h ⊢; simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm
  have hQ : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      SmallLevelRamifiedTwo.Q 22 12 (by decide)=δ • SmallLevelOriginal.fourierFunction (2*m) f := by
    apply SmallLevelRamifiedTwo.eigen_of_fricke (by decide : 0<22) (by decide : 2*12=22+2) _ χ δ hfr
    intro z hz
    have h:=hlaw 2 (by decide) z hz
    have ht (G : ℂ → ℂ) (w : ℂ) : FinitenessAnalyticReconstruction.twist G 2 w=G (w+1/2) := by
      unfold FinitenessAnalyticReconstruction.twist
      rw [show (Finset.range 2).filter (fun a => Nat.Coprime a 2)={1} by decide]
      simp
    have hsqrt : Real.sqrt 44=Real.sqrt 2*Real.sqrt 22 := by
      rw [show (44:ℝ)=2*22 by norm_num,Real.sqrt_mul (by norm_num)]
    rw [show Nat.lcm 22 (2^2)=44 by decide,Nat.cast_ofNat,hsqrt,Complex.ofReal_mul,ht,ht] at h
    simpa only [δ,χ,Nat.cast_ofNat,mul_assoc,show (44:ℂ)=2*22 by norm_num] using h
  have hE : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] E=
      δ • SmallLevelOriginal.fourierFunction (2*m) f := by
    have hh:=congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] E) hQ
    rw [← SlashAction.slash_mul,show SmallLevelRamifiedTwo.Q 22 12 (by decide)*E=1 from mul_inv_cancel _,
      SlashAction.slash_one,det_one_smul _ E_det] at hh
    rcases hδ with hc|hc
    · rw [hc] at hh ⊢; simpa using hh.symm
    · rw [hc] at hh ⊢; simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm
  obtain ⟨hn,hp⟩:=tenth_fricke_of_signs m f δ χ hδ hχ hE hW
  have hδχ : δ*χ=1 ∨ δ*χ= -1 := by
    rcases hδ with h|h <;> rcases hχ with h'|h' <;> simp [h,h']
  refine ⟨?_,?_⟩
  · let a:=fullCoefficients f (2*m)
    have ha : PolynomialBound a:=polynomial_bound hf.zero hg (2*m)
    have ha0 : a 0=0:=fullCoefficients_zero hf.zero (2*m)
    have hB0 : tenthCoefficients a 0=0 := by simp [tenthCoefficients,coefficients_zero ha0]
    let F:=SmallLevelOriginal.fourierFunction (2*m) f
    let k : ℤ:=((2*m:ℕ):ℤ)
    have hfourier : (fun z : ℍ => fourier (tenthCoefficients a) z)=
        (F ∣[k] translation (1/10))+(F ∣[k] translation (-1/10)) := by
      funext z
      rw [tenth_fourier ha z z.im_pos]
      simp only [Pi.add_apply,translation_slash]
      change fourier a _+fourier a _=fourier a ((translation (1/10) • z:ℍ):ℂ)+
        fourier a ((translation (-1/10) • z:ℍ):ℂ)
      rw [translation_point,translation_point]
    have hslash : (fun z : ℍ => fourier (tenthCoefficients a) z) ∣[k] fricke 1100 (by decide)=
        (δ*χ) • (fun z : ℍ => fourier (tenthCoefficients a) z) := by
      rw [hfourier,SlashAction.add_slash,hp,hn,← smul_add]
      congr 1
      abel
    have hl:=formula_of_slash 1100 (2*m) (by decide) (fourier (tenthCoefficients a)) (δ*χ) hδχ hslash
    have hc0 : δ*χ≠0 := by rcases hδχ with h|h <;> rw [h] <;> norm_num
    have he:=FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<1100) (by omega : 0<2*m)
      (tenthCoefficients a) (tenth_polynomial ha) hB0 ((δ*χ)/(Complex.I^(2*m)))
      (div_ne_zero hc0 (pow_ne_zero _ Complex.I_ne_zero)) (by
        simpa only [div_mul_cancel₀ _ (pow_ne_zero (2*m) Complex.I_ne_zero)] using hl)
    intro s
    have hh:=he.2.2 s
    have hsign : (δ*χ)/Complex.I^(2*m)=δ*ε := by
      dsimp [χ]
      rw [← mul_assoc,mul_div_cancel_right₀ _ (pow_ne_zero _ Complex.I_ne_zero)]
    simpa only [hsign,δ,a,tenthMellin] using hh
  · have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
    have hfr5 : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients (twisted f 5) (2*m)) z=
        (ε*Complex.I^(2*m))/(((Real.sqrt 550:ℂ)*z)^(2*m))*
          fourier (fullCoefficients (twisted f 5) (2*m)) (-1/((550:ℂ)*z)) := by
      intro z hz
      have href : 0<(-1/((550:ℂ)*z)).im :=
        FinitenessComplexGeometry.reflected_im_pos (by norm_num : (0:ℝ)<550) hz
      simpa only [fourier_twisted hf.zero hg 5 (2*m) hz,
        fourier_twisted hf.zero hg 5 (2*m) href,show Nat.lcm 22 (5^2)=550 by decide,
        root_five,one_mul,mul_assoc,Nat.cast_ofNat] using hlaw 5 (by decide) z hz
    exact (FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<550) (by omega) _
      (polynomial_bound (twisted_zero hf.zero 5) (twisted_growth hg 5) (2*m))
      (fullCoefficients_zero (twisted_zero hf.zero 5) (2*m)) ε hε0 hfr5).2.2

theorem unscaled_reflections_of_laws (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : IsSolution 22 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
      (∀ s : ℂ, evenTenthEntire m f s=(root 22 f 2*ε)*(Real.sqrt 1100:ℂ)^((2*m:ℕ)-2*s)*
        evenTenthEntire m f ((2*m:ℕ)-s)) ∧
      (∀ s : ℂ, SmallLevelTaylor.ramanujanEntire 22 (2*m) f 5 s=
        ε*(Real.sqrt 550:ℂ)^((2*m:ℕ)-2*s)*SmallLevelTaylor.ramanujanEntire 22 (2*m) f 5 ((2*m:ℕ)-s)) := by
  obtain ⟨hc,hr⟩:=scaled_reflections_of_laws m hm hf ε hε hlaw
  refine ⟨QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
    (by decide : 0<1100) _ (root 22 f 2*ε) hc,?_⟩
  intro s
  have h:=QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection (by decide : 0<550) _ ε hr s
  have haxis : axis 1 (fullCoefficients (twisted f 5) (2*m))=
      (fun y : ℝ => fourier (fullCoefficients (twisted f 5) (2*m)) ((y:ℂ)*Complex.I)) := by
    funext y
    simp [axis]
  rw [haxis] at h
  simpa only [SmallLevelTaylor.ramanujanEntire,Nat.cast_ofNat] using h


#print axioms scaled_reflections_of_laws
#print axioms unscaled_reflections_of_laws
end SmallLevelTwentyTwoCoherentReflection
end
end

/-! ## TwentyTwoCoherentFunctionalEquation -/
section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoCoherentReflection
open QuantitativeArithmeticSmallLevelTwentyTwo
open Complex SmallLevelAdditive Filter Set
open scoped Topology

/-- The original level22 Euler input yields a global meromorphic continuation
of the actual quadratic additive combination, with its exact conductor550
functional equation. This includes exceptional denominator zeros. Poles
are still permitted, so this is not the modularity theorem. -/
theorem quadratic_functional_equation_of_laws (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ (bound : ℝ) (G : ℂ → ℂ),
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=quadraticCombination (2*m) f s) ∧
      (∀ s, G s= -ε*(550:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s)) ∧
      (∀ s, denominator m f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator m f s)) := by
  obtain ⟨hc,hr⟩ := unscaled_reflections_of_laws m hm hf ε hε hlaw
  obtain ⟨bound,G,hG,hagree,hpole,hgerm⟩ := original_quadratic_continuation m hm hf
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have hN := numerator_reflection m hf ε hc hr
  have hfe := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator m f s) G
    (reflectionMultiplier m ε) ((2*m:ℕ):ℂ) hG
    (fun s => (reflectionMultiplier_entire m ε).analyticAt s)
    (reflectionMultiplier_ne_zero m hε0) hgerm
    (raw_quotient_reflection m hf ε hN)
  refine ⟨bound,G,hG,hagree,?_,hpole,hgerm⟩
  intro s
  simpa only [reflectionMultiplier] using hfe s

#print axioms quadratic_functional_equation_of_laws
end SmallLevelTwentyTwoCoherentReflection
end
end

/-! ## TwentyTwoNonsingular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix SmallLevelPrimeRates SmallLevelTwentyTwoParameters
open QuantitativeArithmeticSmallLevelTwentyTwo SmallLevelTwentyTwoLaurent

theorem parameter_negative_integer (p m n : ℕ) :
    parameter p m ((m:ℂ)-(n:ℂ))=((p:ℂ)⁻¹)^n := by
  unfold parameter
  rw [show (m:ℂ)-(n:ℂ)-(m:ℂ)= -(n:ℂ) by ring,Complex.cpow_neg,
    Complex.cpow_natCast,inv_pow]

theorem leadingMatrix_det_ne_zero {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (s : ℂ) (hd : residual (phase m ε) (sigmaTwo f)
      (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) ((Real.sqrt 3:ℂ)*f 3)≠0) :
    (gridLeadingMatrix m f ε s).det≠0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro w z hw
  have hn : gridLeadingMatrix m f ε s *ᵥ (w-z)=0 := by
    rw [Matrix.mulVec_sub,hw,sub_self]
  rw [gridLeadingMatrix_mulVec,coreRows_actual] at hn
  exact sub_eq_zero.mp (core_kernel_zero _ _ _ _ _ _ _ (phase_sign m hε)
    (sigmaTwo_sign hf.toEulerData) (sigmaEleven_sign hf.toEulerData)
    (parameter_ne_zero 2 m (by decide) s) (parameter_ne_zero 3 m (by decide) s)
    (parameter_ne_zero 11 m (by decide) s) hd (w-z) hn)

theorem leadingMatrix_nonsingular {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1) :
    ∃ s : ℂ, (gridLeadingMatrix m f ε s).det≠0 := by
  have h:=residual_some_point (phase m ε) (sigmaTwo f) ((Real.sqrt 3:ℂ)*f 3)
    (phase_sign m hε) (sigmaTwo_sign hf.toEulerData)
  have hp (p n : ℕ) := parameter_negative_integer p m n
  rcases h with h|h
  · refine ⟨(m:ℂ)-(1:ℂ),leadingMatrix_det_ne_zero hf ε hε _ ?_⟩
    have h2:=hp 2 1
    have h3:=hp 3 1
    have h11:=hp 11 1
    norm_num at h2 h3 h11
    rw [h2,h3,h11]
    exact h
  · refine ⟨(m:ℂ)-(2:ℂ),leadingMatrix_det_ne_zero hf ε hε _ ?_⟩
    have h2:=hp 2 2
    have h3:=hp 3 2
    have h11:=hp 11 2
    norm_num at h2 h3 h11
    rw [h2,h3,h11]
    exact h

#print axioms leadingMatrix_det_ne_zero
#print axioms leadingMatrix_nonsingular
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoContinuedSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix Filter Set QuantitativeArithmeticSmallLevelTwentyTwo
open scoped Topology

theorem grid_continuation_of_laws {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∃ G : ℂ→Fin 66→ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=gridVector (2*m) f z := by
  obtain ⟨B,E,hF,hH,hrow⟩:=coherent_matrix_system hm hf hε hlaw
  refine ⟨B,?_⟩
  apply SmallLevelContinuation.closed_system_continuation B (gridVector (2*m) f)
    (gridLeadingMatrix m f ε) (gridShiftMatrix m f ε) (errorVector m f ε E)
    hF (leadingMatrix_analytic m f ε) (leadingMatrix_nonsingular hf ε hε)
    (shiftMatrix_analytic m f ε) hH
  intro n z hz i
  simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using
    congrFun (hrow n z hz) i

theorem continued_extended_system {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∃ G : ℂ→Fin 66→ℂ, ∃ E : Fin 35→ℕ→ℂ→ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      (∀ z, B<z.re → G z=gridVector (2*m) f z) ∧
      (∀ i z, B<z.re → AnalyticAt ℂ (fun w => G w i) z) ∧
      (∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
        AnalyticAt ℂ (fun w => extendedError m f ε E n w i) z) ∧
      ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
        (fun z => ∑ j, extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
          (fun z => extendedError m f ε E n z i+
            ∑ a∈Finset.range n, ∑ j, extendedShift m f ε a z i j*G (z+((a:ℂ)+1)) j) := by
  obtain ⟨B₀,G,hG,heG⟩:=grid_continuation_of_laws hm hf ε hε hlaw
  obtain ⟨B₁,E,hF,hH,hrow⟩:=extended_matrix_system hm hf hε hlaw
  let B : ℝ:=max B₀ B₁
  have hGF (z : ℂ) (hz : B<z.re) : G z=gridVector (2*m) f z :=
    heG z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hH' (n : ℕ) (i : Fin 68) (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) :
      AnalyticAt ℂ (fun w => extendedError m f ε E n w i) z := by
    apply hH n i z
    have hb : B₁≤B:=le_max_right _ _
    linarith
  refine ⟨B,G,E,hG,hGF,?_,hH',?_⟩
  · intro i z hz
    apply (hF i z (lt_of_le_of_lt (le_max_right _ _) hz)).congr
    have hn : ∀ᶠ w in 𝓝 z, B<w.re:=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hn] with w hw
    exact (congrFun (hGF w hw) i).symm
  · apply QuantitativeArithmeticRectangularContinuation.continued_meromorphic_rows
      B (gridVector (2*m) f) G (extendedLeading m f ε) (extendedShift m f ε)
      (extendedError m f ε E) (fun i x => (hG i x).meromorphicAt) hGF
      (extendedLeading_analytic m f ε) (extendedShift_analytic m f ε)
      (fun n i z hz => (hH' n i z hz).meromorphicAt)
    intro n z hz
    exact hrow n z (lt_of_le_of_lt (le_max_right _ _) hz)

#print axioms grid_continuation_of_laws
#print axioms continued_extended_system
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoFiniteOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoCoherentReflection
open Complex SmallLevelTaylor QuantitativeArithmeticSmallLevelTwentyTwo
open FinitenessOriginalInput

/-- The actual level22 numerator has finite order before any pole removal. -/
theorem numerator_bound (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 22 (2*m) f) : FinitenessFiniteOrder.Bound (numerator m f) := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  obtain ⟨χ,_hχ,_he,hb,_hfe⟩:=original_tenth_entire m hm hf
  have ht : FinitenessFiniteOrder.Bound (evenTenthEntire m f) :=
    SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<1100) _ hb
  have hr := (SmallLevelRamanujanReflectionOrder.original_ramanujan_laws
    (by decide : 0<22) (by omega : 0<2*m) hf ε hε hlaw (by decide : 0<5)).1
  have hh : FinitenessFiniteOrder.Bound (heckeScalar m f) :=
    FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
      (SmallLevelMellinUnscale.negative_cpow_bound (by norm_num : (0:ℝ)<2))
  exact FinitenessFiniteOrderClosure.add
    (FinitenessFiniteOrder.mul
      (FinitenessFiniteOrderClosure.sub (FinitenessInputBounds.bound_const 1) hh) hr)
    (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const 2) ht)

/-- Entire division by the actual ramified Hecke2 factor preserves finite order. -/
theorem finiteOrder_of_entire {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : IsSolution 22 (2*m) f) {G : ℂ→ℂ} (hG : Differentiable ℂ G)
    (hprod : ∀ s, denominator m f s*G s=numerator m f s) : FiniteOrder G := by
  apply QuantitativeArithmeticQuadraticTwistQuotient.finiteOrder_of_two_factor
    (-(FinitenessNormalizedTwistProduct.root 22 f 2)) (m:ℂ)
    (original_numerator_entire m hm hf).continuous
    (FinitenessInputBounds.bound_finiteOrder (numerator_bound m hm hf)) hG
  intro s
  simpa only [denominator,heckeScalar_eq,add_comm] using hprod s

#print axioms numerator_bound
#print axioms finiteOrder_of_entire
end SmallLevelTwentyTwoCoherentReflection
end
end

/-! ## TwentyTwoFirstRowsAnalytic -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoLaurent
open Complex SmallLevelPrimeRates

theorem firstRows_analytic (η u v a : ℂ) (m : ℕ) (w : Fin 66→ℂ) (z : ℂ) (i : Fin 68) :
    AnalyticAt ℂ (fun s => firstRows η u v (parameter 2 m s)
      (parameter 3 m s) (parameter 11 m s) a w i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [firstRows]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem firstRows_basis (η u v X Y Z a : ℂ) (w : Fin 66→ℂ) (i : Fin 68) :
    (∑ j,firstRows η u v X Y Z a (Pi.single j 1) i*w j)=
      firstRows η u v X Y Z a w i := by
  classical
  fin_cases i <;>
    simp [firstRows,Pi.single_apply,div_eq_mul_inv,mul_add,add_mul,sub_mul,
      mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,←mul_assoc]
  all_goals ring

#print axioms firstRows_analytic
#print axioms firstRows_basis
end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoFivePairBridge -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoPartners
open Complex Matrix UpperHalfPlane SmallLevelNormalized
open QuantitativeArithmeticSmallLevelTwentyTwo
open QuantitativeArithmeticQuadraticFive (quadraticFourier twist_five)
open FinitenessOriginalFourier FinitenessFourierConstruction FinitenessAnalyticReconstruction
open scoped MatrixGroups ModularForm

theorem exchanged_pair_law {k : ℕ} {f : ℕ→ℂ} (ε : ℂ)
    (hlaw : GridFrickeLaws k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (-ε*Complex.I^k)/(((Real.sqrt 550:ℂ)*z)^k)*quadraticFourier k f (-1/((550:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im →
      fourier (fullCoefficients f k) (z+2/5)+fourier (fullCoefficients f k) (z-2/5)=
        (ε*Complex.I^k)/(((Real.sqrt 550:ℂ)*z)^k)*
          (fourier (fullCoefficients f k) (-1/((550:ℂ)*z)+1/5)+
            fourier (fullCoefficients f k) (-1/((550:ℂ)*z)-1/5)) := by
  intro z hz
  have hr:=hlaw 5 (by decide) z hz
  rw [show Nat.lcm 22 (5^2)=550 by decide,root_five,one_mul,
    twist_five _ (periodic _),twist_five _ (periodic _)] at hr
  have hc:=hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  norm_num only [Nat.cast_ofNat] at hr
  simp only [sub_eq_add_neg] at hr hc ⊢
  linear_combination (hr-hc)/2

theorem sqrt_conductor_five : Real.sqrt 550=5*Real.sqrt 22 := by
  rw [show (550:ℝ)=25*22 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem five_positive : fricke 22 (by decide)*SpecialLinearGroup.mapGL ℝ A5*
    translation (2/5)=translation (1/5)*fricke 550 (by decide) := by
  have ht : (Real.sqrt 22)^2=22:=Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0:=(Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,A5,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor_five] <;>
    field_simp [hn] <;> norm_num [ht]

theorem five_negative : fricke 22 (by decide)*SpecialLinearGroup.mapGL ℝ B5*
    translation (-(2/5))=translation (-(1/5))*fricke 550 (by decide) := by
  have ht : (Real.sqrt 22)^2=22:=Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0:=(Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,B5,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor_five] <;>
    field_simp [hn] <;> norm_num [ht]

theorem five_pair_of_quadratic_fricke {k : ℕ} {f : ℕ→ℂ} (ε : ℂ)
    (hlaw : GridFrickeLaws k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (-ε*Complex.I^k)/(((Real.sqrt 550:ℂ)*z)^k)*quadraticFourier k f (-1/((550:ℂ)*z))) :
    FivePair k f := by
  have h:=exchanged_pair_of_fricke 22 550 k (by decide) (by decide) (1/5) (2/5)
    (fourier (fullCoefficients f k)) (ε*Complex.I^k) (by
      intro z hz
      simpa [FinitenessNormalizedTwistProduct.root,twist,Finset.sum_range_succ] using
        hlaw 1 (by decide) z hz) (by
      simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one,
        Nat.cast_ofNat] using exchanged_pair_law ε hlaw hquad)
  have hfun : (fun z : ℍ => fourier (fullCoefficients f k) z)=SmallLevelOriginal.fourierFunction k f := rfl
  rw [hfun] at h
  have hp : (fricke 22 (by decide))⁻¹*translation (1/5)*fricke 550 (by decide)=
      SpecialLinearGroup.mapGL ℝ A5*translation (2/5) := by
    rw [mul_assoc,← five_positive]
    group
  have hn : (fricke 22 (by decide))⁻¹*translation (-(1/5))*fricke 550 (by decide)=
      SpecialLinearGroup.mapGL ℝ B5*translation (-(2/5)) := by
    rw [mul_assoc,← five_negative]
    group
  rw [hp,hn] at h
  have hh:=congrArg (fun F : ℍ→ℂ => F ∣[(k:ℤ)] translation (2/5)) h
  simp only [SlashAction.add_slash,← SlashAction.slash_mul,mul_assoc,translation_mul] at hh
  norm_num only [show (2/5:ℝ)+2/5=4/5 by ring,
    show (-(2/5):ℝ)+2/5=0 by ring] at hh
  have ht : translation 0=(1:GL (Fin 2) ℝ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  simp only [ht,mul_one,SlashAction.slash_one,SlashAction.slash_mul] at hh
  unfold FivePair
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]
  linear_combination hh

#print axioms five_pair_of_quadratic_fricke
end SmallLevelTwentyTwoPartners
end
end

/-! ## TwentyTwoPoleSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix Filter QuantitativeArithmeticSmallLevelTwentyTwo
open scoped Topology

/-- The actual continued rectangular Mellin system, including its original
right-half-plane identification. No pole bound is part of this structure. -/
structure PoleSystem (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) where
  B : ℝ
  G : ℂ→Fin 66→ℂ
  H : ℕ→ℂ→Fin 68→ℂ
  meromorphic : ∀ i z, MeromorphicNFAt (fun s => G s i) z
  original : ∀ z, B<z.re → G z=gridVector (2*m) f z
  halfplane : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z
  error : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z
  rows : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
    (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
      (fun z => H n z i+∑ b∈Finset.range n,
        ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j)

theorem exists_poleSystem {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    Nonempty (PoleSystem m f ε) := by
  obtain ⟨B,G,E,hG,hGF,hhalf,hH,hrow⟩:=continued_extended_system hm hf ε hε hlaw
  exact ⟨⟨B,G,extendedError m f ε E,hG,hGF,hhalf,hH,hrow⟩⟩

#print axioms exists_poleSystem
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoJetBlockModel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoJetBlock
open Complex Matrix SmallLevelFiniteShift SmallLevelTwentyTwoSystem
open SmallLevelTwentyTwoParameters SmallLevelPrimeRates SmallLevelTwentyTwoLaurent
open SmallLevelTwentyOneKnownWords (jetScale jetScale_binomial)

def scaledJetStack (m : ℕ) (w : Fin 264→ℂ) (b : Fin 4×Fin 66) : ℂ :=
  jetScale (1-(m:ℂ)) b.1*w (finProdFinEquiv b)

theorem parameter_candidate_lower (p m n : ℕ) (hp : p≠0) :
    parameter p m ((m:ℂ)+1-(n:ℂ))=(p:ℂ)/(p:ℂ)^n := by
  unfold parameter
  rw [show (m:ℂ)+1-(n:ℂ)-(m:ℂ)=1-(n:ℂ) by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one,Complex.cpow_natCast]

theorem leading_apply_laurent (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 66→ℂ) (i : Fin 68) :
    (∑ j,extendedLeading m f ε s i j*w j)=
      leadingRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) ((Real.sqrt 3:ℂ)*f 3) w i := by
  simpa only [Matrix.mulVec,dotProduct] using congrFun (extendedLeading_actual m f ε s w) i

theorem shift_apply_laurent (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 66→ℂ) (i : Fin 68) :
    (∑ j,extendedShift m f ε n s i j*w j)=
      (I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1))*
      positiveTaylorRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) n w i :=
  extendedShift_actual m f ε n s w i

/-- Exact falling-factorial normalization of the four-point block at the
sole physical first-jet candidate. The identity itself allows every weight. -/
theorem actual_jetBlockRow (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (hu : sigmaTwo f= -1) (ha : (Real.sqrt 3:ℂ)*f 3= -7/3)
    (n : Fin 4) (r : Fin 68) (w : Fin 264→ℂ) :
    (∑ b,blockLeading 3 (extendedLeading m f ε) (extendedShift m f ε)
      ((m:ℂ)+1) (n,r) b*scaledJetStack m w b)=
        jetScale (1-(m:ℂ)) n*jetBlockRow (phase m ε) (sigmaEleven f) n r w := by
  rw [blockLeading_apply]
  simp only [scaledJetStack,leading_apply_laurent,shift_apply_laurent,
    leadingRows_scale,positiveTaylorRows_scale,
    parameter_candidate_lower 2 m n.val (by decide),
    parameter_candidate_lower 3 m n.val (by decide),
    parameter_candidate_lower 11 m n.val (by decide),hu,ha,Nat.cast_ofNat]
  unfold jetBlockRow jetSlice
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha'
  have ha'' : a<n.val:=Finset.mem_range.mp ha'
  have he : (m:ℂ)+1-(n.val:ℂ)+((a+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=
      (1-(m:ℂ))-(n.val:ℂ)+((a+1:ℕ):ℂ) := by push_cast; ring
  rw [he,← mul_assoc,jetScale_binomial (1-(m:ℂ)) n a ha'']
  ring

#print axioms actual_jetBlockRow
end SmallLevelTwentyTwoJetBlock
end
end

/-! ## TwentyTwoJetBlockKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoJetBlock
open Complex Matrix SmallLevelFiniteShift SmallLevelTwentyTwoSystem
open SmallLevelTwentyTwoParameters
open SmallLevelTwentyOneKnownWords (jetScale jetScale_ne_zero)

theorem jetBlock_kernel_zero (η v : ℂ) (hη : η=1 ∨ η= -1) (hv : v=1 ∨ v= -1)
    (w : Fin 264→ℂ) (hw : ∀ n i,jetBlockRow η v n i w=0) : w=0 := by
  rcases hη with rfl|rfl <;> rcases hv with rfl|rfl
  · exact kernel_case3 w hw
  · exact kernel_case2 w hw
  · exact kernel_case1 w hw
  · exact kernel_case0 w hw

/-- The genuine four-point Mellin block is injective at the sole candidate
for weights at least four. -/
theorem actual_block_kernel_zero (m : ℕ) (hm : 2≤m) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phase m ε=1 ∨ phase m ε= -1)
    (hv : sigmaEleven f=1 ∨ sigmaEleven f= -1)
    (hu : sigmaTwo f= -1) (ha : (Real.sqrt 3:ℂ)*f 3= -7/3)
    (w : Fin 4×Fin 66→ℂ)
    (hw : ∀ r, ∑ b,blockLeading 3 (extendedLeading m f ε) (extendedShift m f ε)
      ((m:ℂ)+1) r b*w b=0) : w=0 := by
  let e : (Fin 4×Fin 66)≃Fin 264:=finProdFinEquiv
  let q : Fin 264→ℂ:=fun j => w (e.symm j)/jetScale (1-(m:ℂ)) (e.symm j).1
  have he : scaledJetStack m q=w := by
    funext b
    simp only [scaledJetStack,q,e,Equiv.symm_apply_apply]
    field_simp [jetScale_ne_zero m hm b.1]
  have hq (n : Fin 4) (i : Fin 68) : jetBlockRow (phase m ε) (sigmaEleven f) n i q=0 := by
    have hh:=hw (n,i)
    rw [←he,actual_jetBlockRow m f ε hu ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left (jetScale_ne_zero m hm n)
  have hq0:=jetBlock_kernel_zero _ _ hη hv q hq
  rw [←he,hq0]
  funext b
  simp [scaledJetStack]

#print axioms jetBlock_kernel_zero
#print axioms actual_block_kernel_zero
end SmallLevelTwentyTwoJetBlock
end
end

/-! ## TwentyTwoRightmostPole -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix Filter SmallLevelTwentyTwoParameters
open SmallLevelFiniteShift QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem PoleSystem.regular_tail_pole_at_weight {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) (x : ℂ) (w : Fin 66→ℂ) (hw : IsLeadingVector S.G x w)
    (htail : ∀ d b : ℕ, d≤b → ∀ i j, ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-d) ∧
      (fun z => extendedShift m f ε b z i j*S.G (z+((b:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-d)] R) :
    x=((2*m:ℕ):ℂ) := by
  by_contra hx
  obtain ⟨he,hu,ha⟩:=candidate_of_regular_tails hf ε hε S.B S.G S.H
    S.error S.rows x hx w hw htail
  have hm2 : 2≤m := by
    have hm1 : m≠1 := by intro h; subst m; norm_num at he; exact hx he
    omega
  obtain ⟨v,hv,hvk⟩:=continued_regular_block_kernel S.B S.G
    (extendedLeading m f ε) (extendedShift m f ε) S.H x 3
    S.meromorphic (extendedLeading_analytic m f ε) (extendedShift_analytic m f ε)
    S.error (fun n b hb i j => htail n.val b hb i j) S.rows
    (hw.exists_pole (fun j => S.meromorphic j x))
  apply hv
  apply SmallLevelTwentyTwoJetBlock.actual_block_kernel_zero m hm2 f ε
    (phase_sign m hε) (sigmaEleven_sign hf.toEulerData) hu ha v
  simpa only [he] using hvk

theorem PoleSystem.rightmost_pole_at_weight {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) (x : ℂ) (w : Fin 66→ℂ) (hw : IsLeadingVector S.G x w)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n)) :
    x=((2*m:ℕ):ℂ) :=
  S.regular_tail_pole_at_weight hm hf hε x w hw
    (fun d b hb i j => regular_pole_tail (extendedShift m f ε) (extendedShift_analytic m f ε)
      S.G S.meromorphic x d hshift b hb i j)

#print axioms PoleSystem.regular_tail_pole_at_weight
#print axioms PoleSystem.rightmost_pole_at_weight
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoUpperRegularity -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex QuantitativeArithmeticUniversalPoleVector

theorem PoleSystem.regular_above_weight {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) (x : ℂ) (hx : ((2*m:ℕ):ℝ)<x.re) (i : Fin 66) :
    0≤meromorphicOrderAt (fun z => S.G z i) x := by
  by_contra! hi
  obtain ⟨n,hp,hshift⟩:=SmallLevelPoleGrid.rightmost_pole (fun j z => S.G z j)
    (x:=x) ⟨i,hi⟩ S.B S.halfplane
  obtain ⟨w,hw⟩:=exists_leading_vector S.G (x+n)
    (fun j => (S.meromorphic j _).meromorphicAt) hp
  have he:=S.rightmost_pole_at_weight hm hf hε (x+n) w hw hshift
  have hr:=congrArg Complex.re he
  simp only [Complex.add_re,Complex.natCast_re] at hr
  have hn : (0:ℝ)≤n:=Nat.cast_nonneg n
  linarith

#print axioms PoleSystem.regular_above_weight
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoSelectedRegularizedFirstShift -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyTwoParameters
open SmallLevelTwentyTwoLaurent QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem selected_regularized_polynomial_first_shift {ρ : Type*} [Fintype ρ]
    (rows : ρ→Fin 68) (η u v a : ℂ)
    (coeff : ℂ→ℂ→ℂ→ρ→ℂ)
    (hsyz : ∀ X Y Z : ℂ, X≠0 → Y≠0 → Z≠0 → ∀ w : Fin 66→ℂ,
      ∑ i,coeff X Y Z i*leadingRows η u v X Y Z a w (rows i)=0)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phase m ε=η) (hu : sigmaTwo f=u) (hv : sigmaEleven f=v)
    (ha : (Real.sqrt 3:ℂ)*f 3=a)
    (hcoeff : ∀ z i, AnalyticAt ℂ
      (fun s => coeff (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) i) z)
    (B : ℝ) (G : ℂ→Fin 66→ℂ) (H : ℕ→ℂ→Fin 68→ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ b∈Finset.range n,
          ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j))
    (x : ℂ) (w : Fin 66→ℂ)
    (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*G z j) x w)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n)) :
    ∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3) (parameter 11 m x/11) i*
      firstRows η u v (parameter 2 m x) (parameter 3 m x) (parameter 11 m x) a w (rows i)=0 := by
  classical
  let K : ℂ→ρ→ℂ:=fun z => coeff (parameter 2 m z) (parameter 3 m z) (parameter 11 m z)
  let A : ℂ→Matrix ρ (Fin 66) ℂ:=fun z i => extendedLeading m f ε z (rows i)
  let C : ℕ→ℂ→Matrix ρ (Fin 66) ℂ:=fun n z i => extendedShift m f ε n z (rows i)
  let L : ℂ→Matrix Unit ρ ℂ:=fun z _ i => K z i
  let D : ℂ→Matrix Unit (Fin 66) ℂ:=fun z _ j =>
    I*∑ i,K (z-1) i*firstRows η u v (parameter 2 m z) (parameter 3 m z)
      (parameter 11 m z) a (Pi.single j 1) (rows i)
  have hKA (z : ℂ) (q : Fin 66→ℂ) : ∑ i,K z i*(∑ j,A z i j*q j)=0 := by
    have he (i : Fin 68) : (∑ j,extendedLeading m f ε z i j*q j)=
        leadingRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
          (parameter 2 m z) (parameter 3 m z) (parameter 11 m z) ((Real.sqrt 3:ℂ)*f 3) q i :=
      congrFun (extendedLeading_actual m f ε z q) i
    simp only [A,he,hη,hu,hv,ha,K]
    exact hsyz _ _ _ (parameter_ne_zero 2 m (by decide) z)
      (parameter_ne_zero 3 m (by decide) z) (parameter_ne_zero 11 m (by decide) z) q
  have hLA (z : ℂ) : L z*A z=0 := by
    ext r j
    have hh:=hKA z (Pi.single j 1)
    simpa [Matrix.mul_apply,L,A,Pi.single_apply] using hh
  have hD (r : Unit) (j : Fin 66) : AnalyticAt ℂ (fun z => D z r j) x := by
    apply analyticAt_const.mul
    apply Finset.analyticAt_fun_sum
    intro i _
    exact ((hcoeff (x-1) i).comp (f:=fun z : ℂ => z-1)
      (analyticAt_id.sub analyticAt_const)).mul
      (firstRows_analytic η u v a m (Pi.single j 1) x (rows i))
  have hfactor (z : ℂ) (r : Unit) (j : Fin 66) :
      (L (z-1)*C 0 (z-1)) r j=(z-((2*m:ℕ):ℂ))*D z r j := by
    have he (i : ρ) : extendedShift m f ε 0 (z-1) (rows i) j=
        (I*(z-((2*m:ℕ):ℂ)))*firstRows η u v (parameter 2 m z) (parameter 3 m z)
          (parameter 11 m z) a (Pi.single j 1) (rows i) := by
      simpa only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true,hη,hu,hv,ha] using
        firstShift_actual m f ε z (Pi.single j 1) (rows i)
    simp only [Matrix.mul_apply,L,C,D,he]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hh:=IsLeadingVector.factored_first_shift B G A C (fun n z i => H n z (rows i)) L
    hG (fun n z i j => extendedShift_analytic m f ε n z (rows i) j)
    (fun n i z hz => hH n (rows i) z hz) (fun z _ i => hcoeff z i) hLA
    (fun n i z hz => hrow n (rows i) z hz) x hshift
    (fun z => z-((2*m:ℕ):ℂ)) D hD hfactor w hw
  have hh':=congrFun hh ()
  change (∑ j,(I*∑ i,K (x-1) i*firstRows η u v (parameter 2 m x)
    (parameter 3 m x) (parameter 11 m x) a (Pi.single j 1) (rows i))*w j)=0 at hh'
  simp only [mul_assoc,←Finset.mul_sum,Finset.sum_mul] at hh'
  rw [Finset.sum_comm] at hh'
  simp only [←Finset.mul_sum,firstRows_basis,K,
    parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 11 m (by decide),Nat.cast_ofNat] at hh'
  exact (mul_eq_zero.mp hh').resolve_left I_ne_zero

#print axioms selected_regularized_polynomial_first_shift
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoRegularizedCandidate -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyTwoParameters
open SmallLevelTwentyTwoLaurent QuantitativeArithmeticUniversalPoleVector SmallLevelFiniteShift
open scoped Topology

theorem candidate_of_regularized_vector {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (B : ℝ) (G : ℂ→Fin 66→ℂ) (H : ℕ→ℂ→Fin 68→ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ b∈Finset.range n,
          ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j))
    (x : ℂ) (w : Fin 66→ℂ)
    (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*G z j) x w)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (x+n)) :
    x=(m:ℂ)+1 ∧ sigmaTwo f= -1 ∧ (Real.sqrt 3:ℂ)*f 3= -7/3 := by
  have hη:=phase_sign m hε
  have hu:=sigmaTwo_sign hf.toEulerData
  have hv:=sigmaEleven_sign hf.toEulerData
  have hwG:=hw.of_analytic_factor (fun z => z-((2*m:ℕ):ℂ))
    (analyticAt_id.sub analyticAt_const)
  have hlead:=hwG.regular_tail_leading B G (extendedLeading m f ε) (extendedShift m f ε)
    H x w (extendedLeading_analytic m f ε x) hH
    (fun b i j => by
      simpa only [Nat.cast_zero,sub_zero] using
        (regular_pole_tail (extendedShift m f ε) (extendedShift_analytic m f ε)
          G hG x 0 hshift b (Nat.zero_le b) i j)) hrow
  rw [extendedLeading_actual] at hlead
  have hcore : coreRows (phase m ε) (sigmaTwo f) (sigmaEleven f)
      (parameter 2 m x) (parameter 3 m x) (parameter 11 m x) ((Real.sqrt 3:ℂ)*f 3) w=0 := by
    funext i
    exact congrFun hlead ⟨i.val,by omega⟩
  have hjet:=firstJet_equations m (phase m ε) (sigmaTwo f) (sigmaEleven f)
    ((Real.sqrt 3:ℂ)*f 3) x hη hu hv w hcore hw.1
    (fun r rows coeff hcoeff hsyz => selected_regularized_polynomial_first_shift
      rows _ _ _ _ coeff hsyz m f ε rfl rfl rfl rfl hcoeff B G H hG hH hrow x w hw hshift)
  exact physical_candidate m _ _ _ _ x hη hu hv w hcore hw.1 hjet.1 hjet.2

#print axioms candidate_of_regularized_vector
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoTaylorRowsAnalytic -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoLaurent
open Complex SmallLevelPrimeRates

theorem positiveTaylorRows_analytic (η u v : ℂ) (m n : ℕ) (w : Fin 66→ℂ)
    (z : ℂ) (i : Fin 68) : AnalyticAt ℂ (fun s => positiveTaylorRows η u v
      (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) n w i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 11 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 11 m (by decide) z
  fin_cases i <;> norm_num [positiveTaylorRows]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem positiveTaylorRows_basis (η u v X Y Z : ℂ) (n : ℕ) (w : Fin 66→ℂ) (i : Fin 68) :
    (∑ j,positiveTaylorRows η u v X Y Z n (Pi.single j 1) i*w j)=
      positiveTaylorRows η u v X Y Z n w i := by
  classical
  fin_cases i <;>
    simp [positiveTaylorRows,Pi.single_apply,div_eq_mul_inv,mul_add,add_mul,sub_mul,
      mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,←mul_assoc]
  all_goals ring

#print axioms positiveTaylorRows_analytic
#print axioms positiveTaylorRows_basis
end SmallLevelTwentyTwoLaurent
end
end

/-! ## TwentyTwoRegularizedTaylor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoJetBlock
open Complex SmallLevelTwentyTwoSystem SmallLevelTwentyTwoParameters SmallLevelPrimeRates
open SmallLevelTwentyTwoLaurent
open SmallLevelTwentyOneKnownWords (weightOneChooseQuot weightOneChoose_factor)

def weightOneTaylorQuot (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (z : ℂ) :
    Matrix (Fin 68) (Fin 66) ℂ:=fun i j =>
  (I^n.val*weightOneChooseQuot n z)*positiveTaylorRows (phase 1 ε) (sigmaTwo f) (sigmaEleven f)
    (parameter 2 1 (z-n.val)) (parameter 3 1 (z-n.val)) (parameter 11 1 (z-n.val))
    (n.val-1) (Pi.single j 1) i

theorem weightOneTaylorQuot_apply (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (z : ℂ)
    (i : Fin 68) (w : Fin 66→ℂ) :
    (∑ j,weightOneTaylorQuot f ε n z i j*w j)=
      (I^n.val*weightOneChooseQuot n z)*positiveTaylorRows (phase 1 ε) (sigmaTwo f) (sigmaEleven f)
        (parameter 2 1 (z-n.val)) (parameter 3 1 (z-n.val)) (parameter 11 1 (z-n.val))
        (n.val-1) w i := by
  simp only [weightOneTaylorQuot,mul_assoc,←Finset.mul_sum,positiveTaylorRows_basis]

theorem weightOneTaylorQuot_analytic (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4)
    (z : ℂ) (i : Fin 68) (j : Fin 66) :
    AnalyticAt ℂ (fun s => weightOneTaylorQuot f ε n s i j) z := by
  have hq : AnalyticAt ℂ (fun s => weightOneChooseQuot n s) z := by
    fin_cases n
    · exact analyticAt_const
    · exact analyticAt_const
    · exact (analyticAt_id.sub analyticAt_const).div_const
    · exact ((analyticAt_id.sub analyticAt_const).mul
        (analyticAt_id.sub analyticAt_const)).div_const
  exact (analyticAt_const.mul hq).mul
    ((positiveTaylorRows_analytic (phase 1 ε) (sigmaTwo f) (sigmaEleven f) 1 (n.val-1)
      (Pi.single j 1) (z-n.val) i).comp (f:=fun s : ℂ => s-(n.val:ℂ))
        (analyticAt_id.sub analyticAt_const))

theorem weightOneTaylorQuot_factor (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (hn : n≠0)
    (z : ℂ) (i : Fin 68) (j : Fin 66) :
    extendedShift 1 f ε (n.val-1) (z-n.val) i j=(z-2)*weightOneTaylorQuot f ε n z i j := by
  have hnpos : 0<n.val:=Fin.pos_iff_ne_zero.mpr hn
  have hnv : n.val-1+1=n.val:=by omega
  have he:=shift_apply_laurent 1 f ε (n.val-1) (z-n.val) (Pi.single j 1) i
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true] at he
  rw [he,hnv]
  have hz : z-(n.val:ℂ)+(n.val:ℂ)-((2*1:ℕ):ℂ)=z-2 := by norm_num
  rw [hz,weightOneChoose_factor n hn]
  unfold weightOneTaylorQuot
  ring

#print axioms weightOneTaylorQuot_factor
#print axioms weightOneTaylorQuot_analytic
end SmallLevelTwentyTwoJetBlock
end
end

/-! ## TwentyTwoRegularizedBlockModel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoJetBlock
open Complex Matrix SmallLevelFiniteShift SmallLevelTwentyTwoSystem
open SmallLevelTwentyTwoParameters SmallLevelPrimeRates SmallLevelTwentyTwoLaurent
open SmallLevelTwentyOneKnownWords (regularizedJetScale weightOneChooseQuot)

def regularizedScaledStack (w : Fin 264→ℂ) (b : Fin 4×Fin 66) : ℂ :=
  regularizedJetScale b.1*w (finProdFinEquiv b)

theorem actual_regularizedBlockRow (f : ℕ→ℂ) (ε : ℂ)
    (hu : sigmaTwo f= -1) (ha : (Real.sqrt 3:ℂ)*f 3= -7/3)
    (n : Fin 4) (r : Fin 68) (w : Fin 264→ℂ) :
    (∑ b,regularizedBlock 3 (extendedLeading 1 f ε) (extendedShift 1 f ε)
      (weightOneTaylorQuot f ε) 2 (n,r) b*regularizedScaledStack w b)=
        regularizedJetScale n*jetBlockRow (phase 1 ε) (sigmaEleven f) n r w := by
  have hp (p t : ℕ) (hp : p≠0) : parameter p 1 (2-(t:ℂ))=(p:ℂ)/(p:ℂ)^t := by
    simpa only [Nat.cast_one,one_add_one_eq_two] using parameter_candidate_lower p 1 t hp
  have hp0 (p : ℕ) (hp' : p≠0) : parameter p 1 2=(p:ℂ) := by
    simpa using hp p 0 hp'
  have hslice (n : Fin 4) : jetSlice w n=(fun j => w (finProdFinEquiv (n,j))) := rfl
  rw [regularizedBlock_apply]
  simp only [regularizedScaledStack,leading_apply_laurent,shift_apply_laurent,
    weightOneTaylorQuot_apply,leadingRows_scale,positiveTaylorRows_scale,
    hp 2 _ (by decide),hp 3 _ (by decide),hp 11 _ (by decide),hu,ha,Nat.cast_ofNat]
  fin_cases n <;>
    norm_num [jetBlockRow,jetSlice,regularizedJetScale,weightOneChooseQuot,
      Finset.sum_range_succ,lowerIndex,Ring.choose_eq_smul,←Polynomial.aeval_eq_smeval,
      descPochhammer_succ_right,I_sq,pow_succ]
  all_goals try simp only [hslice]
  all_goals norm_num [hp0 2 (by decide),hp0 3 (by decide),hp0 11 (by decide)]
    <;> ring_nf <;> norm_num [I_sq] <;> ring

#print axioms actual_regularizedBlockRow
end SmallLevelTwentyTwoJetBlock
end
end

/-! ## TwentyTwoWeightPoleOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex Matrix SmallLevelTwentyTwoParameters SmallLevelTwentyTwoJetBlock
open SmallLevelFiniteShift QuantitativeArithmeticUniversalPoleVector
open SmallLevelTwentyOneKnownWords (regularizedJetScale regularizedJetScale_ne_zero)

theorem PoleSystem.weight_pole_order {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) :
    ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) ((2*m:ℕ):ℂ) := by
  have hshift : ∀ n : ℕ, 0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (((2*m:ℕ):ℂ)+n) := by
    intro n hn j
    apply S.regular_above_weight hm hf hε _ _ j
    simp only [Complex.add_re,Complex.natCast_re]
    have hn' : (0:ℝ)<n:=by exact_mod_cast hn
    linarith
  by_contra h
  push Not at h
  obtain ⟨w,hw⟩:=exists_regularized_leading_vector S.G ((2*m:ℕ):ℂ)
    (fun j => (S.meromorphic j _).meromorphicAt) h
  obtain ⟨hx,hu,ha⟩:=candidate_of_regularized_vector hf ε hε S.B S.G S.H
    S.meromorphic S.error S.rows _ w hw hshift
  have hm1 : m=1 := by
    have hr:=congrArg Complex.re hx
    norm_num at hr
    exact_mod_cast (show (m:ℝ)=1 by linarith)
  subst m
  have hpole : ∃ j,meromorphicOrderAt (fun z => (z-(2:ℂ))*S.G z j) 2<0 := by
    obtain ⟨j,hj⟩:=h
    norm_num at hj
    refine ⟨j,?_⟩
    have hloc : MeromorphicAt (fun z : ℂ => z-2) 2 :=
      (analyticAt_id.sub analyticAt_const).meromorphicAt
    change meromorphicOrderAt ((fun z : ℂ => z-2)*(fun z => S.G z j)) 2<0
    rw [meromorphicOrderAt_mul hloc (S.meromorphic j 2).meromorphicAt,
      meromorphicOrderAt_id_sub_const]
    lift meromorphicOrderAt (fun z => S.G z j) 2 to ℤ using hj.ne_top with q hq
    have hqlt : q< -1 := by
      change (q:WithTop ℤ)<((-1:ℤ):WithTop ℤ) at hj
      exact WithTop.coe_lt_coe.mp hj
    exact_mod_cast (show 1+q<0 by omega)
  obtain ⟨v,hv0,hvk⟩:=regularized_block_kernel S.B S.G (extendedLeading 1 f ε)
    (extendedShift 1 f ε) S.H 2 3 (weightOneTaylorQuot f ε) S.meromorphic
    (extendedLeading_analytic 1 f ε) (extendedShift_analytic 1 f ε)
    (fun n r j => weightOneTaylorQuot_analytic f ε n 2 r j)
    (weightOneTaylorQuot_factor f ε) S.error (by simpa using hshift) S.rows hpole
  let e : (Fin 4×Fin 66)≃Fin 264:=finProdFinEquiv
  let q : Fin 264→ℂ:=fun j => v (e.symm j)/regularizedJetScale (e.symm j).1
  have he : regularizedScaledStack q=v := by
    funext b
    simp only [regularizedScaledStack,q,e,Equiv.symm_apply_apply]
    field_simp [regularizedJetScale_ne_zero b.1]
  have hq (n : Fin 4) (i : Fin 68) : jetBlockRow (phase 1 ε) (sigmaEleven f) n i q=0 := by
    have hh:=hvk (n,i)
    rw [←he,actual_regularizedBlockRow f ε hu ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left (regularizedJetScale_ne_zero n)
  have hq0:=jetBlock_kernel_zero _ _ (phase_sign 1 hε) (sigmaEleven_sign hf.toEulerData) q hq
  apply hv0
  rw [←he,hq0]
  funext b
  simp [regularizedScaledStack]

#print axioms PoleSystem.weight_pole_order
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoShiftCancellation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex QuantitativeArithmeticSmallLevelTwentyTwo

theorem shiftMatrix_zero_at_weight (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (i j : Fin 66) : gridShiftMatrix m f ε n s i j=0 := by
  have he : s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=0 := by
    rw [Nat.cast_add,Nat.cast_one,hs,sub_self]
  have hg (r : Fin 35) : gridMatrixScalar m
      (FinitenessNormalizedTwistProduct.root 22 f 2) (ε*I^(2*m)) r (n+1) s=0 := by
    unfold gridMatrixScalar
    rw [he,Ring.choose_zero_succ,mul_zero]
  have ht (r : Fin 11) : gridTaylorCoefficient m f ε r (n+1) s=0 := by
    unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar
    rw [he,Ring.choose_zero_succ,mul_zero]
  rw [gridShiftMatrix_apply]
  unfold gridShiftRows gridAssemble
  split_ifs
  · simp only [hg,zero_mul]
  · simp only [ht,zero_mul]
  · rfl
  · rfl

theorem extendedShift_zero_at_weight (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (i : Fin 68) (j : Fin 66) :
    extendedShift m f ε n s i j=0 := by
  unfold extendedShift
  split_ifs
  · exact shiftMatrix_zero_at_weight m f ε n s hs _ j
  · rfl

#print axioms extendedShift_zero_at_weight
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoFullPoleBound -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoSystem
open Complex SmallLevelFiniteShift QuantitativeArithmeticUniversalPoleVector

theorem PoleSystem.regular_off_weight {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) (x : ℂ) (hx : x≠((2*m:ℕ):ℂ)) (i : Fin 66) :
    AnalyticAt ℂ (fun z => S.G z i) x := by
  apply (S.meromorphic i x).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hi
  obtain ⟨n,hne,hp,hshift⟩:=SmallLevelPoleGrid.rightmost_pole_away
    (fun j z => S.G z j) (x:=x) ((2*m:ℕ):ℂ) hx ⟨i,hi⟩ S.B S.halfplane
  obtain ⟨w,hw⟩:=exists_leading_vector S.G (x+n)
    (fun j => (S.meromorphic j _).meromorphicAt) hp
  apply hne
  apply S.regular_tail_pole_at_weight hm hf hε (x+n) w hw
  intro d b hb r j
  exact allowed_simple_pole_tail (extendedShift m f ε) ((2*m:ℕ):ℂ)
    (extendedShift_analytic m f ε) (extendedShift_zero_at_weight m f ε)
    S.G S.meromorphic (x+n) d hshift (S.weight_pole_order hm hf hε) b hb r j

#print axioms PoleSystem.regular_off_weight
end SmallLevelTwentyTwoSystem
end
end

/-! ## TwentyTwoUniformOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoCoherentReflection
open Complex Filter Set QuantitativeArithmeticSmallLevelTwentyTwo
open scoped Topology

theorem uniform_product_identity {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=quadraticCombination (2*m) f s) :
    ∀ s, denominator m f s*G s=numerator m f s := by
  obtain ⟨C,hC⟩ := original_quotient_identity m hm hf
  have hleft := (denominator_entire m f).mul hG
  have hright := original_numerator_entire m hm hf
  intro s
  have he : (fun z => denominator m f z*G z)=ᶠ[𝓝[≠] s] numerator m f := by
    apply SmallLevelContinuation.halfplane_germ_identity (s.re-1) (max B C)
    · exact fun z _ => (hleft.analyticAt z).meromorphicAt
    · exact fun z _ => (hright.analyticAt z).meromorphicAt
    · intro z hz
      dsimp only
      rw [hGF z (lt_of_le_of_lt (le_max_left _ _) hz)]
      exact (hC z (lt_of_le_of_lt (le_max_right _ _) hz)).symm
    · linarith
  exact (((hleft.analyticAt s).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hright.analyticAt s).meromorphicNFAt).mp he).eq_of_nhds

theorem uniform_finiteOrder {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f)
    {G : ℂ→ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=quadraticCombination (2*m) f s) :
    FinitenessOriginalInput.FiniteOrder G :=
  finiteOrder_of_entire hm hf hG (uniform_product_identity hm hf hG B hGF)

#print axioms uniform_product_identity
#print axioms uniform_finiteOrder
end SmallLevelTwentyTwoCoherentReflection
end
end

/-! ## TwentyTwoPartnerFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoPartners
open Complex SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelTwentyTwo SmallLevelTwentyTwoCoherentReflection
open QuantitativeArithmeticQuadraticFive

/-- Conditional final Mellin inversion, with the original sign retained. -/
theorem fricke_of_simple_partners {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : GridFrickeLaws (2*m) f ε)
    (BG : ℝ) (Gp Gn : ℂ→ℂ)
    (hGp : ∀ s, MeromorphicAt Gp s) (hGn : ∀ s, MeromorphicAt Gn s)
    (hGpa : ∀ s, s≠((2*m:ℕ):ℂ) → AnalyticAt ℂ Gp s)
    (hGna : ∀ s, s≠((2*m:ℕ):ℂ) → AnalyticAt ℂ Gn s)
    (hGpo : (-1:WithTop ℤ)≤meromorphicOrderAt Gp ((2*m:ℕ):ℂ))
    (hGno : (-1:WithTop ℤ)≤meromorphicOrderAt Gn ((2*m:ℕ):ℂ))
    (hGpF : ∀ s, BG<s.re → Gp s=original (2*m) f (-5/22) s)
    (hGnF : ∀ s, BG<s.re → Gn s=original (2*m) f (5/22) s)
    : ∀ z : ℂ, 0<z.im → quadraticFourier (2*m) f z=
      (-ε*I^(2*m))/(((Real.sqrt 550:ℂ)*z)^(2*m))*
        quadraticFourier (2*m) f (-1/((550:ℂ)*z)) := by
  obtain ⟨BQ,Q,hQ,hQF,hFE,hQD,_hgerm⟩:=quadratic_functional_equation_of_laws m hm hf ε hε hlaw
  have hent : Differentiable ℂ Q := fun s =>
    (quadratic_entire_of_simple_partners hm hf ε hlaw BG Gp Gn hGp hGn
      hGpa hGna hGpo hGno hGpF hGnF BQ Q hQ hQF hQD s).differentiableAt
  have hfinite:=uniform_finiteOrder hm hf hent BQ hQF
  obtain ⟨τ,_hτ,hgrowth⟩:=hf.growth
  apply QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
    (by decide : 0<550) hf.zero hgrowth (1/5) (-1/5) (2/5) (-2/5) Q hent hfinite
  · intro s hs
    rw [hQF s hs]
    unfold quadraticCombination evenOne evenTwo
    ring
  · rcases hε with rfl|rfl <;> norm_num
  · have he : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
    simpa only [Nat.cast_ofNat,he] using hFE

#print axioms fricke_of_simple_partners
end SmallLevelTwentyTwoPartners
end
end

/-! ## TwentyTwoModularFromGrid -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoPartners
open Complex SmallLevelAdditive QuantitativeArithmeticSmallLevelTwentyTwo

/-- Conditional modularity endpoint. The sole remaining analytic obligation
is a global66-grid continuation regular off the weight, with at most simple
poles there. This theorem does not assert those pole bounds. -/
theorem modular_of_grid_pole_bound {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε)
    (B : ℝ) (G : ℂ→Fin 66→ℂ)
    (hG : ∀ i s, MeromorphicNFAt (fun z => G z i) s)
    (hGF : ∀ s, B<s.re → G s=gridVector (2*m) f s)
    (hGa : ∀ i s, s≠((2*m:ℕ):ℂ) → AnalyticAt ℂ (fun z => G z i) s)
    (hGo : ∀ i, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z i) ((2*m:ℕ):ℂ)) :
    SmallLevelOriginal.IsModular 22 (2*m) f := by
  have hp (s : ℂ) (hs : B<s.re) : G s (gridIndex (-15))=original (2*m) f (-5/22) s := by
    convert congrFun (hGF s hs) (gridIndex (-15)) using 1
    norm_num [gridVector_index,grid]
  have hn (s : ℂ) (hs : B<s.re) : G s (gridIndex 15)=original (2*m) f (5/22) s := by
    convert congrFun (hGF s hs) (gridIndex 15) using 1
    norm_num [gridVector_index,grid]
  apply modular_of_five_pair (by omega : 0<2*m) (even_two_mul m) hf
  apply five_pair_of_quadratic_fricke ε hlaw
  exact fricke_of_simple_partners hm hf ε hε hlaw B
    (fun s => G s (gridIndex (-15))) (fun s => G s (gridIndex 15))
    (fun s => (hG _ s).meromorphicAt) (fun s => (hG _ s).meromorphicAt)
    (hGa _) (hGa _) (hGo _) (hGo _) hp hn

#print axioms modular_of_grid_pole_bound
end SmallLevelTwentyTwoPartners
end
end

/-! ## TwentyTwoModular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelOriginal
open Complex SmallLevelTwentyTwoSystem QuantitativeArithmeticSmallLevelTwentyTwo

/-- Original-input level22 modularity, including all signs, all Hecke
values, every positive even weight and all cusps. -/
theorem level_twenty_two {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 k f) : IsModular 22 k f := by
  obtain ⟨m,hm⟩:=heven
  have hkm : k=2*m:=by omega
  rw [hkm] at hf ⊢
  have hmpos : 0<m:=by omega
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  obtain ⟨S⟩:=exists_poleSystem hmpos hf ε hε hlaw
  apply SmallLevelTwentyTwoPartners.modular_of_grid_pole_bound hmpos hf ε hε hlaw
    S.B S.G S.meromorphic S.original
  · intro i s hs
    exact S.regular_off_weight hmpos hf hε s hs i
  · exact S.weight_pole_order hmpos hf hε

#print axioms level_twenty_two
end SmallLevelOriginal
end
end
