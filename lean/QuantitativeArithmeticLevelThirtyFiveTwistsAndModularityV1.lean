module
public import QuantitativeArithmeticLevelThirtyFiveChiThreeRegularityV1
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticLevelThirtyFivePoleAlgebraV4
-- Bounded certificate elaboration.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

set_option Elab.async false

/-! ## ThirtyFiveChiThreeFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelNormalized SmallLevelOriginal
open scoped ModularForm

certificate_batch {
def quadraticFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/3:ℝ))-
  fourier (fullCoefficients f k) (z+(-1/3:ℝ))

/-- The quadratic-three Fourier law, retaining the same sign as the
untwisted Fricke law. All analytic continuation is derived from original input. -/
theorem original_quadratic_fricke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=
        (ε*I^(2*m)) • fourierFunction (2*m) f ∧
      ∀ z : ℂ, 0<z.im → quadraticFourier (2*m) f z=
        (ε*I^(2*m))/(((Real.sqrt 315:ℂ)*z)^(2*m))*
          quadraticFourier (2*m) f (-1/((315:ℂ)*z)) := by
  obtain ⟨ε,B,G,hε,hlaw,hW,hent,hfinite,hGF,hFE⟩ :=
    QuantitativeArithmeticSmallLevelThirtyFiveKnownWords.original_chi3_entire hm hf
  obtain ⟨σ,_hσ,hgrowth⟩ := hf.growth
  refine ⟨ε,hε,hlaw,hW,?_⟩
  have h := QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
    (k := 2*m) (ε := ε) (B := B)
    (by decide : 0<315) hf.zero hgrowth (1/3) 0 (-1/3) 0 G hent hfinite
    (by
      intro s hs
      rw [hGF s hs]
      ring)
    (by rcases hε with rfl|rfl <;> norm_num)
    (by
      have he : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
      simpa only [Nat.cast_ofNat,he] using hFE)
  intro z hz
  dsimp only at h
  unfold quadraticFourier
  convert h z hz using 1 <;> ring

#print axioms original_quadratic_fricke
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveChiThreeIndividual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

certificate_batch {
/-- The Ramanujan-three and quadratic-three equations separate into the
two individual additive equations without dividing by a Hecke eigenvalue. -/
theorem individual_laws {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*I^k)/(((Real.sqrt 315:ℂ)*z)^k)*quadraticFourier k f (-1/((315:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im →
      (fourier (fullCoefficients f k) (z+1/3)=
        (ε*I^k)/(((Real.sqrt 315:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((315:ℂ)*z)+1/3)) ∧
      (fourier (fullCoefficients f k) (z-1/3)=
        (ε*I^k)/(((Real.sqrt 315:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((315:ℂ)*z)-1/3)) := by
  intro z hz
  have hr := hlaw 3 (by decide) z hz
  rw [show Nat.lcm 35 (3^2)=315 by decide,root_three,one_mul,
    SmallLevelThree.twist_three _ (periodic _),
    SmallLevelThree.twist_three _ (periodic _)] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hc := hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  simp only [sub_eq_add_neg] at hr hc ⊢
  constructor
  · linear_combination (hr+hc)/2
  · linear_combination (hr-hc)/2

#print axioms individual_laws
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveGroupHecke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  QuantitativeArithmeticRetainedReconstruction
open scoped MatrixGroups ModularForm

certificate_batch {
theorem original_hecke_two {f : ℕ → ℂ} (hf : EulerData 35 f) (m : ℕ) :
    heckeTwo ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)=
      (FinitenessAllLevelHeckePower.scale 2 m*f 2/2) • SmallLevelOriginal.fourierFunction (2*m) f := by
  exact SmallLevelGoodHeckeTwo.original_hecke_two (by decide : ¬2∣35) hf m

#print axioms original_hecke_two
}

end QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
end
end

/-! ## ThirtyFiveGroupHeckeConsequence -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
  QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open scoped MatrixGroups ModularForm

certificate_batch {
def Cplus : SL(2,ℤ) := ⟨!![3,-1;-35,12],by decide⟩
def Cminus : SL(2,ℤ) := ⟨!![3,1;35,12],by decide⟩
def H : SL(2,ℤ) := ⟨!![41,-17;70,-29],by decide⟩

theorem branch_zero : heckeFinite 0*SpecialLinearGroup.mapGL ℝ (six⁻¹)=
    SpecialLinearGroup.mapGL ℝ Cminus*heckeInfinity := by
  rw [show six⁻¹=(⟨!![6,1;35,6],by decide⟩ : SL(2,ℤ)) by decide]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,heckeInfinity,six,Cminus,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem branch_infinity : heckeInfinity*SpecialLinearGroup.mapGL ℝ (six⁻¹)=
    SpecialLinearGroup.mapGL ℝ (Cplus⁻¹)*heckeFinite 0 := by
  rw [show Cplus⁻¹=(⟨!![12,1;35,3],by decide⟩ : SL(2,ℤ)) by decide]
  rw [show six⁻¹=(⟨!![6,1;35,6],by decide⟩ : SL(2,ℤ)) by decide]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,heckeInfinity,six,Cplus,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem branch_one : heckeFinite 1*SpecialLinearGroup.mapGL ℝ (six⁻¹)=
    SpecialLinearGroup.mapGL ℝ H*heckeFinite 1 := by
  rw [show six⁻¹=(⟨!![6,1;35,6],by decide⟩ : SL(2,ℤ)) by decide]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,six,H,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- The extra matrix H is forced by Hecke2 once C+ and C- are invariant.
No division by the Hecke eigenvalue is involved. -/
theorem original_H (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (hp : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cplus=
      SmallLevelOriginal.fourierFunction (2*m) f)
    (hn : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cminus=
      SmallLevelOriginal.fourierFunction (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] H=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let K := slashStabilizer k F
  have hb : F ∣[k] six⁻¹=F := K.inv_mem (original_six (by omega) hf)
  have hpi : F ∣[k] Cplus⁻¹=F := K.inv_mem hp
  have he := original_hecke_two hf.toEulerData m
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] six⁻¹) he
  simp only [heckeTwo,SlashAction.add_slash,ModularForm.SL_smul_slash] at hh
  rw [hb] at hh
  have hi : (F ∣[k] heckeInfinity) ∣[k] six⁻¹=F ∣[k] heckeFinite 0 := by
    change (F ∣[k] heckeInfinity) ∣[k] SpecialLinearGroup.mapGL ℝ (six⁻¹)=_
    rw [← SlashAction.slash_mul,branch_infinity,SlashAction.slash_mul]
    change (F ∣[k] Cplus⁻¹) ∣[k] heckeFinite 0=_
    rw [hpi]
  have h0 : (F ∣[k] heckeFinite 0) ∣[k] six⁻¹=F ∣[k] heckeInfinity := by
    change (F ∣[k] heckeFinite 0) ∣[k] SpecialLinearGroup.mapGL ℝ (six⁻¹)=_
    rw [← SlashAction.slash_mul,branch_zero,SlashAction.slash_mul]
    change (F ∣[k] Cminus) ∣[k] heckeInfinity=_
    rw [hn]
  have h1 : (F ∣[k] heckeFinite 1) ∣[k] six⁻¹=(F ∣[k] H) ∣[k] heckeFinite 1 := by
    change (F ∣[k] heckeFinite 1) ∣[k] SpecialLinearGroup.mapGL ℝ (six⁻¹)=_
    rw [← SlashAction.slash_mul,branch_one,SlashAction.slash_mul]
    rfl
  have hz : (F ∣[k] H) ∣[k] heckeFinite 1=F ∣[k] heckeFinite 1 := by
    change (F ∣[k] heckeInfinity) ∣[k] six⁻¹+
      (F ∣[k] heckeFinite 0) ∣[k] six⁻¹+
      (F ∣[k] heckeFinite 1) ∣[k] six⁻¹=_ at hh
    rw [hi,h0,h1] at hh
    change (F ∣[k] heckeInfinity)+(F ∣[k] heckeFinite 0)+(F ∣[k] heckeFinite 1)=_ at he
    funext z
    have hh' := congrFun hh z
    have he' := congrFun he z
    simp only [Pi.add_apply] at hh' he'
    linear_combination hh'-he'
  have hc := congrArg (fun G : ℍ → ℂ => G ∣[k] (heckeFinite 1)⁻¹) hz
  simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using hc

#print axioms original_H
}

end QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
end
end

/-! ## ThirtyFiveChiThreeMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Matrix UpperHalfPlane SmallLevelNormalized
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

certificate_batch {
theorem sqrt_three_conductor : Real.sqrt 315=3*Real.sqrt 35 := by
  rw [show (315:ℝ)=9*35 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem plus_branch : fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Cplus*translation (1/3)=
    translation (1/3)*fricke 315 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Cplus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_three_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem minus_branch : fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Cminus*translation (-1/3)=
    translation (-1/3)*fricke 315 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Cminus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_three_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem plus_conjugate : (fricke 35 (by decide))⁻¹*translation (1/3)*fricke 315 (by decide)*
    (translation (1/3))⁻¹=SpecialLinearGroup.mapGL ℝ Cplus := by
  calc
    _=(fricke 35 (by decide))⁻¹*(translation (1/3)*fricke 315 (by decide))*(translation (1/3))⁻¹ := by group
    _=(fricke 35 (by decide))⁻¹*(fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Cplus*translation (1/3))*(translation (1/3))⁻¹ := by rw [plus_branch]
    _=_ := by group

theorem minus_conjugate : (fricke 35 (by decide))⁻¹*translation (-1/3)*fricke 315 (by decide)*
    (translation (-1/3))⁻¹=SpecialLinearGroup.mapGL ℝ Cminus := by
  calc
    _=(fricke 35 (by decide))⁻¹*(translation (-1/3)*fricke 315 (by decide))*(translation (-1/3))⁻¹ := by group
    _=(fricke 35 (by decide))⁻¹*(fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Cminus*translation (-1/3))*(translation (-1/3))⁻¹ := by rw [minus_branch]
    _=_ := by group

#print axioms plus_conjugate
#print axioms minus_conjugate
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveChiThreeTransformations -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

certificate_batch {
/-- Original Euler/Fricke input forces both denominator-three matrices,
including the zero Hecke-eigenvalue cases. -/
theorem original_C_plus_minus {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cplus=fourierFunction (2*m) f ∧
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cminus=fourierFunction (2*m) f := by
  obtain ⟨ε,_hε,hlaw,_hW,hquad⟩ := original_quadratic_fricke hm hf
  have hF : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*Complex.I^(2*m))/(((Real.sqrt 35:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((35:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have hind := individual_laws ε hlaw hquad
  constructor
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_of_fricke
      35 315 (2*m) (by decide) (by decide) (1/3) _ _ hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_one,
          Complex.ofReal_ofNat] using (hind z hz).1)
    rw [plus_conjugate] at h
    exact h
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_of_fricke
      35 315 (2*m) (by decide) (by decide) (-1/3) _ _ hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat,
          Complex.ofReal_one,sub_eq_add_neg,neg_div] using (hind z hz).2)
    rw [minus_conjugate] at h
    exact h

#print axioms original_C_plus_minus
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveTwelveGenerators -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized SmallLevelOriginal
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open scoped MatrixGroups ModularForm

certificate_batch {
theorem original_H_unconditional {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] H=fourierFunction (2*m) f := by
  obtain ⟨hp,hn⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_C_plus_minus hm hf
  exact original_H m hm hf hp hn

def generator : Fin 4 → SL(2,ℤ)
  | 0 => ⟨!![12,-1;-35,3],by decide⟩
  | 1 => ⟨!![12,1;35,3],by decide⟩
  | 2 => ⟨!![12,-5;-175,73],by decide⟩
  | 3 => ⟨!![12,5;175,73],by decide⟩

def center : Fin 4 → ℝ := ![1/12,-1/12,5/12,-5/12]

theorem original_generators {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (i : Fin 4) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] generator i=fourierFunction (2*m) f := by
  let K := slashStabilizer (((2*m:ℕ):ℤ)) (fourierFunction (2*m) f)
  obtain ⟨hp,hn⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_C_plus_minus hm hf
  have hh : H∈K := original_H_unconditional hm hf
  have he : QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3∈K := original_rows (by omega) hf 3
  have ht : T∈K := original_T (2*m) f
  have hu : lower 35∈K := original_lower (by decide) hf
  change generator i∈K
  fin_cases i
  · change generator 0∈K
    rw [show generator 0=Cminus⁻¹ by decide]
    exact K.inv_mem hn
  · change generator 1∈K
    rw [show generator 1=Cplus⁻¹ by decide]
    exact K.inv_mem hp
  · change generator 2∈K
    rw [show generator 2=QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3*H by decide]
    exact K.mul_mem he hh
  · change generator 3∈K
    rw [show generator 3=(lower 35*QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3*T)*(T⁻¹*H⁻¹*T) by decide]
    exact K.mul_mem (K.mul_mem (K.mul_mem hu he) ht)
      (K.mul_mem (K.mul_mem (K.inv_mem ht) (K.inv_mem hh)) ht)

#print axioms original_H_unconditional
#print axioms original_generators
}

end QuantitativeArithmeticSmallLevelThirtyFiveTwelve
end
end

/-! ## ThirtyFiveChiFourWordMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized SmallLevelOriginal
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open scoped MatrixGroups ModularForm

certificate_batch {
def integral : Fin 6 → SL(2,ℤ)
  | 0 => ⟨!![2,-1;-105,53],by decide⟩
  | 1 => ⟨!![2,-1;-35,18],by decide⟩
  | 2 => ⟨!![3,-2;35,-23],by decide⟩
  | 3 => Cplus
  | 4 => ⟨!![6,-5;35,-29],by decide⟩
  | 5 => ⟨!![12,-7;-245,143],by decide⟩

theorem original_integral {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (i : Fin 6) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] integral i=fourierFunction (2*m) f := by
  let K := slashStabilizer (((2*m:ℕ):ℤ)) (fourierFunction (2*m) f)
  obtain ⟨hp,hn⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_C_plus_minus hm hf
  have hh : H∈K := QuantitativeArithmeticSmallLevelThirtyFiveTwelve.original_H_unconditional hm hf
  have he : QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3∈K := original_rows (by omega) hf 3
  have ht : T∈K := original_T (2*m) f
  change integral i∈K
  fin_cases i
  · exact original_rows (by omega) hf 2
  · exact he
  · change integral 2∈K
    rw [show integral 2=Cminus*T⁻¹ by decide]
    exact K.mul_mem hn (K.inv_mem ht)
  · exact hp
  · exact original_rows (by omega) hf 6
  · change integral 5∈K
    rw [show integral 5=QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3*H⁻¹ by decide]
    exact K.mul_mem he (K.inv_mem hh)

def matrix : Fin 9 → GL (Fin 2) ℝ
  | 0 => fricke 35 (by decide)
  | 1 => fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ T⁻¹
  | 2 => SpecialLinearGroup.mapGL ℝ (integral 0)
  | 3 => SpecialLinearGroup.mapGL ℝ (integral 1)
  | 4 => SpecialLinearGroup.mapGL ℝ (integral 2)
  | 5 => SpecialLinearGroup.mapGL ℝ (integral 3)
  | 6 => SpecialLinearGroup.mapGL ℝ (integral 4)
  | 7 => SpecialLinearGroup.mapGL ℝ (integral 5)
  | 8 => fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (integral 1)

def isFricke (i : Fin 9) : Bool := i=0 || i=1 || i=8

def sign (χ : ℂ) (i : Fin 9) : ℂ := if isFricke i then χ else 1

def raw : Fin 9 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![0,-1;35,0]
  | 1 => !![0,-1;35,-35]
  | 2 => !![2,-1;-105,53]
  | 3 => !![2,-1;-35,18]
  | 4 => !![3,-2;35,-23]
  | 5 => !![3,-1;-35,12]
  | 6 => !![6,-5;35,-29]
  | 7 => !![12,-7;-245,143]
  | 8 => !![35,-18;70,-35]

def scale (i : Fin 9) : ℝ := if isFricke i then 1/Real.sqrt 35 else 1

theorem matrix_det (i : Fin 9) : (GeneralLinearGroup.det (matrix i):ℝ)=1 := by
  have hd : (fricke 35 (by decide)).val.det=1 := fricke_det 35 (by decide)
  fin_cases i <;> simp [matrix,hd]

theorem sign_cases {χ : ℂ} (hχ : χ=1 ∨ χ= -1) (i : Fin 9) :
    sign χ i=1 ∨ sign χ i= -1 := by
  unfold sign
  split_ifs
  · exact hχ
  · exact Or.inl rfl

theorem original_matrix_actions {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (i : Fin 9) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] matrix i=
      sign (ε*Complex.I^(2*m)) i • fourierFunction (2*m) f := by
  obtain ⟨_hχ,hW⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<35) m ε hε hlaw
  have hi (j : Fin 6) : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      SpecialLinearGroup.mapGL ℝ (integral j)=fourierFunction (2*m) f := original_integral hm hf j
  have ht : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T⁻¹=fourierFunction (2*m) f :=
    (slashStabilizer (((2*m:ℕ):ℤ)) (fourierFunction (2*m) f)).inv_mem (original_T (2*m) f)
  change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ T⁻¹=
    fourierFunction (2*m) f at ht
  fin_cases i
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=
      (ε*Complex.I^(2*m)) • fourierFunction (2*m) f
    exact hW
  · change _ ∣[_] (fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ T⁻¹)=
      (ε*Complex.I^(2*m)) • _
    rw [SlashAction.slash_mul,hW,det_one_smul _ (by simp)]
    rw [ht]
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 0)=1 • _
    rw [one_smul]
    exact hi 0
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 1)=1 • _
    rw [one_smul]
    exact hi 1
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 2)=1 • _
    rw [one_smul]
    exact hi 2
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 3)=1 • _
    rw [one_smul]
    exact hi 3
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 4)=1 • _
    rw [one_smul]
    exact hi 4
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 5)=1 • _
    rw [one_smul]
    exact hi 5
  · change _ ∣[_] (fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (integral 1))=
      (ε*Complex.I^(2*m)) • _
    rw [SlashAction.slash_mul,hW,det_one_smul _ (by simp)]
    rw [hi 1]

#print axioms original_integral
#print axioms original_matrix_actions
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourRawRates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

certificate_batch {
theorem raw_det_pos (i : Fin 9) : 0<(raw i).det := by fin_cases i <;> decide

theorem scale_pos (i : Fin 9) : 0<scale i := by
  unfold scale
  split_ifs
  · exact one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  · norm_num

theorem raw_coordinates (i : Fin 9) (a b : Fin 2) :
    (matrix i).val a b=scale i*(raw i a b:ℝ) := by
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hT : T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) := by decide
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [matrix,integral,raw,scale,isFricke,fricke,SmallLevelNormalized.matrix,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.Cplus,hT,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith [ht]

theorem scale_squared_det (i : Fin 9) : (scale i)^2*((raw i).det:ℝ)=1 := by
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> norm_num [scale,isFricke,raw,Matrix.det_fin_two,ht,hn]

def coordA (i : Fin 9) : ℝ := (matrix i).val 0 0
def coordB (i : Fin 9) : ℝ := (matrix i).val 0 1
def coordC (i : Fin 9) : ℝ := (matrix i).val 1 0
def coordD (i : Fin 9) : ℝ := (matrix i).val 1 1

theorem coordinate_det (i : Fin 9) : coordA i*coordD i-coordB i*coordC i=1 := by
  have hd := matrix_det i
  change (matrix i).val.det=1 at hd
  simpa only [Matrix.det_fin_two,coordA,coordB,coordC,coordD] using hd

def rawDen (i : Fin 9) (t : ℤ) : ℤ := raw i 1 0*t+raw i 1 1*420

def rawNumer (i : Fin 9) (t : ℤ) : ℤ := raw i 0 0*t+raw i 0 1*420

def rate (i : Fin 9) (t : ℤ) : ℚ := (rawDen i t:ℚ)^2/((raw i).det*420^2)

def derivative (i : Fin 9) (t : ℤ) : ℚ := (raw i 1 0:ℚ)*rawDen i t/((raw i).det*420)

theorem coordDen_raw (i : Fin 9) (t : ℤ) :
    coordC i*((t:ℝ)/420)+coordD i=scale i*((rawDen i t:ℝ)/420) := by
  simp only [coordC,coordD,raw_coordinates,rawDen,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
  ring

theorem rate_eq (i : Fin 9) (t : ℤ) :
    (coordC i*((t:ℝ)/420)+coordD i)^2=(rate i t:ℝ) := by
  rw [coordDen_raw]
  have hd : ((raw i).det:ℝ)≠0 := by exact_mod_cast (raw_det_pos i).ne'
  have hs := scale_squared_det i
  norm_num only [rate,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat]
  field_simp [hd]
  linear_combination 176400*(rawDen i t:ℝ)^2*hs

theorem derivative_eq (i : Fin 9) (t : ℤ) :
    coordC i*(coordC i*((t:ℝ)/420)+coordD i)=(derivative i t:ℝ) := by
  rw [coordDen_raw]
  simp only [coordC,raw_coordinates]
  have hd : ((raw i).det:ℝ)≠0 := by exact_mod_cast (raw_det_pos i).ne'
  have hs := scale_squared_det i
  norm_num only [derivative,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat]
  field_simp [hd]
  linear_combination (raw i 1 0:ℝ)*(rawDen i t:ℝ)*hs

#print axioms raw_coordinates
#print axioms rate_eq
#print axioms derivative_eq
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourWordTaylor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Matrix UpperHalfPlane SmallLevelNormalized Complex Set
open FinitenessOriginalFourier FinitenessFourierConstruction SmallLevelAdditive
open QuantitativeArithmeticTwoSequenceTaylor
open scoped MatrixGroups ModularForm

certificate_batch {
theorem matrix_fourier_of_slash (m : ℕ) (f : ℕ → ℂ) (χ : ℂ)
    (hχ : χ=1 ∨ χ= -1) (w : Fin 9)
    (hw : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] matrix w=
      sign χ w • SmallLevelOriginal.fourierFunction (2*m) f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f (2*m)) z=
      sign χ w/(((coordC w:ℂ)*z+(coordD w:ℂ))^(2*m))*
        fourier (fullCoefficients f (2*m))
          (((coordA w:ℂ)*z+(coordB w:ℂ))/((coordC w:ℂ)*z+(coordD w:ℂ))) := by
  have hback : SmallLevelOriginal.fourierFunction (2*m) f=
      sign χ w • (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] matrix w) := by
    rcases sign_cases hχ w with hc|hc
    · simpa only [hc,one_smul] using hw.symm
    · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hw.symm
  have h := congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (matrix_det w),_root_.zpow_neg,zpow_natCast] at h
  simp only [SmallLevelOriginal.fourierFunction] at h
  rw [coe_smul_of_det_pos (by rw [matrix_det]; norm_num)] at h
  simpa only [num,denom,coordA,coordB,coordC,coordD,div_eq_mul_inv,
    mul_assoc,mul_comm,mul_left_comm] using h

theorem matrix_taylor_of_law {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε) :
    ∀ w : Fin 9, coordC w≠0 →
      ∀ j : ℝ, coordC w*j+coordD w≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          transform (fullCoefficients f (2*m)) j s-
            sign (ε*Complex.I^(2*m)) w*(((coordC w*j+coordD w)^2:ℝ):ℂ)^(s-(m:ℂ))*
              (∑ n∈Finset.range M, (Complex.I*((coordC w*(coordC w*j+coordD w):ℝ):ℂ))^n*
                Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
                transform (fullCoefficients f (2*m))
                  ((coordA w*j+coordB w)/(coordC w*j+coordD w)) (s+(n:ℂ)))=
            error M s := by
  obtain ⟨hχ,_hfricke⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<35) m ε hε hlaw
  intro w hC j hj
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := matrix_fourier_of_slash m f (ε*Complex.I^(2*m)) hχ w (original_matrix_actions hm hf ε hε hlaw w)
  have hh := matrix_even_rows (polynomial_bound hf.zero hg (2*m))
    (fullCoefficients_zero hf.zero (2*m)) m
    (coordA w) (coordB w) (coordC w) (coordD w) j hC
    (by rw [coordinate_det]; norm_num) hj (sign (ε*Complex.I^(2*m)) w) (by
      simpa only [coordinate_det,Complex.ofReal_one,one_pow,mul_one] using hF)
  simpa only [coordinate_det,div_one] using hh


#print axioms matrix_taylor_of_law
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourRowData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Matrix Complex SmallLevelAdditive
open QuantitativeArithmeticSmallLevelThirtyFiveChiFour (coordinate)

certificate_batch {
def matrixIndex : Fin 29 → Fin 9 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,1,2,2,3,3,4,4,4,4,4,4,5,5,6,6,7,8]

def source : Fin 29 → ℤ :=
  ![24,36,40,42,48,60,80,120,168,180,240,252,414,204,210,168,180,240,252,270,273,280,288,120,126,330,336,240,189]

def partner : Fin 29 → ℤ :=
  ![-210,-140,-126,-120,-105,-84,-63,-42,-30,-28,-21,-20,840,-6,0,-21,-20,40,42,60,84,0,24,-30,-28,80,84,-20,270]

def sourceIndex : Fin 29 → Fin 35 :=
  ![1,2,3,4,5,6,7,10,12,13,17,18,34,15,16,12,13,17,18,19,20,21,22,10,11,26,27,17,14]

def targetIndex : Fin 29 → Fin 35 :=
  ![16,21,23,24,25,27,28,29,30,31,32,33,0,34,0,32,33,3,4,6,8,0,1,30,31,7,8,33,19]

theorem nonaffine (i : Fin 29) : raw (matrixIndex i) 1 0≠0 := by
  fin_cases i <;> decide

theorem denominator_ne_zero (i : Fin 29) : rawDen (matrixIndex i) (source i)≠0 := by
  fin_cases i <;> decide

theorem row_closed (i : Fin 29) :
    420*rawNumer (matrixIndex i) (source i)=partner i*rawDen (matrixIndex i) (source i) := by
  fin_cases i <;> decide

theorem source_coordinate (i : Fin 29) : (coordinate (sourceIndex i)).val=source i := by
  fin_cases i <;> decide

theorem target_coordinate (i : Fin 29) : (coordinate (targetIndex i)).val=partner i%420 := by
  fin_cases i <;> decide

def gridVector (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 35) : ℂ :=
  grid k f 420 (coordinate i).val s

theorem grid_source (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 29) :
    gridVector k f s (sourceIndex i)=grid k f 420 (source i) s := by
  rw [gridVector,source_coordinate]

theorem grid_target (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 29) :
    gridVector k f s (targetIndex i)=grid k f 420 (partner i) s := by
  rw [gridVector,target_coordinate]
  exact grid_mod k f (by decide : 0<420) (partner i) s

#print axioms row_closed
#print axioms grid_target
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourGridRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Complex Matrix Set SmallLevelAdditive SmallLevelTaylor FinitenessOriginalFourier

certificate_batch {
/-- The exact normalized matrices act on the selected rational grid points. -/
theorem row_partner (i : Fin 29) :
    (coordA (matrixIndex i)*((source i:ℝ)/420)+coordB (matrixIndex i))/
      (coordC (matrixIndex i)*((source i:ℝ)/420)+coordD (matrixIndex i))=(partner i:ℝ)/420 := by
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  fin_cases i <;>
    norm_num [coordA,coordB,coordC,coordD,raw_coordinates,matrixIndex,source,partner,
      raw,scale,isFricke] <;> field_simp [hn] <;> nlinarith [ht]

theorem row_nonaffine (i : Fin 29) : coordC (matrixIndex i)≠0 := by
  rw [coordC,raw_coordinates]
  exact mul_ne_zero (scale_pos _).ne' (by exact_mod_cast nonaffine i)

theorem row_den_ne_zero (i : Fin 29) :
    coordC (matrixIndex i)*((source i:ℝ)/420)+coordD (matrixIndex i)≠0 := by
  rw [coordDen_raw]
  exact mul_ne_zero (scale_pos _).ne'
    (div_ne_zero (by exact_mod_cast denominator_ne_zero i) (by norm_num))

def rowCoefficient (m : ℕ) (χ : ℂ) (i : Fin 29) (n : ℕ) (s : ℂ) : ℂ :=
  sign χ (matrixIndex i)*((rate (matrixIndex i) (source i):ℂ))^(s-(m:ℂ))*
    (I*(derivative (matrixIndex i) (source i):ℂ))^n*
      Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

/-- All 29 nonaffine rows in the chi4 certificate are actual original-input
Taylor equations, with every positive shift retained on the selected grid. -/
theorem original_word_rows {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (i : Fin 29) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector (2*m) f s (sourceIndex i)-
          rowCoefficient m (ε*I^(2*m)) i 0 s*gridVector (2*m) f s (targetIndex i)=
        error M s+∑ n∈Finset.range M,
          rowCoefficient m (ε*I^(2*m)) i (n+1) s*
            gridVector (2*m) f (s+((n:ℂ)+1)) (targetIndex i) := by
  obtain ⟨B,error,hrow⟩ := matrix_taylor_of_law hm hf ε hε hlaw (matrixIndex i)
    (row_nonaffine i) ((source i:ℝ)/420) (row_den_ne_zero i)
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one] using (hrow (M+1)).1
  · intro s hs
    have he := (hrow (M+1)).2 s hs
    rw [row_partner,rate_eq,derivative_eq,Finset.sum_range_succ'] at he
    simp only [Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one,
      Nat.cast_add,Nat.cast_one,Complex.ofReal_ratCast] at he
    simp only [grid_source,grid_target,grid,original,rowCoefficient,Nat.cast_zero,add_zero,
      pow_zero,Ring.choose_zero_right,mul_one,Nat.cast_add,Nat.cast_one]
    rw [mul_add,Finset.mul_sum] at he
    simp only [mul_assoc,one_mul] at he ⊢
    linear_combination he

#print axioms row_partner
#print axioms original_word_rows
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourRamanujanRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessRamanujanSum
open FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (gridVector)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFour (coordinate)

certificate_batch {
def rowQ : Fin 2 → ℕ := ![4,5]
def rowT : Fin 2 → ℤ := ![15,21]
def rowL (i : Fin 2) : ℕ := Nat.lcm 35 ((rowQ i)^2)
def rowD : Fin 2 → ℤ := ![315,1008]
def rowPartner (i : Fin 2) : ℤ := -(rowD i/rowT i)
def entireSpecs : Fin 4 → ℕ := ![1,4,5,10]

theorem specs_valid (i : Fin 2) : 0<rowQ i ∧ rowQ i∣420 ∧ rowT i≠0 ∧
    (rowL i:ℤ)*rowD i=(420:ℤ)^2 ∧ rowT i∣rowD i := by fin_cases i <;> decide

theorem entireSpecs_valid (i : Fin 4) : 0<entireSpecs i ∧ entireSpecs i∣420 := by
  fin_cases i <;> decide

def plusRows (v : Fin 35 → ℂ) : Fin 2 → ℂ :=
  ![v 10+v 26,v 9+v 14+v 20+v 28]
def minusRows (v : Fin 35 → ℂ) : Fin 2 → ℂ :=
  ![v 8+v 23,v 2+v 10+v 15+v 22]
def entireRows (v : Fin 35 → ℂ) : Fin 4 → ℂ :=
  ![v 0,v 9+v 25,v 8+v 12+v 18+v 27,v 4+v 11+v 23+v 29]

theorem plusRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 2) :
    plusRows (gridVector k f s) i=gridSum k f 420 (rowQ i) (rowT i) s := by
  fin_cases i <;>
    norm_num [plusRows,gridVector,coordinate,gridSum,rowQ,rowT,residues,Finset.sum_filter,Finset.sum_range_succ]

theorem minusRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 2) :
    minusRows (gridVector k f s) i=gridSum k f 420 (rowQ i) (rowPartner i) s := by
  fin_cases i <;>
    norm_num [minusRows,gridVector,coordinate,gridSum,rowQ,rowPartner,rowD,rowT,
      residues,Finset.sum_filter,Finset.sum_range_succ]

theorem entireRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 4) :
    entireRows (gridVector k f s) i=gridSum k f 420 (entireSpecs i) 0 s := by
  fin_cases i <;>
    norm_num [entireRows,gridVector,coordinate,gridSum,entireSpecs,residues,Finset.sum_filter,Finset.sum_range_succ]

def rowCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 2) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (rowL i) ((rowT i:ℝ)/420) (root 35 f (rowQ i)*ε*I^k) n s

def rowError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 2) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f (rowQ i)) k)
    (rowL i) ((rowT i:ℝ)/420) (root 35 f (rowQ i)*ε*I^k) (M+1)) s

theorem original_taylor_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε) (i : Fin 2) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (rowError (2*m) f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        plusRows (gridVector (2*m) f s) i-
          rowCoefficient (2*m) f ε i 0 s*minusRows (gridVector (2*m) f s) i=
        rowError (2*m) f ε i M s+∑ n∈Finset.range M,
          rowCoefficient (2*m) f ε i (n+1) s*
            minusRows (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  obtain ⟨B,hB⟩ := QuantitativeArithmeticCoherentTaylor.closed_grid_taylor_rows_of_law
    (by decide : 0<35) (even_two_mul m) hf ε hlaw 420 (rowQ i) (by decide)
    (specs_valid i).1 (specs_valid i).2.1 (rowT i) (rowD i)
    (specs_valid i).2.2.1 (specs_valid i).2.2.2.1 (specs_valid i).2.2.2.2
  refine ⟨B,?_⟩
  intro M
  refine ⟨(hB M).1,?_⟩
  intro s hs
  simpa only [plusRows_grid,minusRows_grid,rowCoefficient,rowError,rowPartner,rowL,Nat.cast_ofNat] using (hB M).2 s hs

theorem original_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    (∀ i : Fin 4, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 35 k f (entireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 4, ∀ s : ℂ, B<s.re →
        ramanujanEntire 35 k f (entireSpecs i) s=entireRows (gridVector k f s) i := by
  have hh (i : Fin 4) := original_ramanujan_entire (by decide : 0<35) hk hf (entireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
    rw [entireRows_grid,hb i s (lt_of_le_of_lt hbi hs)]
    have hg := ramanujanAdditive_grid k f (by decide : 0<420)
      (entireSpecs_valid i).1 (entireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

#print axioms original_taylor_rows
#print axioms original_entire_rows
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan
end
end

/-! ## ThirtyFiveChiFourSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (sourceIndex targetIndex gridVector)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (plusRows minusRows entireRows)

inductive RowKind where
  | group : Fin 29 → RowKind
  | taylor : Fin 2 → RowKind
  | entire : Fin 4 → RowKind
  deriving DecidableEq

certificate_batch {
def rowKind : Fin 35 → RowKind :=
  ![.entire 0,.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.group 24,.group 25,.group 26,.group 27,.group 28,.entire 1,.taylor 0,.entire 2,.taylor 1,.entire 3]

def assemble (G : Fin 29 → ℂ) (T : Fin 2 → ℂ) (E : Fin 4 → ℂ) (i : Fin 35) : ℂ :=
  match rowKind i with
  | .group j => G j
  | .taylor j => T j
  | .entire j => E j

def groupCoefficient (m : ℕ) (ε : ℂ) (i : Fin 29) (n : ℕ) (s : ℂ) : ℂ :=
  QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows.rowCoefficient m (ε*I^(2*m)) i n s

def taylorCoefficient (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 2) (n : ℕ) (s : ℂ) : ℂ :=
  QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan.rowCoefficient (2*m) f ε i n s

def leadingRows (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 35 → ℂ) : Fin 35 → ℂ :=
  assemble (fun i => v (sourceIndex i)-groupCoefficient m ε i 0 s*v (targetIndex i))
    (fun i => plusRows v i-taylorCoefficient m f ε i 0 s*minusRows v i) (entireRows v)

def shiftRows (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 35 → ℂ) : Fin 35 → ℂ :=
  assemble (fun i => groupCoefficient m ε i (n+1) s*v (targetIndex i))
    (fun i => taylorCoefficient m f ε i (n+1) s*minusRows v i) 0

def leadingLinear (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : (Fin 35 → ℂ) →ₗ[ℂ] (Fin 35 → ℂ) where
  toFun := leadingRows m f ε s
  map_add' := by
    intro v w
    funext i
    fin_cases i <;> simp [leadingRows,assemble,rowKind,plusRows,minusRows,entireRows] <;> ring
  map_smul' := by
    intro c v
    funext i
    fin_cases i <;> simp [leadingRows,assemble,rowKind,plusRows,minusRows,entireRows,smul_eq_mul] <;> ring

def shiftLinear (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : (Fin 35 → ℂ) →ₗ[ℂ] (Fin 35 → ℂ) where
  toFun := shiftRows m f ε n s
  map_add' := by
    intro v w
    funext i
    fin_cases i <;> simp [shiftRows,assemble,rowKind,minusRows] <;> ring
  map_smul' := by
    intro c v
    funext i
    fin_cases i <;> simp [shiftRows,assemble,rowKind,minusRows,smul_eq_mul] <;> ring

def leadingMatrix (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : Matrix (Fin 35) (Fin 35) ℂ :=
  (leadingLinear m f ε s).toMatrix'
def shiftMatrix (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 35) (Fin 35) ℂ :=
  (shiftLinear m f ε n s).toMatrix'

theorem leadingMatrix_mulVec (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 35 → ℂ) :
    leadingMatrix m f ε s *ᵥ v=leadingRows m f ε s v := LinearMap.toMatrix'_mulVec _ _
theorem shiftMatrix_mulVec (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 35 → ℂ) :
    shiftMatrix m f ε n s *ᵥ v=shiftRows m f ε n s v := LinearMap.toMatrix'_mulVec _ _

#print axioms leadingMatrix_mulVec
#print axioms shiftMatrix_mulVec
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFourEntries -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (rate matrixIndex source rate_eq row_den_ne_zero)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (specs_valid)

certificate_batch {
theorem groupCoefficient_analytic (m : ℕ) (ε : ℂ) (i : Fin 29) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (groupCoefficient m ε i n) s := by
  have hr : (rate (matrixIndex i) (source i):ℝ)≠0 := by
    rw [← rate_eq]
    exact pow_ne_zero _ (row_den_ne_zero i)
  have hc : (rate (matrixIndex i) (source i):ℂ)≠0 := by exact_mod_cast hr
  have hp : AnalyticAt ℂ (fun z : ℂ => (rate (matrixIndex i) (source i):ℂ)^(z-(m:ℂ))) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hc]
    fun_prop
  exact ((analyticAt_const.mul hp).mul analyticAt_const).mul
    (SmallLevelTaylor.binomial_shift_analytic (2*m) n s)

theorem taylorCoefficient_analytic (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 2) (n : ℕ) (s : ℂ) :
  AnalyticAt ℂ (taylorCoefficient m f ε i n) s := by
  apply SmallLevelTaylor.taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<35) (pow_pos (specs_valid i).1 2)
  · exact div_ne_zero (by exact_mod_cast (specs_valid i).2.2.1) (by norm_num)

theorem leadingMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i j : Fin 35) :
    leadingMatrix m f ε s i j=leadingRows m f ε s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _
theorem shiftMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (i j : Fin 35) :
    shiftMatrix m f ε n s i j=shiftRows m f ε n s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

theorem leadingMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i j : Fin 35) :
    AnalyticAt ℂ (fun s => leadingMatrix m f ε s i j) x := by
  simp only [leadingMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((groupCoefficient_analytic m ε a 0 x).mul analyticAt_const)
  | taylor a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((taylorCoefficient_analytic m f ε a 0 x).mul analyticAt_const)
  | entire a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const

theorem shiftMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ) (i j : Fin 35) :
    AnalyticAt ℂ (fun s => shiftMatrix m f ε n s i j) x := by
  simp only [shiftMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [shiftRows,assemble,hi]
    exact (groupCoefficient_analytic m ε a (n+1) x).mul analyticAt_const
  | taylor a =>
    simp only [shiftRows,assemble,hi]
    exact (taylorCoefficient_analytic m f ε a (n+1) x).mul analyticAt_const
  | entire a =>
    simp only [shiftRows,assemble,hi,Pi.zero_apply]
    exact analyticAt_const

#print axioms leadingMatrix_analytic
#print axioms shiftMatrix_analytic
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFourOriginalSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix Set SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (gridVector)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (rowError entireSpecs)

certificate_batch {
/-- The full 35-coordinate system consists of actual original-input rows.
Every positive Taylor shift stays in the same 35 coordinates. -/
theorem original_matrix_system {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε) :
    ∃ B : ℝ, ∃ error : ℕ → ℂ → Fin 35 → ℂ,
      (∀ i : Fin 35, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 35, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => error M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        leadingMatrix m f ε s *ᵥ gridVector (2*m) f s=
          error M s+∑ n∈Finset.range M,
            shiftMatrix m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  have hg (i : Fin 29) := QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows.original_word_rows
    hm hf ε hε hlaw i
  choose bG errG hG using hg
  have ht (i : Fin 2) := QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan.original_taylor_rows
    hf ε hlaw i
  choose bT hT using ht
  obtain ⟨hRE,BR,hR⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan.original_entire_rows
    (by omega : 0<2*m) hf
  obtain ⟨BF,hF⟩ := original_common_halfplane hf
  let BG : ℝ := Finset.univ.sup' Finset.univ_nonempty bG
  let BT : ℝ := Finset.univ.sup' Finset.univ_nonempty bT
  let B : ℝ := max BG (max BT (max BR BF))
  have hBG (i : Fin 29) : bG i≤B := (Finset.le_sup' bG (Finset.mem_univ i)).trans (le_max_left _ _)
  have hBT (i : Fin 2) : bT i≤B := (Finset.le_sup' bT (Finset.mem_univ i)).trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hBR : BR≤B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBF : BF≤B := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let error : ℕ → ℂ → Fin 35 → ℂ := fun M s =>
    assemble (fun i => errG i M s) (fun i => rowError (2*m) f ε i M s)
      (fun i => ramanujanEntire 35 (2*m) f (entireSpecs i) s)
  refine ⟨B,error,?_,?_,?_⟩
  · intro i s hs
    exact (hF (((QuantitativeArithmeticSmallLevelThirtyFiveChiFour.coordinate i).val:ℝ)/420)
      s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have hg' (j : Fin 29) : AnalyticAt ℂ (errG j M) s := by
      apply (hG j M).1 s
      change bG j-((M:ℝ)+1)<s.re
      linarith [hBG j]
    have ht' (j : Fin 2) : AnalyticAt ℂ (rowError (2*m) f ε j M) s := by
      apply (hT j M).1 s
      change bT j-((M:ℝ)+1)<s.re
      linarith [hBT j]
    cases hi : rowKind i with
    | group j => simpa only [error,assemble,hi] using hg' j
    | taylor j => simpa only [error,assemble,hi] using ht' j
    | entire j => simpa only [error,assemble,hi] using hRE j s
  · intro M s hs
    rw [leadingMatrix_mulVec]
    simp_rw [shiftMatrix_mulVec]
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    cases hi : rowKind i with
    | group j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,groupCoefficient] using
        (hG j M).2 s (lt_of_le_of_lt (hBG j) hs)
    | taylor j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,taylorCoefficient] using
        (hT j M).2 s (lt_of_le_of_lt (hBT j) hs)
    | entire j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,Pi.zero_apply,
        Finset.sum_const_zero,add_zero] using (hR j s (lt_of_le_of_lt hBR hs)).symm

#print axioms original_matrix_system
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFourLaurent -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords (fourPrimeMonomial rational_four_prime_power primeParameter)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (rate raw rawDen matrixIndex source sign isFricke)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (rowQ rowT rowL)
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan (phaseRoot badFive root_five)

certificate_batch {
def groupPowers : Fin 29 → ℤ×ℤ×ℤ×ℤ :=
  ![(2,0,-1,-1),(0,2,-1,-1),(2,-2,1,-1),(-2,0,-1,1),(4,0,-1,-1),(0,0,1,-1),(4,-2,1,-1),(2,0,1,-1),(2,0,-1,1),(0,2,1,-1),(4,0,1,-1),(0,2,-1,1),(-2,0,-1,-1),(2,0,0,0),(-2,0,0,0),(4,0,0,0),(0,2,0,0),(0,2,0,0),(2,0,0,0),(-2,0,0,0),(-4,0,0,0),(0,-2,0,0),(0,0,0,0),(2,0,0,0),(-2,2,0,0),(-2,2,0,0),(0,0,0,0),(0,2,0,0),(-2,0,-1,1)]

theorem group_rate_certificate (i : Fin 29) :
    rate (matrixIndex i) (source i)=(2:ℚ)^(groupPowers i).1*(3:ℚ)^(groupPowers i).2.1*
      (5:ℚ)^(groupPowers i).2.2.1*(7:ℚ)^(groupPowers i).2.2.2 := by
  fin_cases i <;> norm_num [rate,rawDen,raw,matrixIndex,source,groupPowers,Matrix.det_fin_two]

def symbolicGroup (χ X Y Z W : ℂ) (i : Fin 29) : ℂ :=
  sign χ (matrixIndex i)*fourPrimeMonomial (groupPowers i) X Y Z W

theorem groupCoefficient_laurent (m : ℕ) (ε s : ℂ) (i : Fin 29) :
    groupCoefficient m ε i 0 s=symbolicGroup (phaseRoot m ε)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) i := by
  simp only [groupCoefficient,QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows.rowCoefficient,
    Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one]
  rw [rational_four_prime_power _ _ (group_rate_certificate i)]
  rfl

theorem root_four (f : ℕ → ℂ) : root 35 f 4=1 := by
  have hp : (4:ℕ).primeFactors={2} := by
    rw [show (4:ℕ)=2*2 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  norm_num [root,hp,FinitenessNormalizedTwistLocal.sign]

def taylorPowers : Fin 2 → ℤ×ℤ×ℤ×ℤ := ![(0,0,1,-1),(-4,0,0,1)]
def taylorSign (χ u : ℂ) (i : Fin 2) : ℂ := ![χ,-χ*u] i

def symbolicTaylor (χ u X Y Z W : ℂ) (i : Fin 2) : ℂ :=
  taylorSign χ u i*fourPrimeMonomial (taylorPowers i) X Y Z W

theorem taylor_rate_certificate (i : Fin 2) :
    (rowL i:ℚ)*((rowT i:ℚ)/420)^2=(2:ℚ)^(taylorPowers i).1*(3:ℚ)^(taylorPowers i).2.1*
      (5:ℚ)^(taylorPowers i).2.2.1*(7:ℚ)^(taylorPowers i).2.2.2 := by
  fin_cases i <;> norm_num [rowL,rowQ,rowT,taylorPowers]

theorem taylorCoefficient_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : Fin 2) :
    taylorCoefficient m f ε i 0 s=symbolicTaylor (phaseRoot m ε) (badFive f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) i := by
  have hsign : root 35 f (rowQ i)*ε*I^(2*m)=taylorSign (phaseRoot m ε) (badFive f) i := by
    fin_cases i
    · change root 35 f 4*ε*I^(2*m)=phaseRoot m ε
      rw [root_four]
      simp [phaseRoot]
    · change root 35 f 5*ε*I^(2*m)= -(phaseRoot m ε)*badFive f
      rw [root_five]
      unfold phaseRoot
      ring
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  have hc : (((rowL i:ℝ)*((rowT i:ℝ)/420)^2:ℝ):ℂ)=
      (((rowL i:ℚ)*((rowT i:ℚ)/420)^2:ℚ):ℂ) := by push_cast; rfl
  simp only [taylorCoefficient,QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan.rowCoefficient,
    taylorRowScalar,pow_zero,Ring.choose_zero_right,mul_one,hex,hc,hsign]
  rw [rational_four_prime_power _ _ (taylor_rate_certificate i)]
  rfl

#print axioms groupCoefficient_laurent
#print axioms taylorCoefficient_laurent
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFour -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour

certificate_batch {
/-- The 35 selected original-row formulas, with global Fricke sign E and
bad-five sign u. The bad-seven sign and good-prime eigenvalues do not occur.
These are explicit algebraic rows, not assumed original-input consequences. -/
def selectedRows (E u X Y Z W : ℂ) (rho : Fin 420 → ℂ) : Fin 35 → ℂ :=
  ![-- ['ginf', 0, 1, -35, 0, 0]
    ((1))*rho 0,
    -- ['g', 0, 1, -35, 0, -1, 24]
    ((1))*rho 24 + (((-1)*E*X^2)/(Z*W))*rho 210,
    -- ['g', 0, 1, -35, 0, -1, 36]
    ((1))*rho 36 + (((-1)*E*Y^2)/(Z*W))*rho 280,
    -- ['g', 0, 1, -35, 0, -1, 40]
    ((1))*rho 40 + (((-1)*E*X^2*Z)/(Y^2*W))*rho 294,
    -- ['g', 0, 1, -35, 0, -1, 42]
    ((1))*rho 42 + (((-1)*E*W)/(X^2*Z))*rho 300,
    -- ['g', 0, 1, -35, 0, -1, 48]
    ((1))*rho 48 + (((-1)*E*X^4)/(Z*W))*rho 315,
    -- ['g', 0, 1, -35, 0, -1, 60]
    ((1))*rho 60 + (((-1)*E*Z)/(W))*rho 336,
    -- ['g', 0, 1, -35, 0, -1, 80]
    ((1))*rho 80 + (((-1)*E*X^4*Z)/(Y^2*W))*rho 357,
    -- ['g', 0, 1, -35, 0, -1, 120]
    ((1))*rho 120 + (((-1)*E*X^2*Z)/(W))*rho 378,
    -- ['g', 0, 1, -35, 0, -1, 168]
    ((1))*rho 168 + (((-1)*E*X^2*W)/(Z))*rho 390,
    -- ['g', 0, 1, -35, 0, -1, 180]
    ((1))*rho 180 + (((-1)*E*Y^2*Z)/(W))*rho 392,
    -- ['g', 0, 1, -35, 0, -1, 240]
    ((1))*rho 240 + (((-1)*E*X^4*Z)/(W))*rho 399,
    -- ['g', 0, 1, -35, 0, -1, 252]
    ((1))*rho 252 + (((-1)*E*Y^2*W)/(Z))*rho 400,
    -- ['g', 0, 1, -35, 35, -1, 414]
    (((-1)*E)/(X^2*Z*W))*rho 0 + ((1))*rho 414,
    -- ['g', 2, -1, -105, 53, 1, 204]
    ((1))*rho 204 + ((-1)*X^2)*rho 414,
    -- ['g', 2, -1, -105, 53, 1, 210]
    (((-1))/(X^2))*rho 0 + ((1))*rho 210,
    -- ['g', 2, -1, -35, 18, 1, 168]
    ((1))*rho 168 + ((-1)*X^4)*rho 399,
    -- ['g', 2, -1, -35, 18, 1, 180]
    ((1))*rho 180 + ((-1)*Y^2)*rho 400,
    -- ['g', 3, -2, 35, -23, 1, 240]
    ((-1)*Y^2)*rho 40 + ((1))*rho 240,
    -- ['g', 3, -2, 35, -23, 1, 252]
    ((-1)*X^2)*rho 42 + ((1))*rho 252,
    -- ['g', 3, -2, 35, -23, 1, 270]
    (((-1))/(X^2))*rho 60 + ((1))*rho 270,
    -- ['g', 3, -2, 35, -23, 1, 273]
    (((-1))/(X^4))*rho 84 + ((1))*rho 273,
    -- ['g', 3, -2, 35, -23, 1, 280]
    (((-1))/(Y^2))*rho 0 + ((1))*rho 280,
    -- ['g', 3, -2, 35, -23, 1, 288]
    ((-1))*rho 24 + ((1))*rho 288,
    -- ['g', 3, -1, -35, 12, 1, 120]
    ((1))*rho 120 + ((-1)*X^2)*rho 390,
    -- ['g', 3, -1, -35, 12, 1, 126]
    ((1))*rho 126 + (((-1)*Y^2)/(X^2))*rho 392,
    -- ['g', 6, -5, 35, -29, 1, 330]
    (((-1)*Y^2)/(X^2))*rho 80 + ((1))*rho 330,
    -- ['g', 6, -5, 35, -29, 1, 336]
    ((-1))*rho 84 + ((1))*rho 336,
    -- ['g', 12, -7, -245, 143, 1, 240]
    ((1))*rho 240 + ((-1)*Y^2)*rho 400,
    -- ['g', 35, -18, 70, -35, -1, 189]
    ((1))*rho 189 + (((-1)*E*W)/(X^2*Z))*rho 270,
    -- ['R', 4]
    ((1))*rho 105 + ((1))*rho 315,
    -- ['F', 4, 15]
    (((-1)*E*Z)/(W))*rho 84 + ((1))*rho 120 + (((-1)*E*Z)/(W))*rho 294 + ((1))*rho 330,
    -- ['R', 5]
    ((1))*rho 84 + ((1))*rho 168 + ((1))*rho 252 + ((1))*rho 336,
    -- ['F', 5, 21]
    ((E*u*W)/(X^4))*rho 36 + ((1))*rho 105 + ((E*u*W)/(X^4))*rho 120 + ((1))*rho 189 + ((E*u*W)/(X^4))*rho 204 + ((1))*rho 273 + ((E*u*W)/(X^4))*rho 288 + ((1))*rho 357,
    -- ['R', 10]
    ((1))*rho 42 + ((1))*rho 126 + ((1))*rho 294 + ((1))*rho 378]

/-- Both Fricke signs and both ramified-five signs: the exact selected
row system annihilates the chi4 target even at singular spectral parameters.
Only geometric prime powers are required to be nonzero. -/
theorem target (E u X Y Z W : ℂ) (hE : E= -1 ∨ E=1) (hu : u= -1 ∨ u=1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (rho : Fin 420 → ℂ) (hrows : selectedRows E u X Y Z W rho=0) :
    rho 105-rho 315=0 := by
  rcases hE with rfl|rfl <;> rcases hu with rfl|rfl
  · apply target_case0 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows0, neg_mul, one_mul, neg_neg] using hrows
  · apply target_case2 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows2, neg_mul, one_mul, neg_neg] using hrows
  · apply target_case4 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows4, neg_mul, one_mul, neg_neg] using hrows
  · apply target_case6 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows6, neg_mul, one_mul, neg_neg] using hrows

#print axioms target

}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourMatrix -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Matrix

certificate_batch {
/-- All coordinates appearing in the selected rows vanish in their kernel. -/
theorem selected_kernel (E u X Y Z W : ℂ) (hE : E= -1 ∨ E=1) (hu : u= -1 ∨ u=1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (rho : Fin 420 → ℂ) (hrows : selectedRows E u X Y Z W rho=0) :
    ∀ i : Fin 35, rho (coordinate i)=0 := by
  rcases hE with rfl|rfl <;> rcases hu with rfl|rfl
  · apply selected_kernel_case0 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows0, neg_mul, one_mul, neg_neg] using hrows
  · apply selected_kernel_case2 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows2, neg_mul, one_mul, neg_neg] using hrows
  · apply selected_kernel_case4 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows4, neg_mul, one_mul, neg_neg] using hrows
  · apply selected_kernel_case6 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows6, neg_mul, one_mul, neg_neg] using hrows

/-- Zero extension from the selected 35 coordinates to the 420-grid. -/
def embed (v : Fin 35 → ℂ) (j : Fin 420) : ℂ :=
  match j.val with
  | 0 => v 0
  | 24 => v 1
  | 36 => v 2
  | 40 => v 3
  | 42 => v 4
  | 48 => v 5
  | 60 => v 6
  | 80 => v 7
  | 84 => v 8
  | 105 => v 9
  | 120 => v 10
  | 126 => v 11
  | 168 => v 12
  | 180 => v 13
  | 189 => v 14
  | 204 => v 15
  | 210 => v 16
  | 240 => v 17
  | 252 => v 18
  | 270 => v 19
  | 273 => v 20
  | 280 => v 21
  | 288 => v 22
  | 294 => v 23
  | 300 => v 24
  | 315 => v 25
  | 330 => v 26
  | 336 => v 27
  | 357 => v 28
  | 378 => v 29
  | 390 => v 30
  | 392 => v 31
  | 399 => v 32
  | 400 => v 33
  | 414 => v 34
  | _ => 0

theorem embed_coordinate (v : Fin 35 → ℂ) (i : Fin 35) : embed v (coordinate i)=v i := by
  fin_cases i <;> rfl

def reducedRows (E u X Y Z W : ℂ) (v : Fin 35 → ℂ) : Fin 35 → ℂ :=
  selectedRows E u X Y Z W (embed v)

def selectedLinear (E u X Y Z W : ℂ) : (Fin 420 → ℂ) →ₗ[ℂ] (Fin 35 → ℂ) where
  toFun := selectedRows E u X Y Z W
  map_add' := by
    intro v w
    funext i
    fin_cases i <;> dsimp [selectedRows] <;> ring1
  map_smul' := by
    intro c v
    funext i
    fin_cases i <;> dsimp [selectedRows] <;> ring1

def embedLinear : (Fin 35 → ℂ) →ₗ[ℂ] (Fin 420 → ℂ) where
  toFun := embed
  map_add' := by
    intro v w
    funext j
    dsimp only [embed, Pi.add_apply]
    split <;> simp
  map_smul' := by
    intro c v
    funext j
    dsimp only [embed, Pi.smul_apply]
    split <;> simp

def reducedLinear (E u X Y Z W : ℂ) : (Fin 35 → ℂ) →ₗ[ℂ] (Fin 35 → ℂ) :=
  (selectedLinear E u X Y Z W).comp embedLinear

def reducedMatrix (E u X Y Z W : ℂ) : Matrix (Fin 35) (Fin 35) ℂ :=
  (reducedLinear E u X Y Z W).toMatrix'

theorem reducedMatrix_mulVec (E u X Y Z W : ℂ) (v : Fin 35 → ℂ) :
    reducedMatrix E u X Y Z W *ᵥ v=reducedRows E u X Y Z W v :=
  LinearMap.toMatrix'_mulVec _ _

/-- A 35-coordinate subsystem is nonsingular at every nonzero geometric
specialization, for both signs. There is no residual spectral locus and no
Hecke eigenvalue hypothesis. The actual analytic row realization is separate. -/
theorem reducedMatrix_det_ne_zero (E u X Y Z W : ℂ)
    (hE : E= -1 ∨ E=1) (hu : u= -1 ∨ u=1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) :
    (reducedMatrix E u X Y Z W).det≠0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : reducedMatrix E u X Y Z W *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [reducedMatrix_mulVec] at hz
  have he := selected_kernel E u X Y Z W hE hu hX hY hZ hW (embed (v-w)) hz
  apply sub_eq_zero.mp
  funext i
  simpa only [embed_coordinate, Pi.zero_apply] using he i

#print axioms selected_kernel
#print axioms embed_coordinate
#print axioms reducedMatrix_det_ne_zero
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourComparison -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords (fourPrimeMonomial primeParameter)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (sourceIndex targetIndex matrixIndex sign isFricke)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (plusRows minusRows entireRows)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFour (selectedRows embed reducedMatrix)
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan (phaseRoot phaseRoot_sign badFive badFive_sign)

certificate_batch {
def symbolicRows (χ u X Y Z W : ℂ) (v : Fin 35 → ℂ) : Fin 35 → ℂ :=
  assemble (fun i => v (sourceIndex i)-symbolicGroup χ X Y Z W i*v (targetIndex i))
    (fun i => plusRows v i-symbolicTaylor χ u X Y Z W i*minusRows v i) (entireRows v)

/-- Exact rational comparison with the already checked algebraic certificate. -/
theorem symbolic_rows (χ u X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 35 → ℂ) :
    symbolicRows χ u X Y Z W v=selectedRows χ u X Y Z W (embed v) := by
  funext i
  fin_cases i <;>
    norm_num [symbolicRows,assemble,rowKind,symbolicGroup,symbolicTaylor,taylorSign,
      groupPowers,taylorPowers,fourPrimeMonomial,sign,isFricke,matrixIndex,
      sourceIndex,targetIndex,plusRows,minusRows,entireRows,selectedRows,embed] <;>
    field_simp [hX,hY,hZ,hW] <;> ring

theorem actual_leading_rows (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 35 → ℂ) :
    leadingRows m f ε s v=selectedRows (phaseRoot m ε) (badFive f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) (embed v) := by
  have he : leadingRows m f ε s v=symbolicRows (phaseRoot m ε) (badFive f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) v := by
    funext i
    cases hi : rowKind i <;> simp only [leadingRows,symbolicRows,assemble,hi,
      groupCoefficient_laurent,taylorCoefficient_laurent]
  rw [he]
  apply symbolic_rows <;> exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem actual_leading_matrix (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) :
    leadingMatrix m f ε s=reducedMatrix (phaseRoot m ε) (badFive f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [leadingMatrix_mulVec,QuantitativeArithmeticSmallLevelThirtyFiveChiFour.reducedMatrix_mulVec]
  exact actual_leading_rows m f ε s v

/-- No spectral parameters remain in this determinant: it never vanishes. -/
theorem original_leading_nonsingular {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (s : ℂ) : (leadingMatrix m f ε s).det≠0 := by
  rw [actual_leading_matrix]
  apply QuantitativeArithmeticSmallLevelThirtyFiveChiFour.reducedMatrix_det_ne_zero
    _ _ _ _ _ _ (phaseRoot_sign m hε).symm (badFive_sign hf.toEulerData).symm <;>
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

#print axioms symbolic_rows
#print axioms actual_leading_matrix
#print axioms original_leading_nonsingular
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveTwelveMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

certificate_batch {
theorem sqrt_twelve_conductor : Real.sqrt 5040=12*Real.sqrt 35 := by
  rw [show (5040:ℝ)=144*35 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem fricke_branch (a : Fin 4) :
    fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (generator a)*translation (center a)=
    translation (center a)*fricke 5040 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases a <;> apply Units.ext <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [fricke,generator,center,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_twelve_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

#print axioms fricke_branch
}

end QuantitativeArithmeticSmallLevelThirtyFiveTwelve
end
end

/-! ## ThirtyFiveTwelveEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open SmallLevelNormalized SmallLevelOriginal QuantitativeArithmeticTranslatedFricke
  Complex Filter Set MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction
  Matrix UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

certificate_batch {
def centeredMellin (m : ℕ) (f : ℕ → ℂ) (j : Fin 4) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 5040
    (SmallLevelAdditive.coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center j)))

/-- Four individual Fricke equations with a common original sign. -/
theorem original_centers_with_fricke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f (χ/Complex.I^(2*m)) ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=χ • fourierFunction (2*m) f ∧
      ∀ j : Fin 4,
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center j))
        ∣[((2*m:ℕ):ℤ)] fricke 5040 (by decide)=
      χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center j)) := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law (by decide : 0<35) hf
  let χ : ℂ := ε*Complex.I^(2*m)
  obtain ⟨hχ,hF⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law (by decide : 0<35) m ε hε hlaw
  have hlawχ : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f (χ/Complex.I^(2*m)) := by
    simpa only [χ,mul_div_cancel_right₀ _ (pow_ne_zero _ Complex.I_ne_zero)] using hlaw
  refine ⟨χ,hχ,hlawχ,hF,?_⟩
  intro j
  exact translated_slash 35 5040 (2*m) (by decide) (by decide) _ χ _
    (SpecialLinearGroup.mapGL ℝ (generator j)) (by simp)
    hF (original_generators hm hf j) (fricke_branch j)

/-- Actual entire finite-order denominator-twelve Mellin transforms. -/
theorem original_centers_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f (χ/Complex.I^(2*m)) ∧
      ∀ j : Fin 4,
      Differentiable ℂ (centeredMellin m f j) ∧
      FinitenessFiniteOrder.Bound (centeredMellin m f j) ∧
      ∀ s : ℂ, centeredMellin m f j s=
        (χ/(Complex.I^(2*m)))*centeredMellin m f j ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hlaw,_hW,hF⟩ := original_centers_with_fricke hm hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨χ,hχ,hlaw,fun j => ?_⟩
  exact translated_mellin_entire 5040 (2*m) (by decide) (by omega) _
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)) (center j) χ hχ
    (hF j)

#print axioms original_centers_with_fricke
#print axioms original_centers_entire
}

end QuantitativeArithmeticSmallLevelThirtyFiveTwelve
end
end

/-! ## ThirtyFiveChiFourNumerator -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open QuantitativeArithmeticSmallLevelThirtyFiveTwelve QuantitativeArithmeticMellinScale
  SmallLevelAdditive SmallLevelTaylor Complex Filter Set MeasureTheory
  FinitenessFourierConstruction FinitenessOriginalFourier

certificate_batch {
/-- The entire numerator before division by the Hecke polynomial. -/
def translateMellin (m : ℕ) (f : ℕ → ℂ) (r : ℝ) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1 (coefficients (fullCoefficients f (2*m)) r))

def numerator (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  translateMellin m f (1/12) s-translateMellin m f (-1/12) s+
    translateMellin m f (5/12) s-translateMellin m f (-5/12) s

def denominator (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  1+(((3:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 3*(3:ℂ)^(-s)+(3:ℂ)^k*(9:ℂ)^(-s)

theorem original_numerator_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    Differentiable ℂ (numerator m f) := by
  obtain ⟨χ,_,_,h⟩ := original_centers_entire hm hf
  have hj (j : Fin 4) : Differentiable ℂ (translateMellin m f (center j)) :=
    entire_at_one (by decide : 0<5040) _ (h j).1
  exact ((hj 0).sub (hj 1) |>.add (hj 2)).sub (hj 3)

theorem denominator_entire (k : ℕ) (f : ℕ → ℂ) : Differentiable ℂ (denominator k f) := by
  unfold denominator
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (9:ℂ)≠0)]
  fun_prop

/-- An exact original-input Hecke identity, identifying the quadratic-twist
numerator on a half-plane. No division or continuation premise is used. -/
theorem original_hecke_identity (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      numerator m f s=denominator (2*m) f s*
        (original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_additive_hecke hf (by decide : Nat.Prime 3) (by decide)
  refine ⟨max B H,?_⟩
  intro s hs
  have hsB := lt_of_le_of_lt (le_max_left B H) hs
  have hsH := lt_of_le_of_lt (le_max_right B H) hs
  have hper (r : ℝ) : original (2*m) f (r+1) s=original (2*m) f r s := by
    rw [← (hB (r+1) s hsB).2,← (hB r s hsB).2]
    congr 1
    funext y
    have hh := periodic (fullCoefficients f (2*m)) ((r:ℂ)+(y:ℂ)*I)
    have he : ((r+1:ℝ):ℂ)+(y:ℂ)*I=((r:ℂ)+(y:ℂ)*I)+1 := by
      push_cast
      ring1
    rw [he]
    exact hh
  have hp := hH (1/12) s hsH
  have hn := hH (-(1/12)) s hsH
  norm_num [Finset.sum_range_succ] at hp hn
  have h1 := hper (-(1/4))
  have h2 := hper (-(5/12))
  norm_num at h1 h2
  rw [h1] at hp
  rw [h2] at hn
  have h3 := hper (-(3/4))
  norm_num at h3
  rw [← h3] at hn
  have he (r : ℝ) : translateMellin m f r s=original (2*m) f r s := by
    unfold translateMellin
    have heq : FinitenessAllLevelAxisDecay.axis 1 (coefficients (fullCoefficients f (2*m)) r)=
        (fun y : ℝ => fourier (fullCoefficients f (2*m)) ((r:ℂ)+(y:ℂ)*I)) :=
      funext (axis_one_translate (fullCoefficients f (2*m)) r)
    rw [heq,(hB r s hsB).2]
  have hnum : numerator m f s=original (2*m) f (1/12) s-original (2*m) f (-1/12) s+
      original (2*m) f (5/12) s-original (2*m) f (-5/12) s := by
    simp only [numerator,he]
  rw [hnum]
  unfold denominator
  push_cast
  simp only [neg_div] at hp hn ⊢
  linear_combination hp-hn

#print axioms original_numerator_entire
#print axioms denominator_entire
#print axioms original_hecke_identity
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourContinuation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex Filter Set SmallLevelAdditive
open scoped Topology

certificate_batch {
/-- Three fixed evaluations exclude an identically zero denominator for
every complex Hecke eigenvalue, including zero. -/
theorem denominator_nonzero (k : ℕ) (f : ℕ → ℂ) : ∃ s : ℂ, denominator k f s≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  norm_num [denominator,Complex.cpow_neg,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0-(3/4:ℂ)*h1+(27/16:ℂ)*h2
  norm_num at hbad

/-- The actual odd additive combination modulo4 has a global meromorphic
continuation from the original hypotheses. Its only possible poles are
zeros of the explicit Hecke-3 denominator. Pole removal is still separate. -/
theorem original_continuation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ → ℂ), (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator (2*m) f s)) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_hecke_identity m hf
  obtain ⟨G,hG,hagree,hpole,hgerm⟩ := QuantitativeArithmeticEntireQuotient.continuation
    (numerator m f) (denominator (2*m) f)
    (fun s => original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) (max B H)
    (fun z => (original_numerator_entire m hm hf).analyticAt z)
    (fun z => (denominator_entire (2*m) f).analyticAt z)
    (denominator_nonzero (2*m) f)
    (fun z hz => (hB (1/4) z (lt_of_le_of_lt (le_max_left _ _) hz)).1.sub
      (hB (-(1/4)) z (lt_of_le_of_lt (le_max_left _ _) hz)).1)
    (fun z hz => hH z (lt_of_le_of_lt (le_max_right _ _) hz))
  exact ⟨max B H,G,hG,hagree,hpole,hgerm⟩

#print axioms denominator_nonzero
#print axioms original_continuation
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourGridEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (gridVector)

certificate_batch {
/-- The actual selected 35 additive twists all have entire continuations. -/
theorem original_entire_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε) :
    ∃ B : ℝ, ∃ G : ℂ → Fin 35 → ℂ,
      (∀ i, Differentiable ℂ (fun z => G z i)) ∧
      ∀ z, B<z.re → G z=gridVector (2*m) f z := by
  obtain ⟨B,H,hF,hH,hrow⟩ := original_matrix_system hm hf ε hε hlaw
  obtain ⟨G,hG,hGF⟩ := QuantitativeArithmeticClosedEntire.closed_system_entire B
    (gridVector (2*m) f) (leadingMatrix m f ε) (shiftMatrix m f ε) H
    hF (leadingMatrix_analytic m f ε) (original_leading_nonsingular hf ε hε)
    (shiftMatrix_analytic m f ε) hH hrow
  exact ⟨B,G,hG,hGF⟩

#print axioms original_entire_grid
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFourReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex SmallLevelAdditive QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open FinitenessOriginalFourier
certificate_batch {
def scaleThree (k : ℕ) (s : ℂ) : ℂ := (3:ℂ)^((k:ℂ)-2*s)
def reflectionMultiplier (k : ℕ) (ε s : ℂ) : ℂ := ε*(Real.sqrt 560:ℂ)^((k:ℂ)-2*s)

theorem scaleThree_ne_zero (k : ℕ) (s : ℂ) : scaleThree k s≠0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem scaleThree_eq (k : ℕ) (s : ℂ) : scaleThree k s=(3:ℂ)^k*(9:ℂ)^(-s) := by
  have h4 : (9:ℂ)^(-s)=(3:ℂ)^(-2*s) := by
    have h := Complex.natCast_cpow_natCast_mul 3 2 (-s)
    norm_num only [Nat.cast_ofNat] at h
    rw [← h]
    congr 1
    ring
  rw [h4,← Complex.cpow_natCast,← Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0)]
  unfold scaleThree
  congr 1
  ring

theorem scaleThree_product (k : ℕ) (s : ℂ) : scaleThree k s*scaleThree k ((k:ℂ)-s)=1 := by
  unfold scaleThree
  rw [← Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0)]
  rw [show (k:ℂ)-2*s+((k:ℂ)-2*((k:ℂ)-s))=0 by ring,Complex.cpow_zero]

theorem center_conductor_factor (k : ℕ) (s : ℂ) :
    (Real.sqrt 5040:ℂ)^((k:ℂ)-2*s)=scaleThree k s*(Real.sqrt 560:ℂ)^((k:ℂ)-2*s) := by
  have hs : Real.sqrt 5040=3*Real.sqrt 560 := by
    rw [show (5040:ℝ)=9*560 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs,Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤3) (Real.sqrt_nonneg _) _

theorem reflectionMultiplier_entire (k : ℕ) (ε : ℂ) : Differentiable ℂ (reflectionMultiplier k ε) := by
  have hn : (Real.sqrt 560:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

theorem reflectionMultiplier_ne_zero (k : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier k ε s≠0 := by
  apply mul_ne_zero hε
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'))

theorem reflectionMultiplier_even (m : ℕ) (ε s : ℂ) :
    reflectionMultiplier (2*m) ε s=ε*(560:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt 560:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : (Real.sqrt 560:ℂ)*(Real.sqrt 560:ℂ)=560 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤560)
  have hp := Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg 560) (Real.sqrt_nonneg 560) ((m:ℂ)-s)
  rw [hs] at hp
  unfold reflectionMultiplier
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,← hp]


theorem denominator_reflection (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator k f s=scaleThree k s*denominator k f ((k:ℂ)-s) := by
  have hp : scaleThree k s*(3:ℂ)^(-((k:ℂ)-s))=(3:ℂ)^(-s) := by
    unfold scaleThree
    rw [← Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0)]
    congr 1
    ring
  have hq := scaleThree_product k s
  unfold denominator
  rw [← scaleThree_eq,← scaleThree_eq]
  linear_combination -hq - (((3:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 3*hp

theorem original_numerator_reflection (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∀ s : ℂ, numerator m f s=scaleThree (2*m) s*reflectionMultiplier (2*m) ε s*
        numerator m f ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hlaw,hc⟩ := original_centers_entire hm hf
  let ε : ℂ := χ/I^(2*m)
  have hε : ε=1 ∨ ε= -1 := by
    have hi : I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hχ with rfl|rfl <;> simp [ε,hi,h]
  have hp (j : Fin 4) (s : ℂ) :=
    QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
      (by decide : 0<5040)
      (coefficients (fullCoefficients f (2*m)) (center j)) ε (hc j).2.2 s
  refine ⟨ε,hε,hlaw,fun s => ?_⟩
  have h0 := hp 0 s
  have h1 := hp 1 s
  have h2 := hp 2 s
  have h3 := hp 3 s
  norm_num only [center,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Nat.cast_ofNat] at h0 h1 h2 h3
  rw [center_conductor_factor] at h0 h1 h2 h3
  unfold numerator translateMellin reflectionMultiplier
  simp only [neg_div] at h0 h1 h2 h3 ⊢
  linear_combination h0-h1+h2-h3

theorem original_quadratic_functional_equation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (ε : ℂ) (bound : ℝ) (G : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) ∧
      (∀ s, G s=ε*(560:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s)) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) := by
  obtain ⟨ε,hε,hlaw,hN⟩ := original_numerator_reflection m hm hf
  obtain ⟨B,G,hG,hagree,hpole,hgerm⟩ := original_continuation m hm hf
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have hraw (s : ℂ) : numerator m f s/denominator (2*m) f s=
      reflectionMultiplier (2*m) ε s*(numerator m f ((2*m:ℕ)-s)/denominator (2*m) f ((2*m:ℕ)-s)) := by
    rw [hN s,denominator_reflection (2*m) f s,mul_assoc,
      mul_div_mul_left _ _ (scaleThree_ne_zero (2*m) s)]
    ring
  have hfe := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) ε) ((2*m:ℕ):ℂ) hG
    (fun s => (reflectionMultiplier_entire (2*m) ε).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hε0) hgerm hraw
  refine ⟨ε,B,G,hε,hlaw,hG,hagree,?_,hpole⟩
  intro s
  simpa only [reflectionMultiplier_even] using hfe s
#print axioms original_quadratic_functional_equation
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourFiniteOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex Filter Set SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open scoped Topology

certificate_batch {
theorem original_numerator_bound (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    FinitenessFiniteOrder.Bound (numerator m f) := by
  obtain ⟨χ,_,_,h⟩ := original_centers_entire hm hf
  have hj (j : Fin 4) : FinitenessFiniteOrder.Bound (translateMellin m f (center j)) :=
    SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<5040) _ (h j).2.1
  exact FinitenessFiniteOrderClosure.sub
    (FinitenessFiniteOrderClosure.add (FinitenessFiniteOrderClosure.sub (hj 0) (hj 1)) (hj 2)) (hj 3)

theorem denominator_quadratic (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator (2*m) f s=1+((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s)+
      ((3:ℂ)^((m:ℂ)-s))^2 := by
  have hfirst := SmallLevelTaylor.hecke_first_scalar (by decide : 0<3) m (f 3) s
  have hsecond := SmallLevelTaylor.hecke_second_scalar (by decide : 0<3) m s
  norm_num only [Nat.cast_ofNat,show (3:ℂ)^2=9 by norm_num] at hfirst hsecond
  unfold denominator
  rw [hfirst,hsecond]

theorem product_identity_of_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) :
    ∀ s, denominator (2*m) f s*G s=numerator m f s := by
  obtain ⟨C,hC⟩ := original_hecke_identity m hf
  have hleft := (denominator_entire (2*m) f).mul hG
  have hright := original_numerator_entire m hm hf
  intro s
  have he : (fun z => denominator (2*m) f z*G z)=ᶠ[𝓝[≠] s] numerator m f := by
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

theorem finiteOrder_of_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) :
    FinitenessOriginalInput.FiniteOrder G := by
  apply QuantitativeArithmeticQuadraticTwistQuotient.finiteOrder_of_real_quadratic
    3 (by norm_num)
    ((Real.sqrt 3:ℂ)*f 3) (m:ℂ) (original_numerator_entire m hm hf).continuous
    (FinitenessInputBounds.bound_finiteOrder (original_numerator_bound m hm hf)) hG
  intro s
  norm_num only [Complex.ofReal_ofNat]
  rw [← denominator_quadratic]
  exact product_identity_of_entire hm hf hG B hGF s

#print axioms original_numerator_bound
#print axioms denominator_quadratic
#print axioms product_identity_of_entire
#print axioms finiteOrder_of_entire
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex Filter Set SmallLevelAdditive
open QuantitativeArithmeticAnalyticGerm
open scoped Topology

certificate_batch {
/-- Original-input entireness, finite order and the coherent conductor560
functional equation for the quadratic-four additive difference. -/
theorem original_chi4_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (ε : ℂ) (B : ℝ) (H : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      Differentiable ℂ H ∧ FinitenessOriginalInput.FiniteOrder H ∧
      (∀ s, B<s.re → H s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) ∧
      ∀ s, H s=ε*(560:ℂ)^((m:ℂ)-s)*H ((2*m:ℕ)-s) := by
  obtain ⟨ε,B,H,hε,hlaw,hH,hagree,hfe,_haway⟩ := original_quadratic_functional_equation m hm hf
  obtain ⟨BG,G,hG,hGF⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem.original_entire_grid
    hm hf ε hε hlaw
  have hdiff : Differentiable ℂ (fun z => G z 9-G z 25) := (hG 9).sub (hG 25)
  have hgrid (x : ℂ) : (fun z => G z 9-G z 25)=ᶠ[𝓝[≠] x] H := by
    apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max BG B) _ _ _ x (by linarith)
    · intro z _
      exact (hdiff.analyticAt z).meromorphicAt
    · intro z _
      exact (hH z).meromorphicAt
    · intro z hz
      change G z 9-G z 25=H z
      rw [hGF z (lt_of_le_of_lt (le_max_left BG B) hz),
        hagree z (lt_of_le_of_lt (le_max_right BG B) hz)]
      have hp := grid_mod (2*m) f (by decide : 0<420) (-105) z
      norm_num [grid] at hp
      norm_num [QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows.gridVector,coordinate,grid]
      exact hp
  have hentire : Differentiable ℂ H := by
    intro s
    exact ((HasAnalyticGerm.of_analytic (hdiff.analyticAt s)).congr (hgrid s)).analyticAt (hH s) |>.differentiableAt
  exact ⟨ε,B,H,hε,hlaw,hentire,finiteOrder_of_entire hm hf hentire B hagree,hagree,hfe⟩

#print axioms original_chi4_entire
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelNormalized SmallLevelOriginal
open scoped ModularForm

certificate_batch {
def quadraticFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/4:ℝ))-
  fourier (fullCoefficients f k) (z+(-1/4:ℝ))

/-- The quadratic-four Fourier law, retaining the same sign as the
untwisted Fricke law. All analytic continuation is derived from original input. -/
theorem original_quadratic_fricke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=
        (ε*I^(2*m)) • fourierFunction (2*m) f ∧
      ∀ z : ℂ, 0<z.im → quadraticFourier (2*m) f z=
        (ε*I^(2*m))/(((Real.sqrt 560:ℂ)*z)^(2*m))*
          quadraticFourier (2*m) f (-1/((560:ℂ)*z)) := by
  obtain ⟨ε,B,G,hε,hlaw,hent,hfinite,hGF,hFE⟩ :=
    original_chi4_entire hm hf
  obtain ⟨_hχ,hW⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law (by decide : 0<35) m ε hε hlaw
  obtain ⟨σ,_hσ,hgrowth⟩ := hf.growth
  refine ⟨ε,hε,hlaw,hW,?_⟩
  have h := QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
    (k := 2*m) (ε := ε) (B := B)
    (by decide : 0<560) hf.zero hgrowth (1/4) 0 (-1/4) 0 G hent hfinite
    (by
      intro s hs
      rw [hGF s hs]
      ring)
    (by rcases hε with rfl|rfl <;> norm_num)
    (by
      have he : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
      simpa only [Nat.cast_ofNat,he] using hFE)
  intro z hz
  dsimp only at h
  unfold quadraticFourier
  convert h z hz using 1 <;> ring

#print axioms original_quadratic_fricke
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourIndividual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem (root_four)

certificate_batch {
/-- The Ramanujan-four and quadratic-four equations separate into the
two individual additive equations without dividing by a Hecke eigenvalue. -/
theorem individual_laws {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*I^k)/(((Real.sqrt 560:ℂ)*z)^k)*quadraticFourier k f (-1/((560:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im →
      (fourier (fullCoefficients f k) (z+1/4)=
        (ε*I^k)/(((Real.sqrt 560:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((560:ℂ)*z)+1/4)) ∧
      (fourier (fullCoefficients f k) (z-1/4)=
        (ε*I^k)/(((Real.sqrt 560:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((560:ℂ)*z)-1/4)) := by
  intro z hz
  have hr := hlaw 4 (by decide) z hz
  rw [show Nat.lcm 35 (4^2)=560 by decide,root_four,one_mul,
    SmallLevelThirty.twist_four _ (periodic _),
    SmallLevelThirty.twist_four _ (periodic _)] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hc := hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  simp only [sub_eq_add_neg] at hr hc ⊢
  constructor
  · linear_combination (hr+hc)/2
  · linear_combination (hr-hc)/2

#print axioms individual_laws
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Matrix UpperHalfPlane SmallLevelNormalized
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

certificate_batch {
def Dplus : SL(2,ℤ) := ⟨!![4,-1;-35,9],by decide⟩
def Dminus : SL(2,ℤ) := ⟨!![4,1;35,9],by decide⟩

theorem sqrt_four_conductor : Real.sqrt 560=4*Real.sqrt 35 := by
  rw [show (560:ℝ)=16*35 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem plus_branch : fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Dplus*translation (1/4)=
    translation (1/4)*fricke 560 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Dplus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_four_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem minus_branch : fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Dminus*translation (-1/4)=
    translation (-1/4)*fricke 560 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Dminus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_four_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem plus_conjugate : (fricke 35 (by decide))⁻¹*translation (1/4)*fricke 560 (by decide)*
    (translation (1/4))⁻¹=SpecialLinearGroup.mapGL ℝ Dplus := by
  calc
    _=(fricke 35 (by decide))⁻¹*(translation (1/4)*fricke 560 (by decide))*(translation (1/4))⁻¹ := by group
    _=(fricke 35 (by decide))⁻¹*(fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Dplus*translation (1/4))*(translation (1/4))⁻¹ := by rw [plus_branch]
    _=_ := by group

theorem minus_conjugate : (fricke 35 (by decide))⁻¹*translation (-1/4)*fricke 560 (by decide)*
    (translation (-1/4))⁻¹=SpecialLinearGroup.mapGL ℝ Dminus := by
  calc
    _=(fricke 35 (by decide))⁻¹*(translation (-1/4)*fricke 560 (by decide))*(translation (-1/4))⁻¹ := by group
    _=(fricke 35 (by decide))⁻¹*(fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Dminus*translation (-1/4))*(translation (-1/4))⁻¹ := by rw [minus_branch]
    _=_ := by group

#print axioms plus_conjugate
#print axioms minus_conjugate
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourTransformations -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

certificate_batch {
/-- Original Euler/Fricke input forces both denominator-four matrices,
including the zero Hecke-eigenvalue cases. -/
theorem original_D_plus_minus {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Dplus=fourierFunction (2*m) f ∧
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Dminus=fourierFunction (2*m) f := by
  obtain ⟨ε,_hε,hlaw,_hW,hquad⟩ := original_quadratic_fricke hm hf
  have hF : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*Complex.I^(2*m))/(((Real.sqrt 35:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((35:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have hind := individual_laws ε hlaw hquad
  constructor
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_of_fricke
      35 560 (2*m) (by decide) (by decide) (1/4) _ _ hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_one,
          Complex.ofReal_ofNat] using (hind z hz).1)
    rw [plus_conjugate] at h
    exact h
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_of_fricke
      35 560 (2*m) (by decide) (by decide) (-1/4) _ _ hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat,
          Complex.ofReal_one,sub_eq_add_neg,neg_div] using (hind z hz).2)
    rw [minus_conjugate] at h
    exact h

#print axioms original_D_plus_minus
}

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveGroupData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

certificate_batch {
def kernel (i : Fin 18) : SL(2,ℤ) :=
  match i.val with
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![1,0;35,1],by decide⟩
  | 2 => ⟨!![2,-1;-35,18],by decide⟩
  | 3 => ⟨!![6,-1;-35,6],by decide⟩
  | 4 => ⟨!![3,-1;-35,12],by decide⟩
  | 5 => ⟨!![3,1;35,12],by decide⟩
  | 6 => ⟨!![41,-17;70,-29],by decide⟩
  | 7 => ⟨!![4,-1;-35,9],by decide⟩
  | 8 => ⟨!![4,1;35,9],by decide⟩
  | 9 => ⟨!![1,0;-35,1],by decide⟩
  | 10 => ⟨!![1,-1;0,1],by decide⟩
  | 11 => ⟨!![18,1;35,2],by decide⟩
  | 12 => ⟨!![6,1;35,6],by decide⟩
  | 13 => ⟨!![12,1;35,3],by decide⟩
  | 14 => ⟨!![12,-1;-35,3],by decide⟩
  | 15 => ⟨!![-29,-2;595,41],by decide⟩
  | 16 => ⟨!![9,1;35,4],by decide⟩
  | _ => ⟨!![9,-1;-35,4],by decide⟩

def letter : Fin 37 → SL(2,ℤ)
  | 0 => kernel 0
  | 1 => kernel 1
  | 2 => kernel 2
  | 3 => kernel 3
  | 4 => kernel 4
  | 5 => kernel 5
  | 6 => kernel 6
  | 7 => kernel 7
  | 8 => kernel 8
  | 9 => kernel 9
  | 10 => kernel 10
  | 11 => kernel 11
  | 12 => kernel 12
  | 13 => kernel 13
  | 14 => kernel 14
  | 15 => kernel 15
  | 16 => kernel 16
  | 17 => kernel 17
  | 18 => (kernel 0)⁻¹
  | 19 => (kernel 1)⁻¹
  | 20 => (kernel 2)⁻¹
  | 21 => (kernel 3)⁻¹
  | 22 => (kernel 4)⁻¹
  | 23 => (kernel 5)⁻¹
  | 24 => (kernel 6)⁻¹
  | 25 => (kernel 7)⁻¹
  | 26 => (kernel 8)⁻¹
  | 27 => (kernel 9)⁻¹
  | 28 => (kernel 10)⁻¹
  | 29 => (kernel 11)⁻¹
  | 30 => (kernel 12)⁻¹
  | 31 => (kernel 13)⁻¹
  | 32 => (kernel 14)⁻¹
  | 33 => (kernel 15)⁻¹
  | 34 => (kernel 16)⁻¹
  | 35 => (kernel 17)⁻¹
  | _ => -1

def word (w : List (Fin 37)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 18, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (w : List (Fin 37)) : word w∈K := by
  have hl (i : Fin 37) : letter i∈K := by
    fin_cases i
    · exact hK 0
    · exact hK 1
    · exact hK 2
    · exact hK 3
    · exact hK 4
    · exact hK 5
    · exact hK 6
    · exact hK 7
    · exact hK 8
    · exact hK 9
    · exact hK 10
    · exact hK 11
    · exact hK 12
    · exact hK 13
    · exact hK 14
    · exact hK 15
    · exact hK 16
    · exact hK 17
    · exact K.inv_mem (hK 0)
    · exact K.inv_mem (hK 1)
    · exact K.inv_mem (hK 2)
    · exact K.inv_mem (hK 3)
    · exact K.inv_mem (hK 4)
    · exact K.inv_mem (hK 5)
    · exact K.inv_mem (hK 6)
    · exact K.inv_mem (hK 7)
    · exact K.inv_mem (hK 8)
    · exact K.inv_mem (hK 9)
    · exact K.inv_mem (hK 10)
    · exact K.inv_mem (hK 11)
    · exact K.inv_mem (hK 12)
    · exact K.inv_mem (hK 13)
    · exact K.inv_mem (hK 14)
    · exact K.inv_mem (hK 15)
    · exact K.inv_mem (hK 16)
    · exact K.inv_mem (hK 17)
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def rowClass (c d : ZMod 35) : ℕ :=
  (if c.val%5=0 then 5 else (d.val%5*([0,1,3,2,4] : List ℕ).getD (c.val%5) 0)%5)*8+
  (if c.val%7=0 then 7 else (d.val%7*([0,1,4,5,2,3,6] : List ℕ).getD (c.val%7) 0)%7)

def repRow (c d : ZMod 35) : SL(2,ℤ) :=
  match rowClass c d with
  | 0 => ⟨!![0,-1;1,0],by decide⟩
  | 9 => ⟨!![0,-1;1,1],by decide⟩
  | 38 => ⟨!![0,-1;1,-1],by decide⟩
  | 18 => ⟨!![0,-1;1,2],by decide⟩
  | 29 => ⟨!![0,-1;1,-2],by decide⟩
  | 19 => ⟨!![-1,0;2,-1],by decide⟩
  | 27 => ⟨!![0,-1;1,3],by decide⟩
  | 28 => ⟨!![-1,0;-2,-1],by decide⟩
  | 20 => ⟨!![0,-1;1,-3],by decide⟩
  | 10 => ⟨!![-1,1;2,-3],by decide⟩
  | 26 => ⟨!![-1,0;3,-1],by decide⟩
  | 36 => ⟨!![0,-1;1,4],by decide⟩
  | 37 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 21 => ⟨!![-1,0;-3,-1],by decide⟩
  | 11 => ⟨!![0,-1;1,-4],by decide⟩
  | 35 => ⟨!![1,1;-3,-2],by decide⟩
  | 1 => ⟨!![-1,2;2,-5],by decide⟩
  | 17 => ⟨!![-1,1;3,-4],by decide⟩
  | 13 => ⟨!![-1,0;4,-1],by decide⟩
  | 5 => ⟨!![0,-1;1,5],by decide⟩
  | 12 => ⟨!![-1,1;-3,2],by decide⟩
  | 6 => ⟨!![-1,-2;-2,-5],by decide⟩
  | 30 => ⟨!![-1,-1;-3,-4],by decide⟩
  | 34 => ⟨!![-1,0;-4,-1],by decide⟩
  | 2 => ⟨!![0,-1;1,-5],by decide⟩
  | 4 => ⟨!![1,2;-3,-5],by decide⟩
  | 46 => ⟨!![2,1;-5,-2],by decide⟩
  | 32 => ⟨!![-1,3;2,-7],by decide⟩
  | 22 => ⟨!![1,1;-4,-3],by decide⟩
  | 8 => ⟨!![-1,2;3,-7],by decide⟩
  | 44 => ⟨!![-1,0;5,-1],by decide⟩
  | 14 => ⟨!![0,-1;1,6],by decide⟩
  | 3 => ⟨!![-1,2;-3,5],by decide⟩
  | 41 => ⟨!![-2,1;-5,2],by decide⟩
  | 25 => ⟨!![-1,1;-4,3],by decide⟩
  | 43 => ⟨!![-1,0;-5,-1],by decide⟩
  | 33 => ⟨!![0,-1;1,-6],by decide⟩
  | 45 => ⟨!![2,-1;-5,3],by decide⟩
  | 40 => ⟨!![2,3;-5,-7],by decide⟩
  | 15 => ⟨!![3,1;-7,-2],by decide⟩
  | 24 => ⟨!![1,2;-4,-7],by decide⟩
  | 39 => ⟨!![2,1;-7,-3],by decide⟩
  | 16 => ⟨!![0,-1;1,7],by decide⟩
  | 42 => ⟨!![2,1;5,3],by decide⟩
  | 7 => ⟨!![3,-2;-7,5],by decide⟩
  | 23 => ⟨!![3,4;-7,-9],by decide⟩
  | 31 => ⟨!![2,-1;-7,4],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 35) : List (Fin 37) :=
  match rowClass c d with
  | 0 => [36]
  | 9 => [10]
  | 38 => [0, 36]
  | 19 => [36]
  | 28 => [36]
  | 26 => [36]
  | 21 => [36]
  | 35 => [36]
  | 13 => [36]
  | 12 => [36]
  | 34 => [36]
  | 46 => [36]
  | 22 => [36]
  | 44 => [36]
  | 14 => [3]
  | 41 => [36]
  | 25 => [36]
  | 43 => [36]
  | 33 => [12, 36]
  | 45 => [36]
  | 15 => [36]
  | 39 => [36]
  | 16 => [7, 13, 36, 2, 0]
  | 42 => [36]
  | 7 => [36]
  | 23 => [10, 11, 4, 16]
  | 31 => [36]
  | _ => []

def edgeTRow (c d : ZMod 35) : List (Fin 37) :=
  match rowClass c d with
  | 47 => [0]
  | 19 => [10, 36]
  | 26 => [36]
  | 13 => [36]
  | 6 => [11, 9, 36, 5]
  | 30 => [13, 2, 36, 0]
  | 34 => [16, 4]
  | 4 => [14, 8, 36]
  | 44 => [17, 5]
  | 41 => [36]
  | 43 => [12]
  | 40 => [10, 6, 36]
  | 24 => [17, 36]
  | 39 => [14, 1, 36, 15, 2, 0]
  | 16 => [7, 36]
  | 42 => [13, 7]
  | 23 => [10, 11, 36, 4, 16, 3, 8]
  | _ => []

def rep (g : SL(2,ZMod 35)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)
theorem row_primitive (g : SL(2,ZMod 35)) :
    ∃ a b : ZMod 35, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe

}

end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end

/-! ## ThirtyFiveGroupEdgesSFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

















































end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end
end

/-! ## ThirtyFiveGroupEdgesTFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

















































end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end
end

/-! ## ThirtyFiveGroupGenerators -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

certificate_batch {
private theorem boundedEdgeSRow0 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (0:ZMod 35).val d.val) 35 = 1 →
    repRow (0:ZMod 35) d*S*(repRow d (-(0:ZMod 35)))⁻¹=word (edgeSRow (0:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow1 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (1:ZMod 35).val d.val) 35 = 1 →
    repRow (1:ZMod 35) d*S*(repRow d (-(1:ZMod 35)))⁻¹=word (edgeSRow (1:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow2 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (2:ZMod 35).val d.val) 35 = 1 →
    repRow (2:ZMod 35) d*S*(repRow d (-(2:ZMod 35)))⁻¹=word (edgeSRow (2:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow3 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (3:ZMod 35).val d.val) 35 = 1 →
    repRow (3:ZMod 35) d*S*(repRow d (-(3:ZMod 35)))⁻¹=word (edgeSRow (3:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow4 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (4:ZMod 35).val d.val) 35 = 1 →
    repRow (4:ZMod 35) d*S*(repRow d (-(4:ZMod 35)))⁻¹=word (edgeSRow (4:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow5 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (5:ZMod 35).val d.val) 35 = 1 →
    repRow (5:ZMod 35) d*S*(repRow d (-(5:ZMod 35)))⁻¹=word (edgeSRow (5:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow6 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (6:ZMod 35).val d.val) 35 = 1 →
    repRow (6:ZMod 35) d*S*(repRow d (-(6:ZMod 35)))⁻¹=word (edgeSRow (6:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow7 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (7:ZMod 35).val d.val) 35 = 1 →
    repRow (7:ZMod 35) d*S*(repRow d (-(7:ZMod 35)))⁻¹=word (edgeSRow (7:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow8 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (8:ZMod 35).val d.val) 35 = 1 →
    repRow (8:ZMod 35) d*S*(repRow d (-(8:ZMod 35)))⁻¹=word (edgeSRow (8:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow9 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (9:ZMod 35).val d.val) 35 = 1 →
    repRow (9:ZMod 35) d*S*(repRow d (-(9:ZMod 35)))⁻¹=word (edgeSRow (9:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow10 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (10:ZMod 35).val d.val) 35 = 1 →
    repRow (10:ZMod 35) d*S*(repRow d (-(10:ZMod 35)))⁻¹=word (edgeSRow (10:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow11 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (11:ZMod 35).val d.val) 35 = 1 →
    repRow (11:ZMod 35) d*S*(repRow d (-(11:ZMod 35)))⁻¹=word (edgeSRow (11:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow12 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (12:ZMod 35).val d.val) 35 = 1 →
    repRow (12:ZMod 35) d*S*(repRow d (-(12:ZMod 35)))⁻¹=word (edgeSRow (12:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow13 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (13:ZMod 35).val d.val) 35 = 1 →
    repRow (13:ZMod 35) d*S*(repRow d (-(13:ZMod 35)))⁻¹=word (edgeSRow (13:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow14 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (14:ZMod 35).val d.val) 35 = 1 →
    repRow (14:ZMod 35) d*S*(repRow d (-(14:ZMod 35)))⁻¹=word (edgeSRow (14:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow15 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (15:ZMod 35).val d.val) 35 = 1 →
    repRow (15:ZMod 35) d*S*(repRow d (-(15:ZMod 35)))⁻¹=word (edgeSRow (15:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow16 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (16:ZMod 35).val d.val) 35 = 1 →
    repRow (16:ZMod 35) d*S*(repRow d (-(16:ZMod 35)))⁻¹=word (edgeSRow (16:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow17 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (17:ZMod 35).val d.val) 35 = 1 →
    repRow (17:ZMod 35) d*S*(repRow d (-(17:ZMod 35)))⁻¹=word (edgeSRow (17:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow18 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (18:ZMod 35).val d.val) 35 = 1 →
    repRow (18:ZMod 35) d*S*(repRow d (-(18:ZMod 35)))⁻¹=word (edgeSRow (18:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow19 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (19:ZMod 35).val d.val) 35 = 1 →
    repRow (19:ZMod 35) d*S*(repRow d (-(19:ZMod 35)))⁻¹=word (edgeSRow (19:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow20 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (20:ZMod 35).val d.val) 35 = 1 →
    repRow (20:ZMod 35) d*S*(repRow d (-(20:ZMod 35)))⁻¹=word (edgeSRow (20:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow21 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (21:ZMod 35).val d.val) 35 = 1 →
    repRow (21:ZMod 35) d*S*(repRow d (-(21:ZMod 35)))⁻¹=word (edgeSRow (21:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow22 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (22:ZMod 35).val d.val) 35 = 1 →
    repRow (22:ZMod 35) d*S*(repRow d (-(22:ZMod 35)))⁻¹=word (edgeSRow (22:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow23 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (23:ZMod 35).val d.val) 35 = 1 →
    repRow (23:ZMod 35) d*S*(repRow d (-(23:ZMod 35)))⁻¹=word (edgeSRow (23:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow24 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (24:ZMod 35).val d.val) 35 = 1 →
    repRow (24:ZMod 35) d*S*(repRow d (-(24:ZMod 35)))⁻¹=word (edgeSRow (24:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow25 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (25:ZMod 35).val d.val) 35 = 1 →
    repRow (25:ZMod 35) d*S*(repRow d (-(25:ZMod 35)))⁻¹=word (edgeSRow (25:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow26 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (26:ZMod 35).val d.val) 35 = 1 →
    repRow (26:ZMod 35) d*S*(repRow d (-(26:ZMod 35)))⁻¹=word (edgeSRow (26:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow27 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (27:ZMod 35).val d.val) 35 = 1 →
    repRow (27:ZMod 35) d*S*(repRow d (-(27:ZMod 35)))⁻¹=word (edgeSRow (27:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow28 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (28:ZMod 35).val d.val) 35 = 1 →
    repRow (28:ZMod 35) d*S*(repRow d (-(28:ZMod 35)))⁻¹=word (edgeSRow (28:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow29 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (29:ZMod 35).val d.val) 35 = 1 →
    repRow (29:ZMod 35) d*S*(repRow d (-(29:ZMod 35)))⁻¹=word (edgeSRow (29:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow30 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (30:ZMod 35).val d.val) 35 = 1 →
    repRow (30:ZMod 35) d*S*(repRow d (-(30:ZMod 35)))⁻¹=word (edgeSRow (30:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow31 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (31:ZMod 35).val d.val) 35 = 1 →
    repRow (31:ZMod 35) d*S*(repRow d (-(31:ZMod 35)))⁻¹=word (edgeSRow (31:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow32 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (32:ZMod 35).val d.val) 35 = 1 →
    repRow (32:ZMod 35) d*S*(repRow d (-(32:ZMod 35)))⁻¹=word (edgeSRow (32:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow33 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (33:ZMod 35).val d.val) 35 = 1 →
    repRow (33:ZMod 35) d*S*(repRow d (-(33:ZMod 35)))⁻¹=word (edgeSRow (33:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRow34 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (34:ZMod 35).val d.val) 35 = 1 →
    repRow (34:ZMod 35) d*S*(repRow d (-(34:ZMod 35)))⁻¹=word (edgeSRow (34:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeSRows : ∀ c d : ZMod 35,
    Nat.gcd (Nat.gcd c.val d.val) 35 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c
  fin_cases c
  · exact boundedEdgeSRow0
  · exact boundedEdgeSRow1
  · exact boundedEdgeSRow2
  · exact boundedEdgeSRow3
  · exact boundedEdgeSRow4
  · exact boundedEdgeSRow5
  · exact boundedEdgeSRow6
  · exact boundedEdgeSRow7
  · exact boundedEdgeSRow8
  · exact boundedEdgeSRow9
  · exact boundedEdgeSRow10
  · exact boundedEdgeSRow11
  · exact boundedEdgeSRow12
  · exact boundedEdgeSRow13
  · exact boundedEdgeSRow14
  · exact boundedEdgeSRow15
  · exact boundedEdgeSRow16
  · exact boundedEdgeSRow17
  · exact boundedEdgeSRow18
  · exact boundedEdgeSRow19
  · exact boundedEdgeSRow20
  · exact boundedEdgeSRow21
  · exact boundedEdgeSRow22
  · exact boundedEdgeSRow23
  · exact boundedEdgeSRow24
  · exact boundedEdgeSRow25
  · exact boundedEdgeSRow26
  · exact boundedEdgeSRow27
  · exact boundedEdgeSRow28
  · exact boundedEdgeSRow29
  · exact boundedEdgeSRow30
  · exact boundedEdgeSRow31
  · exact boundedEdgeSRow32
  · exact boundedEdgeSRow33
  · exact boundedEdgeSRow34

theorem edgeSRow_checked : ∀ c d : ZMod 35, (∃ a b : ZMod 35, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact boundedEdgeSRows c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

private theorem boundedEdgeTRow0 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (0:ZMod 35).val d.val) 35 = 1 →
    repRow (0:ZMod 35) d*T*(repRow (0:ZMod 35) ((0:ZMod 35)+d))⁻¹=word (edgeTRow (0:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow1 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (1:ZMod 35).val d.val) 35 = 1 →
    repRow (1:ZMod 35) d*T*(repRow (1:ZMod 35) ((1:ZMod 35)+d))⁻¹=word (edgeTRow (1:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow2 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (2:ZMod 35).val d.val) 35 = 1 →
    repRow (2:ZMod 35) d*T*(repRow (2:ZMod 35) ((2:ZMod 35)+d))⁻¹=word (edgeTRow (2:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow3 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (3:ZMod 35).val d.val) 35 = 1 →
    repRow (3:ZMod 35) d*T*(repRow (3:ZMod 35) ((3:ZMod 35)+d))⁻¹=word (edgeTRow (3:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow4 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (4:ZMod 35).val d.val) 35 = 1 →
    repRow (4:ZMod 35) d*T*(repRow (4:ZMod 35) ((4:ZMod 35)+d))⁻¹=word (edgeTRow (4:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow5 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (5:ZMod 35).val d.val) 35 = 1 →
    repRow (5:ZMod 35) d*T*(repRow (5:ZMod 35) ((5:ZMod 35)+d))⁻¹=word (edgeTRow (5:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow6 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (6:ZMod 35).val d.val) 35 = 1 →
    repRow (6:ZMod 35) d*T*(repRow (6:ZMod 35) ((6:ZMod 35)+d))⁻¹=word (edgeTRow (6:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow7 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (7:ZMod 35).val d.val) 35 = 1 →
    repRow (7:ZMod 35) d*T*(repRow (7:ZMod 35) ((7:ZMod 35)+d))⁻¹=word (edgeTRow (7:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow8 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (8:ZMod 35).val d.val) 35 = 1 →
    repRow (8:ZMod 35) d*T*(repRow (8:ZMod 35) ((8:ZMod 35)+d))⁻¹=word (edgeTRow (8:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow9 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (9:ZMod 35).val d.val) 35 = 1 →
    repRow (9:ZMod 35) d*T*(repRow (9:ZMod 35) ((9:ZMod 35)+d))⁻¹=word (edgeTRow (9:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow10 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (10:ZMod 35).val d.val) 35 = 1 →
    repRow (10:ZMod 35) d*T*(repRow (10:ZMod 35) ((10:ZMod 35)+d))⁻¹=word (edgeTRow (10:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow11 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (11:ZMod 35).val d.val) 35 = 1 →
    repRow (11:ZMod 35) d*T*(repRow (11:ZMod 35) ((11:ZMod 35)+d))⁻¹=word (edgeTRow (11:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow12 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (12:ZMod 35).val d.val) 35 = 1 →
    repRow (12:ZMod 35) d*T*(repRow (12:ZMod 35) ((12:ZMod 35)+d))⁻¹=word (edgeTRow (12:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow13 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (13:ZMod 35).val d.val) 35 = 1 →
    repRow (13:ZMod 35) d*T*(repRow (13:ZMod 35) ((13:ZMod 35)+d))⁻¹=word (edgeTRow (13:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow14 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (14:ZMod 35).val d.val) 35 = 1 →
    repRow (14:ZMod 35) d*T*(repRow (14:ZMod 35) ((14:ZMod 35)+d))⁻¹=word (edgeTRow (14:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow15 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (15:ZMod 35).val d.val) 35 = 1 →
    repRow (15:ZMod 35) d*T*(repRow (15:ZMod 35) ((15:ZMod 35)+d))⁻¹=word (edgeTRow (15:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow16 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (16:ZMod 35).val d.val) 35 = 1 →
    repRow (16:ZMod 35) d*T*(repRow (16:ZMod 35) ((16:ZMod 35)+d))⁻¹=word (edgeTRow (16:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow17 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (17:ZMod 35).val d.val) 35 = 1 →
    repRow (17:ZMod 35) d*T*(repRow (17:ZMod 35) ((17:ZMod 35)+d))⁻¹=word (edgeTRow (17:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow18 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (18:ZMod 35).val d.val) 35 = 1 →
    repRow (18:ZMod 35) d*T*(repRow (18:ZMod 35) ((18:ZMod 35)+d))⁻¹=word (edgeTRow (18:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow19 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (19:ZMod 35).val d.val) 35 = 1 →
    repRow (19:ZMod 35) d*T*(repRow (19:ZMod 35) ((19:ZMod 35)+d))⁻¹=word (edgeTRow (19:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow20 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (20:ZMod 35).val d.val) 35 = 1 →
    repRow (20:ZMod 35) d*T*(repRow (20:ZMod 35) ((20:ZMod 35)+d))⁻¹=word (edgeTRow (20:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow21 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (21:ZMod 35).val d.val) 35 = 1 →
    repRow (21:ZMod 35) d*T*(repRow (21:ZMod 35) ((21:ZMod 35)+d))⁻¹=word (edgeTRow (21:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow22 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (22:ZMod 35).val d.val) 35 = 1 →
    repRow (22:ZMod 35) d*T*(repRow (22:ZMod 35) ((22:ZMod 35)+d))⁻¹=word (edgeTRow (22:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow23 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (23:ZMod 35).val d.val) 35 = 1 →
    repRow (23:ZMod 35) d*T*(repRow (23:ZMod 35) ((23:ZMod 35)+d))⁻¹=word (edgeTRow (23:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow24 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (24:ZMod 35).val d.val) 35 = 1 →
    repRow (24:ZMod 35) d*T*(repRow (24:ZMod 35) ((24:ZMod 35)+d))⁻¹=word (edgeTRow (24:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow25 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (25:ZMod 35).val d.val) 35 = 1 →
    repRow (25:ZMod 35) d*T*(repRow (25:ZMod 35) ((25:ZMod 35)+d))⁻¹=word (edgeTRow (25:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow26 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (26:ZMod 35).val d.val) 35 = 1 →
    repRow (26:ZMod 35) d*T*(repRow (26:ZMod 35) ((26:ZMod 35)+d))⁻¹=word (edgeTRow (26:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow27 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (27:ZMod 35).val d.val) 35 = 1 →
    repRow (27:ZMod 35) d*T*(repRow (27:ZMod 35) ((27:ZMod 35)+d))⁻¹=word (edgeTRow (27:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow28 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (28:ZMod 35).val d.val) 35 = 1 →
    repRow (28:ZMod 35) d*T*(repRow (28:ZMod 35) ((28:ZMod 35)+d))⁻¹=word (edgeTRow (28:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow29 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (29:ZMod 35).val d.val) 35 = 1 →
    repRow (29:ZMod 35) d*T*(repRow (29:ZMod 35) ((29:ZMod 35)+d))⁻¹=word (edgeTRow (29:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow30 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (30:ZMod 35).val d.val) 35 = 1 →
    repRow (30:ZMod 35) d*T*(repRow (30:ZMod 35) ((30:ZMod 35)+d))⁻¹=word (edgeTRow (30:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow31 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (31:ZMod 35).val d.val) 35 = 1 →
    repRow (31:ZMod 35) d*T*(repRow (31:ZMod 35) ((31:ZMod 35)+d))⁻¹=word (edgeTRow (31:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow32 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (32:ZMod 35).val d.val) 35 = 1 →
    repRow (32:ZMod 35) d*T*(repRow (32:ZMod 35) ((32:ZMod 35)+d))⁻¹=word (edgeTRow (32:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow33 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (33:ZMod 35).val d.val) 35 = 1 →
    repRow (33:ZMod 35) d*T*(repRow (33:ZMod 35) ((33:ZMod 35)+d))⁻¹=word (edgeTRow (33:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRow34 : ∀ d : ZMod 35,
    Nat.gcd (Nat.gcd (34:ZMod 35).val d.val) 35 = 1 →
    repRow (34:ZMod 35) d*T*(repRow (34:ZMod 35) ((34:ZMod 35)+d))⁻¹=word (edgeTRow (34:ZMod 35) d) := by
  decide +kernel

private theorem boundedEdgeTRows : ∀ c d : ZMod 35,
    Nat.gcd (Nat.gcd c.val d.val) 35 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c
  fin_cases c
  · exact boundedEdgeTRow0
  · exact boundedEdgeTRow1
  · exact boundedEdgeTRow2
  · exact boundedEdgeTRow3
  · exact boundedEdgeTRow4
  · exact boundedEdgeTRow5
  · exact boundedEdgeTRow6
  · exact boundedEdgeTRow7
  · exact boundedEdgeTRow8
  · exact boundedEdgeTRow9
  · exact boundedEdgeTRow10
  · exact boundedEdgeTRow11
  · exact boundedEdgeTRow12
  · exact boundedEdgeTRow13
  · exact boundedEdgeTRow14
  · exact boundedEdgeTRow15
  · exact boundedEdgeTRow16
  · exact boundedEdgeTRow17
  · exact boundedEdgeTRow18
  · exact boundedEdgeTRow19
  · exact boundedEdgeTRow20
  · exact boundedEdgeTRow21
  · exact boundedEdgeTRow22
  · exact boundedEdgeTRow23
  · exact boundedEdgeTRow24
  · exact boundedEdgeTRow25
  · exact boundedEdgeTRow26
  · exact boundedEdgeTRow27
  · exact boundedEdgeTRow28
  · exact boundedEdgeTRow29
  · exact boundedEdgeTRow30
  · exact boundedEdgeTRow31
  · exact boundedEdgeTRow32
  · exact boundedEdgeTRow33
  · exact boundedEdgeTRow34

theorem edgeTRow_checked : ∀ c d : ZMod 35, (∃ a b : ZMod 35, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact boundedEdgeTRows c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 35)) :
    rep g*S*(rep (g*reduction 35 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 35 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 35 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 35)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 35)) :
    rep g*T*(rep (g*reduction 35 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 35 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 35 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 35)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 35)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 35, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 18, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 35) : γ∈K := by
  apply transversal_mem (reduction 35) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hK hZ _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hK hZ _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ
#print axioms gamma0_mem

}

end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end

/-! ## ThirtyFiveGroupMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

certificate_batch {
theorem conjugate_fricke (i : Fin 9) :
    SpecialLinearGroup.mapGL ℝ (kernel ⟨i.val+9,by omega⟩)*fricke 35 (by decide)=
      fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel (i.castLE (by decide))) := by
  have hs : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,kernel,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem conjugate_invariant (F : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ)
    (δ : ℂ) (hg : F ∣[k] g=δ • F) (γ κ : SL(2,ℤ))
    (hκ : SpecialLinearGroup.mapGL ℝ κ*g=g*SpecialLinearGroup.mapGL ℝ γ)
    (hγ : F ∣[k] γ=F) : F ∣[k] κ=F := by
  have hh : (F ∣[k] κ) ∣[k] g=F ∣[k] g := by
    change (F ∣[k] SpecialLinearGroup.mapGL ℝ κ) ∣[k] g=F ∣[k] g
    rw [← SlashAction.slash_mul,hκ,SlashAction.slash_mul]
    change (F ∣[k] g) ∣[k] γ=F ∣[k] g
    rw [hg,ModularForm.SL_smul_slash,hγ]
  have h := congrArg (fun G : ℍ → ℂ => G ∣[k] g⁻¹) hh
  simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using h

theorem original_first_four {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) (i : Fin 4) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] kernel (i.castLE (by decide))=
      SmallLevelOriginal.fourierFunction k f := by
  fin_cases i
  · exact original_T k f
  · exact original_lower (by decide) hf
  · have hh := (slashStabilizer (k:ℤ) (SmallLevelOriginal.fourierFunction k f)).inv_mem
      (original_odd (by decide) (by decide : 2*18=35+1) (by decide) hf)
    exact hh
  · exact QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.original_six hk hf

/-- Only the five displayed additional invariances are assumed. The first
four generators and all nine Fricke conjugates follow from original input. -/
theorem original_kernel (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (hextra : ∀ i : Fin 5,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel ⟨i.val+4,by omega⟩=
        SmallLevelOriginal.fourierFunction (2*m) f) (i : Fin 18) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  have hbase (j : Fin 9) :
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel (j.castLE (by decide))=
        SmallLevelOriginal.fourierFunction (2*m) f := by
    by_cases hj : j.val<4
    · exact original_first_four (by omega) hf ⟨j.val,hj⟩
    · have hh := hextra ⟨j.val-4,by omega⟩
      have heq : (⟨(j.val-4)+4,by omega⟩ : Fin 18)=j.castLE (by decide) := by
        apply Fin.ext
        simp only [Fin.val_castLE]
        omega
      simpa only [heq] using hh
  obtain ⟨χ,_,hχ⟩ := original_fricke_sign (by decide : 0<35) m hf
  by_cases hi : i.val<9
  · exact hbase ⟨i.val,hi⟩
  · have hh := conjugate_invariant _ _ _ χ hχ _ _
      (conjugate_fricke ⟨i.val-9,by omega⟩) (hbase ⟨i.val-9,by omega⟩)
    have heq : (⟨(i.val-9)+9,by omega⟩ : Fin 18)=i := by
      apply Fin.ext
      change (i.val-9)+9=i.val
      omega
    simpa only [heq] using hh

#print axioms original_first_four
#print axioms original_kernel
}

end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end

/-! ## ThirtyFiveModular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm

certificate_batch {
/-- All eighteen group generators are forced by the original hypotheses.
The chi3 and chi4 analytic continuations have been proved internally. -/
theorem original_all_generators {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (i : Fin 18) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=fourierFunction (2*m) f := by
  obtain ⟨hCp,hCm⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_C_plus_minus hm hf
  obtain ⟨hDp,hDm⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiFour.original_D_plus_minus hm hf
  have hH := QuantitativeArithmeticSmallLevelThirtyFiveTwelve.original_H_unconditional hm hf
  apply original_kernel m hm hf _ i
  intro j
  fin_cases j
  · exact hCp
  · exact hCm
  · exact hH
  · exact hDp
  · exact hDm

theorem original_gamma0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 35) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  exact gamma0_mem (slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f))
    (original_all_generators hm hf) (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- The level35 converse theorem, from the literal original Euler-product
and entire Fricke hypotheses, including holomorphy at every cusp. -/
theorem level_thirty_five {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) : IsModular 35 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (original_gamma0 (by omega) hf)

#print axioms original_all_generators
#print axioms original_gamma0
#print axioms level_thirty_five
}

end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end

/-! ## ThirtyFivePoleResidual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyFivePole

open Complex Filter Set
open scoped Topology

certificate_batch {
def badProduct (f : ℕ → ℂ) : ℂ :=
  (Real.sqrt 5:ℂ)*f 5*((Real.sqrt 7:ℂ)*f 7)

/-- The product in the level-35 residual has norm one for actual original
Euler data, with no new root-sign assumptions. -/
theorem badProduct_norm {f : ℕ → ℂ} (hf : FinitenessOriginalInput.EulerData 35 f) :
    ‖badProduct f‖=1 := by
  have h5 := FinitenessOriginalTwistLocal.bad_root_sign hf
    (by decide : Nat.Prime 5) (by decide) (by decide)
  have h7 := FinitenessOriginalTwistLocal.bad_root_sign hf
    (by decide : Nat.Prime 7) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat] at h5 h7
  have he : badProduct f=(-f 5*Real.sqrt 5)*(-f 7*Real.sqrt 7) := by
    unfold badProduct
    ring
  rw [he]
  rcases h5 with h5|h5 <;> rcases h7 with h7|h7 <;> rw [h5,h7] <;> norm_num

/-- Exponential form of the numerator 35^(s-k/2)-sigma5*sigma7.
No finite-grid identity for this residual is asserted by this definition. -/
def residual (f : ℕ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.log 35:ℂ)*(z-(k:ℂ)/2))-badProduct f

theorem residual_cpow (f : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    residual f k z=(35:ℂ)^(z-(k:ℂ)/2)-badProduct f := by
  have hl : Complex.log (35:ℂ)=(Real.log 35:ℂ) := by
    simp
  rw [residual,Complex.cpow_def_of_ne_zero (by norm_num : (35:ℂ)≠0),hl]

theorem residual_analytic (f : ℕ → ℂ) (k : ℕ) (x : ℂ) :
    AnalyticAt ℂ (residual f k) x := by
  unfold residual
  fun_prop

theorem original_residual_central {k : ℕ} {f : ℕ → ℂ} {z : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) (hz : residual f k z=0) :
    z.re=(k:ℝ)/2 := by
  apply SmallLevelPoleGrid.exponential_zero_central
    (α:=Real.log 35) (s:=badProduct f)
    (Real.log_pos (by norm_num : (1:ℝ)<35)).ne' (badProduct_norm hf.toEulerData)
  have hh := sub_eq_zero.mp hz
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat]
    using hh

/-- The residual cannot vanish identically, including when either good-prime
Hecke eigenvalue is zero. -/
theorem original_residual_not_identically_zero {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    ∃ z : ℂ, residual f k z≠0 := by
  refine ⟨(((k:ℝ)/2+1:ℝ):ℂ),?_⟩
  intro hz
  have h := original_residual_central hf hz
  simp only [Complex.ofReal_re] at h
  linarith

/-- Once the finite row certificate shows that the residual kills the whole
leading vector, its nonzero value forces the pole onto the central line. -/
theorem central_of_residual_kernel {ι : Type*} {k : ℕ} {f : ℕ → ℂ} {z : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) (v : ι → ℂ) (hv : v≠0)
    (hrow : ∀ i, residual f k z*v i=0) : z.re=(k:ℝ)/2 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  apply original_residual_central hf
  exact (mul_eq_zero.mp (hrow i)).resolve_right hi

#print axioms badProduct_norm
#print axioms residual_cpow
#print axioms residual_analytic
#print axioms original_residual_central
#print axioms original_residual_not_identically_zero
#print axioms central_of_residual_kernel

}

end SmallLevelThirtyFivePole
end
end
