module

public import QuantitativeArithmeticSmallLevelTwentySevenPoleExtraHeckeV1
public import QuantitativeArithmeticSmallLevelTwentySevenSourceDispatchTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenPoleSource. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenPoleFamilyV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPoleSource
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenObservation (factorMatrix basisMatrix)
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point originalVector)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource (basisValues basisValues_original)
open QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch (physicalEval kindCoefficient kindCoefficient_analytic kindShift kindShift_action weighted_factor family_with_extra_ramanujan)
open QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource (heckePoly ramanujanSpec ramanujanCoefficient ramanujanObservation ramanujan_shift_factor ramanujan_coefficient_analytic extraPoly2 extraOriginal2 hecke_original)

inductive Kind where
  | old (r : QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.Kind)
  | hecke (i : Fin 17)
  | ramanujan (i : Fin 4)
  | entire

def sourceRow (r : Kind) (m : ℕ) (f : ℕ → ℂ) (η s : ℂ) : ℂ :=
  match r with
  | .old t => QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.row t m f η s
  | .hecke i => physicalEval (heckePoly i) m f s
  | .ramanujan i => QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.leading (ramanujanSpec i) m η s
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) s)
  | .entire => physicalEval extraPoly2 m f s

def sourceShift (r : Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) : ℂ :=
  match r with
  | .old t => kindShift t m η n s v
  | .ramanujan i => QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.shift (ramanujanSpec i) m η n s v
  | _ => 0

def sourceCoefficient (r : Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (j : Fin 321) : ℂ :=
  match r with
  | .old t => kindCoefficient t m η n s j
  | .ramanujan i => ramanujanCoefficient i m η n s*factorMatrix (ramanujanObservation i) j
  | _ => 0

theorem sourceCoefficient_analytic (r : Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (j : Fin 321) :
    AnalyticAt ℂ (fun z => sourceCoefficient r m η n z j) s := by
  cases r with
  | old t => exact kindCoefficient_analytic t m η n s j
  | hecke i => exact analyticAt_const
  | entire => exact analyticAt_const
  | ramanujan i => exact (ramanujan_coefficient_analytic i m η n s).mul analyticAt_const

theorem sourceShift_action (r : Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) :
    (∑ j : Fin 321, sourceCoefficient r m η n s j*basisValues v j)=sourceShift r m η n s v := by
  cases r with
  | old t => exact kindShift_action t m η n s v
  | hecke i => simp [sourceCoefficient,sourceShift]
  | entire => simp [sourceCoefficient,sourceShift]
  | ramanujan i =>
    change (∑ j : Fin 321, (ramanujanCoefficient i m η n s*factorMatrix (ramanujanObservation i) j)*basisValues v j)=_
    rw [weighted_factor]
    exact (ramanujan_shift_factor i m η n s v).symm

/-- All old rows and all22 additional rows follow from the original input,
with the same sign and uniform half-plane. -/
theorem original_family (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ (η : ℂ) (B : ℝ) (error : Kind → ℕ → ℂ → ℂ),
      (η=1 ∨ η= -1) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (error r M) s) ∧
      ∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B<s.re → sourceRow r m f η s=error r M s+
        ∑ n∈Finset.range M, sourceShift r m η n s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1))) := by
  obtain ⟨η,B0,E0,ER,hη,ha0,hr0,haR,hrR⟩ := family_with_extra_ramanujan m hm hf
  obtain ⟨BH,hH⟩ := hecke_original m hm hf
  obtain ⟨BE,EE,haE,hrE⟩ := extraOriginal2 m hm hf
  let B := max B0 (max BH BE)
  have h0 : B0≤B := le_max_left _ _
  have hH' : BH≤B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hE' : BE≤B := le_trans (le_max_right _ _) (le_max_right _ _)
  let err : Kind → ℕ → ℂ → ℂ := fun r M s =>
    match r with
    | .old t => E0 t M s
    | .hecke _ => 0
    | .ramanujan i => ER i M s
    | .entire => EE s
  refine ⟨η,B,err,hη,?_,?_⟩
  · intro r M s hs
    cases r with
    | old t => exact ha0 t M s (by linarith)
    | hecke i => exact analyticAt_const
    | ramanujan i => exact haR i M s (by linarith)
    | entire => exact haE.analyticAt s
  · intro r M s hs
    cases r with
    | old t => exact hr0 t M s (lt_of_le_of_lt h0 hs)
    | hecke i =>
      simpa only [sourceRow,sourceShift,err,Finset.sum_const_zero,add_zero] using hH i s (lt_of_le_of_lt hH' hs)
    | ramanujan i => exact hrR i M s (lt_of_le_of_lt h0 hs)
    | entire =>
      simpa only [sourceRow,sourceShift,err,Finset.sum_const_zero,add_zero] using hrE s (lt_of_le_of_lt hE' hs)

def selectedRows {d : ℕ} (selection : Fin d → Kind) (m : ℕ) (f : ℕ → ℂ) (η s : ℂ) : Fin d → ℂ :=
  fun i => sourceRow (selection i) m f η s

def selectedCoefficient {d : ℕ} (selection : Fin d → Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin d) (Fin 321) ℂ :=
  fun i => sourceCoefficient (selection i) m η n s

theorem selected_shift_action {d : ℕ} (selection : Fin d → Kind) (m : ℕ) (η : ℂ) (n : ℕ) (s : ℂ) (v : ℕ → ℂ) (i : Fin d) :
    (selectedCoefficient selection m η n s *ᵥ basisValues v) i=sourceShift (selection i) m η n s v :=
  sourceShift_action (selection i) m η n s v

theorem family_selection {d : ℕ} (selection : Fin d → Kind) (m : ℕ) (f : ℕ → ℂ)
    (η : ℂ) (B : ℝ) (error : Kind → ℕ → ℂ → ℂ)
    (hr : ∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B<s.re → sourceRow r m f η s=error r M s+
      ∑ n∈Finset.range M, sourceShift r m η n s
        (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1)))) :
    ∀ M : ℕ, ∀ s : ℂ, B<s.re → selectedRows selection m f η s=(fun i => error (selection i) M s)+
      ∑ n∈Finset.range M, selectedCoefficient selection m η n s *ᵥ
        (basisMatrix *ᵥ originalVector m f (s+((n:ℂ)+1))) := by
  intro M s hs
  funext i
  simp only [Pi.add_apply,Finset.sum_apply]
  simp_rw [← basisValues_original,selected_shift_action]
  exact hr (selection i) M s hs
#print axioms original_family
#print axioms family_selection
#print axioms sourceCoefficient_analytic
#print axioms sourceShift_action
end QuantitativeArithmeticSmallLevelTwentySevenPoleSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenPoleFamilyFixedSignV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPoleSource
open Matrix
open QuantitativeArithmeticSmallLevelTwentySevenObservation (factorMatrix basisMatrix)
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point originalVector)
open QuantitativeArithmeticSmallLevelTwentySevenShiftSource (basisValues basisValues_original)
open QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch (physicalEval kindCoefficient kindCoefficient_analytic kindShift kindShift_action weighted_factor family_with_extra_ramanujan)
open QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource (heckePoly ramanujanSpec ramanujanCoefficient ramanujanObservation ramanujan_shift_factor ramanujan_coefficient_analytic extraPoly2 extraOriginal2 hecke_original)

theorem family_at_sign (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hlaw : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.TaylorLaw point m f η) :
    ∃ (B : ℝ) (error : Kind → ℕ → ℂ → ℂ),
      (η=1 ∨ η= -1) ∧
      (∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (error r M) s) ∧
      ∀ r : Kind, ∀ M : ℕ, ∀ s : ℂ, B<s.re → sourceRow r m f η s=error r M s+
        ∑ n∈Finset.range M, sourceShift r m η n s
          (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s+((n:ℂ)+1))) := by
  obtain ⟨B0,E0,ER,_,ha0,hr0,haR,hrR⟩ := QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.family_with_ramanujan_extension_at_sign ramanujanSpec QuantitativeArithmeticSmallLevelTwentySevenPoleExtraSource.ramanujan_valid m hm hf η hη hlaw
  obtain ⟨BH,hH⟩ := hecke_original m hm hf
  obtain ⟨BE,EE,haE,hrE⟩ := extraOriginal2 m hm hf
  let B := max B0 (max BH BE)
  have h0 : B0≤B := le_max_left _ _
  have hH' : BH≤B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hE' : BE≤B := le_trans (le_max_right _ _) (le_max_right _ _)
  let err : Kind → ℕ → ℂ → ℂ := fun r M s =>
    match r with
    | .old t => E0 t M s
    | .hecke _ => 0
    | .ramanujan i => ER i M s
    | .entire => EE s
  refine ⟨B,err,hη,?_,?_⟩
  · intro r M s hs
    cases r with
    | old t => exact ha0 t M s (by linarith)
    | hecke i => exact analyticAt_const
    | ramanujan i => exact haR i M s (by linarith)
    | entire => exact haE.analyticAt s
  · intro r M s hs
    cases r with
    | old t => exact hr0 t M s (lt_of_le_of_lt h0 hs)
    | hecke i =>
      simpa only [sourceRow,sourceShift,err,Finset.sum_const_zero,add_zero] using hH i s (lt_of_le_of_lt hH' hs)
    | ramanujan i => exact hrR i M s (lt_of_le_of_lt h0 hs)
    | entire =>
      simpa only [sourceRow,sourceShift,err,Finset.sum_const_zero,add_zero] using hrE s (lt_of_le_of_lt hE' hs)

#print axioms family_at_sign
end QuantitativeArithmeticSmallLevelTwentySevenPoleSource
end
end
