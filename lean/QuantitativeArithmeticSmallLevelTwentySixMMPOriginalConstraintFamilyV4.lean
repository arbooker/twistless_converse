module
public import QuantitativeArithmeticSmallLevelTwentySixMMPConstraintIndexEvalSeriesV4
public import QuantitativeArithmeticSmallLevelTwentySixMMPPrimitiveTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixMMPSyzygyGermFamilyV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

namespace QuantitativeArithmeticSmallLevelTwentySixMMPOriginalConstraint6
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixGermDAG (replayVector)
open QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive SmallLevelTwentySixMMPPari

/-- The sparse constraint is an analytic germ of the original continued
functions. Its multiplier may vanish: the proof only multiplies and subtracts
analytic germs and never divides by the syzygy multiplier. -/
theorem signed_original_constraint_germ {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (s u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v) :
    HasAnalyticGerm (fun z => eval
      (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) constraint6Row) s := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have h := QuantitativeArithmeticSmallLevelTwentySixMMPSyzygyGerm6.constraint_germ
    (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
    (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
    (fun z => badParameter f 3*parameter 3 m z)
    (fun z => badParameter f 5*parameter 5 m z) (replayVector m S.G) s
    (analyticAt_const.mul (parameter_analytic 2 m (by decide) s))
    ((parameter_analytic 3 m (by decide) s).pow 2)
    (analyticAt_const.mul (parameter_analytic 13 m (by decide) s))
    ((parameter_analytic 5 m (by decide) s).pow 2)
    (analyticAt_const.mul (parameter_analytic 3 m (by decide) s))
    (analyticAt_const.mul (parameter_analytic 5 m (by decide) s))
    (signed_original_primitive_germs S s u v hu hv hshift hs hs1 hη hs2 hs13)
  apply h.congr
  apply Filter.Eventually.of_forall
  intro z
  exact (QuantitativeArithmeticSmallLevelTwentySixMMPConstraint6Eval.constraint6_eval _ _ _ _ _ _ _
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) z))
    (pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) z))
    (mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) z))
    (pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) z))).symm

#print axioms signed_original_constraint_germ
end QuantitativeArithmeticSmallLevelTwentySixMMPOriginalConstraint6
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

namespace QuantitativeArithmeticSmallLevelTwentySixMMPOriginalConstraint7
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixGermDAG (replayVector)
open QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive SmallLevelTwentySixMMPPari

/-- The sparse constraint is an analytic germ of the original continued
functions. Its multiplier may vanish: the proof only multiplies and subtracts
analytic germs and never divides by the syzygy multiplier. -/
theorem signed_original_constraint_germ {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (s u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v) :
    HasAnalyticGerm (fun z => eval
      (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) constraint7Row) s := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have h := QuantitativeArithmeticSmallLevelTwentySixMMPSyzygyGerm7.constraint_germ
    (fun z => u*parameter 2 m z) (fun z => (parameter 3 m z)^2)
    (fun z => v*parameter 13 m z) (fun z => (parameter 5 m z)^2)
    (fun z => badParameter f 3*parameter 3 m z)
    (fun z => badParameter f 5*parameter 5 m z) (replayVector m S.G) s
    (analyticAt_const.mul (parameter_analytic 2 m (by decide) s))
    ((parameter_analytic 3 m (by decide) s).pow 2)
    (analyticAt_const.mul (parameter_analytic 13 m (by decide) s))
    ((parameter_analytic 5 m (by decide) s).pow 2)
    (analyticAt_const.mul (parameter_analytic 3 m (by decide) s))
    (analyticAt_const.mul (parameter_analytic 5 m (by decide) s))
    (signed_original_primitive_germs S s u v hu hv hshift hs hs1 hη hs2 hs13)
  apply h.congr
  apply Filter.Eventually.of_forall
  intro z
  exact (QuantitativeArithmeticSmallLevelTwentySixMMPConstraint7Eval.constraint7_eval _ _ _ _ _ _ _
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) z))
    (pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) z))
    (mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) z))
    (pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) z))).symm

#print axioms signed_original_constraint_germ
end QuantitativeArithmeticSmallLevelTwentySixMMPOriginalConstraint7
end
