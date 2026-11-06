module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSymbolicEvaluationV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

def freeArgument (free : Fin 68 → Fin 1050) (v : Fin 1050 → ℂ) (j : ℕ) : ℂ :=
  v (free ⟨j%68,Nat.mod_lt _ (by decide)⟩)

def sparseGauge (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (x y z w a b c : ℂ) (v : Fin 1050 → ℂ) (j : Fin 1050) : ℂ :=
  v j-eval x y z w a b c (freeArgument free v) (basis j.val)

theorem periodic_sparseGauge (basis : ℕ → Poly)
    (hperiodic : ∀ j, basis (j%1050)=basis j) (free : Fin 68 → Fin 1050)
    (x y z w a b c : ℂ) (v : Fin 1050 → ℂ) (j : ℕ) :
    periodicVector (sparseGauge basis free x y z w a b c v) j=
      periodicVector v j-eval x y z w a b c (freeArgument free v) (basis j) := by
  simp only [periodicVector,sparseGauge,hperiodic]

theorem sparseGauge_free (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hb : ∀ j, basis (free j).val=unitPoly j.val)
    (x y z w a b c : ℂ) (v : Fin 1050 → ℂ) (j : Fin 68) :
    sparseGauge basis free x y z w a b c v (free j)=0 := by
  rw [sparseGauge,hb,eval_unitPoly]
  simp [freeArgument,Nat.mod_eq_of_lt j.isLt]

theorem sparseGauge_old (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hb : ∀ j : Fin 150, basis (7*j.val)=[])
    (x y z w a b c : ℂ) (v : Fin 1050 → ℂ) (j : Fin 150) :
    sparseGauge basis free x y z w a b c v ⟨7*j.val,by omega⟩=v ⟨7*j.val,by omega⟩ := by
  simp only [sparseGauge,hb,eval_nil,sub_zero]

/-- A checked polynomial identity preserves the associated sparse row after
removing the free component. The basis is extended periodically so no implicit
support assumption is required in this argument. -/
theorem sparseGauge_row (basis : ℕ → Poly)
    (hperiodic : ∀ j, basis (j%1050)=basis j) (free : Fin 68 → Fin 1050)
    (x y z w a b c : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (v : Fin 1050 → ℂ) (p q : Poly) (hpoly : normalizedPoly p=q)
    (hzero : substitute basis q=[]) :
    eval x y z w a b c (periodicVector (sparseGauge basis free x y z w a b c v)) p=
      eval x y z w a b c (periodicVector v) p := by
  rw [← eval_normalizedPoly x y z w a b c _ hx hy hz hw p,hpoly]
  rw [← eval_normalizedPoly x y z w a b c (periodicVector v) hx hy hz hw p,hpoly]
  have hg : periodicVector (sparseGauge basis free x y z w a b c v)=
      fun j => periodicVector v j-eval x y z w a b c (freeArgument free v) (basis j) :=
    funext (periodic_sparseGauge basis hperiodic free x y z w a b c v)
  rw [hg]
  exact gauge_source x y z w a b c (periodicVector v) (freeArgument free v)
    hx hy hz hw basis q hzero

private theorem parameter_nonzero (p m : ℕ) (hp : p≠0) (s : ℂ) : primeParameter p m s≠0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))

def physicalGauge (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (v : Fin 1050 → ℂ) : Fin 1050 → ℂ :=
  sparseGauge basis free (primeParameter 2 m s) (primeParameter 3 m s)
    (primeParameter 5 m s) (primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7) v

theorem physicalGauge_leading (basis : ℕ → Poly)
    (hperiodic : ∀ j, basis (j%1050)=basis j) (free : Fin 68 → Fin 1050)
    (r : SourceRow) {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε s : ℂ) (χ : ℚ) (hχ : ε*I^(2*m)=(χ:ℂ))
    (v : Fin 1050 → ℂ) (p : Poly)
    (hpoly : normalizedPoly (rawSourcePoly χ r)=p) (hzero : substitute basis p=[]) :
    sourceLeading r m f ε s (physicalGauge basis free m f s v)=sourceLeading r m f ε s v := by
  rw [← eval_rawSourcePoly r hf ε s χ hχ,← eval_rawSourcePoly r hf ε s χ hχ]
  exact sparseGauge_row basis hperiodic free _ _ _ _ _ _ _
    (parameter_nonzero 2 m (by decide) s) (parameter_nonzero 3 m (by decide) s)
    (parameter_nonzero 5 m (by decide) s) (parameter_nonzero 7 m (by decide) s)
    v (rawSourcePoly χ r) p hpoly hzero

/-- The gauge cancels every higher Taylor source at its shifted argument. -/
theorem physicalGauge_shifted (basis : ℕ → Poly)
    (hperiodic : ∀ j, basis (j%1050)=basis j) (free : Fin 68 → Fin 1050)
    (r : SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s t : ℂ)
    (v : Fin 1050 → ℂ) (p : Poly)
    (hpoly : normalizedPoly (rawTailPoly r)=p) (hzero : substitute basis p=[]) :
    sourceShifted r m f ε n s (physicalGauge basis free m f t v)=sourceShifted r m f ε n s v := by
  rw [eval_rawTailPoly r m f ε n s (primeParameter 2 m t) (primeParameter 3 m t)
    (primeParameter 5 m t) (primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)]
  rw [eval_rawTailPoly r m f ε n s (primeParameter 2 m t) (primeParameter 3 m t)
    (primeParameter 5 m t) (primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)]
  congr 1
  exact sparseGauge_row basis hperiodic free _ _ _ _ _ _ _
    (parameter_nonzero 2 m (by decide) t) (parameter_nonzero 3 m (by decide) t)
    (parameter_nonzero 5 m (by decide) t) (parameter_nonzero 7 m (by decide) t)
    v (rawTailPoly r) p hpoly hzero

private theorem parameter_analytic (p m : ℕ) (hp : p≠0) (s : ℂ) :
    AnalyticAt ℂ (primeParameter p m) s := by
  unfold primeParameter
  simp_rw [Complex.cpow_def_of_ne_zero (show (p:ℂ)≠0 by exact_mod_cast hp)]
  fun_prop

theorem physicalGauge_analytic (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (F : ℂ → Fin 1050 → ℂ)
    (hF : ∀ j, AnalyticAt ℂ (fun z => F z j) s) (j : Fin 1050) :
    AnalyticAt ℂ (fun z => physicalGauge basis free m f z (F z) j) s := by
  apply (hF j).sub
  apply eval_analytic
    (primeParameter 2 m) (primeParameter 3 m) (primeParameter 5 m) (primeParameter 7 m)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7) s
    (fun z => freeArgument free (F z)) (basis j.val)
    (parameter_analytic 2 m (by decide) s) (parameter_analytic 3 m (by decide) s)
    (parameter_analytic 5 m (by decide) s) (parameter_analytic 7 m (by decide) s)
    (parameter_nonzero 2 m (by decide) s) (parameter_nonzero 3 m (by decide) s)
    (parameter_nonzero 5 m (by decide) s) (parameter_nonzero 7 m (by decide) s)
  exact fun i => hF _

#print axioms physicalGauge_leading
#print axioms physicalGauge_shifted
#print axioms physicalGauge_analytic
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
