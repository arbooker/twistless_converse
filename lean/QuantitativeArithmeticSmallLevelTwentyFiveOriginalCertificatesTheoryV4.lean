module

public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModelTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveFullPlusFirstTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveOriginalRowEvaluationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates
open Complex Matrix QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

def rowIndex (i : Fin 4518) : FullPlusFirst.RowIndex :=
  if h : i.val<4450 then .inl ⟨i.val,h⟩ else .inr ⟨i.val-4450,by omega⟩

def physicalEval (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (v : ℕ → ℂ) (p : Poly) : ℂ :=
  eval (primeParameter 2 m s) (primeParameter 3 m s)
    (primeParameter 5 m s) (primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7) v p

def actualJet (i : ℕ) : Poly :=
  if h : i<4450 then normalizedPoly (rawFirstJetPoly 1 (FullPlusFirst.sourceRow ⟨i,h⟩)) else []

theorem source_evaluation {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε s : ℂ) (hχ : ε*I^(2*m)=1) (v : Fin 1050 → ℂ) (i : Fin 4518) :
    physicalEval m f s (periodicVector v) (FullPlusLeading.source i.val)=
      (FullPlusFirst.leadingMatrix m f ε s *ᵥv) (rowIndex i) := by
  rw [FullPlusFirst.leadingMatrix,augmentedMatrix_mulVec]
  by_cases hip : i.val<4450
  · have hp := AuxPlusLaurent.all_actual_source ⟨i.val,by omega⟩
    rw [FullPlusLeading.source_physical ⟨i.val,hip⟩] at hp
    have hn (p : ℕ) (hp0 : p≠0) : primeParameter p m s≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp0))
    have he := eval_rawSourcePoly (FullPlusFirst.sourceRow ⟨i.val,hip⟩) hf ε s 1
      (by simpa using hχ) v
    rw [← eval_normalizedPoly _ _ _ _ _ _ _ _ (hn 2 (by decide)) (hn 3 (by decide))
      (hn 5 (by decide)) (hn 7 (by decide))] at he
    change normalizedPoly (rawSourcePoly 1 (FullPlusFirst.sourceRow ⟨i.val,hip⟩))=
      AuxPlusLaurent.source i.val at hp
    rw [hp] at he
    simpa only [physicalEval,FullPlusLeading.source,ite_eq_left hip,rowIndex,dite_eq_left hip,
      augmentedLeading,Sum.elim_inl] using he
  · simp only [physicalEval,FullPlusLeading.source,ite_eq_right hip,rowIndex,dite_eq_right hip,
      augmentedLeading,Sum.elim_inr,eval,monomial,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Rat.cast_one,zpow_zero,pow_zero,mul_one,one_mul,add_zero]
    rw [FullPlusLeading.gauge_coordinate ⟨i.val-4450,by omega⟩,periodicVector_fin]

theorem lower_source_evaluation {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε s : ℂ) (hχ : ε*I^(2*m)=1) (v : Fin 1050 → ℂ) (i : Fin 4518) :
    physicalEval m f s (periodicVector v) (lowerPoly (FullPlusLeading.source i.val))=
      (FullPlusFirst.leadingMatrix m f ε (s-1) *ᵥv) (rowIndex i) := by
  unfold physicalEval
  rw [eval_lowerPoly_physical]
  exact source_evaluation hf ε (s-1) hχ v i

theorem first_shift_evaluation (m : ℕ) (f : ℕ → ℂ)
    (ε s : ℂ) (hχ : ε*I^(2*m)=1) (v : Fin 1050 → ℂ) (i : Fin 4518) :
    (FullPlusFirst.shiftMatrix m f ε 0 (s-1) *ᵥv) (rowIndex i)=
      I*(s-((2*m:ℕ):ℂ))*physicalEval m f s (periodicVector v) (actualJet i.val) := by
  rw [FullPlusFirst.shiftMatrix,augmentedShiftMatrix_mulVec]
  by_cases hip : i.val<4450
  · have hn (p : ℕ) (hp0 : p≠0) : primeParameter p m s≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp0))
    have he := eval_rawFirstJetPoly (FullPlusFirst.sourceRow ⟨i.val,hip⟩) m f ε s 1
      (by simpa using hχ) v
    rw [← eval_normalizedPoly _ _ _ _ _ _ _ _ (hn 2 (by decide)) (hn 3 (by decide))
      (hn 5 (by decide)) (hn 7 (by decide))] at he
    simpa only [rowIndex,dite_eq_left hip,augmentedShifted,Sum.elim_inl,physicalEval,
      actualJet] using he
  · simp [rowIndex,hip,augmentedShifted,actualJet,physicalEval]

#print axioms source_evaluation
#print axioms lower_source_evaluation
#print axioms first_shift_evaluation
end QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveOriginalSyzygyMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates
open Complex Matrix QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

def indexNat (i : ℕ) : FullPlusFirst.RowIndex := rowIndex ⟨i%4518,Nat.mod_lt _ (by decide)⟩

def syzygyMatrix (O : Poly) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    Matrix Unit FullPlusFirst.RowIndex ℂ := fun _ r =>
  physicalEval m f (s+1) (fun j => (Pi.single r (1:ℂ) : FullPlusFirst.RowIndex → ℂ) (indexNat j)) O

theorem physicalEval_analytic (m : ℕ) (f : ℕ → ℂ) (s d : ℂ)
    (v : ℂ → ℕ → ℂ) (p : Poly)
    (hv : ∀ j,AnalyticAt ℂ (fun z => v z j) s) :
    AnalyticAt ℂ (fun z => physicalEval m f (z+d) (v z) p) s := by
  have hpa (q : ℕ) (hq : q≠0) : AnalyticAt ℂ (fun z => primeParameter q m (z+d)) s := by
    unfold primeParameter
    simp_rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq : (q:ℂ)≠0)]
    fun_prop
  have hpn (q : ℕ) (hq : q≠0) : primeParameter q m (s+d)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hq))
  exact eval_analytic _ _ _ _ _ _ _ _ v p
    (hpa 2 (by decide)) (hpa 3 (by decide)) (hpa 5 (by decide)) (hpa 7 (by decide))
    (hpn 2 (by decide)) (hpn 3 (by decide)) (hpn 5 (by decide)) (hpn 7 (by decide)) hv

theorem syzygyMatrix_analytic (O : Poly) (m : ℕ) (f : ℕ → ℂ)
    (s : ℂ) (u : Unit) (r : FullPlusFirst.RowIndex) :
    AnalyticAt ℂ (fun z => syzygyMatrix O m f z u r) s :=
  physicalEval_analytic m f s 1 _ O (fun _ => analyticAt_const)

theorem syzygyMatrix_lower_zero (O : Poly)
    (hO : ∀ t ∈ O,t.2.1<4518)
    {m : ℕ} {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε s : ℂ) (hχ : ε*I^(2*m)=1)
    (hker : ∀ v : Fin 1050 → ℂ,
      physicalEval m f (s+1) (fun j => physicalEval m f (s+1)
        (periodicVector v) (lowerPoly (FullPlusLeading.source j))) O=0) :
    syzygyMatrix O m f s * FullPlusFirst.leadingMatrix m f ε s=0 := by
  classical
  ext u j
  cases u
  let v : Fin 1050 → ℂ := Pi.single j 1
  have he : physicalEval m f (s+1) (fun n => physicalEval m f (s+1)
      (periodicVector v) (lowerPoly (FullPlusLeading.source n))) O=
      physicalEval m f (s+1) (fun n =>
        (FullPlusFirst.leadingMatrix m f ε s *ᵥv) (indexNat n)) O := by
    apply eval_congr_support
    intro t ht
    have h := lower_source_evaluation hf ε (s+1) hχ v ⟨t.2.1,hO t ht⟩
    simpa only [indexNat,Nat.mod_eq_of_lt (hO t ht),add_sub_cancel_right] using h
  have hh := hker v
  rw [he] at hh
  have hm : FullPlusFirst.leadingMatrix m f ε s *ᵥv=
      fun r => FullPlusFirst.leadingMatrix m f ε s r j := by
    funext r
    simp [v,Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [hm] at hh
  have hfin := eval_finite_coordinates (ι := FullPlusFirst.RowIndex) indexNat
    (primeParameter 2 m (s+1)) (primeParameter 3 m (s+1))
    (primeParameter 5 m (s+1)) (primeParameter 7 m (s+1))
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
    (fun r : FullPlusFirst.RowIndex => FullPlusFirst.leadingMatrix m f ε s r j) O
  change (∑ r,physicalEval m f (s+1)
    (fun n => (Pi.single r (1:ℂ) : FullPlusFirst.RowIndex → ℂ) (indexNat n)) O*
      FullPlusFirst.leadingMatrix m f ε s r j)=0
  exact hfin.symm.trans hh

#print axioms physicalEval_analytic
#print axioms syzygyMatrix_analytic
#print axioms syzygyMatrix_lower_zero
end QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveOriginalSyzygyFirstShiftV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates
open Complex Matrix QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

def jetFunctional (O : Poly) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (v : Fin 1050 → ℂ) : ℂ :=
  physicalEval m f s (fun j => physicalEval m f s (periodicVector v) (actualJet j)) O

def syzygyJetMatrix (O : Poly) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    Matrix Unit (Fin 1050) ℂ := fun _ j => I*jetFunctional O m f s (Pi.single j 1)

theorem jetFunctional_substitute (O : Poly) (m : ℕ) (f : ℕ → ℂ)
    (s : ℂ) (v : Fin 1050 → ℂ) :
    jetFunctional O m f s v=physicalEval m f s (periodicVector v) (substitute actualJet O) := by
  have hn (q : ℕ) (hq : q≠0) : primeParameter q m s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hq))
  unfold jetFunctional physicalEval
  exact (eval_substitute _ _ _ _ _ _ _ _ (hn 2 (by decide)) (hn 3 (by decide))
    (hn 5 (by decide)) (hn 7 (by decide)) actualJet O).symm

theorem syzygyJetMatrix_analytic (O : Poly) (m : ℕ) (f : ℕ → ℂ)
    (s : ℂ) (u : Unit) (j : Fin 1050) :
    AnalyticAt ℂ (fun z => syzygyJetMatrix O m f z u j) s := by
  apply AnalyticAt.mul analyticAt_const
  have h := physicalEval_analytic m f s 0
    (fun z n => physicalEval m f z (periodicVector (Pi.single j 1)) (actualJet n)) O
    (fun n => by
      simpa only [add_zero] using
        physicalEval_analytic m f s 0 (fun _ => periodicVector (Pi.single j 1))
          (actualJet n) (fun _ => analyticAt_const))
  simpa only [add_zero,jetFunctional] using h

theorem syzygyJetMatrix_mulVec (O : Poly) (m : ℕ) (f : ℕ → ℂ)
    (s : ℂ) (v : Fin 1050 → ℂ) :
    (syzygyJetMatrix O m f s *ᵥv) ()=I*jetFunctional O m f s v := by
  classical
  have he : jetFunctional O m f s v=
      ∑ j,jetFunctional O m f s (Pi.single j 1)*v j := by
    simp_rw [jetFunctional_substitute]
    exact eval_finite_coordinates (fun n => (⟨n%1050,Nat.mod_lt _ (by decide)⟩ : Fin 1050))
      _ _ _ _ _ _ _ v (substitute actualJet O)
  calc
    (syzygyJetMatrix O m f s *ᵥv) ()=
        ∑ j,(I*jetFunctional O m f s (Pi.single j 1))*v j := rfl
    _=I*(∑ j,jetFunctional O m f s (Pi.single j 1)*v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=I*jetFunctional O m f s v := by rw [← he]

theorem syzygyMatrix_first_shift_factor (O : Poly)
    (hO : ∀ t ∈ O,t.2.1<4518)
    (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (hχ : ε*I^(2*m)=1) :
    syzygyMatrix O m f (s-1)*FullPlusFirst.shiftMatrix m f ε 0 (s-1)=
      (s-((2*m:ℕ):ℂ)) • syzygyJetMatrix O m f s := by
  classical
  ext u j
  cases u
  let v : Fin 1050 → ℂ := Pi.single j 1
  have hm : FullPlusFirst.shiftMatrix m f ε 0 (s-1) *ᵥv=
      fun r => FullPlusFirst.shiftMatrix m f ε 0 (s-1) r j := by
    funext r
    simp [v,Matrix.mulVec,dotProduct,Pi.single_apply]
  have he : physicalEval m f s (fun n =>
      (FullPlusFirst.shiftMatrix m f ε 0 (s-1) *ᵥv) (indexNat n)) O=
      I*(s-((2*m:ℕ):ℂ))*jetFunctional O m f s v := by
    calc
      _=physicalEval m f s (fun n => I*(s-((2*m:ℕ):ℂ))*
          physicalEval m f s (periodicVector v) (actualJet n)) O := by
        apply eval_congr_support
        intro t ht
        have h := first_shift_evaluation m f ε s hχ v ⟨t.2.1,hO t ht⟩
        simpa only [indexNat,Nat.mod_eq_of_lt (hO t ht)] using h
      _=I*(s-((2*m:ℕ):ℂ))*jetFunctional O m f s v :=
        eval_smul _ _ _ _ _ _ _ _ _ O
  rw [hm] at he
  have hfin := eval_finite_coordinates indexNat
    (primeParameter 2 m s) (primeParameter 3 m s)
    (primeParameter 5 m s) (primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
    (fun r => FullPlusFirst.shiftMatrix m f ε 0 (s-1) r j) O
  change physicalEval m f s (fun n => FullPlusFirst.shiftMatrix m f ε 0 (s-1) (indexNat n) j) O=
    ∑ r,physicalEval m f s (fun n => (Pi.single r (1:ℂ) : FullPlusFirst.RowIndex → ℂ) (indexNat n)) O*
      FullPlusFirst.shiftMatrix m f ε 0 (s-1) r j at hfin
  rw [hfin] at he
  change (∑ r,syzygyMatrix O m f (s-1) () r*FullPlusFirst.shiftMatrix m f ε 0 (s-1) r j)=
    (s-((2*m:ℕ):ℂ))*(I*jetFunctional O m f s v)
  simpa only [syzygyMatrix,sub_add_cancel,mul_assoc,mul_comm I] using he

#print axioms jetFunctional_substitute
#print axioms syzygyJetMatrix_analytic
#print axioms syzygyJetMatrix_mulVec
#print axioms syzygyMatrix_first_shift_factor
end QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveOriginalSyzygyConsequencesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates
open Complex Matrix QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector

theorem allowed_jet_zero
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=1) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge AuxPlusLaurent.basis
      AuxPlusLaurent.freeCoordinate m f z (gridVector 1050 (2*m) f z))
    (O : Poly) (hO : ∀ t ∈ O,t.2.1<4518)
    (hker : ∀ z (v : Fin 1050 → ℂ),
      physicalEval m f (z+1) (fun j => physicalEval m f (z+1)
        (periodicVector v) (lowerPoly (FullPlusLeading.source j))) O=0)
    (s : ℂ) (v : Fin 1050 → ℂ)
    (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ,0<n → (s+n)≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hweight : ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ))
    (hs : s≠((2*m:ℕ):ℂ)) : jetFunctional O m f s v=0 := by
  have hz := FullPlusFirst.original_first_shift_allowed hm hf ε hε hlaw hχ BG G hG hGF
    (syzygyMatrix O m f) (syzygyMatrix_analytic O m f)
    (fun z => syzygyMatrix_lower_zero O hO hf ε z hχ (hker z)) s v hv hshift hweight
  rw [syzygyMatrix_first_shift_factor O hO m f ε s hχ, Matrix.smul_mulVec] at hz
  have hh := congrFun hz ()
  change (s-((2*m:ℕ):ℂ))*((syzygyJetMatrix O m f s *ᵥv) ())=0 at hh
  rw [syzygyJetMatrix_mulVec] at hh
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hs))).resolve_left
    Complex.I_ne_zero

theorem regularized_jet_zero
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=1) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge AuxPlusLaurent.basis
      AuxPlusLaurent.freeCoordinate m f z (gridVector 1050 (2*m) f z))
    (O : Poly) (hO : ∀ t ∈ O,t.2.1<4518)
    (hker : ∀ z (v : Fin 1050 → ℂ),
      physicalEval m f (z+1) (fun j => physicalEval m f (z+1)
        (periodicVector v) (lowerPoly (FullPlusLeading.source j))) O=0)
    (s : ℂ) (v : Fin 1050 → ℂ)
    (hv : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*G z j) s v)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    jetFunctional O m f s v=0 := by
  have hz := FullPlusFirst.original_regularized_first_shift hm hf ε hε hlaw hχ BG G hG hGF
    (syzygyMatrix O m f) (syzygyMatrix_analytic O m f)
    (fun z => syzygyMatrix_lower_zero O hO hf ε z hχ (hker z))
    s v hv hshift (syzygyJetMatrix O m f) (syzygyJetMatrix_analytic O m f s)
    (fun z r j => by
      have hh := congrFun (congrFun (syzygyMatrix_first_shift_factor O hO m f ε z hχ) r) j
      exact hh)
  have hh := congrFun hz ()
  rw [syzygyJetMatrix_mulVec] at hh
  exact (mul_eq_zero.mp hh).resolve_left Complex.I_ne_zero

#print axioms allowed_jet_zero
#print axioms regularized_jet_zero
end QuantitativeArithmeticSmallLevelTwentyFive.OriginalCertificates
end
end
