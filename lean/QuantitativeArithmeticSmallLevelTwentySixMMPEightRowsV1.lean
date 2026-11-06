module
public import QuantitativeArithmeticSmallLevelTwentySixMMPOriginalChartV1
public import QuantitativeArithmeticSmallLevelTwentySixMMPOriginalConstraintFamilyV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPEightRows
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixGermDAG (replayVector)
open QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive SmallLevelTwentySixMMPPari
open QuantitativeArithmeticSmallLevelTwentySixMMPOriginalChart

def extraRows : Fin 3 → Poly := ![primitiveRows 5, constraint6Row, constraint7Row]
def eightRows (i : Fin 8) : Poly :=
  if h : i.val<5 then primitiveRows ⟨i.val, by omega⟩ else extraRows ⟨i.val-5, by omega⟩

theorem extra_support (i : Fin 3) : ∀ t,t∈extraRows i → t.2.1=0 ∨ t.2.1=1 := by
  fin_cases i
  · decide +kernel
  · exact constraint6_support
  · exact constraint7_support

/-- Eight simultaneous polynomial equations forced by an original pole.
The projective parameter is shared by all rows, including both syzygies.
No polynomial equation or bound on lower-layer pole orders is assumed. -/
theorem original_eight_rows {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (s u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0) :
    ∃ θ : ℂ,∀ i : Fin 8,eval
      (u*parameter 2 m s) ((parameter 3 m s)^2)
      (v*parameter 13 m s) ((parameter 5 m s)^2)
      (badParameter f 3*parameter 3 m s) (badParameter f 5*parameter 5 m s)
      1 (fun j => if j=0 then 1 else θ) (eightRows i)=0 := by
  have hg : ∀ i,HasAnalyticGerm (fun z => eval
      (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) (extraRows i)) s := by
    intro i
    fin_cases i
    · exact signed_original_primitive_germs S s u v hu hv hshift hs hs1 hη hs2 hs13 5
    · exact QuantitativeArithmeticSmallLevelTwentySixMMPOriginalConstraint6.signed_original_constraint_germ
        S s u v hu hv hshift hs hs1 hη hs2 hs13
    · exact QuantitativeArithmeticSmallLevelTwentySixMMPOriginalConstraint7.signed_original_constraint_germ
        S s u v hu hv hshift hs hs1 hη hs2 hs13
  obtain ⟨θ,hθ⟩ := original_first_chart S T s u v hu hv hshift hs hs1 hη hs2 hs13
    hpole extraRows extra_support hg
  refine ⟨θ,fun i => ?_⟩
  by_cases hi : i.val<5
  · simpa only [eightRows, dite_eq_left hi, augmentedRows, Sum.elim_inl] using
      hθ (Sum.inl ⟨i.val,hi⟩)
  · simpa only [eightRows, dite_eq_right hi, augmentedRows, Sum.elim_inr] using
      hθ (Sum.inr ⟨i.val-5, by omega⟩)

/-- Scalar form of the same simultaneous system, for polynomial elimination. -/
theorem original_scalar_system {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (s u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0) :
    let x := u*parameter 2 m s
    let y := (parameter 3 m s)^2
    let z := v*parameter 13 m s
    let w := (parameter 5 m s)^2
    let a := badParameter f 3*parameter 3 m s
    let b := badParameter f 5*parameter 5 m s
    ∃ θ : ℂ,
      (∀ i : Fin 6,eval x y z w a b 1 (fun j => if j=0 then 1 else θ)
        (primitiveRows ⟨i.val,by omega⟩)=0) ∧
      constraint6 x y z w a b (fun j => if j=0 then 1 else θ)=0 ∧
      constraint7 x y z w a b (fun j => if j=0 then 1 else θ)=0 := by
  dsimp only
  obtain ⟨θ,hθ⟩ := original_eight_rows S T s u v hu hv hshift hs hs1 hη hs2 hs13 hpole
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hx := mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s)
  have hy := pow_ne_zero 2 (parameter_ne_zero 3 m (by decide) s)
  have hz := mul_ne_zero hv0 (parameter_ne_zero 13 m (by decide) s)
  have hw := pow_ne_zero 2 (parameter_ne_zero 5 m (by decide) s)
  refine ⟨θ,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact hθ 0
    · exact hθ 1
    · exact hθ 2
    · exact hθ 3
    · exact hθ 4
    · exact hθ 5
  · have h := hθ 6
    change eval _ _ _ _ _ _ 1 _ constraint6Row=0 at h
    rw [QuantitativeArithmeticSmallLevelTwentySixMMPConstraint6Eval.constraint6_eval _ _ _ _ _ _ _ hx hy hz hw] at h
    exact h
  · have h := hθ 7
    change eval _ _ _ _ _ _ 1 _ constraint7Row=0 at h
    rw [QuantitativeArithmeticSmallLevelTwentySixMMPConstraint7Eval.constraint7_eval _ _ _ _ _ _ _ hx hy hz hw] at h
    exact h

#print axioms original_scalar_system
#print axioms extra_support
#print axioms original_eight_rows
end QuantitativeArithmeticSmallLevelTwentySixMMPEightRows
