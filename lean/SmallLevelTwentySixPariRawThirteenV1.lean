module
public import SmallLevelTwentySixGermThirteenTheoryV4
public import SmallLevelTwentySixPariRawSourceFamilyV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariRawThirteen
open QuantitativeArithmeticSevenLaurentRows

def rows (i : Fin 13) : Poly :=
  if i=11 then SmallLevelTwentySixPariRawSource87.rawData else
  if i=12 then SmallLevelTwentySixPariRawSource89.rawData else
  SmallLevelTwentySixGermThirteen.rows i

/-- The common normalized vector annihilates the rational source rows used
by the candidate elimination. The two denominator scales are certified. -/
theorem raw_rows_zero (x y z w a b u : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (h : ∀ i : Fin 13,eval x y z w a b 1 (fun j => if j=0 then 1 else u)
      (SmallLevelTwentySixGermThirteen.rows i)=0) :
    ∀ i : Fin 13,eval x y z w a b 1 (fun j => if j=0 then 1 else u) (rows i)=0 := by
  intro i
  by_cases h11 : i=11
  · subst i
    simp only [rows,ite_true]
    have hi:=h (11:Fin 13)
    rw [SmallLevelTwentySixGermThirteen.row_eleven] at hi
    exact SmallLevelTwentySixPariRawSource87.raw_zero_of_integer x y z w a b 1 _ hx hy hz hw hi
  by_cases h12 : i=12
  · subst i
    simp only [rows, show (12:Fin 13)≠11 from by decide, ite_false,ite_true]
    have hi:=h (12:Fin 13)
    rw [SmallLevelTwentySixGermThirteen.row_twelve] at hi
    exact SmallLevelTwentySixPariRawSource89.raw_zero_of_integer x y z w a b 1 _ hx hy hz hw hi
  simpa only [rows,ite_eq_right h11,ite_eq_right h12] using h i

#print axioms raw_rows_zero
end SmallLevelTwentySixPariRawThirteen
