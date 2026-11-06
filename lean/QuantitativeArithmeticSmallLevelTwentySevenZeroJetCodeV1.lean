module
public import QuantitativeArithmeticSmallLevelTwentySevenZeroJetTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open QuantitativeArithmeticSmallLevelTwentySevenZeroJet
open FinitenessRamanujanSum

def samplesCode (q : ℕ) (t : ℕ → ℕ) : Poly :=
  ((List.range q).filter (fun j => j.Coprime q)).map (fun j => (1,t j,(0,0,0,0,0,0,0)))
theorem eval_samplesCode (x y z w a b c : ℂ) (v : ℕ → ℂ) (q : ℕ) (t : ℕ → ℕ) :
    eval x y z w a b c v (samplesCode q t)=
      QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval q t v := by
  have h := List.sum_toFinset (fun j => v (t j))
    (List.Nodup.filter (fun j => decide (j.Coprime q)) (show (List.range q).Nodup from List.nodup_range))
  have hr : (List.range q).toFinset=Finset.range q := by
    ext j
    simp
  simpa [samplesCode,eval,monomial,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval,
    residues,Function.comp_def,hr] using h.symm

def leadingCode (r : Source) (ε : ℚ) : Poly :=
  match r with
  | .ramanujan t _ _ _ => samplesCode t.q t.left ++
      mono (-ε) t.e₂ t.e₃ t.e₅ t.e₇ (samplesCode t.q t.right)
  | .hecke t _ => List.ofFn (fun i : Fin t.p => (1,t.sample i,(0,0,0,0,0,0,0))) ++
      if t.p=2 then [(-1,t.first,(-1,0,0,0,1,0,0)),(1,t.second,(-2,0,0,0,0,0,0))]
      else if t.p=3 then []
      else if t.p=5 then [(-1,t.first,(0,0,-1,0,0,1,0)),(1,t.second,(0,0,-2,0,0,0,0))]
      else [(-1,t.first,(0,0,0,-1,0,0,1)),(1,t.second,(0,0,0,-2,0,0,0))]
  | _ => leadingPoly r ε

def ramanujanFirstCode (t : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (ε : ℚ) : Poly :=
  mono (ε*(Nat.lcm 27 (t.q^2):ℚ)*(t.t:ℚ)/(t.Q:ℚ))
    t.e₂ t.e₃ t.e₅ t.e₇ (samplesCode t.q t.right)
def firstCode (r : Source) (ε : ℚ) : Poly :=
  match r with
  | .old (.ramanujan i) => ramanujanFirstCode (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected i) ε
  | .ramanujan t _ _ _ => ramanujanFirstCode t ε
  | _ => firstPoly r ε

theorem eval_ramanujanFirstCode (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (t : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (ε : ℚ) :
    eval x y z w a b c v (ramanujanFirstCode t ε)=ramanujanHigher t ε x y z w 1 v := by
  rw [ramanujanFirstCode,eval_mono x y z w a b c v hx hy hz hw,eval_samplesCode]
  simp only [ramanujanHigher,pow_one,Nat.factorial_one,Nat.cast_one,div_one,Rat.cast_mul,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  ring

theorem eval_firstCode (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (r : Source) (ε : ℚ) :
    eval x y z w a b c v (firstCode r ε)=formalHigher r ε x y z w 1 v := by
  cases r with
  | old t => cases t <;> simp only [firstCode,eval_firstPoly x y z w a b c v hx hy hz hw,eval_ramanujanFirstCode x y z w a b c v hx hy hz hw,formalHigher]
  | matrix t ht obs ho => exact eval_firstPoly x y z w a b c v hx hy hz hw (.matrix t ht obs ho) ε
  | ramanujan t ht obs ho => exact eval_ramanujanFirstCode x y z w a b c v hx hy hz hw t ε
  | hecke t ht => rfl
  | entire p hp => rfl

theorem eval_leadingCode (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (r : Source) (ε : ℚ) :
    eval x y z w a b c v (leadingCode r ε)=formalRow r ε x y z w a b c v := by
  cases r with
  | old t => exact eval_leadingPoly x y z w a b c v hx hy hz hw (.old t) ε
  | matrix t ht obs ho => exact eval_leadingPoly x y z w a b c v hx hy hz hw (.matrix t ht obs ho) ε
  | ramanujan t ht obs ho =>
    rw [leadingCode,eval_append,eval_mono x y z w a b c v hx hy hz hw]
    simp [eval_samplesCode,formalRow,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,sub_eq_add_neg]
  | hecke t ht =>
    have hs : eval x y z w a b c v
        (List.ofFn (fun i : Fin t.p => (1,t.sample i,(0,0,0,0,0,0,0))))=
        ∑ i : Fin t.p, v (t.sample i) := by simp [eval,monomial,List.map_ofFn,List.sum_ofFn]
    have hold : eval x y z w a b c v
        ((Finset.univ : Finset (Fin t.p)).toList.map (fun i => (1,t.sample i,(0,0,0,0,0,0,0))))=
        ∑ i : Fin t.p, v (t.sample i) := by simp [eval,monomial]
    rw [formalRow,← eval_heckeLeading x y z w a b c v t]
    simp only [leadingCode,heckeLeading,eval_append,hs,hold]
  | entire p hp => rfl

def jetPolynomial (r : Source) (ε : ℚ) (d : ℕ) : Poly := normalizeLaurent
  (if d=0 then move 607 (zeroA (leadingCode r ε))
   else lower (zeroA (leadingCode r ε)) ++
     mono (-1) 0 0 0 0 (move 607 (lower (firstCode r ε))))
theorem eval_jetPolynomial (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (r : Source) (ε : ℚ) (d : ℕ) :
    eval x y z w a b c v (jetPolynomial r ε d)=formalJet r ε d x y z w b c v := by
  have hx' : x/2≠0 := div_ne_zero hx (by norm_num)
  have hy' : y/3≠0 := div_ne_zero hy (by norm_num)
  have hz' : z/5≠0 := div_ne_zero hz (by norm_num)
  have hw' : w/7≠0 := div_ne_zero hw (by norm_num)
  rw [jetPolynomial,eval_normalizeLaurent]
  by_cases hd : d=0
  · rw [ite_eq_left hd,eval_move,eval_zeroA,eval_leadingCode x y z w 0 b c _ hx hy hz hw]
    simp only [formalJet,ite_eq_left hd]
  · rw [ite_eq_right hd,eval_append,eval_lower,eval_zeroA,
      eval_leadingCode (x/2) (y/3) (z/5) (w/7) 0 b c _ hx' hy' hz' hw',
      eval_mono x y z w a b c v hx hy hz hw,eval_move,eval_lower,
      eval_firstCode (x/2) (y/3) (z/5) (w/7) a b c _ hx' hy' hz' hw']
    simp [formalJet,hd,sub_eq_add_neg]

#print axioms eval_jetPolynomial
end QuantitativeArithmeticSmallLevelTwentySevenZeroJetCode
