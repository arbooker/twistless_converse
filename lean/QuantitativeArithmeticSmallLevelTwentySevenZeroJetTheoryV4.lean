module

public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamilyModelV1
public import QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamilyTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenFourthSourceRaw0000V1
public import QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSourceRawBundleV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenZeroJet. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenZeroJetPolynomialModelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJet
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open FinitenessRamanujanSum

def single (j : ℕ) : Poly := [(1,j,(0,0,0,0,0,0,0))]
def samples (q : ℕ) (v : ℕ → ℕ) : Poly :=
  (residues q).toList.map (fun j => (1,v j,(0,0,0,0,0,0,0)))
def mono (c : ℚ) (e₂ e₃ e₅ e₇ : ℤ) (p : Poly) : Poly :=
  shift c (e₂,e₃,e₅,e₇,0,0,0) p

theorem eval_single (x y z w a b c : ℂ) (v : ℕ → ℂ) (j : ℕ) :
    eval x y z w a b c v (single j)=v j := by simp [single,eval,monomial]
theorem eval_samples (x y z w a b c : ℂ) (v : ℕ → ℂ) (q : ℕ) (t : ℕ → ℕ) :
    eval x y z w a b c v (samples q t)=
      QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval q t v := by
  simp [samples,eval,monomial,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.sampleEval]
theorem eval_mono (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (r : ℚ) (e₂ e₃ e₅ e₇ : ℤ) (p : Poly) :
    eval x y z w a b c v (mono r e₂ e₃ e₅ e₇ p)=
      (r:ℂ)*(x^e₂*y^e₃*z^e₅*w^e₇)*eval x y z w a b c v p := by
  rw [mono,eval_shift x y z w a b c v hx hy hz hw]
  simp [monomial]

def matrixLeading (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) : Poly :=
  single r.left ++ mono (-1) r.e₂ r.e₃ r.e₅ r.e₇ (single r.right)
def ramanujanLeading (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (ε : ℚ) : Poly :=
  samples r.q r.left ++ mono (-ε) r.e₂ r.e₃ r.e₅ r.e₇ (samples r.q r.right)
def matrixFirst (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) : Poly :=
  mono ((QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.entry r.word 1 0:ℚ)*
    QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.denominator
      QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.point r)
    r.e₂ r.e₃ r.e₅ r.e₇ (single r.right)
def ramanujanFirst (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (ε : ℚ) : Poly :=
  mono (ε*(Nat.lcm 27 (r.q^2):ℚ)*(r.t:ℚ)/(r.Q:ℚ))
    r.e₂ r.e₃ r.e₅ r.e₇ (samples r.q r.right)

theorem eval_matrixLeading (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) :
    eval x y z w a b c v (matrixLeading r)=
      QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading r x y z w v := by
  rw [matrixLeading,eval_append,eval_mono x y z w a b c v hx hy hz hw]
  simp [eval_single,QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.formalLeading,sub_eq_add_neg]
theorem eval_ramanujanLeading (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (ε : ℚ) :
    eval x y z w a b c v (ramanujanLeading r ε)=
      QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading r x y z w (ε:ℂ) v := by
  rw [ramanujanLeading,eval_append,eval_mono x y z w a b c v hx hy hz hw]
  simp [eval_samples,QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.formalLeading,sub_eq_add_neg]
theorem eval_matrixFirst (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (r : QuantitativeArithmeticSmallLevelTwentySevenMatrixSource.Spec) :
    eval x y z w a b c v (matrixFirst r)=matrixHigher r x y z w 1 v := by
  rw [matrixFirst,eval_mono x y z w a b c v hx hy hz hw,eval_single]
  simp only [matrixHigher,pow_one,Nat.factorial_one,Nat.cast_one,div_one,Rat.cast_mul,Rat.cast_intCast]
  ring
theorem eval_ramanujanFirst (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (r : QuantitativeArithmeticSmallLevelTwentySevenRamanujanSource.Spec) (ε : ℚ) :
    eval x y z w a b c v (ramanujanFirst r ε)=ramanujanHigher r ε x y z w 1 v := by
  rw [ramanujanFirst,eval_mono x y z w a b c v hx hy hz hw,eval_samples]
  simp only [ramanujanHigher,pow_one,Nat.factorial_one,Nat.cast_one,div_one,Rat.cast_mul,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  ring

def firstPoly (r : Source) (ε : ℚ) : Poly :=
  match r with
  | .old (.matrix i) => matrixFirst (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Matrix.selected i)
  | .old (.ramanujan i) => ramanujanFirst (QuantitativeArithmeticSmallLevelTwentySevenShiftSource.Ramanujan.selected i) ε
  | .old _ => []
  | .matrix t _ _ _ => matrixFirst t
  | .ramanujan t _ _ _ => ramanujanFirst t ε
  | .hecke _ _ => []
  | .entire _ _ => []

theorem eval_firstPoly (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (r : Source) (ε : ℚ) :
    eval x y z w a b c v (firstPoly r ε)=formalHigher r ε x y z w 1 v := by
  cases r with
  | old t => cases t <;> simp only [firstPoly,formalHigher,eval_nil,eval_matrixFirst x y z w a b c v hx hy hz hw,eval_ramanujanFirst x y z w a b c v hx hy hz hw]
  | matrix t ht obs ho => exact eval_matrixFirst x y z w a b c v hx hy hz hw t
  | ramanujan t ht obs ho => exact eval_ramanujanFirst x y z w a b c v hx hy hz hw t ε
  | hecke t ht => rfl
  | entire p hp => rfl
def heckeLeading (r : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec) : Poly :=
  (Finset.univ : Finset (Fin r.p)).toList.map (fun i => (1,r.sample i,(0,0,0,0,0,0,0))) ++
  if r.p=2 then [(-1,r.first,(-1,0,0,0,1,0,0)),(1,r.second,(-2,0,0,0,0,0,0))]
  else if r.p=3 then []
  else if r.p=5 then [(-1,r.first,(0,0,-1,0,0,1,0)),(1,r.second,(0,0,-2,0,0,0,0))]
  else [(-1,r.first,(0,0,0,-1,0,0,1)),(1,r.second,(0,0,0,-2,0,0,0))]
theorem eval_heckeLeading (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (r : QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.Spec) :
    eval x y z w a b c v (heckeLeading r)=
      QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading r x y z w a b c v := by
  have hs : eval x y z w a b c v
      ((Finset.univ : Finset (Fin r.p)).toList.map (fun i => (1,r.sample i,(0,0,0,0,0,0,0))))=
      ∑ i : Fin r.p, v (r.sample i) := by simp [eval,monomial]
  rw [heckeLeading,eval_append,hs]
  by_cases h2 : r.p=2
  · norm_num [h2,eval,monomial,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue]
    ring
  · by_cases h3 : r.p=3
    · simp [h3,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue]
    · by_cases h5 : r.p=5
      · norm_num [h2,h3,h5,eval,monomial,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue]
        ring
      · norm_num [h2,h3,h5,eval,monomial,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.formalLeading,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.rate,QuantitativeArithmeticSmallLevelTwentySevenHeckeSource.eigenvalue]
        ring

def leadingPoly (r : Source) (ε : ℚ) : Poly :=
  match r with
  | .old t => QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch.signedPoly ε t
  | .matrix t _ _ _ => matrixLeading t
  | .ramanujan t _ _ _ => ramanujanLeading t ε
  | .hecke t _ => heckeLeading t
  | .entire p _ => p

theorem eval_leadingPoly (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (r : Source) (ε : ℚ) :
    eval x y z w a b c v (leadingPoly r ε)=formalRow r ε x y z w a b c v := by
  cases r with
  | old t => rfl
  | matrix t ht obs ho => exact eval_matrixLeading x y z w a b c v hx hy hz hw t
  | ramanujan t ht obs ho => exact eval_ramanujanLeading x y z w a b c v hx hy hz hw t ε
  | hecke t ht => exact eval_heckeLeading x y z w a b c v t
  | entire p hp => rfl
#print axioms eval_firstPoly
#print axioms eval_leadingPoly
end QuantitativeArithmeticSmallLevelTwentySevenZeroJet
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenZeroJetPolynomialV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJet
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily

def move (n : ℕ) (p : Poly) : Poly := p.map (fun t => (t.1,n+t.2.1,t.2.2))
def lower (p : Poly) : Poly := p.map (fun t =>
  (t.1/((2:ℚ)^t.2.2.1*(3:ℚ)^t.2.2.2.1*(5:ℚ)^t.2.2.2.2.1*(7:ℚ)^t.2.2.2.2.2.1),t.2.1,t.2.2))

theorem eval_move (x y z w a b c : ℂ) (v : ℕ → ℂ) (n : ℕ) (p : Poly) :
    eval x y z w a b c v (move n p)=eval x y z w a b c (fun j => v (n+j)) p := by
  simp [eval,move,List.map_map,Function.comp_def]
theorem monomial_lower (x y z w a b c : ℂ) (e : Exponent) :
    monomial x y z w a b c e /
      ((2:ℂ)^e.1*(3:ℂ)^e.2.1*(5:ℂ)^e.2.2.1*(7:ℂ)^e.2.2.2.1)=
      monomial (x/2) (y/3) (z/5) (w/7) a b c e := by
  simp only [monomial,div_zpow]
  ring
theorem eval_lower (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (lower p)=eval (x/2) (y/3) (z/5) (w/7) a b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨r,j,e⟩
    simp only [lower,List.map_cons,eval_cons] at ih ⊢
    rw [ih,← monomial_lower]
    push_cast
    ring

def jetPolynomial (r : Source) (ε : ℚ) (d : ℕ) : Poly := normalizeLaurent
  (if d=0 then move 607 (zeroA (leadingPoly r ε))
   else lower (zeroA (leadingPoly r ε)) ++
     mono (-1) 0 0 0 0 (move 607 (lower (firstPoly r ε))))
def formalJet (r : Source) (ε : ℚ) (d : ℕ) (x y z w b c : ℂ) (v : ℕ → ℂ) : ℂ :=
  if d=0 then formalRow r ε x y z w 0 b c (fun j => v (607+j))
  else formalRow r ε (x/2) (y/3) (z/5) (w/7) 0 b c v -
    formalHigher r ε (x/2) (y/3) (z/5) (w/7) 1 (fun j => v (607+j))

theorem eval_jetPolynomial (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (r : Source) (ε : ℚ) (d : ℕ) :
    eval x y z w a b c v (jetPolynomial r ε d)=formalJet r ε d x y z w b c v := by
  have hx' : x/2≠0 := div_ne_zero hx (by norm_num)
  have hy' : y/3≠0 := div_ne_zero hy (by norm_num)
  have hz' : z/5≠0 := div_ne_zero hz (by norm_num)
  have hw' : w/7≠0 := div_ne_zero hw (by norm_num)
  rw [jetPolynomial,eval_normalizeLaurent]
  by_cases hd : d=0
  · rw [ite_eq_left hd,eval_move,eval_zeroA,eval_leadingPoly x y z w 0 b c _ hx hy hz hw]
    simp only [formalJet,ite_eq_left hd]
  · rw [ite_eq_right hd,eval_append,eval_lower,eval_zeroA,
      eval_leadingPoly (x/2) (y/3) (z/5) (w/7) 0 b c _ hx' hy' hz' hw',
      eval_mono x y z w a b c v hx hy hz hw,eval_move,eval_lower,
      eval_firstPoly (x/2) (y/3) (z/5) (w/7) a b c _ hx' hy' hz' hw']
    simp [formalJet,hd,sub_eq_add_neg]
#print axioms eval_jetPolynomial
end QuantitativeArithmeticSmallLevelTwentySevenZeroJet
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenZeroJetPhysicalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJet
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticTaylorLayerNormalization

def packed (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (j : ℕ) : ℂ :=
  if j<607 then originalLayer m f 1 s j else originalLayer m f 0 s (j-607)

theorem packed_top (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (j : ℕ) :
    packed m f s (607+j)=originalLayer m f 0 s j := by
  simp [packed,show ¬607+j<607 by omega]

theorem formalRow_packed_lower (r : Source) (ε : ℚ)
    (hr : ∀ t∈leadingPoly r ε, t.2.1<607)
    (m : ℕ) (f : ℕ → ℂ) (s x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    formalRow r ε x y z w a b c (packed m f s)=
      formalRow r ε x y z w a b c (originalLayer m f 1 s) := by
  rw [← eval_leadingPoly x y z w a b c _ hx hy hz hw,
    ← eval_leadingPoly x y z w a b c _ hx hy hz hw]
  apply eval_congr
  intro t ht
  simp only [packed,ite_eq_left (hr t ht)]

theorem formalJet_original (r : Source) (ε : ℚ)
    (hr : ∀ t∈leadingPoly r ε, t.2.1<607) (m : ℕ) {f : ℕ → ℂ}
    (hf2 : f 2=0) (d : ℕ) (hd : d≤1) (s : ℂ) :
    formalJet r ε d (primeRate 2 m s) (primeRate 3 m s)
      (primeRate 5 m s) (primeRate 7 m s)
      ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7) (packed m f s)=
      unprofiledRow r ε m f d s := by
  have htop : (fun j => packed m f s (607+j))=originalLayer m f 0 s := by
    funext j
    exact packed_top m f s j
  interval_cases d
  · simp only [formalJet,unprofiledRow,ite_true,htop,Nat.cast_zero,sub_zero,
      Finset.range_zero,Finset.sum_empty,hf2,mul_zero]
  · have h2 : primeRate 2 m (s-1)=primeRate 2 m s/2 := by
      simpa using primeRate_sub_nat 2 m (by norm_num) s 1
    have h3 : primeRate 3 m (s-1)=primeRate 3 m s/3 := by
      simpa using primeRate_sub_nat 3 m (by norm_num) s 1
    have h5 : primeRate 5 m (s-1)=primeRate 5 m s/5 := by
      simpa using primeRate_sub_nat 5 m (by norm_num) s 1
    have h7 : primeRate 7 m (s-1)=primeRate 7 m s/7 := by
      simpa using primeRate_sub_nat 7 m (by norm_num) s 1
    simp only [formalJet,show ¬(1:ℕ)=0 by decide,ite_false,htop,unprofiledRow,
      Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add,Nat.cast_one,
      Nat.sub_self,hf2,mul_zero,h2,h3,h5,h7]
    congr 1
    apply formalRow_packed_lower r ε hr
    · exact div_ne_zero (primeRate_nonzero 2 m s) (by norm_num)
    · exact div_ne_zero (primeRate_nonzero 3 m s) (by norm_num)
    · exact div_ne_zero (primeRate_nonzero 5 m s) (by norm_num)
    · exact div_ne_zero (primeRate_nonzero 7 m s) (by norm_num)

theorem jetPolynomial_original (r : Source) (ε : ℚ)
    (hr : ∀ t∈leadingPoly r ε, t.2.1<607) (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) (hf2 : f 2=0)
    (d : ℕ) (hd : d≤1) (s : ℂ)
    (hscale : ∀ j≤d, scale (s-((2*m:ℕ):ℂ)) j≠0) :
    eval (primeRate 2 m s) (primeRate 3 m s) (primeRate 5 m s) (primeRate 7 m s)
      0 ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7) (packed m f s) (jetPolynomial r ε d)=
      sourcePrefix r m f ε d s/scale (s-((2*m:ℕ):ℂ)) d := by
  rw [eval_jetPolynomial _ _ _ _ _ _ _ _
    (primeRate_nonzero 2 m s) (primeRate_nonzero 3 m s)
    (primeRate_nonzero 5 m s) (primeRate_nonzero 7 m s),
    formalJet_original r ε hr m hf2 d hd s,unprofiledRow_eq_prefix r ε m d hf s hscale]
#print axioms formalJet_original
#print axioms jetPolynomial_original
end QuantitativeArithmeticSmallLevelTwentySevenZeroJet
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenZeroJetSourceRegistryV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenZeroJet
open QuantitativeArithmeticSmallLevelTwentySevenFourthSourceFamily (Source)
def sourceRaw0 : Source := .old (.matrix ⟨2,by decide⟩)
def sourceRaw1 : Source := .old (.matrix ⟨12,by decide⟩)
def sourceRaw2 : Source := .old (.matrix ⟨6,by decide⟩)
def sourceRaw3 : Source := .old (.matrix ⟨23,by decide⟩)
def sourceRaw4 : Source := .old (.matrix ⟨24,by decide⟩)
def sourceRaw5 : Source := .old (.matrix ⟨25,by decide⟩)
def sourceRaw6 : Source := .old (.matrix ⟨26,by decide⟩)
def sourceRaw7 : Source := .old (.matrix ⟨27,by decide⟩)
def sourceRaw8 : Source := .old (.matrix ⟨28,by decide⟩)
def sourceRaw9 : Source := .old (.matrix ⟨29,by decide⟩)
def sourceRaw10 : Source := .old (.matrix ⟨30,by decide⟩)
def sourceRaw11 : Source := .old (.matrix ⟨31,by decide⟩)
def sourceRaw12 : Source := .old (.matrix ⟨32,by decide⟩)
def sourceRaw13 : Source := .old (.matrix ⟨33,by decide⟩)
def sourceRaw14 : Source := .old (.entire ⟨0,by decide⟩)
def sourceRaw15 : Source := .old (.matrix ⟨34,by decide⟩)
def sourceRaw16 : Source := .old (.matrix ⟨35,by decide⟩)
def sourceRaw17 : Source := .old (.matrix ⟨1,by decide⟩)
def sourceRaw18 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw18Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw18Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw18Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw18Observed
def sourceRaw19 : Source := .old (.matrix ⟨4,by decide⟩)
def sourceRaw20 : Source := .old (.matrix ⟨36,by decide⟩)
def sourceRaw21 : Source := .old (.matrix ⟨37,by decide⟩)
def sourceRaw22 : Source := .old (.matrix ⟨38,by decide⟩)
def sourceRaw23 : Source := .old (.matrix ⟨39,by decide⟩)
def sourceRaw24 : Source := .old (.matrix ⟨3,by decide⟩)
def sourceRaw25 : Source := .old (.matrix ⟨40,by decide⟩)
def sourceRaw26 : Source := .old (.matrix ⟨41,by decide⟩)
def sourceRaw27 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw27Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw27Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw27Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw27Observed
def sourceRaw28 : Source := .old (.matrix ⟨42,by decide⟩)
def sourceRaw29 : Source := .old (.matrix ⟨43,by decide⟩)
def sourceRaw30 : Source := .old (.matrix ⟨44,by decide⟩)
def sourceRaw31 : Source := .old (.matrix ⟨0,by decide⟩)
def sourceRaw32 : Source := .old (.matrix ⟨5,by decide⟩)
def sourceRaw33 : Source := .old (.matrix ⟨45,by decide⟩)
def sourceRaw34 : Source := .old (.matrix ⟨46,by decide⟩)
def sourceRaw35 : Source := .old (.matrix ⟨47,by decide⟩)
def sourceRaw36 : Source := .old (.matrix ⟨48,by decide⟩)
def sourceRaw37 : Source := .old (.matrix ⟨49,by decide⟩)
def sourceRaw38 : Source := .old (.matrix ⟨50,by decide⟩)
def sourceRaw39 : Source := .old (.matrix ⟨51,by decide⟩)
def sourceRaw40 : Source := .old (.matrix ⟨52,by decide⟩)
def sourceRaw41 : Source := .old (.matrix ⟨53,by decide⟩)
def sourceRaw42 : Source := .old (.matrix ⟨54,by decide⟩)
def sourceRaw43 : Source := .old (.matrix ⟨55,by decide⟩)
def sourceRaw44 : Source := .old (.matrix ⟨56,by decide⟩)
def sourceRaw45 : Source := .old (.entire ⟨1,by decide⟩)
def sourceRaw46 : Source := .old (.matrix ⟨57,by decide⟩)
def sourceRaw47 : Source := .old (.matrix ⟨58,by decide⟩)
def sourceRaw48 : Source := .old (.matrix ⟨59,by decide⟩)
def sourceRaw50 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw50Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw50Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw50Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw50Observed
def sourceRaw51 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw51Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw51Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw51Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw51Observed
def sourceRaw68 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw68Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw68Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw68Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw68Observed
def sourceRaw69 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw69Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw69Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw69Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw69Observed
def sourceRaw70 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw70Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw70Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw70Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw70Observed
def sourceRaw71 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw71Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw71Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw71Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw71Observed
def sourceRaw72 : Source := .entire QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw72Poly QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw72Original
def sourceRaw73 : Source := .old (.matrix ⟨60,by decide⟩)
def sourceRaw74 : Source := .old (.matrix ⟨61,by decide⟩)
def sourceRaw75 : Source := .old (.matrix ⟨62,by decide⟩)
def sourceRaw77 : Source := .old (.matrix ⟨7,by decide⟩)
def sourceRaw79 : Source := .old (.matrix ⟨63,by decide⟩)
def sourceRaw80 : Source := .old (.matrix ⟨64,by decide⟩)
def sourceRaw81 : Source := .old (.matrix ⟨65,by decide⟩)
def sourceRaw83 : Source := .old (.matrix ⟨8,by decide⟩)
def sourceRaw109 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw109Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw109Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw109Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw109Observed
def sourceRaw112 : Source := .old (.matrix ⟨66,by decide⟩)
def sourceRaw116 : Source := .old (.matrix ⟨67,by decide⟩)
def sourceRaw120 : Source := .old (.matrix ⟨68,by decide⟩)
def sourceRaw144 : Source := .old (.matrix ⟨9,by decide⟩)
def sourceRaw145 : Source := .old (.matrix ⟨69,by decide⟩)
def sourceRaw149 : Source := .old (.matrix ⟨10,by decide⟩)
def sourceRaw160 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw160Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw160Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw160Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw160Observed
def sourceRaw212 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw212Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw212Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw212Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw212Observed
def sourceRaw235 : Source := .old (.matrix ⟨70,by decide⟩)
def sourceRaw236 : Source := .old (.matrix ⟨11,by decide⟩)
def sourceRaw316 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw316Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw316Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw316Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw316Observed
def sourceRaw568 : Source := .old (.entire ⟨2,by decide⟩)
def sourceRaw569 : Source := .old (.ramanujan ⟨0,by decide⟩)
def sourceRaw570 : Source := .old (.ramanujan ⟨1,by decide⟩)
def sourceRaw573 : Source := .old (.ramanujan ⟨7,by decide⟩)
def sourceRaw574 : Source := .old (.ramanujan ⟨8,by decide⟩)
def sourceRaw579 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw579Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw579Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw579Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw579Observed
def sourceRaw585 : Source := .old (.ramanujan ⟨9,by decide⟩)
def sourceRaw586 : Source := .old (.ramanujan ⟨10,by decide⟩)
def sourceRaw593 : Source := .old (.ramanujan ⟨11,by decide⟩)
def sourceRaw594 : Source := .old (.ramanujan ⟨12,by decide⟩)
def sourceRaw595 : Source := .old (.ramanujan ⟨13,by decide⟩)
def sourceRaw596 : Source := .old (.ramanujan ⟨14,by decide⟩)
def sourceRaw599 : Source := .old (.ramanujan ⟨15,by decide⟩)
def sourceRaw600 : Source := .old (.ramanujan ⟨16,by decide⟩)
def sourceRaw603 : Source := .old (.ramanujan ⟨17,by decide⟩)
def sourceRaw604 : Source := .old (.ramanujan ⟨18,by decide⟩)
def sourceRaw666 : Source := .old (.entire ⟨3,by decide⟩)
def sourceRaw667 : Source := .old (.ramanujan ⟨19,by decide⟩)
def sourceRaw668 : Source := .old (.ramanujan ⟨20,by decide⟩)
def sourceRaw669 : Source := .old (.ramanujan ⟨21,by decide⟩)
def sourceRaw670 : Source := .old (.ramanujan ⟨22,by decide⟩)
def sourceRaw671 : Source := .old (.ramanujan ⟨82,by decide⟩)
def sourceRaw672 : Source := .old (.ramanujan ⟨83,by decide⟩)
def sourceRaw673 : Source := .old (.ramanujan ⟨84,by decide⟩)
def sourceRaw674 : Source := .old (.ramanujan ⟨85,by decide⟩)
def sourceRaw675 : Source := .old (.ramanujan ⟨23,by decide⟩)
def sourceRaw676 : Source := .old (.ramanujan ⟨24,by decide⟩)
def sourceRaw677 : Source := .old (.ramanujan ⟨86,by decide⟩)
def sourceRaw678 : Source := .old (.ramanujan ⟨81,by decide⟩)
def sourceRaw679 : Source := .old (.ramanujan ⟨43,by decide⟩)
def sourceRaw680 : Source := .old (.ramanujan ⟨42,by decide⟩)
def sourceRaw681 : Source := .old (.ramanujan ⟨25,by decide⟩)
def sourceRaw682 : Source := .old (.ramanujan ⟨26,by decide⟩)
def sourceRaw683 : Source := .old (.ramanujan ⟨78,by decide⟩)
def sourceRaw684 : Source := .old (.ramanujan ⟨87,by decide⟩)
def sourceRaw685 : Source := .old (.ramanujan ⟨29,by decide⟩)
def sourceRaw686 : Source := .old (.ramanujan ⟨33,by decide⟩)
def sourceRaw687 : Source := .old (.ramanujan ⟨37,by decide⟩)
def sourceRaw688 : Source := .old (.ramanujan ⟨35,by decide⟩)
def sourceRaw689 : Source := .old (.ramanujan ⟨36,by decide⟩)
def sourceRaw690 : Source := .old (.ramanujan ⟨38,by decide⟩)
def sourceRaw692 : Source := .old (.ramanujan ⟨40,by decide⟩)
def sourceRaw693 : Source := .old (.ramanujan ⟨46,by decide⟩)
def sourceRaw694 : Source := .old (.ramanujan ⟨39,by decide⟩)
def sourceRaw695 : Source := .old (.ramanujan ⟨27,by decide⟩)
def sourceRaw696 : Source := .old (.ramanujan ⟨28,by decide⟩)
def sourceRaw697 : Source := .old (.ramanujan ⟨30,by decide⟩)
def sourceRaw698 : Source := .old (.ramanujan ⟨34,by decide⟩)
def sourceRaw699 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw699Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw699Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw699Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw699Observed
def sourceRaw700 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw700Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw700Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw700Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw700Observed
def sourceRaw701 : Source := .old (.ramanujan ⟨31,by decide⟩)
def sourceRaw702 : Source := .old (.ramanujan ⟨32,by decide⟩)
def sourceRaw723 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw723Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw723Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw723Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw723Observed
def sourceRaw739 : Source := .old (.entire ⟨4,by decide⟩)
def sourceRaw740 : Source := .old (.ramanujan ⟨135,by decide⟩)
def sourceRaw741 : Source := .old (.ramanujan ⟨136,by decide⟩)
def sourceRaw742 : Source := .old (.ramanujan ⟨137,by decide⟩)
def sourceRaw743 : Source := .old (.ramanujan ⟨138,by decide⟩)
def sourceRaw744 : Source := .old (.ramanujan ⟨88,by decide⟩)
def sourceRaw745 : Source := .old (.ramanujan ⟨96,by decide⟩)
def sourceRaw746 : Source := .old (.ramanujan ⟨139,by decide⟩)
def sourceRaw747 : Source := .old (.ramanujan ⟨140,by decide⟩)
def sourceRaw748 : Source := .old (.ramanujan ⟨89,by decide⟩)
def sourceRaw749 : Source := .old (.ramanujan ⟨77,by decide⟩)
def sourceRaw750 : Source := .old (.ramanujan ⟨90,by decide⟩)
def sourceRaw751 : Source := .old (.ramanujan ⟨80,by decide⟩)
def sourceRaw765 : Source := .old (.ramanujan ⟨91,by decide⟩)
def sourceRaw766 : Source := .old (.ramanujan ⟨92,by decide⟩)
def sourceRaw767 : Source := .old (.ramanujan ⟨73,by decide⟩)
def sourceRaw768 : Source := .old (.ramanujan ⟨71,by decide⟩)
def sourceRaw769 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw769Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw769Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw769Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw769Observed
def sourceRaw770 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw770Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw770Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw770Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw770Observed
def sourceRaw790 : Source := .old (.ramanujan ⟨165,by decide⟩)
def sourceRaw791 : Source := .old (.ramanujan ⟨166,by decide⟩)
def sourceRaw792 : Source := .old (.ramanujan ⟨141,by decide⟩)
def sourceRaw793 : Source := .old (.ramanujan ⟨142,by decide⟩)
def sourceRaw794 : Source := .old (.ramanujan ⟨93,by decide⟩)
def sourceRaw795 : Source := .old (.ramanujan ⟨94,by decide⟩)
def sourceRaw796 : Source := .old (.ramanujan ⟨146,by decide⟩)
def sourceRaw797 : Source := .old (.ramanujan ⟨144,by decide⟩)
def sourceRaw798 : Source := .old (.ramanujan ⟨41,by decide⟩)
def sourceRaw800 : Source := .old (.ramanujan ⟨79,by decide⟩)
def sourceRaw801 : Source := .old (.ramanujan ⟨95,by decide⟩)
def sourceRaw802 : Source := .old (.ramanujan ⟨99,by decide⟩)
def sourceRaw803 : Source := .old (.ramanujan ⟨97,by decide⟩)
def sourceRaw844 : Source := .old (.entire ⟨5,by decide⟩)
def sourceRaw845 : Source := .old (.ramanujan ⟨100,by decide⟩)
def sourceRaw846 : Source := .old (.ramanujan ⟨101,by decide⟩)
def sourceRaw847 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw847Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw847Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw847Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw847Observed
def sourceRaw853 : Source := .entire QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw853Poly QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw853Original
def sourceRaw854 : Source := .old (.ramanujan ⟨185,by decide⟩)
def sourceRaw855 : Source := .old (.ramanujan ⟨186,by decide⟩)
def sourceRaw856 : Source := .old (.ramanujan ⟨143,by decide⟩)
def sourceRaw857 : Source := .old (.ramanujan ⟨145,by decide⟩)
def sourceRaw858 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw858Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw858Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw858Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw858Observed
def sourceRaw879 : Source := .old (.ramanujan ⟨103,by decide⟩)
def sourceRaw880 : Source := .old (.ramanujan ⟨102,by decide⟩)
def sourceRaw898 : Source := .old (.ramanujan ⟨106,by decide⟩)
def sourceRaw899 : Source := .old (.ramanujan ⟨107,by decide⟩)
def sourceRaw900 : Source := .old (.ramanujan ⟨108,by decide⟩)
def sourceRaw901 : Source := .old (.ramanujan ⟨104,by decide⟩)
def sourceRaw926 : Source := .old (.ramanujan ⟨175,by decide⟩)
def sourceRaw927 : Source := .old (.ramanujan ⟨176,by decide⟩)
def sourceRaw933 : Source := .old (.ramanujan ⟨105,by decide⟩)
def sourceRaw944 : Source := .entire QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw944Poly QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw944Original
def sourceRaw952 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw952Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw952Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw952Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw952Observed
def sourceRaw970 : Source := .old (.hecke 109 (by decide +kernel))
def sourceRaw971 : Source := .old (.hecke 103 (by decide +kernel))
def sourceRaw972 : Source := .old (.hecke 123 (by decide +kernel))
def sourceRaw974 : Source := .old (.hecke 105 (by decide +kernel))
def sourceRaw975 : Source := .old (.hecke 137 (by decide +kernel))
def sourceRaw976 : Source := .old (.hecke 267 (by decide +kernel))
def sourceRaw978 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw978Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw978Valid
def sourceRaw979 : Source := .old (.hecke 268 (by decide +kernel))
def sourceRaw980 : Source := .old (.hecke 229 (by decide +kernel))
def sourceRaw981 : Source := .old (.hecke 537 (by decide +kernel))
def sourceRaw982 : Source := .old (.hecke 269 (by decide +kernel))
def sourceRaw984 : Source := .old (.hecke 380 (by decide +kernel))
def sourceRaw985 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw985Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw985Valid
def sourceRaw986 : Source := .old (.hecke 119 (by decide +kernel))
def sourceRaw987 : Source := .old (.hecke 503 (by decide +kernel))
def sourceRaw988 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw988Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw988Valid
def sourceRaw989 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw989Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw989Valid
def sourceRaw990 : Source := .old (.hecke 381 (by decide +kernel))
def sourceRaw991 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw991Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw991Valid
def sourceRaw992 : Source := .old (.hecke 256 (by decide +kernel))
def sourceRaw993 : Source := .old (.hecke 120 (by decide +kernel))
def sourceRaw995 : Source := .old (.hecke 122 (by decide +kernel))
def sourceRaw996 : Source := .old (.hecke 505 (by decide +kernel))
def sourceRaw997 : Source := .old (.hecke 534 (by decide +kernel))
def sourceRaw999 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw999Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw999Valid
def sourceRaw1000 : Source := .old (.hecke 382 (by decide +kernel))
def sourceRaw1001 : Source := .old (.hecke 257 (by decide +kernel))
def sourceRaw1002 : Source := .old (.hecke 506 (by decide +kernel))
def sourceRaw1003 : Source := .old (.hecke 125 (by decide +kernel))
def sourceRaw1004 : Source := .old (.hecke 127 (by decide +kernel))
def sourceRaw1005 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1005Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1005Valid
def sourceRaw1006 : Source := .old (.hecke 538 (by decide +kernel))
def sourceRaw1007 : Source := .old (.hecke 261 (by decide +kernel))
def sourceRaw1008 : Source := .old (.hecke 131 (by decide +kernel))
def sourceRaw1009 : Source := .old (.hecke 539 (by decide +kernel))
def sourceRaw1010 : Source := .old (.hecke 263 (by decide +kernel))
def sourceRaw1011 : Source := .old (.hecke 540 (by decide +kernel))
def sourceRaw1012 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1012Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1012Valid
def sourceRaw1014 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1014Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1014Valid
def sourceRaw1015 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1015Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1015Valid
def sourceRaw1016 : Source := .old (.hecke 264 (by decide +kernel))
def sourceRaw1017 : Source := .old (.hecke 544 (by decide +kernel))
def sourceRaw1018 : Source := .old (.hecke 132 (by decide +kernel))
def sourceRaw1020 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1020Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1020Valid
def sourceRaw1021 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1021Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1021Valid
def sourceRaw1022 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1022Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1022Valid
def sourceRaw1024 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1024Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1024Valid
def sourceRaw1025 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1025Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1025Valid
def sourceRaw1026 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1026Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1026Valid
def sourceRaw1027 : Source := .old (.hecke 518 (by decide +kernel))
def sourceRaw1029 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1029Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1029Valid
def sourceRaw1030 : Source := .old (.hecke 383 (by decide +kernel))
def sourceRaw1032 : Source := .old (.hecke 270 (by decide +kernel))
def sourceRaw1033 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1033Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1033Valid
def sourceRaw1034 : Source := .old (.hecke 239 (by decide +kernel))
def sourceRaw1035 : Source := .old (.hecke 271 (by decide +kernel))
def sourceRaw1036 : Source := .old (.hecke 272 (by decide +kernel))
def sourceRaw1038 : Source := .old (.hecke 134 (by decide +kernel))
def sourceRaw1039 : Source := .old (.hecke 273 (by decide +kernel))
def sourceRaw1040 : Source := .old (.hecke 138 (by decide +kernel))
def sourceRaw1041 : Source := .old (.hecke 384 (by decide +kernel))
def sourceRaw1044 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1044Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1044Valid
def sourceRaw1045 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1045Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1045Valid
def sourceRaw1047 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1047Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1047Valid
def sourceRaw1051 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1051Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1051Valid
def sourceRaw1052 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1052Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1052Valid
def sourceRaw1054 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1054Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1054Valid
def sourceRaw1062 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1062Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1062Valid
def sourceRaw1065 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1065Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1065Valid
def sourceRaw1066 : Source := .old (.hecke 507 (by decide +kernel))
def sourceRaw1068 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1068Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1068Valid
def sourceRaw1069 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1069Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1069Valid
def sourceRaw1071 : Source := .old (.hecke 385 (by decide +kernel))
def sourceRaw1072 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1072Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1072Valid
def sourceRaw1075 : Source := .old (.hecke 386 (by decide +kernel))
def sourceRaw1077 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1077Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1077Valid
def sourceRaw1080 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1080Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1080Valid
def sourceRaw1081 : Source := .old (.hecke 387 (by decide +kernel))
def sourceRaw1083 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1083Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1083Valid
def sourceRaw1084 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1084Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1084Valid
def sourceRaw1086 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1086Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1086Valid
def sourceRaw1087 : Source := .old (.hecke 388 (by decide +kernel))
def sourceRaw1089 : Source := .old (.hecke 274 (by decide +kernel))
def sourceRaw1090 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1090Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1090Valid
def sourceRaw1091 : Source := .old (.hecke 226 (by decide +kernel))
def sourceRaw1092 : Source := .old (.hecke 275 (by decide +kernel))
def sourceRaw1095 : Source := .old (.hecke 276 (by decide +kernel))
def sourceRaw1096 : Source := .old (.hecke 140 (by decide +kernel))
def sourceRaw1110 : Source := .old (.hecke 277 (by decide +kernel))
def sourceRaw1111 : Source := .old (.hecke 278 (by decide +kernel))
def sourceRaw1114 : Source := .old (.hecke 279 (by decide +kernel))
def sourceRaw1117 : Source := .old (.hecke 280 (by decide +kernel))
def sourceRaw1119 : Source := .old (.hecke 282 (by decide +kernel))
def sourceRaw1122 : Source := .old (.hecke 284 (by decide +kernel))
def sourceRaw1125 : Source := .old (.hecke 285 (by decide +kernel))
def sourceRaw1126 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1126Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1126Valid
def sourceRaw1131 : Source := .old (.hecke 286 (by decide +kernel))
def sourceRaw1132 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1132Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1132Valid
def sourceRaw1141 : Source := .old (.hecke 287 (by decide +kernel))
def sourceRaw1144 : Source := .old (.hecke 290 (by decide +kernel))
def sourceRaw1146 : Source := .old (.hecke 292 (by decide +kernel))
def sourceRaw1150 : Source := .old (.hecke 293 (by decide +kernel))
def sourceRaw1152 : Source := .old (.hecke 294 (by decide +kernel))
def sourceRaw1155 : Source := .old (.hecke 296 (by decide +kernel))
def sourceRaw1164 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1164Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1164Valid
def sourceRaw1186 : Source := .old (.hecke 298 (by decide +kernel))
def sourceRaw1196 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1196Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1196Valid
def sourceRaw1198 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1198Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1198Valid
def sourceRaw1200 : Source := .old (.hecke 392 (by decide +kernel))
def sourceRaw1201 : Source := .old (.hecke 454 (by decide +kernel))
def sourceRaw1203 : Source := .old (.hecke 455 (by decide +kernel))
def sourceRaw1206 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1206Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1206Valid
def sourceRaw1207 : Source := .old (.hecke 457 (by decide +kernel))
def sourceRaw1209 : Source := .old (.hecke 393 (by decide +kernel))
def sourceRaw1211 : Source := .old (.hecke 113 (by decide +kernel))
def sourceRaw1212 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1212Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1212Valid
def sourceRaw1213 : Source := .old (.hecke 394 (by decide +kernel))
def sourceRaw1240 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1240Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1240Valid
def sourceRaw1247 : Source := .old (.matrix ⟨71,by decide⟩)
def sourceRaw1249 : Source := .old (.matrix ⟨13,by decide⟩)
def sourceRaw1250 : Source := .old (.matrix ⟨14,by decide⟩)
def sourceRaw1252 : Source := .old (.matrix ⟨72,by decide⟩)
def sourceRaw1253 : Source := .old (.matrix ⟨73,by decide⟩)
def sourceRaw1254 : Source := .old (.matrix ⟨74,by decide⟩)
def sourceRaw1255 : Source := .old (.matrix ⟨75,by decide⟩)
def sourceRaw1256 : Source := .old (.matrix ⟨76,by decide⟩)
def sourceRaw1260 : Source := .old (.matrix ⟨77,by decide⟩)
def sourceRaw1261 : Source := .old (.matrix ⟨78,by decide⟩)
def sourceRaw1262 : Source := .old (.matrix ⟨79,by decide⟩)
def sourceRaw1264 : Source := .old (.matrix ⟨80,by decide⟩)
def sourceRaw1265 : Source := .old (.matrix ⟨81,by decide⟩)
def sourceRaw1266 : Source := .old (.matrix ⟨82,by decide⟩)
def sourceRaw1270 : Source := .old (.matrix ⟨83,by decide⟩)
def sourceRaw1271 : Source := .old (.matrix ⟨84,by decide⟩)
def sourceRaw1275 : Source := .old (.matrix ⟨85,by decide⟩)
def sourceRaw1276 : Source := .old (.matrix ⟨86,by decide⟩)
def sourceRaw1277 : Source := .old (.matrix ⟨87,by decide⟩)
def sourceRaw1280 : Source := .old (.matrix ⟨88,by decide⟩)
def sourceRaw1281 : Source := .old (.matrix ⟨89,by decide⟩)
def sourceRaw1282 : Source := .old (.matrix ⟨15,by decide⟩)
def sourceRaw1283 : Source := .old (.matrix ⟨90,by decide⟩)
def sourceRaw1284 : Source := .old (.matrix ⟨91,by decide⟩)
def sourceRaw1285 : Source := .old (.matrix ⟨92,by decide⟩)
def sourceRaw1289 : Source := .old (.matrix ⟨93,by decide⟩)
def sourceRaw1290 : Source := .old (.matrix ⟨94,by decide⟩)
def sourceRaw1294 : Source := .old (.matrix ⟨95,by decide⟩)
def sourceRaw1295 : Source := .old (.matrix ⟨96,by decide⟩)
def sourceRaw1303 : Source := .old (.matrix ⟨97,by decide⟩)
def sourceRaw1325 : Source := .old (.matrix ⟨98,by decide⟩)
def sourceRaw1326 : Source := .old (.matrix ⟨99,by decide⟩)
def sourceRaw1330 : Source := .old (.matrix ⟨100,by decide⟩)
def sourceRaw1331 : Source := .old (.matrix ⟨101,by decide⟩)
def sourceRaw1336 : Source := .old (.matrix ⟨102,by decide⟩)
def sourceRaw1338 : Source := .old (.matrix ⟨103,by decide⟩)
def sourceRaw1361 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1361Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1361Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1361Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1361Observed
def sourceRaw1365 : Source := .old (.matrix ⟨16,by decide⟩)
def sourceRaw1366 : Source := .old (.matrix ⟨104,by decide⟩)
def sourceRaw1372 : Source := .old (.matrix ⟨105,by decide⟩)
def sourceRaw1373 : Source := .old (.matrix ⟨17,by decide⟩)
def sourceRaw1377 : Source := .old (.matrix ⟨106,by decide⟩)
def sourceRaw1395 : Source := .old (.matrix ⟨18,by decide⟩)
def sourceRaw1396 : Source := .old (.matrix ⟨107,by decide⟩)
def sourceRaw1400 : Source := .old (.matrix ⟨108,by decide⟩)
def sourceRaw1401 : Source := .old (.matrix ⟨109,by decide⟩)
def sourceRaw1413 : Source := .matrix QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1413Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1413Valid QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1413Observation QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw1413Observed
def sourceRaw1428 : Source := .old (.matrix ⟨19,by decide⟩)
def sourceRaw1429 : Source := .old (.matrix ⟨110,by decide⟩)
def sourceRaw1465 : Source := .old (.matrix ⟨20,by decide⟩)
def sourceRaw1568 : Source := .old (.matrix ⟨21,by decide⟩)
def sourceRaw1694 : Source := .old (.matrix ⟨111,by decide⟩)
def sourceRaw1696 : Source := .old (.matrix ⟨112,by decide⟩)
def sourceRaw1831 : Source := .old (.ramanujan ⟨2,by decide⟩)
def sourceRaw1832 : Source := .old (.ramanujan ⟨3,by decide⟩)
def sourceRaw1833 : Source := .old (.ramanujan ⟨4,by decide⟩)
def sourceRaw1834 : Source := .old (.ramanujan ⟨5,by decide⟩)
def sourceRaw1835 : Source := .old (.ramanujan ⟨47,by decide⟩)
def sourceRaw1836 : Source := .old (.ramanujan ⟨48,by decide⟩)
def sourceRaw1838 : Source := .old (.ramanujan ⟨6,by decide⟩)
def sourceRaw1857 : Source := .old (.ramanujan ⟨49,by decide⟩)
def sourceRaw1858 : Source := .old (.ramanujan ⟨50,by decide⟩)
def sourceRaw1861 : Source := .old (.ramanujan ⟨51,by decide⟩)
def sourceRaw1862 : Source := .old (.ramanujan ⟨52,by decide⟩)
def sourceRaw1863 : Source := .old (.ramanujan ⟨53,by decide⟩)
def sourceRaw1864 : Source := .old (.ramanujan ⟨54,by decide⟩)
def sourceRaw1914 : Source := .old (.ramanujan ⟨55,by decide⟩)
def sourceRaw1915 : Source := .old (.ramanujan ⟨56,by decide⟩)
def sourceRaw1929 : Source := .old (.ramanujan ⟨109,by decide⟩)
def sourceRaw1930 : Source := .old (.ramanujan ⟨110,by decide⟩)
def sourceRaw1931 : Source := .old (.ramanujan ⟨111,by decide⟩)
def sourceRaw1932 : Source := .old (.ramanujan ⟨112,by decide⟩)
def sourceRaw1933 : Source := .old (.ramanujan ⟨113,by decide⟩)
def sourceRaw1934 : Source := .old (.ramanujan ⟨114,by decide⟩)
def sourceRaw1935 : Source := .old (.ramanujan ⟨115,by decide⟩)
def sourceRaw1936 : Source := .old (.ramanujan ⟨116,by decide⟩)
def sourceRaw1937 : Source := .old (.ramanujan ⟨117,by decide⟩)
def sourceRaw1938 : Source := .old (.ramanujan ⟨118,by decide⟩)
def sourceRaw1941 : Source := .old (.ramanujan ⟨65,by decide⟩)
def sourceRaw1942 : Source := .old (.ramanujan ⟨64,by decide⟩)
def sourceRaw1943 : Source := .old (.ramanujan ⟨119,by decide⟩)
def sourceRaw1944 : Source := .old (.ramanujan ⟨120,by decide⟩)
def sourceRaw1947 : Source := .old (.ramanujan ⟨57,by decide⟩)
def sourceRaw1948 : Source := .old (.ramanujan ⟨58,by decide⟩)
def sourceRaw1951 : Source := .old (.ramanujan ⟨66,by decide⟩)
def sourceRaw1952 : Source := .old (.ramanujan ⟨63,by decide⟩)
def sourceRaw1955 : Source := .old (.ramanujan ⟨59,by decide⟩)
def sourceRaw1956 : Source := .old (.ramanujan ⟨60,by decide⟩)
def sourceRaw1961 : Source := .old (.ramanujan ⟨61,by decide⟩)
def sourceRaw1962 : Source := .old (.ramanujan ⟨62,by decide⟩)
def sourceRaw1986 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1986Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1986Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1986Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1986Observed
def sourceRaw1991 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1991Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1991Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1991Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1991Observed
def sourceRaw1992 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1992Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1992Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1992Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw1992Observed
def sourceRaw2002 : Source := .old (.ramanujan ⟨121,by decide⟩)
def sourceRaw2003 : Source := .old (.ramanujan ⟨122,by decide⟩)
def sourceRaw2004 : Source := .old (.ramanujan ⟨123,by decide⟩)
def sourceRaw2005 : Source := .old (.ramanujan ⟨75,by decide⟩)
def sourceRaw2023 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2023Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2023Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2023Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2023Observed
def sourceRaw2026 : Source := .entire QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2026Poly QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2026Original
def sourceRaw2027 : Source := .old (.ramanujan ⟨190,by decide⟩)
def sourceRaw2028 : Source := .old (.ramanujan ⟨191,by decide⟩)
def sourceRaw2029 : Source := .old (.ramanujan ⟨177,by decide⟩)
def sourceRaw2030 : Source := .old (.ramanujan ⟨179,by decide⟩)
def sourceRaw2031 : Source := .old (.ramanujan ⟨188,by decide⟩)
def sourceRaw2032 : Source := .old (.ramanujan ⟨189,by decide⟩)
def sourceRaw2035 : Source := .old (.ramanujan ⟨167,by decide⟩)
def sourceRaw2036 : Source := .old (.ramanujan ⟨178,by decide⟩)
def sourceRaw2037 : Source := .old (.ramanujan ⟨147,by decide⟩)
def sourceRaw2038 : Source := .old (.ramanujan ⟨168,by decide⟩)
def sourceRaw2052 : Source := .old (.ramanujan ⟨169,by decide⟩)
def sourceRaw2053 : Source := .old (.ramanujan ⟨170,by decide⟩)
def sourceRaw2054 : Source := .old (.ramanujan ⟨157,by decide⟩)
def sourceRaw2055 : Source := .old (.ramanujan ⟨162,by decide⟩)
def sourceRaw2056 : Source := .old (.ramanujan ⟨148,by decide⟩)
def sourceRaw2057 : Source := .old (.ramanujan ⟨149,by decide⟩)
def sourceRaw2058 : Source := .old (.ramanujan ⟨160,by decide⟩)
def sourceRaw2059 : Source := .old (.ramanujan ⟨155,by decide⟩)
def sourceRaw2060 : Source := .old (.ramanujan ⟨150,by decide⟩)
def sourceRaw2061 : Source := .old (.ramanujan ⟨124,by decide⟩)
def sourceRaw2064 : Source := .old (.ramanujan ⟨171,by decide⟩)
def sourceRaw2065 : Source := .old (.ramanujan ⟨164,by decide⟩)
def sourceRaw2066 : Source := .old (.ramanujan ⟨125,by decide⟩)
def sourceRaw2067 : Source := .old (.ramanujan ⟨126,by decide⟩)
def sourceRaw2070 : Source := .old (.ramanujan ⟨127,by decide⟩)
def sourceRaw2071 : Source := .old (.ramanujan ⟨128,by decide⟩)
def sourceRaw2087 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2087Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2087Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2087Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2087Observed
def sourceRaw2090 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2090Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2090Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2090Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2090Observed
def sourceRaw2106 : Source := .old (.entire ⟨6,by decide⟩)
def sourceRaw2107 : Source := .old (.ramanujan ⟨181,by decide⟩)
def sourceRaw2108 : Source := .old (.ramanujan ⟨172,by decide⟩)
def sourceRaw2109 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2109Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2109Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2109Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2109Observed
def sourceRaw2116 : Source := .old (.ramanujan ⟨151,by decide⟩)
def sourceRaw2117 : Source := .old (.ramanujan ⟨152,by decide⟩)
def sourceRaw2136 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2136Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2136Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2136Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2136Observed
def sourceRaw2140 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2140Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2140Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2140Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2140Observed
def sourceRaw2160 : Source := .old (.ramanujan ⟨132,by decide⟩)
def sourceRaw2161 : Source := .old (.ramanujan ⟨134,by decide⟩)
def sourceRaw2162 : Source := .old (.ramanujan ⟨130,by decide⟩)
def sourceRaw2163 : Source := .old (.ramanujan ⟨131,by decide⟩)
def sourceRaw2164 : Source := .old (.ramanujan ⟨133,by decide⟩)
def sourceRaw2165 : Source := .old (.ramanujan ⟨129,by decide⟩)
def sourceRaw2178 : Source := .old (.entire ⟨7,by decide⟩)
def sourceRaw2188 : Source := .old (.ramanujan ⟨153,by decide⟩)
def sourceRaw2189 : Source := .old (.ramanujan ⟨158,by decide⟩)
def sourceRaw2195 : Source := .old (.ramanujan ⟨174,by decide⟩)
def sourceRaw2196 : Source := .old (.ramanujan ⟨173,by decide⟩)
def sourceRaw2197 : Source := .old (.ramanujan ⟨154,by decide⟩)
def sourceRaw2198 : Source := .old (.ramanujan ⟨159,by decide⟩)
def sourceRaw2199 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2199Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2199Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2199Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2199Observed
def sourceRaw2201 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2201Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2201Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2201Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2201Observed
def sourceRaw2202 : Source := .ramanujan QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2202Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2202Valid QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2202Observation QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2202Observed
def sourceRaw2222 : Source := .old (.ramanujan ⟨183,by decide⟩)
def sourceRaw2235 : Source := .old (.hecke 199 (by decide +kernel))
def sourceRaw2240 : Source := .old (.hecke 319 (by decide +kernel))
def sourceRaw2241 : Source := .old (.hecke 524 (by decide +kernel))
def sourceRaw2242 : Source := .old (.hecke 320 (by decide +kernel))
def sourceRaw2243 : Source := .old (.hecke 321 (by decide +kernel))
def sourceRaw2245 : Source := .old (.hecke 232 (by decide +kernel))
def sourceRaw2246 : Source := .old (.hecke 322 (by decide +kernel))
def sourceRaw2247 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2247Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2247Valid
def sourceRaw2248 : Source := .old (.hecke 200 (by decide +kernel))
def sourceRaw2249 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2249Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2249Valid
def sourceRaw2250 : Source := .old (.hecke 403 (by decide +kernel))
def sourceRaw2252 : Source := .old (.hecke 545 (by decide +kernel))
def sourceRaw2253 : Source := .old (.hecke 548 (by decide +kernel))
def sourceRaw2254 : Source := .old (.hecke 404 (by decide +kernel))
def sourceRaw2255 : Source := .old (.hecke 510 (by decide +kernel))
def sourceRaw2256 : Source := .old (.hecke 469 (by decide +kernel))
def sourceRaw2257 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw2257Spec QuantitativeArithmeticSmallLevelTwentySevenFourthSource.raw2257Valid
def sourceRaw2259 : Source := .old (.hecke 405 (by decide +kernel))
def sourceRaw2260 : Source := .old (.hecke 323 (by decide +kernel))
def sourceRaw2261 : Source := .old (.hecke 470 (by decide +kernel))
def sourceRaw2262 : Source := .old (.hecke 406 (by decide +kernel))
def sourceRaw2263 : Source := .old (.hecke 471 (by decide +kernel))
def sourceRaw2264 : Source := .old (.hecke 431 (by decide +kernel))
def sourceRaw2266 : Source := .old (.hecke 201 (by decide +kernel))
def sourceRaw2267 : Source := .old (.hecke 472 (by decide +kernel))
def sourceRaw2268 : Source := .old (.hecke 496 (by decide +kernel))
def sourceRaw2269 : Source := .old (.hecke 407 (by decide +kernel))
def sourceRaw2270 : Source := .old (.hecke 473 (by decide +kernel))
def sourceRaw2271 : Source := .old (.hecke 549 (by decide +kernel))
def sourceRaw2273 : Source := .old (.hecke 474 (by decide +kernel))
def sourceRaw2274 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2274Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2274Valid
def sourceRaw2275 : Source := .old (.hecke 203 (by decide +kernel))
def sourceRaw2276 : Source := .old (.hecke 408 (by decide +kernel))
def sourceRaw2277 : Source := .old (.hecke 409 (by decide +kernel))
def sourceRaw2278 : Source := .old (.hecke 410 (by decide +kernel))
def sourceRaw2280 : Source := .old (.hecke 411 (by decide +kernel))
def sourceRaw2281 : Source := .old (.hecke 412 (by decide +kernel))
def sourceRaw2282 : Source := .old (.hecke 511 (by decide +kernel))
def sourceRaw2283 : Source := .old (.hecke 512 (by decide +kernel))
def sourceRaw2284 : Source := .old (.hecke 204 (by decide +kernel))
def sourceRaw2285 : Source := .old (.hecke 475 (by decide +kernel))
def sourceRaw2287 : Source := .old (.hecke 513 (by decide +kernel))
def sourceRaw2288 : Source := .old (.hecke 476 (by decide +kernel))
def sourceRaw2289 : Source := .old (.hecke 477 (by decide +kernel))
def sourceRaw2290 : Source := .old (.hecke 413 (by decide +kernel))
def sourceRaw2291 : Source := .old (.hecke 478 (by decide +kernel))
def sourceRaw2292 : Source := .old (.hecke 479 (by decide +kernel))
def sourceRaw2294 : Source := .old (.hecke 480 (by decide +kernel))
def sourceRaw2295 : Source := .old (.hecke 481 (by decide +kernel))
def sourceRaw2296 : Source := .old (.hecke 536 (by decide +kernel))
def sourceRaw2297 : Source := .old (.hecke 482 (by decide +kernel))
def sourceRaw2298 : Source := .old (.hecke 483 (by decide +kernel))
def sourceRaw2299 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2299Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2299Valid
def sourceRaw2301 : Source := .old (.hecke 484 (by decide +kernel))
def sourceRaw2302 : Source := .old (.hecke 206 (by decide +kernel))
def sourceRaw2303 : Source := .old (.hecke 525 (by decide +kernel))
def sourceRaw2304 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2304Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2304Valid
def sourceRaw2305 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2305Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2305Valid
def sourceRaw2306 : Source := .old (.hecke 425 (by decide +kernel))
def sourceRaw2308 : Source := .old (.hecke 414 (by decide +kernel))
def sourceRaw2309 : Source := .old (.hecke 485 (by decide +kernel))
def sourceRaw2310 : Source := .old (.hecke 486 (by decide +kernel))
def sourceRaw2311 : Source := .old (.hecke 208 (by decide +kernel))
def sourceRaw2312 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2312Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2312Valid
def sourceRaw2313 : Source := .old (.hecke 514 (by decide +kernel))
def sourceRaw2315 : Source := .old (.hecke 515 (by decide +kernel))
def sourceRaw2316 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2316Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2316Valid
def sourceRaw2317 : Source := .old (.hecke 526 (by decide +kernel))
def sourceRaw2318 : Source := .old (.hecke 415 (by decide +kernel))
def sourceRaw2319 : Source := .old (.hecke 416 (by decide +kernel))
def sourceRaw2320 : Source := .old (.hecke 210 (by decide +kernel))
def sourceRaw2322 : Source := .old (.hecke 324 (by decide +kernel))
def sourceRaw2323 : Source := .old (.hecke 325 (by decide +kernel))
def sourceRaw2324 : Source := .old (.hecke 326 (by decide +kernel))
def sourceRaw2325 : Source := .old (.hecke 327 (by decide +kernel))
def sourceRaw2326 : Source := .old (.hecke 328 (by decide +kernel))
def sourceRaw2327 : Source := .old (.hecke 329 (by decide +kernel))
def sourceRaw2330 : Source := .old (.hecke 487 (by decide +kernel))
def sourceRaw2331 : Source := .old (.hecke 417 (by decide +kernel))
def sourceRaw2332 : Source := .old (.hecke 330 (by decide +kernel))
def sourceRaw2333 : Source := .old (.hecke 516 (by decide +kernel))
def sourceRaw2334 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2334Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2334Valid
def sourceRaw2336 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2336Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2336Valid
def sourceRaw2337 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2337Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2337Valid
def sourceRaw2339 : Source := .old (.hecke 488 (by decide +kernel))
def sourceRaw2340 : Source := .old (.hecke 489 (by decide +kernel))
def sourceRaw2343 : Source := .old (.hecke 418 (by decide +kernel))
def sourceRaw2344 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2344Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2344Valid
def sourceRaw2345 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2345Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2345Valid
def sourceRaw2346 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2346Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2346Valid
def sourceRaw2348 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2348Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2348Valid
def sourceRaw2351 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2351Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2351Valid
def sourceRaw2352 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2352Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2352Valid
def sourceRaw2360 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2360Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2360Valid
def sourceRaw2361 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2361Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2361Valid
def sourceRaw2362 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2362Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2362Valid
def sourceRaw2364 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2364Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2364Valid
def sourceRaw2366 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2366Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2366Valid
def sourceRaw2367 : Source := .old (.hecke 490 (by decide +kernel))
def sourceRaw2368 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2368Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2368Valid
def sourceRaw2369 : Source := .old (.hecke 424 (by decide +kernel))
def sourceRaw2371 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2371Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2371Valid
def sourceRaw2372 : Source := .old (.hecke 432 (by decide +kernel))
def sourceRaw2373 : Source := .old (.hecke 433 (by decide +kernel))
def sourceRaw2374 : Source := .old (.hecke 212 (by decide +kernel))
def sourceRaw2375 : Source := .old (.hecke 491 (by decide +kernel))
def sourceRaw2376 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2376Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2376Valid
def sourceRaw2378 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2378Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2378Valid
def sourceRaw2379 : Source := .old (.hecke 492 (by decide +kernel))
def sourceRaw2381 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2381Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2381Valid
def sourceRaw2382 : Source := .old (.hecke 493 (by decide +kernel))
def sourceRaw2387 : Source := .old (.hecke 437 (by decide +kernel))
def sourceRaw2388 : Source := .old (.hecke 494 (by decide +kernel))
def sourceRaw2389 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2389Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2389Valid
def sourceRaw2390 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2390Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2390Valid
def sourceRaw2393 : Source := .old (.hecke 438 (by decide +kernel))
def sourceRaw2394 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2394Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2394Valid
def sourceRaw2395 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2395Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2395Valid
def sourceRaw2396 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2396Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2396Valid
def sourceRaw2397 : Source := .old (.hecke 497 (by decide +kernel))
def sourceRaw2399 : Source := .old (.hecke 439 (by decide +kernel))
def sourceRaw2400 : Source := .old (.hecke 517 (by decide +kernel))
def sourceRaw2402 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2402Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2402Valid
def sourceRaw2403 : Source := .old (.hecke 331 (by decide +kernel))
def sourceRaw2404 : Source := .old (.hecke 332 (by decide +kernel))
def sourceRaw2406 : Source := .old (.hecke 333 (by decide +kernel))
def sourceRaw2407 : Source := .old (.hecke 334 (by decide +kernel))
def sourceRaw2408 : Source := .old (.hecke 440 (by decide +kernel))
def sourceRaw2409 : Source := .old (.hecke 335 (by decide +kernel))
def sourceRaw2414 : Source := .old (.hecke 214 (by decide +kernel))
def sourceRaw2424 : Source := .old (.hecke 336 (by decide +kernel))
def sourceRaw2427 : Source := .old (.hecke 337 (by decide +kernel))
def sourceRaw2429 : Source := .old (.hecke 338 (by decide +kernel))
def sourceRaw2430 : Source := .old (.hecke 441 (by decide +kernel))
def sourceRaw2432 : Source := .old (.hecke 339 (by decide +kernel))
def sourceRaw2435 : Source := .old (.hecke 341 (by decide +kernel))
def sourceRaw2436 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2436Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2436Valid
def sourceRaw2438 : Source := .old (.hecke 442 (by decide +kernel))
def sourceRaw2439 : Source := .old (.hecke 342 (by decide +kernel))
def sourceRaw2441 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2441Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2441Valid
def sourceRaw2445 : Source := .old (.hecke 343 (by decide +kernel))
def sourceRaw2448 : Source := .old (.hecke 344 (by decide +kernel))
def sourceRaw2450 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2450Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2450Valid
def sourceRaw2451 : Source := .old (.hecke 345 (by decide +kernel))
def sourceRaw2456 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2456Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2456Valid
def sourceRaw2463 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2463Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2463Valid
def sourceRaw2471 : Source := .old (.hecke 346 (by decide +kernel))
def sourceRaw2474 : Source := .old (.hecke 348 (by decide +kernel))
def sourceRaw2476 : Source := .old (.hecke 349 (by decide +kernel))
def sourceRaw2477 : Source := .old (.hecke 350 (by decide +kernel))
def sourceRaw2478 : Source := .old (.hecke 352 (by decide +kernel))
def sourceRaw2480 : Source := .old (.hecke 353 (by decide +kernel))
def sourceRaw2484 : Source := .old (.hecke 354 (by decide +kernel))
def sourceRaw2486 : Source := .old (.hecke 355 (by decide +kernel))
def sourceRaw2487 : Source := .old (.hecke 356 (by decide +kernel))
def sourceRaw2488 : Source := .old (.hecke 358 (by decide +kernel))
def sourceRaw2493 : Source := .old (.hecke 361 (by decide +kernel))
def sourceRaw2504 : Source := .old (.hecke 447 (by decide +kernel))
def sourceRaw2508 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2508Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2508Valid
def sourceRaw2516 : Source := .old (.hecke 363 (by decide +kernel))
def sourceRaw2525 : Source := .old (.hecke 365 (by decide +kernel))
def sourceRaw2532 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2532Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2532Valid
def sourceRaw2537 : Source := .old (.hecke 366 (by decide +kernel))
def sourceRaw2540 : Source := .old (.hecke 367 (by decide +kernel))
def sourceRaw2550 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2550Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2550Valid
def sourceRaw2552 : Source := .old (.hecke 527 (by decide +kernel))
def sourceRaw2553 : Source := .old (.hecke 543 (by decide +kernel))
def sourceRaw2555 : Source := .old (.hecke 528 (by decide +kernel))
def sourceRaw2558 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2558Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2558Valid
def sourceRaw2564 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2564Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2564Valid
def sourceRaw2583 : Source := .hecke QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2583Spec QuantitativeArithmeticSmallLevelTwentySevenZeroJetExtraSource.raw2583Valid
def sourceRaw2637 : Source := .old (.matrix ⟨113,by decide⟩)
def sourceRaw2644 : Source := .old (.matrix ⟨114,by decide⟩)
def sourceRaw2649 : Source := .old (.matrix ⟨115,by decide⟩)
def sourceRaw2651 : Source := .old (.matrix ⟨22,by decide⟩)
def sourceRaw2652 : Source := .old (.matrix ⟨116,by decide⟩)
def sourceRaw2653 : Source := .old (.matrix ⟨117,by decide⟩)
def sourceRaw2654 : Source := .old (.matrix ⟨118,by decide⟩)
def sourceRaw2656 : Source := .old (.ramanujan ⟨67,by decide⟩)
def sourceRaw2657 : Source := .old (.ramanujan ⟨68,by decide⟩)
def sourceRaw2658 : Source := .old (.ramanujan ⟨69,by decide⟩)
def sourceRaw2674 : Source := .old (.ramanujan ⟨70,by decide⟩)
def sourceRaw2675 : Source := .old (.ramanujan ⟨72,by decide⟩)
def sourceRaw2676 : Source := .old (.ramanujan ⟨74,by decide⟩)
def sourceRaw2678 : Source := .old (.ramanujan ⟨76,by decide⟩)
def sourceRaw2698 : Source := .old (.ramanujan ⟨184,by decide⟩)
end QuantitativeArithmeticSmallLevelTwentySevenZeroJet
end
end
