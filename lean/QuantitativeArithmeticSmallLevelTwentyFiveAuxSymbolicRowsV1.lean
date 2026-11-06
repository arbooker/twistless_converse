module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridSourceRowV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData

/-- Sparse encodings of the actual rows, before collecting equal terms. -/
def unitPoly (i : ℕ) : Poly := [(1,i,(0,0,0,0,0,0,0))]
def primeExponent (e : ℤ×ℤ×ℤ×ℤ) : Exponent := (e.1,e.2.1,e.2.2.1,e.2.2.2,0,0,0)
def gridPoly (j : ℤ) : Poly := unitPoly (gridIndex 1050 (by decide) j).val

def samplePoly (q : ℕ) (j : ℤ) : Poly :=
  ((List.range q).filter (fun a => Nat.Coprime a q)).flatMap
    (fun a : ℕ => gridPoly (j+(a:ℤ)*(1050/q:ℕ)))

def completePoly (p : ℕ) (j : ℤ) : Poly :=
  (List.range p).flatMap (fun a : ℕ => gridPoly (j+(a:ℤ)*(1050/p:ℕ)))

def heckePoly (p : ℕ) (j : ℤ) : Poly :=
  completePoly p j ++
  (if p=2 then
    shift (-1) (-1,0,0,0,1,0,0) (gridPoly ((p:ℤ)*j)) ++
    shift 1 (-2,0,0,0,0,0,0) (gridPoly ((p:ℤ)^2*j))
  else if p=3 then
    shift (-1) (0,-1,0,0,0,1,0) (gridPoly ((p:ℤ)*j)) ++
    shift 1 (0,-2,0,0,0,0,0) (gridPoly ((p:ℤ)^2*j))
  else if p=7 then
    shift (-1) (0,0,0,-1,0,0,1) (gridPoly ((p:ℤ)*j)) ++
    shift 1 (0,0,0,-2,0,0,0) (gridPoly ((p:ℤ)^2*j))
  else [])

def rawSourcePoly (χ : ℚ) : SourceRow → Poly
  | .physical (.word r) => gridPoly r.source ++
      shift (-(χ^r.count)) (primeExponent r.powers) (gridPoly r.target)
  | .physical (.taylor r) => samplePoly r.q r.source ++
      shift (-χ) (primeExponent r.powers) (samplePoly r.q r.target)
  | .physical (.entire q _ _) => samplePoly q 0
  | .physical (.hecke p _ _ j) => heckePoly p j
  | .physical (.infinity _ j _ _) => gridPoly j
  | .old j => unitPoly (7*j.val)

def rawTailPoly : SourceRow → Poly
  | .physical (.word r) => gridPoly r.target
  | .physical (.taylor r) => samplePoly r.q r.target
  | _ => []

def normalizedPoly (p : Poly) : Poly := substitute unitPoly p

theorem eval_unitPoly (x y z w a b c : ℂ) (v : ℕ → ℂ) (j : ℕ) :
    eval x y z w a b c v (unitPoly j)=v j := by simp [unitPoly,eval,monomial]

theorem eval_append (x y z w a b c : ℂ) (v : ℕ → ℂ) (p q : Poly) :
    eval x y z w a b c v (p++q)=eval x y z w a b c v p+eval x y z w a b c v q := by
  simp [eval]

theorem eval_normalizedPoly (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (p : Poly) :
    eval x y z w a b c v (normalizedPoly p)=eval x y z w a b c v p := by
  rw [normalizedPoly,eval_substitute x y z w a b c v hx hy hz hw]
  simp only [eval_unitPoly]

/-- Extend grid coordinates periodically to the natural-number indices used
in sparse polynomial data. -/
def periodicVector (v : Fin 1050 → ℂ) (j : ℕ) : ℂ := v ⟨j%1050,Nat.mod_lt _ (by decide)⟩

theorem periodicVector_fin (v : Fin 1050 → ℂ) (j : Fin 1050) :
    periodicVector v j.val=v j := by simp [periodicVector,Nat.mod_eq_of_lt j.isLt]

theorem eval_gridPoly (x y z w a b c : ℂ) (v : Fin 1050 → ℂ) (j : ℤ) :
    eval x y z w a b c (periodicVector v) (gridPoly j)=v (gridIndex 1050 (by decide) j) := by
  rw [gridPoly,eval_unitPoly,periodicVector_fin]

theorem eval_flatMap (x y z w a b c : ℂ) (v : ℕ → ℂ) {α : Type*}
    (L : List α) (P : α → Poly) :
    eval x y z w a b c v (L.flatMap P)=(L.map (fun j => eval x y z w a b c v (P j))).sum := by
  induction L with
  | nil => rfl
  | cons j L ih => simp only [List.flatMap_cons,eval_append,List.map_cons,List.sum_cons,ih]

theorem eval_samplePoly (x y z w a b c : ℂ) (v : Fin 1050 → ℂ) (q : ℕ) (j : ℤ) :
    eval x y z w a b c (periodicVector v) (samplePoly q j)=sampleSum 1050 (by decide) q j v := by
  rw [samplePoly,eval_flatMap (L := (List.range q).filter (fun a => Nat.Coprime a q))]
  simp only [eval_gridPoly,sampleSum,FinitenessRamanujanSum.residues]
  rw [← List.sum_toFinset _ ((List.nodup_range (n := q)).filter _)]
  simp only [List.toFinset_filter,List.toFinset_range,decide_eq_true_eq]

theorem eval_completePoly (x y z w a b c : ℂ) (v : Fin 1050 → ℂ) (p : ℕ) (j : ℤ) :
    eval x y z w a b c (periodicVector v) (completePoly p j)=completeSum 1050 (by decide) p j v := by
  rw [completePoly,eval_flatMap (L := List.range p)]
  simp only [eval_gridPoly,completeSum]
  rw [← List.sum_toFinset _ (List.nodup_range (n := p))]
  simp only [List.toFinset_range]

#print axioms eval_normalizedPoly
#print axioms eval_samplePoly
#print axioms eval_completePoly
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
