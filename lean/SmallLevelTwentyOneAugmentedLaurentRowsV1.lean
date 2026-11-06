module

public import SmallLevelTwentyOneAugmentedLaurentModelV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne

/-- Scalar evaluation of the full Laurent matrix on an arbitrary vector. -/
def augmentedLaurentRow (E u v x y z a : ℂ) (w : Fin 42 → ℂ) : AugmentedRow → ℂ
  | .inl i => w (gridIndex (augmentedWordRows i).row.source)-
      E^(augmentedWordRows i).count*threePrimeMonomial (augmentedWordRows i).powers x y z*
        w (gridIndex (augmentedWordRows i).row.target)
  | .inr (.inl i) => w (gridIndex (augmentedInfinityRows i).source)
  | .inr (.inr (.inl i)) =>
      let r := augmentedTaylorSpecs i
      sampleSum r.1 r.2.1 w-
        E*localRoot u v r.1*threePrimeMonomial (augmentedTaylorPowers i) x y z*
          sampleSum r.1 (-(r.2.2/r.2.1)) w
  | .inr (.inr (.inr (.inl i))) => sampleSum (augmentedEntireSpecs i) 0 w
  | .inr (.inr (.inr (.inr i))) =>
      let r := augmentedHeckeSpecs i
      completeSum r.1 r.2 w-
        (if r.1=2 then a/x else if r.1=3 then u/y else v/z)*
          w (gridIndex ((r.1:ℤ)*r.2))+
        if r.1=2 then x⁻¹^2*w (gridIndex ((r.1:ℤ)^2*r.2)) else 0

def augmentedLaurentShiftRow (E u v x y z : ℂ) (w : Fin 42 → ℂ) : AugmentedRow → ℂ
  | .inl i => E^(augmentedWordRows i).count*
      threePrimeMonomial (augmentedWordRows i).powers (x/2) (y/3) (z/7)*
        ((augmentedWordRows i).slope:ℂ)*w (gridIndex (augmentedWordRows i).row.target)
  | .inr (.inl _) => 0
  | .inr (.inr (.inl i)) =>
      let r := augmentedTaylorSpecs i
      E*localRoot u v r.1*threePrimeMonomial (augmentedTaylorPowers i) (x/2) (y/3) (z/7)*
        (ramanujanSlope r.1 r.2.1:ℂ)*sampleSum r.1 (-(r.2.2/r.2.1)) w
  | .inr (.inr (.inr _)) => 0

theorem augmentedLaurent_apply (E u v x y z a : ℂ) (w : Fin 42 → ℂ) (r : AugmentedRow) :
    (∑ j, augmentedLaurent E u v x y z a r j*w j)=augmentedLaurentRow E u v x y z a w r := by
  rcases r with i | i | i | i | i
  · simp [augmentedLaurent,augmentedLaurentRow,sub_mul,Finset.sum_sub_distrib]
  · simp [augmentedLaurent,augmentedLaurentRow]
  · simp only [augmentedLaurent,augmentedLaurentRow,sub_mul,mul_assoc,
      Finset.sum_sub_distrib,← Finset.mul_sum,samplingRow_apply,sampleSum]
  · exact samplingRow_apply _ _ _ _
  · by_cases h : (augmentedHeckeSpecs i).1=2 <;>
      simp [augmentedLaurent,augmentedLaurentRow,h,sub_mul,add_mul,
        Finset.sum_add_distrib,Finset.sum_sub_distrib,samplingRow_apply,completeSum]

theorem augmentedLaurentShift_apply (E u v x y z : ℂ) (w : Fin 42 → ℂ) (r : AugmentedRow) :
    (∑ j, augmentedLaurentShift E u v x y z r j*w j)=augmentedLaurentShiftRow E u v x y z w r := by
  rcases r with i | i | i | i | i
  · simp [augmentedLaurentShift,augmentedLaurentShiftRow]
  · simp [augmentedLaurentShift,augmentedLaurentShiftRow]
  · simp only [augmentedLaurentShift,augmentedLaurentShiftRow,mul_assoc,
      ← Finset.mul_sum,samplingRow_apply,sampleSum]
  · simp [augmentedLaurentShift,augmentedLaurentShiftRow]
  · simp [augmentedLaurentShift,augmentedLaurentShiftRow]

/-- Global row numbers used in the independently checked sparse certificates. -/
def augmentedIndex (i : Fin 474) : AugmentedRow :=
  if h : i.val<319 then .inl ⟨i.val,h⟩
  else if h' : i.val<353 then .inr (.inl ⟨i.val-319,by omega⟩)
  else if h'' : i.val<425 then .inr (.inr (.inl ⟨i.val-353,by omega⟩))
  else if h''' : i.val<433 then .inr (.inr (.inr (.inl ⟨i.val-425,by omega⟩)))
  else .inr (.inr (.inr (.inr ⟨i.val-433,by omega⟩)))

#print axioms augmentedLaurent_apply
#print axioms augmentedLaurentShift_apply
end SmallLevelTwentyOneKnownWords
