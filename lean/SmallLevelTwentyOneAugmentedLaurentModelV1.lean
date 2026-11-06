module

public import SmallLevelTwentyOneAugmentedTaylorRatesV1
public import SmallLevelTwentyOneAugmentedGermsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne

/-- Laurent coordinates for every actual augmented leading row. -/
def augmentedLaurent (E u v x y z a : ℂ) : Matrix AugmentedRow (Fin 42) ℂ
  | .inl i => fun j =>
      (if j=gridIndex (augmentedWordRows i).row.source then 1 else 0)-
        E^(augmentedWordRows i).count*threePrimeMonomial (augmentedWordRows i).powers x y z*
          (if j=gridIndex (augmentedWordRows i).row.target then 1 else 0)
  | .inr (.inl i) => fun j => if j=gridIndex (augmentedInfinityRows i).source then 1 else 0
  | .inr (.inr (.inl i)) => fun j =>
      let r := augmentedTaylorSpecs i
      samplingRow (FinitenessRamanujanSum.residues r.1) r.1 r.2.1 j-
        E*localRoot u v r.1*threePrimeMonomial (augmentedTaylorPowers i) x y z*
          samplingRow (FinitenessRamanujanSum.residues r.1) r.1 (-(r.2.2/r.2.1)) j
  | .inr (.inr (.inr (.inl i))) =>
      samplingRow (FinitenessRamanujanSum.residues (augmentedEntireSpecs i)) (augmentedEntireSpecs i) 0
  | .inr (.inr (.inr (.inr i))) => fun j =>
      let r := augmentedHeckeSpecs i
      samplingRow (Finset.range r.1) r.1 r.2 j-
        (if r.1=2 then a/x else if r.1=3 then u/y else v/z)*
          (if j=gridIndex ((r.1:ℤ)*r.2) then 1 else 0)+
        if r.1=2 then x⁻¹^2*(if j=gridIndex ((r.1:ℤ)^2*r.2) then 1 else 0) else 0

/-- First-shift matrix after removing the common factor I(s-2m).
The arguments x,y,z are evaluated at s, so the rates use x/2,y/3,z/7. -/
def augmentedLaurentShift (E u v x y z : ℂ) : Matrix AugmentedRow (Fin 42) ℂ
  | .inl i => fun j =>
      E^(augmentedWordRows i).count*
        threePrimeMonomial (augmentedWordRows i).powers (x/2) (y/3) (z/7)*
          ((augmentedWordRows i).slope:ℂ)*
            (if j=gridIndex (augmentedWordRows i).row.target then 1 else 0)
  | .inr (.inl _) => 0
  | .inr (.inr (.inl i)) => fun j =>
      let r := augmentedTaylorSpecs i
      E*localRoot u v r.1*threePrimeMonomial (augmentedTaylorPowers i) (x/2) (y/3) (z/7)*
        (ramanujanSlope r.1 r.2.1:ℂ)*
          samplingRow (FinitenessRamanujanSum.residues r.1) r.1 (-(r.2.2/r.2.1)) j
  | .inr (.inr (.inr _)) => 0

theorem augmentedHeckeSpecs_primes (i : Fin 41) :
    (augmentedHeckeSpecs i).1=2 ∨ (augmentedHeckeSpecs i).1=3 ∨
      (augmentedHeckeSpecs i).1=7 := by revert i; decide

theorem primeParameter_inverse (p m : ℕ) (s : ℂ) :
    (p:ℂ)^((m:ℂ)-s)=(primeParameter p m s)⁻¹ := by
  rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
  rfl

theorem augmentedLeading_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) :
    augmentedLeading m f ε s=
      augmentedLaurent (phaseRoot m ε) (rootU f) (rootV f)
        (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s)
        ((Real.sqrt 2:ℂ)*f 2) := by
  funext r j
  rcases r with i | i | i | i | i
  · change _-_ * _=_-_ * _
    rw [certificateCoefficient_eq (augmentedWordRows i),certificate_leading_laurent]
    rfl
  · rfl
  · change _-fullTaylorCoefficient _ _ _ _ _ 0 s*_=_-_ * _
    rw [fullTaylor_leading_laurent]
  · rfl
  · rcases augmentedHeckeSpecs_primes i with hp | hp | hp
    all_goals
      simp only [augmentedLeading,augmentedLaurent,heckeCoefficientRow,hp,primeParameter_inverse]
      norm_num only [show ¬2∣21 by decide,show 3∣21 by decide,show 7∣21 by decide,
        ite_true,ite_false,show (3:ℕ)≠2 by decide,show (7:ℕ)≠2 by decide,show (7:ℕ)≠3 by decide]
      simp only [rootU_eigenvalue,rootV_eigenvalue,div_eq_mul_inv]

theorem augmentedShift_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (r : AugmentedRow) (j : Fin 42) :
    augmentedShift m f ε 0 (s-1) r j=
      (I*(s-((2*m:ℕ):ℂ))) *
        augmentedLaurentShift (phaseRoot m ε) (rootU f) (rootV f)
          (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) r j := by
  rcases r with i | i | i | i | i
  · change rationalWordCoefficient _ _ _ _ 1 (s-1)*_=_
    rw [certificateCoefficient_eq (augmentedWordRows i),certificate_first_shift_laurent]
    simp only [Pi.smul_apply,smul_eq_mul,augmentedLaurentShift,phaseRoot]
    ring
  · simp [augmentedShift,augmentedLaurentShift]
  · change fullTaylorCoefficient _ _ _ _ _ 1 (s-1)*_=_
    rw [fullTaylor_first_shift_laurent]
    simp only [Pi.smul_apply,smul_eq_mul,augmentedLaurentShift]
    ring
  · simp [augmentedShift,augmentedLaurentShift]
  · simp [augmentedShift,augmentedLaurentShift]

#print axioms augmentedLeading_laurent
#print axioms augmentedShift_laurent
end SmallLevelTwentyOneKnownWords
