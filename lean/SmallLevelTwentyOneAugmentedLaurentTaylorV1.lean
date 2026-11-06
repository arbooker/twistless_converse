module

public import SmallLevelTwentyOneAugmentedLaurentRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne

def augmentedLaurentTaylor (E u v x y z : ℂ) (n : ℕ) :
    Matrix AugmentedRow (Fin 42) ℂ
  | .inl i => fun j =>
      E^(augmentedWordRows i).count*threePrimeMonomial (augmentedWordRows i).powers x y z*
        ((augmentedWordRows i).slope:ℂ)^n*
          (if j=gridIndex (augmentedWordRows i).row.target then 1 else 0)
  | .inr (.inl _) => 0
  | .inr (.inr (.inl i)) => fun j =>
      let r := augmentedTaylorSpecs i
      E*localRoot u v r.1*threePrimeMonomial (augmentedTaylorPowers i) x y z*
        (ramanujanSlope r.1 r.2.1:ℂ)^n*
          samplingRow (FinitenessRamanujanSum.residues r.1) r.1 (-(r.2.2/r.2.1)) j
  | .inr (.inr (.inr _)) => 0

def augmentedLaurentTaylorRow (E u v x y z : ℂ) (n : ℕ) (w : Fin 42 → ℂ) : AugmentedRow → ℂ
  | .inl i => E^(augmentedWordRows i).count*threePrimeMonomial (augmentedWordRows i).powers x y z*
      ((augmentedWordRows i).slope:ℂ)^n*w (gridIndex (augmentedWordRows i).row.target)
  | .inr (.inl _) => 0
  | .inr (.inr (.inl i)) =>
      let r := augmentedTaylorSpecs i
      E*localRoot u v r.1*threePrimeMonomial (augmentedTaylorPowers i) x y z*
        (ramanujanSlope r.1 r.2.1:ℂ)^n*sampleSum r.1 (-(r.2.2/r.2.1)) w
  | .inr (.inr (.inr _)) => 0

theorem augmentedLaurentTaylor_apply (E u v x y z : ℂ) (n : ℕ) (w : Fin 42 → ℂ) (r : AugmentedRow) :
    (∑ j, augmentedLaurentTaylor E u v x y z n r j*w j)=augmentedLaurentTaylorRow E u v x y z n w r := by
  rcases r with i | i | i | i | i
  · simp [augmentedLaurentTaylor,augmentedLaurentTaylorRow]
  · simp [augmentedLaurentTaylor,augmentedLaurentTaylorRow]
  · simp only [augmentedLaurentTaylor,augmentedLaurentTaylorRow,mul_assoc,
      ← Finset.mul_sum,samplingRow_apply,sampleSum]
  · simp [augmentedLaurentTaylor,augmentedLaurentTaylorRow]
  · simp [augmentedLaurentTaylor,augmentedLaurentTaylorRow]

theorem augmentedShift_laurentTaylor (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ)
    (n : ℕ) (r : AugmentedRow) (j : Fin 42) :
    augmentedShift m f ε n s r j=
      (I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1))*
        augmentedLaurentTaylor (phaseRoot m ε) (rootU f) (rootV f)
          (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) (n+1) r j := by
  rcases r with i | i | i | i | i
  · change rationalWordCoefficient _ _ _ _ (n+1) s*_=_
    rw [certificateCoefficient_eq (augmentedWordRows i)]
    simp only [certificateCoefficient]
    rw [rational_three_prime_power _ _ (augmentedWordRows i).powers_eq]
    simp only [augmentedLaurentTaylor,primeParameter,phaseRoot,mul_pow]
    ring
  · simp [augmentedShift,augmentedLaurentTaylor]
  · change fullTaylorCoefficient _ _ _ _ _ (n+1) s*_=_
    rw [fullTaylorCoefficient_rational m f ε (augmentedTaylorSpecs_valid i).2.1,
      rational_three_prime_power _ _ (augmentedTaylor_rate_certificate i)]
    simp only [augmentedLaurentTaylor,primeParameter,mul_pow]
    ring
  · simp [augmentedShift,augmentedLaurentTaylor]
  · simp [augmentedShift,augmentedLaurentTaylor]

theorem augmentedShift_apply_laurentTaylor (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ)
    (n : ℕ) (r : AugmentedRow) (w : Fin 42 → ℂ) :
    (∑ j, augmentedShift m f ε n s r j*w j)=
      (I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1))*
        augmentedLaurentTaylorRow (phaseRoot m ε) (rootU f) (rootV f)
          (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) (n+1) w r := by
  simp only [augmentedShift_laurentTaylor,mul_assoc,← Finset.mul_sum,augmentedLaurentTaylor_apply]

theorem augmentedLaurentRow_scale (E u v x y z a c : ℂ) (w : Fin 42 → ℂ) (r : AugmentedRow) :
    augmentedLaurentRow E u v x y z a (fun j => c*w j) r=c*augmentedLaurentRow E u v x y z a w r := by
  rw [← augmentedLaurent_apply,← augmentedLaurent_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem augmentedLaurentTaylorRow_scale (E u v x y z c : ℂ) (n : ℕ)
    (w : Fin 42 → ℂ) (r : AugmentedRow) :
    augmentedLaurentTaylorRow E u v x y z n (fun j => c*w j) r=
      c*augmentedLaurentTaylorRow E u v x y z n w r := by
  rw [← augmentedLaurentTaylor_apply,← augmentedLaurentTaylor_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms augmentedShift_laurentTaylor
#print axioms augmentedShift_apply_laurentTaylor
end SmallLevelTwentyOneKnownWords
