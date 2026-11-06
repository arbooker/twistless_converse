module

public import SmallLevelTwentyOneThirdShiftScaleV1
public import SmallLevelTwentyOneAugmentedLaurentTaylorV1
public import SmallLevelTwentyOneSelectedLaurentFirstShiftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne SmallLevelFiniteShift

def jetSlice (w : Fin 168 → ℂ) (n : Fin 4) (j : Fin 42) : ℂ := w (finProdFinEquiv (n,j))

/-- The falling-factorial normalized system at the sole physical candidate.
All entries are rational, and all four pole vectors remain unknown. -/
def jetBlockRow (n : Fin 4) (r : AugmentedRow) (w : Fin 168 → ℂ) : ℂ :=
  augmentedLaurentRow (-1) (-1) 1 (2/2^n.val) (3/3^n.val) (7/7^n.val) (-3/2)
    (jetSlice w n) r-
  ∑ a∈Finset.range n.val, (1/((a+1).factorial:ℂ))*
    augmentedLaurentTaylorRow (-1) (-1) 1 (2/2^n.val) (3/3^n.val) (7/7^n.val) (a+1)
      (jetSlice w (lowerIndex n a)) r

def scaledJetStack (m : ℕ) (w : Fin 168 → ℂ) (b : Fin 4×Fin 42) : ℂ :=
  jetScale (1-(m:ℂ)) b.1*w (finProdFinEquiv b)

theorem actual_jetBlockRow (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (hE : phaseRoot m ε= -1) (hu : rootU f= -1) (hv : rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (n : Fin 4) (r : AugmentedRow) (w : Fin 168 → ℂ) :
    (∑ b, blockLeading 3 (augmentedLeading m f ε) (augmentedShift m f ε)
      ((m:ℂ)+1) (n,r) b*scaledJetStack m w b)=
        jetScale (1-(m:ℂ)) n*jetBlockRow n r w := by
  rw [blockLeading_apply]
  simp only [scaledJetStack,augmentedLeading_apply_laurent,augmentedShift_apply_laurentTaylor,
    augmentedLaurentRow_scale,augmentedLaurentTaylorRow_scale,
    primeParameter_candidate_lower 2 m n.val (by decide),
    primeParameter_candidate_lower 3 m n.val (by decide),
    primeParameter_candidate_lower 7 m n.val (by decide),hE,hu,hv,ha,Nat.cast_ofNat]
  unfold jetBlockRow jetSlice
  simp only [neg_div]
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha'
  have ha'' : a<n.val := Finset.mem_range.mp ha'
  have he : (m:ℂ)+1-(n.val:ℂ)+((a+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=
      (1-(m:ℂ))-(n.val:ℂ)+((a+1:ℕ):ℂ) := by push_cast; ring
  rw [he,← mul_assoc,jetScale_binomial (1-(m:ℂ)) n a ha'']
  ring

#print axioms actual_jetBlockRow
end SmallLevelTwentyOneKnownWords
