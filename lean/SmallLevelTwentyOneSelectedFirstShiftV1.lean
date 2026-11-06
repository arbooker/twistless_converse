module

public import SmallLevelTwentyOneAugmentedFirstShiftV1
public import SmallLevelTwentyOneAugmentedLaurentRowsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem primeParameter_ne_zero (p m : ℕ) (hp : p≠0) (s : ℂ) :
    primeParameter p m s≠0 := by
  unfold primeParameter
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp : (p:ℂ)≠0)]
  exact Complex.exp_ne_zero _

theorem primeParameter_analytic (p m : ℕ) (hp : p≠0) (s : ℂ) :
    AnalyticAt ℂ (primeParameter p m) s := by
  unfold primeParameter
  simp_rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp : (p:ℂ)≠0)]
  fun_prop

/-- A small selected row family suffices for a first-shift certificate.
All its rows are restrictions of the original 474-row analytic system. -/
theorem selected_first_shift {ι : Type*} [Fintype ι]
    (rows : ι → AugmentedRow)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (K : ℂ → ι → ℂ)
    (hK : ∀ z i, AnalyticAt ℂ (fun w => K w i) z)
    (hKA : ∀ z (w : Fin 42 → ℂ),
      ∑ i, K z i*(∑ j, augmentedLeading m f ε z (rows i) j*w j)=0) :
    ∑ i, K (x-1) i*(∑ j, augmentedShift m f ε 0 (x-1) (rows i) j*v j)=0 := by
  classical
  obtain ⟨B,H,hH,hrow⟩ := augmented_matrix_germs hm hf ε hε hlaw BG G hG hGF
  let A : ℂ → Matrix ι (Fin 42) ℂ := fun z i => augmentedLeading m f ε z (rows i)
  let C : ℕ → ℂ → Matrix ι (Fin 42) ℂ := fun n z i => augmentedShift m f ε n z (rows i)
  let L : ℂ → Matrix Unit ι ℂ := fun z _ i => K z i
  have hLA (z : ℂ) : L z*A z=0 := by
    ext r j
    have hh := hKA z (Pi.single j 1)
    simpa [Matrix.mul_apply,L,A,Pi.single_apply] using hh
  have h := IsLeadingVector.first_shift B G A C (fun n z i => H n z (rows i)) L hG
    (fun n z i j => augmentedShift_analytic m f ε n z (rows i) j)
    (fun n i z hz => hH n (rows i) z hz)
    (fun z _ i => hK z i) hLA (fun n i z hz => hrow n (rows i) z hz) x v hv hshift
  have hh : (L (x-1) *ᵥ (C 0 (x-1) *ᵥ v)) ()=0 := by
    rw [Matrix.mulVec_mulVec]
    exact congrFun h ()
  exact hh

#print axioms primeParameter_ne_zero
#print axioms primeParameter_analytic
#print axioms selected_first_shift
end SmallLevelTwentyOneKnownWords
