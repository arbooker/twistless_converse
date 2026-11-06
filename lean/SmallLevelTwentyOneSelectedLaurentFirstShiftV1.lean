module

public import SmallLevelTwentyOneSelectedFirstShiftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem augmentedLeading_apply_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ)
    (r : AugmentedRow) (w : Fin 42 → ℂ) :
    (∑ j, augmentedLeading m f ε s r j*w j)=
      augmentedLaurentRow (phaseRoot m ε) (rootU f) (rootV f)
        (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s)
        ((Real.sqrt 2:ℂ)*f 2) w r := by
  rw [augmentedLeading_laurent,augmentedLaurent_apply]

theorem augmentedShift_apply_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ)
    (r : AugmentedRow) (w : Fin 42 → ℂ) :
    (∑ j, augmentedShift m f ε 0 (s-1) r j*w j)=
      I*(s-((2*m:ℕ):ℂ))*augmentedLaurentShiftRow (phaseRoot m ε) (rootU f) (rootV f)
        (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) w r := by
  simp only [augmentedShift_laurent,mul_assoc,← Finset.mul_sum,augmentedLaurentShift_apply]

/-- A checked Laurent syzygy yields a genuine first-jet equation away
from the weight point. No hypothesis on the Hecke eigenvalue is needed. -/
theorem selected_laurent_first_shift {ι : Type*} [Fintype ι]
    (rows : ι → AugmentedRow) (E u v a : ℂ)
    (coeff : ℂ → ℂ → ℂ → ι → ℂ)
    (hsyz : ∀ x y z : ℂ, x≠0 → y≠0 → z≠0 → ∀ w : Fin 42 → ℂ,
      ∑ i, coeff x y z i*augmentedLaurentRow E u v x y z a w (rows i)=0)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (hE : phaseRoot m ε=E) (hu : rootU f=u) (hvsign : rootV f=v)
    (ha : (Real.sqrt 2:ℂ)*f 2=a)
    (hcoeff : ∀ s i, AnalyticAt ℂ
      (fun z => coeff (primeParameter 2 m z) (primeParameter 3 m z) (primeParameter 7 m z) i) s)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (w : Fin 42 → ℂ) (hw : IsLeadingVector G s w)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) :
    ∑ i, coeff (primeParameter 2 m s/2) (primeParameter 3 m s/3) (primeParameter 7 m s/7) i*
      augmentedLaurentShiftRow E u v
        (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) w (rows i)=0 := by
  let K : ℂ → ι → ℂ := fun z => coeff (primeParameter 2 m z) (primeParameter 3 m z) (primeParameter 7 m z)
  have hKA (z : ℂ) (w : Fin 42 → ℂ) :
      ∑ i, K z i*(∑ j, augmentedLeading m f ε z (rows i) j*w j)=0 := by
    simp only [augmentedLeading_apply_laurent,hE,hu,hvsign,ha,K]
    exact hsyz _ _ _ (primeParameter_ne_zero 2 m (by decide) z)
      (primeParameter_ne_zero 3 m (by decide) z) (primeParameter_ne_zero 7 m (by decide) z) w
  have hh := selected_first_shift rows hm hf ε hε hlaw BG G hG hGF s w hw hshift K hcoeff hKA
  simp only [augmentedShift_apply_laurent,hE,hu,hvsign,K,
    primeParameter_shift 2 m (by decide),primeParameter_shift 3 m (by decide),
    primeParameter_shift 7 m (by decide),Nat.cast_ofNat] at hh
  have hh' : I*(s-((2*m:ℕ):ℂ))*(∑ i,
      coeff (primeParameter 2 m s/2) (primeParameter 3 m s/3) (primeParameter 7 m s/7) i*
      augmentedLaurentShiftRow E u v
        (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) w (rows i))=0 := by
    rw [Finset.mul_sum]
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (mul_eq_zero.mp hh').resolve_left (mul_ne_zero I_ne_zero (sub_ne_zero.mpr hs))

#print axioms augmentedLeading_apply_laurent
#print axioms augmentedShift_apply_laurent
#print axioms selected_laurent_first_shift
end SmallLevelTwentyOneKnownWords
