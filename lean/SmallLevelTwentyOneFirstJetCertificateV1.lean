module

public import SmallLevelTwentyOneSelectedLaurentFirstShiftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- Finite checkable data for the two first-shift syzygies and their
consequences. Concrete instances for all eight signs are supplied separately. -/
structure FirstJetCertificate (E u v : ℂ) where
  size0 : ℕ
  size1 : ℕ
  rows0 : Fin size0 → AugmentedRow
  rows1 : Fin size1 → AugmentedRow
  coeff0 : ℂ → ℂ → ℂ → ℂ → Fin size0 → ℂ
  coeff1 : ℂ → ℂ → ℂ → ℂ → Fin size1 → ℂ
  syzygy0 : ∀ x y z a : ℂ, x≠0 → y≠0 → z≠0 → ∀ w : Fin 42 → ℂ,
    ∑ i, coeff0 x y z a i*augmentedLaurentRow E u v x y z a w (rows0 i)=0
  syzygy1 : ∀ x y z a : ℂ, x≠0 → y≠0 → z≠0 → ∀ w : Fin 42 → ℂ,
    ∑ i, coeff1 x y z a i*augmentedLaurentRow E u v x y z a w (rows1 i)=0
  analytic0 : ∀ (m : ℕ) (a s : ℂ) i, AnalyticAt ℂ
    (fun z => coeff0 (primeParameter 2 m z) (primeParameter 3 m z) (primeParameter 7 m z) a i) s
  analytic1 : ∀ (m : ℕ) (a s : ℂ) i, AnalyticAt ℂ
    (fun z => coeff1 (primeParameter 2 m z) (primeParameter 3 m z) (primeParameter 7 m z) a i) s
  conditions : ∀ (x y z a : ℂ), x≠0 → y≠0 → z≠0 → ∀ (w : Fin 42 → ℂ), w 28=1 →
    (∀ r, augmentedLaurentRow E u v x y z a w r=0) →
    (∑ i, coeff0 (x/2) (y/3) (z/7) a i*augmentedLaurentShiftRow E u v x y z w (rows0 i)=0) →
    (∑ i, coeff1 (x/2) (y/3) (z/7) a i*augmentedLaurentShiftRow E u v x y z w (rows1 i)=0) →
    a*x+x^2-1=0 ∧ y+3*u=0 ∧ z=6*E*u+v

/-- Applying a concrete first-jet certificate to the original continued
Euler system, away from the weight point. -/
theorem FirstJetCertificate.pole_conditions {E u v : ℂ} (cert : FirstJetCertificate E u v)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (hE : phaseRoot m ε=E) (hu : rootU f=u) (hvsign : rootV f=v)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (w : Fin 42 → ℂ) (hw : IsLeadingVector G s w) (h28 : w 28=1)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) :
    ((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2-1=0 ∧
      primeParameter 3 m s+3*u=0 ∧ primeParameter 7 m s=6*E*u+v := by
  have hker := augmented_leading_pole hm hf ε hε hlaw BG G hG hGF s w hw hshift
  have hk (r : AugmentedRow) :
      augmentedLaurentRow E u v (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 7 m s) ((Real.sqrt 2:ℂ)*f 2) w r=0 := by
    have hh := congrFun hker r
    change (∑ j, augmentedLeading m f ε s r j*w j)=0 at hh
    simpa only [augmentedLeading_apply_laurent,hE,hu,hvsign] using hh
  apply cert.conditions _ _ _ _ (primeParameter_ne_zero 2 m (by decide) s)
    (primeParameter_ne_zero 3 m (by decide) s) (primeParameter_ne_zero 7 m (by decide) s) w h28 hk
  · exact selected_laurent_first_shift cert.rows0 E u v ((Real.sqrt 2:ℂ)*f 2)
      (fun x y z => cert.coeff0 x y z ((Real.sqrt 2:ℂ)*f 2))
      (fun x y z hx hy hz w => cert.syzygy0 x y z _ hx hy hz w)
      hm hf ε hε hlaw hE hu hvsign rfl (cert.analytic0 m _) BG G hG hGF s w hw hshift hs
  · exact selected_laurent_first_shift cert.rows1 E u v ((Real.sqrt 2:ℂ)*f 2)
      (fun x y z => cert.coeff1 x y z ((Real.sqrt 2:ℂ)*f 2))
      (fun x y z hx hy hz w => cert.syzygy1 x y z _ hx hy hz w)
      hm hf ε hε hlaw hE hu hvsign rfl (cert.analytic1 m _) BG G hG hGF s w hw hshift hs

#print axioms FirstJetCertificate.pole_conditions
end SmallLevelTwentyOneKnownWords
