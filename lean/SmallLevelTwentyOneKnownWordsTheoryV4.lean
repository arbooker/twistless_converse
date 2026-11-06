module

public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import SmallLevelAllowedSimplePoleTailV1
public import SmallLevelPoleGridTheoryV4
public import SmallLevelRegularizedShiftBlockV1
public import SmallLevelRegularizedShiftKernelV1
public import SmallLevelTwentyOneAugmentedFirstShiftV1
public import SmallLevelTwentyOneAugmentedLaurentRowsV1
public import SmallLevelTwentyOneAugmentedLaurentTaylorV1
public import SmallLevelTwentyOneCoherentWordsV1
public import SmallLevelTwentyOneFirstJetCertificateV1
public import SmallLevelTwentyOneFirstJetInstanceFamilyV4
public import SmallLevelTwentyOneLogIndependenceV1
public import SmallLevelTwentyOneNormalizedAugmentedPoleV1
public import SmallLevelTwentyOneSelectedFirstShiftV1
public import SmallLevelTwentyOneSelectedLaurentFirstShiftV1
public import SmallLevelTwentyOneThirdShiftBlockModelV1
public import SmallLevelTwentyOneThirdShiftLinksFamilyV4
public import SmallLevelTwentyOneThirdShiftRationalTheoryV4
public import SmallLevelTwentyOneThirdShiftScaleV1
public import SmallLevelTwentyOneWeightDominanceFamilyV4
public import SmallLevelUniversalFactoredFirstShiftV1
public import SmallLevelUniversalHigherPoleVectorV1
public import SmallLevelUniversalPoleDetectionV1
public import SmallLevelUniversalRegularTailFirstShiftV1
public import SmallLevelUniversalRegularTailLeadingV1

/-! Consolidated chapter: SmallLevelTwentyOneKnownWords. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneActualFirstJetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem firstJetCertificate_all_signs {E u v : ℂ}
    (hE : E=1 ∨ E= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    Nonempty (FirstJetCertificate E u v) := by
  rcases hE with rfl|rfl <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
    first
    | exact ⟨SmallLevelTwentyOneFirstJetInstance0.certificate⟩
    | exact ⟨SmallLevelTwentyOneFirstJetInstance1.certificate⟩
    | exact ⟨SmallLevelTwentyOneFirstJetInstance2.certificate⟩
    | exact ⟨SmallLevelTwentyOneFirstJetInstance3.certificate⟩
    | exact ⟨SmallLevelTwentyOneFirstJetInstance4.certificate⟩
    | exact ⟨SmallLevelTwentyOneFirstJetInstance5.certificate⟩
    | exact ⟨SmallLevelTwentyOneFirstJetInstance6.certificate⟩
    | exact ⟨SmallLevelTwentyOneFirstJetInstance7.certificate⟩

/-- All eight sign cases and zero/nonzero Hecke eigenvalues: genuine
first-jet restrictions on the same normalized universal principal vector. -/
theorem actual_first_jet {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (w : Fin 42 → ℂ) (hw : IsLeadingVector G s w) (h28 : w 28=1)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) :
    ((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2-1=0 ∧
      primeParameter 3 m s+3*rootU f=0 ∧
      primeParameter 7 m s=6*phaseRoot m ε*rootU f+rootV f := by
  obtain ⟨cert⟩ := firstJetCertificate_all_signs (phaseRoot_sign m hε)
    (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData)
  exact cert.pole_conditions hm hf ε hε hlaw rfl rfl rfl BG G hG hGF s w hw h28 hshift hs

/-- Every original solution admits one coherent continued grid, and each
rightmost pole either lies at the weight point or obeys the three explicit
first-jet equations. This is not yet a pole-exclusion or modularity claim. -/
theorem original_first_jet_restrictions {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        ∀ x : ℂ, (∃ i, meromorphicOrderAt (fun z => G z i) x<0) →
          ∃ n : ℕ, ∃ w : Fin 42 → ℂ,
            IsLeadingVector G (x+n) w ∧ w 28=1 ∧
            (∀ a : ℕ, 0<a → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n+a)) ∧
            (x+n=((2*m:ℕ):ℂ) ∨
              (((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m (x+n)+(primeParameter 2 m (x+n))^2-1=0 ∧
                primeParameter 3 m (x+n)+3*rootU f=0 ∧
                primeParameter 7 m (x+n)=6*phaseRoot m ε*rootU f+rootV f)) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,hp⟩ := original_augmented_leading_kernel hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,?_⟩
  intro x hx
  obtain ⟨n,w,hw,h28,hshift,_hker,_haug⟩ := hp x hx
  refine ⟨n,w,hw,h28,hshift,?_⟩
  by_cases hs : x+n=((2*m:ℕ):ℂ)
  · exact Or.inl hs
  · exact Or.inr (actual_first_jet hm hf ε hε hlaw BG G hG hGF (x+n) w hw h28 hshift hs)

#print axioms firstJetCertificate_all_signs
#print axioms actual_first_jet
#print axioms original_first_jet_restrictions
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOnePhysicalFirstJetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex

theorem primeParameter_norm (p m : ℕ) (hp : 0<p) (s : ℂ) :
    ‖primeParameter p m s‖=(p:ℝ)^(s.re-(m:ℝ)) := by
  simpa only [primeParameter,sub_re,natCast_re] using
    Complex.norm_natCast_cpow_of_pos hp (s-(m:ℂ))

theorem primeParameter_on_line (p m : ℕ) (hp : 0<p) (s : ℂ)
    (hs : s.re-(m:ℝ)=1) :
    primeParameter p m s=(p:ℂ)*exp ((Real.log p:ℂ)*(s.im:ℂ)*I) := by
  have he : s-(m:ℂ)=1+(s.im:ℂ)*I := by
    apply Complex.ext
    · simpa using hs
    · simp
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  rw [primeParameter,he,Complex.cpow_add _ _ hp0,Complex.cpow_one,
    Complex.cpow_def_of_ne_zero hp0,← Complex.natCast_log]
  congr 2
  ring

/-- The physical powers leave exactly one exceptional parameter tuple
among all eight signs. The Hecke eigenvalue is never inverted. -/
theorem physical_first_jet (m : ℕ) (s E u v a : ℂ)
    (hE : E=1 ∨ E= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hx : a*primeParameter 2 m s+(primeParameter 2 m s)^2-1=0)
    (hy : primeParameter 3 m s+3*u=0)
    (hz : primeParameter 7 m s=6*E*u+v) :
    E= -1 ∧ u= -1 ∧ v=1 ∧ s=(m:ℂ)+1 ∧ a= -(3/2:ℂ) := by
  have hyn : ‖primeParameter 3 m s‖=3 := by
    have he : primeParameter 3 m s= -3*u := by linear_combination hy
    rw [he]
    rcases hu with rfl|rfl <;> norm_num
  have hreal : s.re-(m:ℝ)=1 := by
    apply (Real.rpow_right_inj (by norm_num : (0:ℝ)<3) (by norm_num : (3:ℝ)≠1)).mp
    simpa only [primeParameter_norm 3 m (by decide),Nat.cast_ofNat,Real.rpow_one] using hyn
  have hzn : ‖primeParameter 7 m s‖=7 := by
    rw [primeParameter_norm 7 m (by decide),hreal,Real.rpow_one]
    norm_num
  have hzs : primeParameter 7 m s=7 ∨ primeParameter 7 m s= -7 := by
    rw [hz] at hzn ⊢
    rcases hE with rfl|rfl <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;>
      norm_num at hzn
    all_goals norm_num
  have hp3 : ((3:ℂ)^(s-(m:ℂ)-1))^(2:ℕ)=1 := by
    rw [Complex.cpow_sub _ _ (by norm_num : (3:ℂ)≠0),Complex.cpow_one]
    change (primeParameter 3 m s/3)^2=1
    have he : primeParameter 3 m s= -3*u := by linear_combination hy
    rw [he]
    rcases hu with rfl|rfl <;> norm_num
  have hp7 : ((7:ℂ)^(s-(m:ℂ)-1))^(2:ℕ)=1 := by
    rw [Complex.cpow_sub _ _ (by norm_num : (7:ℂ)≠0),Complex.cpow_one]
    change (primeParameter 7 m s/7)^2=1
    rcases hzs with h|h <;> rw [h] <;> norm_num
  have he := QuantitativeArithmeticPrimePowerTorsion.distinct_primes_cpow_torsion
    (by decide : Nat.Prime 3) (by decide : Nat.Prime 7) (by decide : (3:ℕ)≠7)
    (s-(m:ℂ)-1) 2 2 (by decide) (by decide) hp3 hp7
  have hs : s=(m:ℂ)+1 := by linear_combination he
  have hp (p : ℕ) : primeParameter p m s=(p:ℂ) := by
    simp only [primeParameter,hs,add_sub_cancel_left,Complex.cpow_one]
  rw [hp 2] at hx
  rw [hp 3] at hy
  rw [hp 7] at hz
  have hu' : u= -1 := by norm_num only [Nat.cast_ofNat] at hy; linear_combination (1/3:ℂ)*hy
  have hsigns : E= -1 ∧ v=1 := by
    rw [hu'] at hz
    rcases hE with hE|hE <;> rcases hv with hv|hv <;> rw [hE,hv] at hz <;>
      norm_num at hz
    exact ⟨hE,hv⟩
  refine ⟨hsigns.1,hu',hsigns.2,hs,?_⟩
  norm_num only [Nat.cast_ofNat] at hx
  linear_combination (1/2:ℂ)*hx

#print axioms primeParameter_norm
#print axioms primeParameter_on_line
#print axioms physical_first_jet
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneActualExceptionalCandidateV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- The only possible rightmost pole away from the weight point has the
stated exceptional signs, location and eigenvalue. The next third-shift
argument must exclude this tuple; this theorem does not yet do so. -/
theorem actual_exceptional_candidate {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (w : Fin 42 → ℂ) (hw : IsLeadingVector G s w) (h28 : w 28=1)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) :
    phaseRoot m ε= -1 ∧ rootU f= -1 ∧ rootV f=1 ∧
      s=(m:ℂ)+1 ∧ (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ) := by
  obtain ⟨hx,hy,hz⟩ := actual_first_jet hm hf ε hε hlaw BG G hG hGF s w hw h28 hshift hs
  exact physical_first_jet m s _ _ _ _ (phaseRoot_sign m hε)
    (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData) hx hy hz

#print axioms actual_exceptional_candidate
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneSimpleWeightCandidateV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem primeParameter_weight (p m : ℕ) :
    primeParameter p m ((2*m:ℕ):ℂ)=(p:ℂ)^m := by
  unfold primeParameter
  have he : ((2*m:ℕ):ℂ)-(m:ℂ)=(m:ℂ) := by push_cast; ring
  rw [he,Complex.cpow_natCast]

/-- The leading rows alone exclude every weight-point pole except the
single weight-two parameter tuple. No first-shift constraint is assumed. -/
theorem actual_weight_pole_candidate {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (w : Fin 42 → ℂ) (hw : IsLeadingVector G ((2*m:ℕ):ℂ) w) (h28 : w 28=1)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (((2*m:ℕ):ℂ)+n)) :
    m=1 ∧ phaseRoot m ε= -1 ∧ rootU f= -1 ∧ rootV f=1 ∧
      (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ) := by
  have hker := augmented_leading_pole hm hf ε hε hlaw BG G hG hGF _ w hw hshift
  have hk (r : AugmentedRow) :
      augmentedLaurentRow (phaseRoot m ε) (rootU f) (rootV f)
        ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) ((Real.sqrt 2:ℂ)*f 2) w r=0 := by
    have hh := congrFun hker r
    change (∑ j, augmentedLeading m f ε ((2*m:ℕ):ℂ) r j*w j)=0 at hh
    simpa only [augmentedLeading_apply_laurent,primeParameter_weight,Nat.cast_ofNat] using hh
  rcases phaseRoot_sign m hε with hE | hE <;>
    rcases rootU_sign hf.toEulerData with hu | hu <;>
    rcases rootV_sign hf.toEulerData with hv | hv
  · simp only [hE,hu,hv] at hk
    exact (SmallLevelTwentyOneWeightDominance7.weight_constraints m hm _ w h28 hk).elim
  · simp only [hE,hu,hv] at hk
    exact (SmallLevelTwentyOneWeightDominance6.weight_constraints m hm _ w h28 hk).elim
  · simp only [hE,hu,hv] at hk
    exact (SmallLevelTwentyOneWeightDominance5.weight_constraints m hm _ w h28 hk).elim
  · simp only [hE,hu,hv] at hk
    exact (SmallLevelTwentyOneWeightDominance4.weight_constraints m hm _ w h28 hk).elim
  · simp only [hE,hu,hv] at hk
    exact (SmallLevelTwentyOneWeightDominance3.weight_constraints m hm _ w h28 hk).elim
  · simp only [hE,hu,hv] at hk
    exact (SmallLevelTwentyOneWeightDominance2.weight_constraints m hm _ w h28 hk).elim
  · simp only [hE,hu,hv] at hk
    obtain ⟨hm1,ha⟩ := SmallLevelTwentyOneWeightDominance1.weight_constraints m hm _ w h28 hk
    exact ⟨hm1,hE,hu,hv,ha⟩
  · simp only [hE,hu,hv] at hk
    exact (SmallLevelTwentyOneWeightDominance0.weight_constraints m hm _ w h28 hk).elim

#print axioms actual_weight_pole_candidate
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularizedPoleVectorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem original_leading_pole_any_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    leadingMatrix m f ε s *ᵥ v=0 := by
  obtain ⟨B,_hF,hH,hrow⟩ := matrix_system_of_law hm hf ε hlaw
  have hH' (n : ℕ) (i : Fin 42) (z : ℂ) (hz : max B BG-((n:ℝ)+1)<z.re) :
      AnalyticAt ℂ (fun w => errorVector m f ε n w i) z :=
    hH n i z (by linarith [le_max_left B BG])
  have he := SmallLevelContinuation.continued_rows (max B BG) (gridVector (2*m) f) G
    (leadingMatrix m f ε) (shiftMatrix m f ε) (errorVector m f ε)
    (fun i z => (hG i z).meromorphicAt)
    (fun z hz => hGF z (lt_of_le_of_lt (le_max_right B BG) hz))
    (leadingMatrix_analytic m f ε) (shiftMatrix_analytic m f ε) hH'
    (fun n z hz => hrow n z (lt_of_le_of_lt (le_max_left B BG) hz))
  funext i
  exact hv.taylor hG hshift (max B BG)
    (fun z => leadingMatrix m f ε z i) (fun a z => shiftMatrix m f ε a z i)
    (fun a z => errorVector m f ε a z i)
    (leadingMatrix_analytic m f ε s i) (fun a => shiftMatrix_analytic m f ε a s i)
    (fun a z hz => hH' a i z hz) (fun a ha => he a i s ha)

/-- Normalize a regularized principal vector without losing either its
regularized or original universal-row property. -/
theorem normalize_regularized_vector {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (c : ℂ → ℂ) (hc : AnalyticAt ℂ c s)
    (v : Fin 42 → ℂ) (hv : IsLeadingVector (fun z i => c z*G z i) s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ∃ w : Fin 42 → ℂ, IsLeadingVector (fun z i => c z*G z i) s w ∧
      IsLeadingVector G s w ∧ w 28=1 := by
  have hvG := hv.of_analytic_factor c hc
  have hker := original_leading_pole_any_grid hm hf ε hlaw BG G hG hGF s v hvG hshift
  have h28 : v 28≠0 := fun h => hvG.1 (original_rank_coordinate hf hε v hker h)
  obtain ⟨w,hw,hw28,_hwe⟩ := hv.normalize 28 h28
  exact ⟨w,hw,hw.of_analytic_factor c hc,hw28⟩

#print axioms original_leading_pole_any_grid
#print axioms normalize_regularized_vector
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRightmostAnyGridV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem normalized_rightmost_any_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (B : ℝ) (hhalf : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z)
    (x : ℂ) (hpole : ∃ j, meromorphicOrderAt (fun z => G z j) x<0) :
    ∃ n : ℕ, ∃ w : Fin 42 → ℂ, IsLeadingVector G (x+n) w ∧ w 28=1 ∧
      ∀ a : ℕ, 0<a → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n+a) := by
  obtain ⟨n,hn,hshift⟩ := SmallLevelPoleGrid.rightmost_pole (fun i z => G z i) hpole B hhalf
  obtain ⟨v,hv⟩ := exists_leading_vector G (x+n) (fun j => (hG j _).meromorphicAt) hn
  have hker := original_leading_pole_any_grid hm hf ε hlaw BG G hG hGF (x+n) v hv hshift
  have h28 : v 28≠0 := fun h => hv.1 (original_rank_coordinate hf hε v hker h)
  obtain ⟨w,hw,hw28,_⟩ := hv.normalize 28 h28
  exact ⟨n,w,hw,hw28,hshift⟩

#print axioms normalized_rightmost_any_grid
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneThirdShiftBlockKernelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open SmallLevelTwentyOneThirdShiftLinks

theorem jetBlock_kernel_zero (w : Fin 168 → ℂ)
    (h : ∀ n r, jetBlockRow n r w=0) : w=0 := by
  apply SmallLevelTwentyOneThirdShiftRational.kernel_zero w
  intro i
  fin_cases i
  · exact (row0000_link w).symm.trans (h 0 (augmentedIndex 0))
  · exact (row0001_link w).symm.trans (h 0 (augmentedIndex 1))
  · exact (row0002_link w).symm.trans (h 0 (augmentedIndex 2))
  · exact (row0003_link w).symm.trans (h 0 (augmentedIndex 3))
  · exact (row0004_link w).symm.trans (h 0 (augmentedIndex 4))
  · exact (row0005_link w).symm.trans (h 0 (augmentedIndex 5))
  · exact (row0006_link w).symm.trans (h 0 (augmentedIndex 6))
  · exact (row0007_link w).symm.trans (h 0 (augmentedIndex 7))
  · exact (row0008_link w).symm.trans (h 0 (augmentedIndex 8))
  · exact (row0009_link w).symm.trans (h 0 (augmentedIndex 9))
  · exact (row0010_link w).symm.trans (h 0 (augmentedIndex 10))
  · exact (row0011_link w).symm.trans (h 0 (augmentedIndex 11))
  · exact (row0038_link w).symm.trans (h 0 (augmentedIndex 38))
  · exact (row0039_link w).symm.trans (h 0 (augmentedIndex 39))
  · exact (row0040_link w).symm.trans (h 0 (augmentedIndex 40))
  · exact (row0043_link w).symm.trans (h 0 (augmentedIndex 43))
  · exact (row0046_link w).symm.trans (h 0 (augmentedIndex 46))
  · exact (row0047_link w).symm.trans (h 0 (augmentedIndex 47))
  · exact (row0048_link w).symm.trans (h 0 (augmentedIndex 48))
  · exact (row0049_link w).symm.trans (h 0 (augmentedIndex 49))
  · exact (row0051_link w).symm.trans (h 0 (augmentedIndex 51))
  · exact (row0319_link w).symm.trans (h 0 (augmentedIndex 319))
  · exact (row0385_link w).symm.trans (h 0 (augmentedIndex 385))
  · exact (row0386_link w).symm.trans (h 0 (augmentedIndex 386))
  · exact (row0387_link w).symm.trans (h 0 (augmentedIndex 387))
  · exact (row0388_link w).symm.trans (h 0 (augmentedIndex 388))
  · exact (row0389_link w).symm.trans (h 0 (augmentedIndex 389))
  · exact (row0390_link w).symm.trans (h 0 (augmentedIndex 390))
  · exact (row0397_link w).symm.trans (h 0 (augmentedIndex 397))
  · exact (row0398_link w).symm.trans (h 0 (augmentedIndex 398))
  · exact (row0401_link w).symm.trans (h 0 (augmentedIndex 401))
  · exact (row0402_link w).symm.trans (h 0 (augmentedIndex 402))
  · exact (row0403_link w).symm.trans (h 0 (augmentedIndex 403))
  · exact (row0404_link w).symm.trans (h 0 (augmentedIndex 404))
  · exact (row0405_link w).symm.trans (h 0 (augmentedIndex 405))
  · exact (row0427_link w).symm.trans (h 0 (augmentedIndex 427))
  · exact (row0437_link w).symm.trans (h 0 (augmentedIndex 437))
  · exact (row0439_link w).symm.trans (h 0 (augmentedIndex 439))
  · exact (row0441_link w).symm.trans (h 0 (augmentedIndex 441))
  · exact (row0442_link w).symm.trans (h 0 (augmentedIndex 442))
  · exact (row0444_link w).symm.trans (h 0 (augmentedIndex 444))
  · exact (row0474_link w).symm.trans (h 1 (augmentedIndex 0))
  · exact (row0475_link w).symm.trans (h 1 (augmentedIndex 1))
  · exact (row0476_link w).symm.trans (h 1 (augmentedIndex 2))
  · exact (row0477_link w).symm.trans (h 1 (augmentedIndex 3))
  · exact (row0478_link w).symm.trans (h 1 (augmentedIndex 4))
  · exact (row0479_link w).symm.trans (h 1 (augmentedIndex 5))
  · exact (row0480_link w).symm.trans (h 1 (augmentedIndex 6))
  · exact (row0481_link w).symm.trans (h 1 (augmentedIndex 7))
  · exact (row0482_link w).symm.trans (h 1 (augmentedIndex 8))
  · exact (row0483_link w).symm.trans (h 1 (augmentedIndex 9))
  · exact (row0484_link w).symm.trans (h 1 (augmentedIndex 10))
  · exact (row0485_link w).symm.trans (h 1 (augmentedIndex 11))
  · exact (row0512_link w).symm.trans (h 1 (augmentedIndex 38))
  · exact (row0513_link w).symm.trans (h 1 (augmentedIndex 39))
  · exact (row0514_link w).symm.trans (h 1 (augmentedIndex 40))
  · exact (row0517_link w).symm.trans (h 1 (augmentedIndex 43))
  · exact (row0520_link w).symm.trans (h 1 (augmentedIndex 46))
  · exact (row0521_link w).symm.trans (h 1 (augmentedIndex 47))
  · exact (row0522_link w).symm.trans (h 1 (augmentedIndex 48))
  · exact (row0523_link w).symm.trans (h 1 (augmentedIndex 49))
  · exact (row0525_link w).symm.trans (h 1 (augmentedIndex 51))
  · exact (row0793_link w).symm.trans (h 1 (augmentedIndex 319))
  · exact (row0859_link w).symm.trans (h 1 (augmentedIndex 385))
  · exact (row0860_link w).symm.trans (h 1 (augmentedIndex 386))
  · exact (row0861_link w).symm.trans (h 1 (augmentedIndex 387))
  · exact (row0862_link w).symm.trans (h 1 (augmentedIndex 388))
  · exact (row0863_link w).symm.trans (h 1 (augmentedIndex 389))
  · exact (row0864_link w).symm.trans (h 1 (augmentedIndex 390))
  · exact (row0871_link w).symm.trans (h 1 (augmentedIndex 397))
  · exact (row0872_link w).symm.trans (h 1 (augmentedIndex 398))
  · exact (row0875_link w).symm.trans (h 1 (augmentedIndex 401))
  · exact (row0876_link w).symm.trans (h 1 (augmentedIndex 402))
  · exact (row0877_link w).symm.trans (h 1 (augmentedIndex 403))
  · exact (row0878_link w).symm.trans (h 1 (augmentedIndex 404))
  · exact (row0879_link w).symm.trans (h 1 (augmentedIndex 405))
  · exact (row0901_link w).symm.trans (h 1 (augmentedIndex 427))
  · exact (row0910_link w).symm.trans (h 1 (augmentedIndex 436))
  · exact (row0911_link w).symm.trans (h 1 (augmentedIndex 437))
  · exact (row0913_link w).symm.trans (h 1 (augmentedIndex 439))
  · exact (row0915_link w).symm.trans (h 1 (augmentedIndex 441))
  · exact (row0916_link w).symm.trans (h 1 (augmentedIndex 442))
  · exact (row0918_link w).symm.trans (h 1 (augmentedIndex 444))
  · exact (row0948_link w).symm.trans (h 2 (augmentedIndex 0))
  · exact (row0949_link w).symm.trans (h 2 (augmentedIndex 1))
  · exact (row0950_link w).symm.trans (h 2 (augmentedIndex 2))
  · exact (row0951_link w).symm.trans (h 2 (augmentedIndex 3))
  · exact (row0952_link w).symm.trans (h 2 (augmentedIndex 4))
  · exact (row0953_link w).symm.trans (h 2 (augmentedIndex 5))
  · exact (row0954_link w).symm.trans (h 2 (augmentedIndex 6))
  · exact (row0955_link w).symm.trans (h 2 (augmentedIndex 7))
  · exact (row0956_link w).symm.trans (h 2 (augmentedIndex 8))
  · exact (row0957_link w).symm.trans (h 2 (augmentedIndex 9))
  · exact (row0958_link w).symm.trans (h 2 (augmentedIndex 10))
  · exact (row0959_link w).symm.trans (h 2 (augmentedIndex 11))
  · exact (row0986_link w).symm.trans (h 2 (augmentedIndex 38))
  · exact (row0987_link w).symm.trans (h 2 (augmentedIndex 39))
  · exact (row0988_link w).symm.trans (h 2 (augmentedIndex 40))
  · exact (row0991_link w).symm.trans (h 2 (augmentedIndex 43))
  · exact (row0994_link w).symm.trans (h 2 (augmentedIndex 46))
  · exact (row0995_link w).symm.trans (h 2 (augmentedIndex 47))
  · exact (row0996_link w).symm.trans (h 2 (augmentedIndex 48))
  · exact (row0997_link w).symm.trans (h 2 (augmentedIndex 49))
  · exact (row0999_link w).symm.trans (h 2 (augmentedIndex 51))
  · exact (row1267_link w).symm.trans (h 2 (augmentedIndex 319))
  · exact (row1333_link w).symm.trans (h 2 (augmentedIndex 385))
  · exact (row1334_link w).symm.trans (h 2 (augmentedIndex 386))
  · exact (row1335_link w).symm.trans (h 2 (augmentedIndex 387))
  · exact (row1336_link w).symm.trans (h 2 (augmentedIndex 388))
  · exact (row1337_link w).symm.trans (h 2 (augmentedIndex 389))
  · exact (row1338_link w).symm.trans (h 2 (augmentedIndex 390))
  · exact (row1345_link w).symm.trans (h 2 (augmentedIndex 397))
  · exact (row1346_link w).symm.trans (h 2 (augmentedIndex 398))
  · exact (row1349_link w).symm.trans (h 2 (augmentedIndex 401))
  · exact (row1350_link w).symm.trans (h 2 (augmentedIndex 402))
  · exact (row1351_link w).symm.trans (h 2 (augmentedIndex 403))
  · exact (row1352_link w).symm.trans (h 2 (augmentedIndex 404))
  · exact (row1353_link w).symm.trans (h 2 (augmentedIndex 405))
  · exact (row1375_link w).symm.trans (h 2 (augmentedIndex 427))
  · exact (row1384_link w).symm.trans (h 2 (augmentedIndex 436))
  · exact (row1385_link w).symm.trans (h 2 (augmentedIndex 437))
  · exact (row1387_link w).symm.trans (h 2 (augmentedIndex 439))
  · exact (row1389_link w).symm.trans (h 2 (augmentedIndex 441))
  · exact (row1390_link w).symm.trans (h 2 (augmentedIndex 442))
  · exact (row1392_link w).symm.trans (h 2 (augmentedIndex 444))
  · exact (row1422_link w).symm.trans (h 3 (augmentedIndex 0))
  · exact (row1423_link w).symm.trans (h 3 (augmentedIndex 1))
  · exact (row1424_link w).symm.trans (h 3 (augmentedIndex 2))
  · exact (row1425_link w).symm.trans (h 3 (augmentedIndex 3))
  · exact (row1426_link w).symm.trans (h 3 (augmentedIndex 4))
  · exact (row1427_link w).symm.trans (h 3 (augmentedIndex 5))
  · exact (row1428_link w).symm.trans (h 3 (augmentedIndex 6))
  · exact (row1429_link w).symm.trans (h 3 (augmentedIndex 7))
  · exact (row1430_link w).symm.trans (h 3 (augmentedIndex 8))
  · exact (row1431_link w).symm.trans (h 3 (augmentedIndex 9))
  · exact (row1432_link w).symm.trans (h 3 (augmentedIndex 10))
  · exact (row1433_link w).symm.trans (h 3 (augmentedIndex 11))
  · exact (row1460_link w).symm.trans (h 3 (augmentedIndex 38))
  · exact (row1461_link w).symm.trans (h 3 (augmentedIndex 39))
  · exact (row1462_link w).symm.trans (h 3 (augmentedIndex 40))
  · exact (row1465_link w).symm.trans (h 3 (augmentedIndex 43))
  · exact (row1468_link w).symm.trans (h 3 (augmentedIndex 46))
  · exact (row1469_link w).symm.trans (h 3 (augmentedIndex 47))
  · exact (row1470_link w).symm.trans (h 3 (augmentedIndex 48))
  · exact (row1471_link w).symm.trans (h 3 (augmentedIndex 49))
  · exact (row1473_link w).symm.trans (h 3 (augmentedIndex 51))
  · exact (row1741_link w).symm.trans (h 3 (augmentedIndex 319))
  · exact (row1807_link w).symm.trans (h 3 (augmentedIndex 385))
  · exact (row1808_link w).symm.trans (h 3 (augmentedIndex 386))
  · exact (row1809_link w).symm.trans (h 3 (augmentedIndex 387))
  · exact (row1810_link w).symm.trans (h 3 (augmentedIndex 388))
  · exact (row1811_link w).symm.trans (h 3 (augmentedIndex 389))
  · exact (row1812_link w).symm.trans (h 3 (augmentedIndex 390))
  · exact (row1819_link w).symm.trans (h 3 (augmentedIndex 397))
  · exact (row1820_link w).symm.trans (h 3 (augmentedIndex 398))
  · exact (row1823_link w).symm.trans (h 3 (augmentedIndex 401))
  · exact (row1824_link w).symm.trans (h 3 (augmentedIndex 402))
  · exact (row1825_link w).symm.trans (h 3 (augmentedIndex 403))
  · exact (row1826_link w).symm.trans (h 3 (augmentedIndex 404))
  · exact (row1827_link w).symm.trans (h 3 (augmentedIndex 405))
  · exact (row1849_link w).symm.trans (h 3 (augmentedIndex 427))
  · exact (row1850_link w).symm.trans (h 3 (augmentedIndex 428))
  · exact (row1858_link w).symm.trans (h 3 (augmentedIndex 436))
  · exact (row1859_link w).symm.trans (h 3 (augmentedIndex 437))
  · exact (row1861_link w).symm.trans (h 3 (augmentedIndex 439))
  · exact (row1863_link w).symm.trans (h 3 (augmentedIndex 441))
  · exact (row1864_link w).symm.trans (h 3 (augmentedIndex 442))
  · exact (row1866_link w).symm.trans (h 3 (augmentedIndex 444))

#print axioms jetBlock_kernel_zero
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneOffWeightPoleExclusionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne SmallLevelFiniteShift
open QuantitativeArithmeticUniversalPoleVector

/-- The exceptional off-weight tuple is impossible: the finite stack of
four points has a nonzero Laurent vector, whereas the normalized rational
block has zero kernel. No lower-point pole-order assumption is used. -/
theorem actual_rightmost_pole_at_weight {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (w : Fin 42 → ℂ) (hw : IsLeadingVector G s w) (h28 : w 28=1)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    s=((2*m:ℕ):ℂ) := by
  by_contra hs
  obtain ⟨hE,hu,hv,hs0,ha⟩ := actual_exceptional_candidate hm hf ε hε hlaw BG G hG hGF
    s w hw h28 hshift hs
  have hm2 : 2≤m := by
    have hm1 : m≠1 := by intro h; subst m; norm_num at hs0; exact hs hs0
    omega
  obtain ⟨B,H,hH,hrow⟩ := augmented_matrix_germs hm hf ε hε hlaw BG G hG hGF
  obtain ⟨v,hv0,hvk⟩ := continued_block_kernel B G (augmentedLeading m f ε)
    (augmentedShift m f ε) H s 3 hG (augmentedLeading_analytic m f ε)
    (augmentedShift_analytic m f ε) hH hshift hrow (hw.exists_pole (fun j => hG j s))
  let e : (Fin 4×Fin 42) ≃ Fin 168 := finProdFinEquiv
  let u : Fin 168 → ℂ := fun i =>
    v (e.symm i)/jetScale (1-(m:ℂ)) (e.symm i).1
  have hrepr : scaledJetStack m u=v := by
    funext b
    simp only [scaledJetStack,u,e,Equiv.symm_apply_apply]
    field_simp [jetScale_ne_zero m hm2 b.1]
  have huk (n : Fin 4) (r : AugmentedRow) : jetBlockRow n r u=0 := by
    have hh := hvk (n,r)
    rw [hs0,← hrepr,actual_jetBlockRow m f ε hE hu hv ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left (jetScale_ne_zero m hm2 n)
  have hu0 := jetBlock_kernel_zero u huk
  apply hv0
  rw [← hrepr,hu0]
  funext b
  simp [scaledJetStack]

#print axioms actual_rightmost_pole_at_weight
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneLaurentShiftAnalyticV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne

theorem shifted_monomial_analytic (e : ℤ×ℤ×ℤ) (m : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z => threePrimeMonomial e (primeParameter 2 m z/2)
      (primeParameter 3 m z/3) (primeParameter 7 m z/7)) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  unfold threePrimeMonomial
  exact ((h2.div_const.zpow (by simpa using hn2)).mul
    (h3.div_const.zpow (by simpa using hn3))).mul
      (h7.div_const.zpow (by simpa using hn7))

theorem laurentShift_analytic (E u v : ℂ) (m : ℕ) (s : ℂ) (r : AugmentedRow) (j : Fin 42) :
    AnalyticAt ℂ (fun z => augmentedLaurentShift E u v
      (primeParameter 2 m z) (primeParameter 3 m z) (primeParameter 7 m z) r j) s := by
  rcases r with i | i | i | i | i
  · exact ((analyticAt_const.mul (shifted_monomial_analytic (augmentedWordRows i).powers m s)).mul
      analyticAt_const).mul analyticAt_const
  · exact analyticAt_const
  · exact ((analyticAt_const.mul (shifted_monomial_analytic (augmentedTaylorPowers i) m s)).mul
      analyticAt_const).mul analyticAt_const
  · exact analyticAt_const
  · exact analyticAt_const

#print axioms shifted_monomial_analytic
#print axioms laurentShift_analytic
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneSelectedRegularizedFirstShiftV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem selected_regularized_first_shift {ι : Type*} [Fintype ι]
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
    (s : ℂ) (w : Fin 42 → ℂ)
    (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*G z j) s w)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ∑ i, coeff (primeParameter 2 m s/2) (primeParameter 3 m s/3) (primeParameter 7 m s/7) i*
      augmentedLaurentShiftRow E u v
        (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) w (rows i)=0 := by
  classical
  obtain ⟨B,H,hH,hrow⟩ := augmented_matrix_germs hm hf ε hε hlaw BG G hG hGF
  let K : ℂ → ι → ℂ := fun z => coeff (primeParameter 2 m z) (primeParameter 3 m z) (primeParameter 7 m z)
  let A : ℂ → Matrix ι (Fin 42) ℂ := fun z i => augmentedLeading m f ε z (rows i)
  let C : ℕ → ℂ → Matrix ι (Fin 42) ℂ := fun n z i => augmentedShift m f ε n z (rows i)
  let L : ℂ → Matrix Unit ι ℂ := fun z _ i => K z i
  let D : ℂ → Matrix Unit (Fin 42) ℂ := fun z _ j =>
    I*∑ i, K (z-1) i*augmentedLaurentShift E u v
      (primeParameter 2 m z) (primeParameter 3 m z) (primeParameter 7 m z) (rows i) j
  have hKA (z : ℂ) (w : Fin 42 → ℂ) :
      ∑ i, K z i*(∑ j, A z i j*w j)=0 := by
    simp only [A,augmentedLeading_laurent,augmentedLaurent_apply,hE,hu,hvsign,ha,K]
    exact hsyz _ _ _ (primeParameter_ne_zero 2 m (by decide) z)
      (primeParameter_ne_zero 3 m (by decide) z) (primeParameter_ne_zero 7 m (by decide) z) w
  have hLA (z : ℂ) : L z*A z=0 := by
    ext r j
    have hh := hKA z (Pi.single j 1)
    simpa [Matrix.mul_apply,L,A,Pi.single_apply] using hh
  have hD (r : Unit) (j : Fin 42) : AnalyticAt ℂ (fun z => D z r j) s := by
    apply analyticAt_const.mul
    apply Finset.analyticAt_fun_sum
    intro i _
    exact ((hcoeff (s-1) i).comp (f:=fun z : ℂ => z-1)
      (analyticAt_id.sub analyticAt_const)).mul (laurentShift_analytic E u v m s (rows i) j)
  have hfactor (z : ℂ) (r : Unit) (j : Fin 42) :
      (L (z-1)*C 0 (z-1)) r j=(z-((2*m:ℕ):ℂ))*D z r j := by
    simp only [Matrix.mul_apply,L,C,D,augmentedShift_laurent,hE,hu,hvsign]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hh := IsLeadingVector.factored_first_shift B G A C
    (fun n z i => H n z (rows i)) L hG
    (fun n z i j => augmentedShift_analytic m f ε n z (rows i) j)
    (fun n i z hz => hH n (rows i) z hz) (fun z _ i => hcoeff z i)
    hLA (fun n i z hz => hrow n (rows i) z hz) s hshift
    (fun z => z-((2*m:ℕ):ℂ)) D hD hfactor w hw
  have hh' := congrFun hh ()
  change (∑ j, (I*∑ i, K (s-1) i*augmentedLaurentShift E u v
    (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) (rows i) j)*w j)=0 at hh'
  simp only [mul_assoc,← Finset.mul_sum,Finset.sum_mul] at hh'
  rw [Finset.sum_comm] at hh'
  simp only [← Finset.mul_sum,augmentedLaurentShift_apply,K,
    primeParameter_shift 2 m (by decide),primeParameter_shift 3 m (by decide),
    primeParameter_shift 7 m (by decide),Nat.cast_ofNat] at hh'
  exact (mul_eq_zero.mp hh').resolve_left I_ne_zero

#print axioms selected_regularized_first_shift
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularizedFirstJetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- The same checked certificate applies to a regularized pole vector,
including at the weight point where the first Taylor factor vanishes. -/
theorem FirstJetCertificate.regularized_pole_conditions {E u v : ℂ} (cert : FirstJetCertificate E u v)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (hE : phaseRoot m ε=E) (hu : rootU f=u) (hvsign : rootV f=v)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (w : Fin 42 → ℂ) (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*G z j) s w) (h28 : w 28=1)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2-1=0 ∧
      primeParameter 3 m s+3*u=0 ∧ primeParameter 7 m s=6*E*u+v := by
  have hwG := hw.of_analytic_factor (fun z => z-((2*m:ℕ):ℂ))
    (analyticAt_id.sub analyticAt_const)
  have hker := augmented_leading_pole hm hf ε hε hlaw BG G hG hGF s w hwG hshift
  have hk (r : AugmentedRow) :
      augmentedLaurentRow E u v (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 7 m s) ((Real.sqrt 2:ℂ)*f 2) w r=0 := by
    have hh := congrFun hker r
    change (∑ j, augmentedLeading m f ε s r j*w j)=0 at hh
    simpa only [augmentedLeading_apply_laurent,hE,hu,hvsign] using hh
  apply cert.conditions _ _ _ _ (primeParameter_ne_zero 2 m (by decide) s)
    (primeParameter_ne_zero 3 m (by decide) s) (primeParameter_ne_zero 7 m (by decide) s) w h28 hk
  · exact selected_regularized_first_shift cert.rows0 E u v ((Real.sqrt 2:ℂ)*f 2)
      (fun x y z => cert.coeff0 x y z ((Real.sqrt 2:ℂ)*f 2))
      (fun x y z hx hy hz w => cert.syzygy0 x y z _ hx hy hz w)
      hm hf ε hε hlaw hE hu hvsign rfl (cert.analytic0 m _) BG G hG hGF s w hw hshift
  · exact selected_regularized_first_shift cert.rows1 E u v ((Real.sqrt 2:ℂ)*f 2)
      (fun x y z => cert.coeff1 x y z ((Real.sqrt 2:ℂ)*f 2))
      (fun x y z hx hy hz w => cert.syzygy1 x y z _ hx hy hz w)
      hm hf ε hε hlaw hE hu hvsign rfl (cert.analytic1 m _) BG G hG hGF s w hw hshift


#print axioms FirstJetCertificate.regularized_pole_conditions
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneHigherWeightCandidateV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- A higher-order rightmost pole at the weight point forces weight two
and the same exceptional signs/eigenvalue. The regularized block argument
must then exclude this remaining higher-order possibility. -/
theorem higher_weight_pole_candidate {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (((2*m:ℕ):ℂ)+n))
    (hpole : ∃ j, meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)<(-1:WithTop ℤ)) :
    m=1 ∧ phaseRoot m ε= -1 ∧ rootU f= -1 ∧ rootV f=1 ∧
      (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ) := by
  obtain ⟨v,hv⟩ := exists_regularized_leading_vector G ((2*m:ℕ):ℂ)
    (fun j => (hG j _).meromorphicAt) hpole
  obtain ⟨w,hw,_hwG,h28⟩ := normalize_regularized_vector hm hf ε hε hlaw BG G hG hGF
    ((2*m:ℕ):ℂ) (fun z => z-((2*m:ℕ):ℂ)) (analyticAt_id.sub analyticAt_const) v hv hshift
  obtain ⟨cert⟩ := firstJetCertificate_all_signs (phaseRoot_sign m hε)
    (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData)
  obtain ⟨hx,hy,hz⟩ := cert.regularized_pole_conditions hm hf ε hε hlaw rfl rfl rfl
    BG G hG hGF ((2*m:ℕ):ℂ) w hw h28 hshift
  obtain ⟨hE,hu,hv,hs,ha⟩ := physical_first_jet m ((2*m:ℕ):ℂ) _ _ _ _
    (phaseRoot_sign m hε) (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData) hx hy hz
  have hm1 : m=1 := by
    have hh := congrArg Complex.re hs
    norm_num at hh
    have hmR : (m:ℝ)=1 := by linarith
    exact_mod_cast hmR
  exact ⟨hm1,hE,hu,hv,ha⟩

#print axioms higher_weight_pole_candidate
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularizedTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne SmallLevelFiniteShift

theorem monomial_analytic (e : ℤ×ℤ×ℤ) (m : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z => threePrimeMonomial e (primeParameter 2 m z)
      (primeParameter 3 m z) (primeParameter 7 m z)) s := by
  have h2 := primeParameter_analytic 2 m (by decide) s
  have h3 := primeParameter_analytic 3 m (by decide) s
  have h7 := primeParameter_analytic 7 m (by decide) s
  have hn2 := primeParameter_ne_zero 2 m (by decide) s
  have hn3 := primeParameter_ne_zero 3 m (by decide) s
  have hn7 := primeParameter_ne_zero 7 m (by decide) s
  unfold threePrimeMonomial
  exact ((h2.zpow hn2).mul (h3.zpow hn3)).mul (h7.zpow hn7)

theorem laurentTaylor_analytic (E u v : ℂ) (m n : ℕ) (s : ℂ)
    (r : AugmentedRow) (j : Fin 42) :
    AnalyticAt ℂ (fun z => augmentedLaurentTaylor E u v
      (primeParameter 2 m z) (primeParameter 3 m z) (primeParameter 7 m z) n r j) s := by
  rcases r with i | i | i | i | i
  · exact ((analyticAt_const.mul (monomial_analytic (augmentedWordRows i).powers m s)).mul
      analyticAt_const).mul analyticAt_const
  · exact analyticAt_const
  · exact ((analyticAt_const.mul (monomial_analytic (augmentedTaylorPowers i) m s)).mul
      analyticAt_const).mul analyticAt_const
  · exact analyticAt_const
  · exact analyticAt_const

def weightOneChooseQuot (n : Fin 4) (z : ℂ) : ℂ :=
  (![0,1,(z-3)/2,(z-3)*(z-4)/6] : Fin 4 → ℂ) n

theorem weightOneChoose_factor (n : Fin 4) (hn : n≠0) (z : ℂ) :
    Ring.choose (z-2) n.val=(z-2)*weightOneChooseQuot n z := by
  fin_cases n <;> norm_num at hn
  all_goals
    norm_num [weightOneChooseQuot,Ring.choose_eq_smul,← Polynomial.aeval_eq_smeval,
      descPochhammer_succ_right] <;> ring_nf <;> norm_num [map_ofNat] <;> ring

def weightOneTaylorQuot (f : ℕ → ℂ) (ε : ℂ) (n : Fin 4) (z : ℂ) :
    Matrix AugmentedRow (Fin 42) ℂ := fun r j =>
  (I^n.val*weightOneChooseQuot n z)*augmentedLaurentTaylor (phaseRoot 1 ε) (rootU f) (rootV f)
    (primeParameter 2 1 (z-n.val)) (primeParameter 3 1 (z-n.val))
    (primeParameter 7 1 (z-n.val)) n.val r j

theorem weightOneTaylorQuot_analytic (f : ℕ → ℂ) (ε : ℂ) (n : Fin 4)
    (s : ℂ) (r : AugmentedRow) (j : Fin 42) :
    AnalyticAt ℂ (fun z => weightOneTaylorQuot f ε n z r j) s := by
  have hq : AnalyticAt ℂ (fun z => weightOneChooseQuot n z) s := by
    fin_cases n
    · exact analyticAt_const
    · exact analyticAt_const
    · exact (analyticAt_id.sub analyticAt_const).div_const
    · exact ((analyticAt_id.sub analyticAt_const).mul
        (analyticAt_id.sub analyticAt_const)).div_const
  exact (analyticAt_const.mul hq).mul
    ((laurentTaylor_analytic (phaseRoot 1 ε) (rootU f) (rootV f) 1 n.val
      (s-n.val) r j).comp (f:=fun z : ℂ => z-(n.val:ℂ))
        (analyticAt_id.sub analyticAt_const))

theorem weightOneTaylorQuot_factor (f : ℕ → ℂ) (ε : ℂ) (n : Fin 4) (hn : n≠0)
    (z : ℂ) (r : AugmentedRow) (j : Fin 42) :
    augmentedShift 1 f ε (n.val-1) (z-n.val) r j=(z-2)*weightOneTaylorQuot f ε n z r j := by
  have hnpos : 0<n.val := Fin.pos_iff_ne_zero.mpr hn
  have hnval : n.val-1+1=n.val := by omega
  rw [augmentedShift_laurentTaylor,hnval]
  have he : z-(n.val:ℂ)+(n.val:ℂ)-((2*1:ℕ):ℂ)=z-2 := by norm_num
  rw [he,weightOneChoose_factor n hn]
  unfold weightOneTaylorQuot
  ring

def regularizedJetScale (n : Fin 4) : ℂ := (![1,I,-I^2,2*I^3] : Fin 4 → ℂ) n

theorem regularizedJetScale_ne_zero (n : Fin 4) : regularizedJetScale n≠0 := by
  fin_cases n <;> norm_num [regularizedJetScale,I_sq,I_ne_zero,pow_succ]

theorem regularizedJetScale_top (n : Fin 4) (hn : n≠0) :
    I^n.val*weightOneChooseQuot n 2=regularizedJetScale n/(n.val.factorial:ℂ) := by
  fin_cases n <;> norm_num at hn
  all_goals norm_num [weightOneChooseQuot,regularizedJetScale,I_sq,pow_succ] <;> ring

theorem regularizedJetScale_lower (n : Fin 4) (a : ℕ) (ha : a<n.val-1) :
    I^(a+1)*Ring.choose (-((n.val:ℂ))+((a+1:ℕ):ℂ)) (a+1)*
      regularizedJetScale (lowerIndex n a)=regularizedJetScale n/((a+1).factorial:ℂ) := by
  have ha2 : a≤1 := by omega
  interval_cases a <;> fin_cases n <;> norm_num at ha
  all_goals norm_num [regularizedJetScale,lowerIndex,Ring.choose_eq_smul,
    ← Polynomial.aeval_eq_smeval,descPochhammer_succ_right,I_sq,pow_succ] <;> ring

#print axioms weightOneTaylorQuot_factor
#print axioms weightOneTaylorQuot_analytic
#print axioms regularizedJetScale_lower
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularizedBlockModelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne SmallLevelFiniteShift

def regularizedScaledStack (w : Fin 168 → ℂ) (b : Fin 4×Fin 42) : ℂ :=
  regularizedJetScale b.1*w (finProdFinEquiv b)

theorem weightOneTaylorQuot_apply (f : ℕ → ℂ) (ε : ℂ) (n : Fin 4) (z : ℂ)
    (r : AugmentedRow) (w : Fin 42 → ℂ) :
    (∑ j, weightOneTaylorQuot f ε n z r j*w j)=
      (I^n.val*weightOneChooseQuot n z)*
        augmentedLaurentTaylorRow (phaseRoot 1 ε) (rootU f) (rootV f)
          (primeParameter 2 1 (z-n.val)) (primeParameter 3 1 (z-n.val))
          (primeParameter 7 1 (z-n.val)) n.val w r := by
  simp only [weightOneTaylorQuot,mul_assoc,← Finset.mul_sum,augmentedLaurentTaylor_apply]

theorem actual_regularizedBlockRow (f : ℕ → ℂ) (ε : ℂ)
    (hE : phaseRoot 1 ε= -1) (hu : rootU f= -1) (hv : rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (n : Fin 4) (r : AugmentedRow) (w : Fin 168 → ℂ) :
    (∑ b, regularizedBlock 3 (augmentedLeading 1 f ε) (augmentedShift 1 f ε)
      (weightOneTaylorQuot f ε) 2 (n,r) b*regularizedScaledStack w b)=
        regularizedJetScale n*jetBlockRow n r w := by
  have hp (p t : ℕ) (hp : p≠0) : primeParameter p 1 (2-(t:ℂ))=(p:ℂ)/(p:ℂ)^t := by
    simpa only [Nat.cast_one,one_add_one_eq_two] using primeParameter_candidate_lower p 1 t hp
  have hp0 (p : ℕ) (hpp : p≠0) : primeParameter p 1 2=(p:ℂ) := by
    simpa using hp p 0 hpp
  have hslice (n : Fin 4) : jetSlice w n=(fun j => w (finProdFinEquiv (n,j))) := rfl
  rw [regularizedBlock_apply]
  simp only [regularizedScaledStack,augmentedLeading_apply_laurent,
    augmentedShift_apply_laurentTaylor,weightOneTaylorQuot_apply,
    augmentedLaurentRow_scale,augmentedLaurentTaylorRow_scale,
    hp 2 _ (by decide),hp 3 _ (by decide),hp 7 _ (by decide),hE,hu,hv,ha,Nat.cast_ofNat]
  fin_cases n <;>
    norm_num [jetBlockRow,jetSlice,regularizedJetScale,weightOneChooseQuot,
      Finset.sum_range_succ,lowerIndex,Ring.choose_eq_smul,← Polynomial.aeval_eq_smeval,
      descPochhammer_succ_right,I_sq,pow_succ]
  all_goals try simp only [hslice]
  all_goals norm_num [hp0 2 (by decide),hp0 3 (by decide),hp0 7 (by decide)]
    <;> ring_nf <;> norm_num [I_sq] <;> ring

#print axioms actual_regularizedBlockRow
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneWeightPoleOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne SmallLevelFiniteShift
open QuantitativeArithmeticUniversalPoleVector

/-- Every rightmost pole at the weight point has order at most one.
The weight-two exceptional case is excluded using a regularized four-point
block; no equality or bound on lower-point pole orders is assumed. -/
theorem rightmost_weight_pole_order {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (((2*m:ℕ):ℂ)+n)) :
    ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ) := by
  by_contra h
  push Not at h
  obtain ⟨hm1,hE,hu,hv,ha⟩ := higher_weight_pole_candidate hm hf ε hε hlaw BG G hG hGF hshift h
  subst m
  have hpole : ∃ j, meromorphicOrderAt (fun z => (z-(2:ℂ))*G z j) 2<0 := by
    obtain ⟨j,hj⟩ := h
    norm_num at hj
    refine ⟨j,?_⟩
    have hloc : MeromorphicAt (fun z : ℂ => z-2) 2 :=
      (analyticAt_id.sub analyticAt_const).meromorphicAt
    change meromorphicOrderAt ((fun z : ℂ => z-2)*(fun z => G z j)) 2<0
    rw [meromorphicOrderAt_mul hloc (hG j 2).meromorphicAt,
      meromorphicOrderAt_id_sub_const]
    lift meromorphicOrderAt (fun z => G z j) 2 to ℤ using hj.ne_top with q hq
    have hqlt : q< -1 := by
      change (q:WithTop ℤ)<((-1:ℤ):WithTop ℤ) at hj
      exact WithTop.coe_lt_coe.mp hj
    exact_mod_cast (show 1+q<0 by omega)
  obtain ⟨B,H,hH,hrow⟩ := augmented_matrix_germs (by decide) hf ε hε hlaw BG G hG hGF
  obtain ⟨v,hv0,hvk⟩ := regularized_block_kernel B G (augmentedLeading 1 f ε)
    (augmentedShift 1 f ε) H 2 3 (weightOneTaylorQuot f ε) hG
    (augmentedLeading_analytic 1 f ε) (augmentedShift_analytic 1 f ε)
    (fun n r j => weightOneTaylorQuot_analytic f ε n 2 r j)
    (weightOneTaylorQuot_factor f ε) hH (by simpa using hshift) hrow hpole
  let e : (Fin 4×Fin 42) ≃ Fin 168 := finProdFinEquiv
  let u : Fin 168 → ℂ := fun i => v (e.symm i)/regularizedJetScale (e.symm i).1
  have hrepr : regularizedScaledStack u=v := by
    funext b
    simp only [regularizedScaledStack,u,e,Equiv.symm_apply_apply]
    field_simp [regularizedJetScale_ne_zero b.1]
  have huk (n : Fin 4) (r : AugmentedRow) : jetBlockRow n r u=0 := by
    have hh := hvk (n,r)
    rw [← hrepr,actual_regularizedBlockRow f ε hE hu hv ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left (regularizedJetScale_ne_zero n)
  have hu0 := jetBlock_kernel_zero u huk
  apply hv0
  rw [← hrepr,hu0]
  funext b
  simp [regularizedScaledStack]

#print axioms rightmost_weight_pole_order
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneGlobalWeightOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem any_pole_reaches_weight {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (B : ℝ) (hhalf : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z)
    (x : ℂ) (hpole : ∃ j, meromorphicOrderAt (fun z => G z j) x<0) :
    ∃ n : ℕ, x+n=((2*m:ℕ):ℂ) := by
  obtain ⟨n,w,hw,h28,hshift⟩ := normalized_rightmost_any_grid hm hf ε hε hlaw BG G hG hGF B hhalf x hpole
  exact ⟨n,actual_rightmost_pole_at_weight hm hf ε hε hlaw BG G hG hGF (x+n) w hw h28 hshift⟩

theorem regular_above_weight {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (B : ℝ) (hhalf : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z) :
    ∀ a : ℕ, 0<a → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (((2*m:ℕ):ℂ)+a) := by
  intro a ha j
  by_contra! hj
  obtain ⟨n,hn⟩ := any_pole_reaches_weight hm hf ε hε hlaw BG G hG hGF B hhalf
    (((2*m:ℕ):ℂ)+a) ⟨j,hj⟩
  have hh := congrArg Complex.re hn
  simp only [Complex.add_re,Complex.natCast_re] at hh
  have ha' : (0:ℝ)<a := by exact_mod_cast ha
  have hn' : (0:ℝ)≤n := Nat.cast_nonneg n
  linarith

theorem global_weight_pole_order {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (B : ℝ) (hhalf : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z) :
    ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ) :=
  rightmost_weight_pole_order hm hf ε hε hlaw BG G hG hGF
    (regular_above_weight hm hf ε hε hlaw BG G hG hGF B hhalf)

#print axioms any_pole_reaches_weight
#print axioms global_weight_pole_order
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularTailV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix Filter SmallLevelTwentyOne SmallLevelFiniteShift
open scoped Topology

theorem augmentedShift_zero_at_weight (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (s : ℂ) (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (r : AugmentedRow) (j : Fin 42) :
    augmentedShift m f ε n s r j=0 := by
  rw [augmentedShift_laurentTaylor]
  have he : s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using sub_eq_zero.mpr hs
  rw [he,Ring.choose_zero_succ,mul_zero,zero_mul]

/-- Every positive tail term remains regular if the only permitted upper
pole is a simple pole at the weight point. -/
theorem augmented_regular_tail (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (G : ℂ → Fin 42 → ℂ) (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (x : ℂ) (d : ℕ)
    (hshift : ∀ n : ℕ, 0<n → x+n≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (hk : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ))
    (a : ℕ) (ha : d≤a) (r : AugmentedRow) (j : Fin 42) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R (x-d) ∧
      (fun z => augmentedShift m f ε a z r j*G (z+((a:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-d)] R := by
  exact allowed_simple_pole_tail (augmentedShift m f ε) ((2*m:ℕ):ℂ)
    (augmentedShift_analytic m f ε) (augmentedShift_zero_at_weight m f ε)
    G hG x d hshift hk a ha r j

#print axioms augmentedShift_zero_at_weight
#print axioms augmented_regular_tail
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularSelectedShiftV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- A small selected row family suffices for a first-shift certificate.
All its rows are restrictions of the original 474-row analytic system. -/
theorem regular_selected_first_shift {ι : Type*} [Fintype ι]
    (rows : ι → AugmentedRow)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → x+n≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (hweight : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ))
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
  have h := IsLeadingVector.regular_tail_first_shift B G A C (fun n z i => H n z (rows i)) L
    (fun n z i j => augmentedShift_analytic m f ε n z (rows i) j)
    (fun n i z hz => hH n (rows i) z hz)
    (fun z _ i => hK z i) hLA (fun n i z hz => hrow n (rows i) z hz) x v hv
    (fun a ha i j => by simpa only [C,Nat.cast_one] using
      augmented_regular_tail m f ε G hG x 1 hshift hweight a ha (rows i) j)
  have hh : (L (x-1) *ᵥ (C 0 (x-1) *ᵥ v)) ()=0 := by
    rw [Matrix.mulVec_mulVec]
    exact congrFun h ()
  exact hh

#print axioms regular_selected_first_shift
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularSelectedLaurentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- A checked Laurent syzygy yields a genuine first-jet equation away
from the weight point. No hypothesis on the Hecke eigenvalue is needed. -/
theorem regular_selected_laurent_first_shift {ι : Type*} [Fintype ι]
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
    (hshift : ∀ n : ℕ, 0<n → s+n≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hweight : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ))
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
  have hh := regular_selected_first_shift rows hm hf ε hε hlaw BG G hG hGF s w hw hshift hweight K hcoeff hKA
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

#print axioms regular_selected_laurent_first_shift
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularAugmentedLeadingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem regular_augmented_leading_pole {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (w : Fin 42 → ℂ) (hw : IsLeadingVector G s w)
    (hshift : ∀ n : ℕ, 0<n → s+n≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hweight : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)) :
    augmentedLeading m f ε s *ᵥw=0 := by
  obtain ⟨B,H,hH,hrow⟩ := augmented_matrix_germs hm hf ε hε hlaw BG G hG hGF
  apply hw.regular_tail_leading B G (augmentedLeading m f ε) (augmentedShift m f ε)
    H s w (augmentedLeading_analytic m f ε s) hH
  · intro a r j
    simpa only [Nat.cast_zero,sub_zero] using
      augmented_regular_tail m f ε G hG s 0 hshift hweight a (Nat.zero_le a) r j
  · exact hrow

#print axioms regular_augmented_leading_pole
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularFirstJetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- Applying a concrete first-jet certificate to the original continued
Euler system, away from the weight point. -/
theorem FirstJetCertificate.regular_pole_conditions {E u v : ℂ} (cert : FirstJetCertificate E u v)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (hE : phaseRoot m ε=E) (hu : rootU f=u) (hvsign : rootV f=v)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (w : Fin 42 → ℂ) (hw : IsLeadingVector G s w) (h28 : w 28=1)
    (hshift : ∀ n : ℕ, 0<n → s+n≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hweight : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ))
    (hs : s≠((2*m:ℕ):ℂ)) :
    ((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2-1=0 ∧
      primeParameter 3 m s+3*u=0 ∧ primeParameter 7 m s=6*E*u+v := by
  have hker := regular_augmented_leading_pole hm hf ε hε hlaw BG G hG hGF s w hw hshift hweight
  have hk (r : AugmentedRow) :
      augmentedLaurentRow E u v (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 7 m s) ((Real.sqrt 2:ℂ)*f 2) w r=0 := by
    have hh := congrFun hker r
    change (∑ j, augmentedLeading m f ε s r j*w j)=0 at hh
    simpa only [augmentedLeading_apply_laurent,hE,hu,hvsign] using hh
  apply cert.conditions _ _ _ _ (primeParameter_ne_zero 2 m (by decide) s)
    (primeParameter_ne_zero 3 m (by decide) s) (primeParameter_ne_zero 7 m (by decide) s) w h28 hk
  · exact regular_selected_laurent_first_shift cert.rows0 E u v ((Real.sqrt 2:ℂ)*f 2)
      (fun x y z => cert.coeff0 x y z ((Real.sqrt 2:ℂ)*f 2))
      (fun x y z hx hy hz w => cert.syzygy0 x y z _ hx hy hz w)
      hm hf ε hε hlaw hE hu hvsign rfl (cert.analytic0 m _) BG G hG hGF s w hw hshift hweight hs
  · exact regular_selected_laurent_first_shift cert.rows1 E u v ((Real.sqrt 2:ℂ)*f 2)
      (fun x y z => cert.coeff1 x y z ((Real.sqrt 2:ℂ)*f 2))
      (fun x y z hx hy hz w => cert.syzygy1 x y z _ hx hy hz w)
      hm hf ε hε hlaw hE hu hvsign rfl (cert.analytic1 m _) BG G hG hGF s w hw hshift hweight hs

#print axioms FirstJetCertificate.regular_pole_conditions
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneRegularOriginalLeadingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem shiftMatrix_zero_at_weight (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (s : ℂ) (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (i j : Fin 42) :
    shiftMatrix m f ε n s i j=0 := by
  have he : s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using sub_eq_zero.mpr hs
  have hc (a : Fin 28) : rowCoefficient (2*m) f ε a (n+1) s=0 := by
    simp only [rowCoefficient,SmallLevelTaylor.taylorRowScalar,he,Ring.choose_zero_succ,mul_zero]
  rw [shiftMatrix_apply]
  fin_cases i <;> simp [shiftRows,assemble,hc]

theorem regular_original_leading_pole {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → s+n≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hk : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)) :
    leadingMatrix m f ε s *ᵥ v=0 := by
  obtain ⟨B,_hF,hH,hrow⟩ := matrix_system_of_law hm hf ε hlaw
  have hH' (n : ℕ) (i : Fin 42) (z : ℂ) (hz : max B BG-((n:ℝ)+1)<z.re) :
      AnalyticAt ℂ (fun w => errorVector m f ε n w i) z :=
    hH n i z (by linarith [le_max_left B BG])
  have he := SmallLevelContinuation.continued_rows (max B BG) (gridVector (2*m) f) G
    (leadingMatrix m f ε) (shiftMatrix m f ε) (errorVector m f ε)
    (fun i z => (hG i z).meromorphicAt)
    (fun z hz => hGF z (lt_of_le_of_lt (le_max_right B BG) hz))
    (leadingMatrix_analytic m f ε) (shiftMatrix_analytic m f ε) hH'
    (fun n z hz => hrow n z (lt_of_le_of_lt (le_max_left B BG) hz))
  apply hv.regular_tail_leading (max B BG) G (leadingMatrix m f ε)
    (shiftMatrix m f ε) (errorVector m f ε) s v
    (leadingMatrix_analytic m f ε s) hH'
  · intro a i j
    simpa only [Nat.cast_zero,sub_zero] using
      SmallLevelFiniteShift.allowed_simple_pole_tail (shiftMatrix m f ε) ((2*m:ℕ):ℂ)
        (shiftMatrix_analytic m f ε) (shiftMatrix_zero_at_weight m f ε)
        G hG s 0 hshift hk a (Nat.zero_le a) i j
  · intro n i y hy
    exact he n i y hy

#print axioms regular_original_leading_pole
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneWeightTwoLowerPolesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- At weight two, allowing a simple pole at two introduces no lower poles:
the complete Taylor tails remain regular and the first jet forces the
rightmost remaining pole back to two, a contradiction. -/
theorem weightTwo_no_offweight_pole {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 2 f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 2 f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector 2 f z)
    (B : ℝ) (hhalf : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z)
    (hweight : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) 2)
    (x : ℂ) (hx : x≠2) :
    ∀ j, 0≤meromorphicOrderAt (fun z => G z j) x := by
  by_contra h
  push Not at h
  obtain ⟨n,hne,hn,hshift⟩ := SmallLevelPoleGrid.rightmost_pole_away
    (fun i z => G z i) 2 hx h B hhalf
  obtain ⟨v,hv⟩ := exists_leading_vector G (x+n) (fun j => (hG j _).meromorphicAt) hn
  have hker := regular_original_leading_pole (m:=1) (by decide) hf ε hlaw BG G hG hGF
    (x+n) v hv hshift hweight
  have h28 : v 28≠0 := fun h0 => hv.1 (original_rank_coordinate hf hε v hker h0)
  obtain ⟨w,hw,hw28,_⟩ := hv.normalize 28 h28
  obtain ⟨cert⟩ := firstJetCertificate_all_signs (phaseRoot_sign 1 hε)
    (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData)
  obtain ⟨hx',hy,hz⟩ := cert.regular_pole_conditions (m:=1) (by decide) hf ε hε hlaw
    rfl rfl rfl BG G hG hGF (x+n) w hw hw28 hshift hweight hne
  obtain ⟨_,_,_,hs,_⟩ := physical_first_jet 1 (x+n) _ _ _ _
    (phaseRoot_sign 1 hε) (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData) hx' hy hz
  apply hne
  simpa only [Nat.cast_one,one_add_one_eq_two] using hs

#print axioms weightTwo_no_offweight_pole
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneFullPoleBoundV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem any_pole_exceptional_parameters {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (B : ℝ) (hhalf : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z)
    (x : ℂ) (hpole : ∃ j, meromorphicOrderAt (fun z => G z j) x<0) :
    m=1 ∧ phaseRoot m ε= -1 ∧ rootU f= -1 ∧ rootV f=1 ∧
      (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ) := by
  obtain ⟨n,w,hw,h28,hshift⟩ := normalized_rightmost_any_grid hm hf ε hε hlaw BG G hG hGF B hhalf x hpole
  have hs := actual_rightmost_pole_at_weight hm hf ε hε hlaw BG G hG hGF (x+n) w hw h28 hshift
  rw [hs] at hw hshift
  exact actual_weight_pole_candidate hm hf ε hε hlaw BG G hG hGF w hw h28 hshift

theorem any_grid_full_pole_bound {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (B : ℝ) (hhalf : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z) :
    (∀ x : ℂ, x≠((2*m:ℕ):ℂ) → ∀ j, AnalyticAt ℂ (fun z => G z j) x) ∧
    (∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)) ∧
    ((∃ j, meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)<0) →
      m=1 ∧ phaseRoot m ε= -1 ∧ rootU f= -1 ∧ rootV f=1 ∧
        (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) := by
  have hweight := global_weight_pole_order hm hf ε hε hlaw BG G hG hGF B hhalf
  refine ⟨?_,hweight,any_pole_exceptional_parameters hm hf ε hε hlaw BG G hG hGF B hhalf _⟩
  intro x hx j
  apply (hG j x).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hj
  have hm1 := (any_pole_exceptional_parameters hm hf ε hε hlaw BG G hG hGF B hhalf x ⟨j,hj⟩).1
  subst m
  have hh := weightTwo_no_offweight_pole hf ε hε hlaw BG G hG hGF B hhalf
    (by simpa using hweight) x (by simpa using hx) j
  exact (not_lt_of_ge hh) hj

/-- Original-input all-sign pole bound on the entire 42-grid. Only a simple
weight-two pole at the single exceptional parameter tuple remains. -/
theorem original_full_pole_bound {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ x : ℂ, x≠((2*m:ℕ):ℂ) → ∀ j, AnalyticAt ℂ (fun z => G z j) x) ∧
        (∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)) ∧
        ((∃ j, meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)<0) →
          m=1 ∧ phaseRoot m ε= -1 ∧ rootU f= -1 ∧ rootV f=1 ∧
            (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law
    (by decide : 0<21) hf
  obtain ⟨BG,G,hG,hGF,hhalf,_hH,_hrow⟩ := continued_system_of_law hm hf ε hε hlaw
  exact ⟨ε,hε,hlaw,BG,G,hG,hGF,any_grid_full_pole_bound hm hf ε hε hlaw BG G hG hGF BG hhalf⟩

#print axioms any_pole_exceptional_parameters
#print axioms any_grid_full_pole_bound
#print axioms original_full_pole_bound
end SmallLevelTwentyOneKnownWords
end
end

/-! ## SmallLevelTwentyOneTenthExchangeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Matrix ModularGroup UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelOriginal Complex
open scoped MatrixGroups ModularForm

def tenthExchange : SL(2,ℤ) := (-1)*(oddMatrix 21 11 (by decide))⁻¹*T

theorem tenthExchange_matrix : tenthExchange=(⟨!![-2,-1;21,10],by decide⟩ : SL(2,ℤ)) := by decide

theorem original_tenthExchange {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] tenthExchange=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  have hn : (-1:SL(2,ℤ))∈K := SmallLevelThirtySix.slash_neg_one_even _ m
  have he : (oddMatrix 21 11 (by decide))⁻¹∈K := K.inv_mem
    (original_odd (by decide) (by decide : 2*11=21+1) (by decide) hf)
  have ht : T∈K := original_T (2*m) f
  exact K.mul_mem (K.mul_mem hn he) ht

theorem sqrt_twentyOne_hundred : Real.sqrt 2100=10*Real.sqrt 21 := by
  rw [show (2100:ℝ)=100*21 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem tenth_exchange_factor :
    translation (-1/10)*fricke 2100 (by decide)=
      SpecialLinearGroup.mapGL ℝ tenthExchange*fricke 21 (by decide)*translation (1/10) := by
  rw [tenthExchange_matrix]
  have hs : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,translation,SmallLevelNormalized.matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_twentyOne_hundred] <;>
    field_simp [hn] <;> norm_num [hs]

/-- The two tenth translates are exchanged by conductor-2100 Fricke with
the original coherent phase. This precedes the quadratic-twist argument. -/
theorem original_tenth_exchange {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (-1/10)) ∣[((2*m:ℕ):ℤ)]
      fricke 2100 (by decide)=
        (ε*Complex.I^(2*m)) • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (1/10)) := by
  obtain ⟨_,hfr⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<21) m ε hε hlaw
  rw [← SlashAction.slash_mul,tenth_exchange_factor,SlashAction.slash_mul,SlashAction.slash_mul]
  change ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] tenthExchange) ∣[((2*m:ℕ):ℤ)]
    fricke 21 (by decide)) ∣[((2*m:ℕ):ℤ)] translation (1/10)=_
  rw [original_tenthExchange hf,hfr,det_one_smul _ (translation_det _)]

#print axioms tenth_exchange_factor
#print axioms original_tenth_exchange
end SmallLevelTwentyOneKnownWords
end
end
