module

public import QuantitativeMaassExceptionalWindowLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

namespace QuantitativeMaass

/-- The complementary smoothed windows partition the probability mass exactly. -/
theorem smoothedWindow_add_compl (K : SchwartzMap ℝ ℝ) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (S : Set ℝ) (hS : MeasurableSet S) (x : ℝ) :
    smoothedWindow K R S x+smoothedWindow K R Sᶜ x=1 := by
  unfold smoothedWindow
  rw [integral_add_compl hS ((scaledWindowKernel_integrable K R hR).comp_sub_left x),
    integral_sub_left_eq_self _ volume x,scaledWindowKernel_mass_one K hm R hR]

/-- A point separated from the complement has an explicit lower approximation. -/
theorem smoothedWindow_interior_lower (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) (S : Set ℝ) (hS : MeasurableSet S)
    (x δ : ℝ) (hδ : 0<δ) (hsep : ∀ u∈Sᶜ,δ≤|x-u|) (k : ℕ) :
    1-(∫ u,|u|^k*K u)/(R*δ)^k ≤ smoothedWindow K R S x := by
  have htail := smoothedWindow_distance_tail K hK R hR Sᶜ hS.compl x δ hδ hsep k
  have hmass := smoothedWindow_add_compl K hm R hR S hS x
  linarith

theorem enlarged_interval_complement_separation (a b δ x u : ℝ)
    (hx : x∈Icc a b) (hu : u∉Icc (a-δ) (b+δ)) : δ≤|x-u| := by
  by_cases hua : u<a-δ
  · have h := le_abs_self (x-u)
    linarith [hx.1]
  · have hub : b+δ<u := by
      by_contra hn
      exact hu ⟨le_of_not_gt hua,le_of_not_gt hn⟩
    have h := neg_le_abs (x-u)
    linarith [hx.2]

theorem enlarged_symmetricWindow_lower (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) (a b δ x : ℝ)
    (hδ : 0<δ) (hx : x∈Icc a b) (k : ℕ) :
    1-(∫ u,|u|^k*K u)/(R*δ)^k ≤
      smoothedWindow K R (Icc (a-δ) (b+δ)∪Icc (-(b+δ)) (-(a-δ))) x := by
  apply smoothedWindow_interior_lower K hK hm R hR _
    (measurableSet_Icc.union measurableSet_Icc) x δ hδ _ k
  intro u hu
  exact enlarged_interval_complement_separation a b δ x u hx
    (fun h => hu (Or.inl h))

/-- The normalized squared scalar window is at least one on the target interval. -/
theorem enlarged_squaredWindow_majorant (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x)
    (hm : (∫ x,K x)=1) (R : ℝ) (hR : 0<R) (a b δ x : ℝ)
    (hδ : 0<δ) (hx : x∈Icc a b) (k : ℕ)
    (htail : (∫ u,|u|^k*K u)/(R*δ)^k<1) :
    1≤(smoothedWindow K R (Icc (a-δ) (b+δ)∪Icc (-(b+δ)) (-(a-δ))) x)^2/
      (1-(∫ u,|u|^k*K u)/(R*δ)^k)^2 := by
  have hl := enlarged_symmetricWindow_lower K hK hm R hR a b δ x hδ hx k
  have hd : 0<1-(∫ u,|u|^k*K u)/(R*δ)^k := sub_pos.mpr htail
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  simpa only [one_mul] using pow_le_pow_left₀ hd.le hl 2

/-- Actual packet energy for one principal eigenvector dominates the same
explicit interior constant; no abstract multiplier identification is assumed. -/
theorem enlarged_windowWavePacket_eigen_lower (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (hKe : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b δ r : ℝ) (hδ : 0<δ) (ha : 0<a-δ)
    (hr : r∈Icc a b) (k : ℕ) (htail : (∫ u,|u|^k*K u)/(R*δ)^k≤1)
    (v : AutomorphicSpace N) (hv : ‖v‖=1)
    (hgraph : FriedrichsGraph N v (((1/4+r^2:ℝ):ℂ) • v)) :
    (1-(∫ u,|u|^k*K u)/(R*δ)^k)^2 ≤
      ‖windowWavePacket N K hc R hR (a-δ) (b+δ) v‖^2 := by
  rw [windowWavePacket_principal N K hKe hc R hR (a-δ) (b+δ) ha r hgraph,
    norm_smul,hv,mul_one,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact pow_le_pow_left₀ (sub_nonneg.mpr htail)
    (enlarged_symmetricWindow_lower K hK hm R hR a b δ r hδ hr k) 2

def principalWindowIndices {ι : Type*} (e : ι → ℝ) (a b : ℝ) : Set ι :=
  {i | 1/4≤e i ∧ Real.sqrt (e i-1/4)∈Icc a b}

/-- Actual finite-window counting follows from the previously proved coarse
cuspidal energy bound. This is not a Weyl asymptotic. -/
theorem principalWindowIndices_finite {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) (a b : ℝ) :
    (principalWindowIndices e a b).Finite := by
  obtain ⟨B,hB,hcount⟩ := cuspidal_spectral_band_polynomial N hN
  have hf := (hcount ι v hv hcusp e he hgraph (1/4+b^2) (by positivity)).1
  apply hf.subset
  intro i hi
  have hs := Real.sq_sqrt (sub_nonneg.mpr hi.1)
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg (e i-1/4)) hi.2.2 2
  change e i≤1/4+b^2
  nlinarith

/-- The literal number of principal cusp eigenvectors in the window is
controlled by the actual positive packet trace with an explicit normalization. -/
theorem principalWindow_count_le_packet {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (hKe : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b δ : ℝ) (hδ : 0<δ) (ha : 0<a-δ)
    (k : ℕ) (htail : (∫ u,|u|^k*K u)/(R*δ)^k≤1) :
    (1-(∫ u,|u|^k*K u)/(R*δ)^k)^2*(Nat.card (principalWindowIndices e a b):ℝ) ≤
      ∑' i,‖windowWavePacket N K hc R hR (a-δ) (b+δ) (v i)‖^2 := by
  classical
  let S := principalWindowIndices e a b
  have hf : S.Finite := principalWindowIndices_finite N hN v hv hcusp e he hgraph a b
  have hsum := windowWavePacket_square_summable N hN v hv hcusp e he hgraph K hc R hR (a-δ) (b+δ)
  have hpoint (i : ι) (hi : i∈S) :
      (1-(∫ u,|u|^k*K u)/(R*δ)^k)^2 ≤ ‖windowWavePacket N K hc R hR (a-δ) (b+δ) (v i)‖^2 := by
    have hsq := Real.sq_sqrt (sub_nonneg.mpr hi.1)
    have heq : 1/4+(Real.sqrt (e i-1/4))^2=e i := by linarith
    apply enlarged_windowWavePacket_eigen_lower N K hK hm hKe hc R hR a b δ
      (Real.sqrt (e i-1/4)) hδ ha hi.2 k htail (v i) (hv.norm_eq_one i)
    rw [heq]
    exact hgraph i
  calc
    _ = ∑ _i∈hf.toFinset,(1-(∫ u,|u|^k*K u)/(R*δ)^k)^2 := by
      have hcard : Nat.card S=hf.toFinset.card := Set.ncard_eq_toFinset_card S hf
      change _*(Nat.card S:ℝ)=_
      rw [hcard]
      simp [mul_comm]
    _ ≤ ∑ i∈hf.toFinset,‖windowWavePacket N K hc R hR (a-δ) (b+δ) (v i)‖^2 :=
      Finset.sum_le_sum (fun i hi => hpoint i (hf.mem_toFinset.mp hi))
    _ ≤ _ := Summable.sum_le_tsum _ (fun i _ => sq_nonneg _) hsum

/-- The chosen smoothing margin resolves the positive-radius packet. -/
theorem positiveWindowRadius_smoothing_product (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => positiveWindowRadius ε t*smoothingWidth (slowScale t) (ε t))
      atTop atTop := by
  have hp := (shrinking_window_parameters ε hε hproduct).2.2.2
  simp only [mul_comm] at hp
  refine tendsto_atTop_mono' atTop ?_ hp
  filter_upwards with t
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

/-- The explicit first-moment loss tends to zero at the original schedule. -/
theorem window_majorant_loss_tendsto (K : SchwartzMap ℝ ℝ) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (∫ u,|u| * K u)/
      (positiveWindowRadius ε t*smoothingWidth (slowScale t) (ε t))) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp (positiveWindowRadius_smoothing_product ε hε hproduct)
  simpa only [div_eq_mul_inv,Function.comp_def,mul_zero] using hi.const_mul (∫ u,|u| * K u)

theorem window_majorant_normalization_tendsto (K : SchwartzMap ℝ ℝ) (ε : ℝ → ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => (1-(∫ u,|u| * K u)/
      (positiveWindowRadius ε t*smoothingWidth (slowScale t) (ε t)))^2) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1)).sub
    (window_majorant_loss_tendsto K ε hε hproduct)).pow 2
  simpa only [sub_zero,one_pow] using h

/-- Enlarging the window preserves the main mass with explicit endpoint and
smoothing errors. This is a scalar integral, not a geometric trace identity. -/
theorem enlarged_squaredWindow_plancherel_mass (t ε δ : ℝ)
    (ht : 0<t-δ) (hε : 0≤ε) (hδ : 0≤δ)
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) :
    Integrable (fun x => (smoothedWindow K R
      (Icc (t-δ) (t+ε+δ)∪Icc (-(t+ε+δ)) (-(t-δ))) x)^2*windowPlancherelWeight x) ∧
    |(∫ x,(smoothedWindow K R (Icc (t-δ) (t+ε+δ)∪Icc (-(t+ε+δ)) (-(t-δ))) x)^2*
      windowPlancherelWeight x)-2*t*ε| ≤
      8*(1+t+ε+δ)*(∫ u,|u| * K u)/R+8*(∫ u,|u|^2*K u)/R^2+
        4*t*δ+ε^2+2*ε*δ+2*(ε+2*δ) := by
  obtain ⟨hi,hb⟩ := symmetric_squaredWindow_plancherel_mass (t-δ) (t+ε+δ) ht
    (by linarith) K hK hm R hR
  refine ⟨hi,?_⟩
  have hdiff : |((t+ε+δ)^2-(t-δ)^2)-2*t*ε|=4*t*δ+ε^2+2*ε*δ := by
    rw [show ((t+ε+δ)^2-(t-δ)^2)-2*t*ε=4*t*δ+ε^2+2*ε*δ by ring]
    apply abs_of_nonneg
    have ht0 : 0≤t := by linarith
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht0) hδ)
      (sq_nonneg ε)) (mul_nonneg (mul_nonneg (by norm_num) hε) hδ)
  have h := (abs_sub_le (∫ x,(smoothedWindow K R
    (Icc (t-δ) (t+ε+δ)∪Icc (-(t+ε+δ)) (-(t-δ))) x)^2*windowPlancherelWeight x)
    ((t+ε+δ)^2-(t-δ)^2) (2*t*ε)).trans (add_le_add hb (le_of_eq hdiff))
  convert h using 1
  ring

/-- The upper comparison for the original shrinking-window schedule. Its
coefficient tends to one and its right side is the literal positive-operator
diagonal. The geometric evaluation of that diagonal is a separate theorem. -/
theorem shrinking_principalWindow_count_comparison {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (K : SchwartzMap ℝ ℝ) (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (hKe : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∃ η : ℝ → ℝ,Tendsto η atTop (𝓝 1) ∧ ∀ᶠ t in atTop,
      η t*(Nat.card (principalWindowIndices e t (t+ε t)):ℝ) ≤
        ∑' i,(inner ℂ (v i)
          ((windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
            (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))).comp
           (windowWavePacket N K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
            (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))) (v i))).re := by
  let η := fun t => (1-(∫ u,|u| * K u)/
    (positiveWindowRadius ε t*smoothingWidth (slowScale t) (ε t)))^2
  have hep : ∀ᶠ t in atTop,0<ε t := hε.mono (fun _ h => h.1)
  refine ⟨η,window_majorant_normalization_tendsto K ε hep hproduct,?_⟩
  have hδ := (shrinking_window_parameters ε hep hproduct).2.2.1
  have hsmall := hδ.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have htail := (window_majorant_loss_tendsto K ε hep hproduct).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hε,hsmall,htail,slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
    eventually_gt_atTop (2:ℝ)] with t het hdt htt hLt ht
  have hp : 0<propagation (slowScale t) (ε t) := Real.sqrt_pos.mpr (div_pos hLt het.1)
  have hdpos : 0<smoothingWidth (slowScale t) (ε t) := Real.sqrt_pos.mpr (div_pos het.1 hp)
  have hdle : smoothingWidth (slowScale t) (ε t)<1 := by
    have h := (div_lt_iff₀ het.1).mp hdt
    linarith [het.2]
  simp_rw [windowWavePacket_square_diagonal N K hKe hc]
  have h := principalWindow_count_le_packet N hN v hv hcusp e he hgraph K hK hm hKe hc
    (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t)
    (smoothingWidth (slowScale t) (ε t)) hdpos (by linarith) 1
    (by simpa only [pow_one] using htt.le)
  simpa only [pow_one] using h

#print axioms shrinking_principalWindow_count_comparison

#print axioms positiveWindowRadius_smoothing_product
#print axioms window_majorant_loss_tendsto
#print axioms window_majorant_normalization_tendsto
#print axioms enlarged_squaredWindow_plancherel_mass

#print axioms smoothedWindow_add_compl
#print axioms smoothedWindow_interior_lower
#print axioms enlarged_interval_complement_separation
#print axioms enlarged_symmetricWindow_lower
#print axioms enlarged_squaredWindow_majorant
#print axioms enlarged_windowWavePacket_eigen_lower
#print axioms principalWindowIndices_finite
#print axioms principalWindow_count_le_packet

end QuantitativeMaass
