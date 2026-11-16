module

public import QuantitativeMaassCuspCountingV1
public import QuantitativeMaassAbelEnergyBoundsV1
public import QuantitativeArithmeticMaassCuspidalDiscretenessV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open QuantitativeSpectralObservability QuantitativeArithmeticMaassOverlap
open QuantitativeArithmeticMaassCuspBand
open scoped ENNReal MatrixGroups ContDiff

namespace QuantitativeMaass

universe u

theorem shortRadius_cosh_sub_one_le_one (R : ℝ) (hR : 0≤R) (hR4 : R≤1/4) :
    Real.cosh R-1≤1 := by
  have he := Real.exp_bound_div_one_sub_of_interval hR (by linarith : R<1)
  have hd : (1:ℝ)/(1-R)≤2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hn : Real.exp (-R)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.cosh_eq]
  linarith

/-- A deliberately coarse polynomial bound for genuine cuspidal Friedrichs
eigenfamilies. This supplies polynomial growth for smoothing arguments; it is
not the Weyl main term or a short-window asymptotic. -/
theorem cuspidal_eigenfamily_polynomial_bound (N : ℕ) (hN : 0<N) :
    ∃ B : ℝ,0<B ∧ ∀ (ι : Type u) (E : ℝ),0≤E → ∀ v : ι → AutomorphicSpace N,
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      ∀ e : ι → ℝ,(∀ i,0≤e i) → (∀ i,e i≤E) →
      (∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) →
      ∀ s : Finset ι,(s.card:ℝ)≤B*(E+1)^6 := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨C,D,hC,hD,hgeo⟩ := cuspCore_overlap_polynomial N hN
  obtain ⟨A,hA,hprofile⟩ := abelCutoff_square_energy_uniform
  obtain ⟨c,hc,hmass⟩ := abelCutoff_time_mass_uniform_lower
  let Q : ℝ := Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  let T : ℝ := 8*Q*N^2*(N+1)
  let K : ℝ := 50+2*T
  have hQ : 0≤Q := Nat.cast_nonneg _
  have hT : 0≤T := by dsimp [T]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  let B : ℝ := 128*(D*A*(Q*40))*K^4/c^2+1
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro ι E hE v hv hcusp e he heE hgraph s
  choose u hu hform using fun i => (friedrichsGraph_iff_form N _ _).mp (hgraph i)
  have henergy (i : ι) : (quotientClosedEnergy N (u i) (u i)).re≤E*‖energyInclusion N (u i)‖^2 := by
    have hself : (inner ℂ (v i) (v i)).re=‖v i‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) _
    rw [hform i (u i),hu i,inner_smul_right (𝕜:=ℂ) (v i) (v i) (e i:ℂ),
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hself]
    exact mul_le_mul_of_nonneg_right (heE i) (sq_nonneg ‖v i‖)
  let R : ℝ := 1/(4*(E+1))
  have hd : 0<4*(E+1) := by positivity
  have hR : 0<R := by dsimp [R]; positivity
  have hR4 : R≤1/4 := by
    dsimp [R]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hR1 : R≤1 := by linarith
  have hReq : R*(4*(E+1))=1 := div_mul_cancel₀ 1 hd.ne'
  have hsmall : 4*R^2*(E+1)≤1 := by
    calc
      _ = R*(R*(4*(E+1))) := by ring
      _ = R := by rw [hReq,mul_one]
      _ ≤ 1 := hR1
  let Y : ℝ := 2+Real.sqrt (T*E)
  have hY : 2≤Y := by dsimp [Y]; linarith [Real.sqrt_nonneg (T*E)]
  have hTE : 0≤T*E := mul_nonneg hT hE
  have hsize : 8*Q*N^2*(N+1)*E≤Y^2 := by
    change T*E≤Y^2
    dsimp [Y]
    nlinarith [Real.sq_sqrt hTE,Real.sqrt_nonneg (T*E)]
  have hY2 : (Y+3)^2≤K*(E+1) := by
    dsimp [Y,K]
    nlinarith [Real.sq_sqrt hTE,sq_nonneg (Real.sqrt (T*E)-5)]
  have hY8 : (Y+3)^8≤K^4*(E+1)^4 := by
    have hh := pow_le_pow_left₀ (sq_nonneg (Y+3)) hY2 4
    simpa only [←pow_mul,mul_pow] using hh
  let L := Real.log (C*(Y+3)^2)
  have hcore := (hgeo Y hY).1
  have hmult := (hgeo Y hY).2 R hR.le hR1
  let F := abelCutoff (Real.cosh R-1)
  have ha : 0<Real.cosh R-1 := sub_pos.mpr (Real.one_lt_cosh.mpr hR.ne')
  have hFc : HasCompactSupport F := abelCutoff_compact _ ha
  have hFs : Function.support F⊆Iic (Real.cosh R) := abelCutoff_radius_support R hR
  have hFr (q : ℝ) : star (F q)=F q := by simp [F,abelCutoff]
  let g := abelProfile F
  have hg : ContDiff ℝ ∞ g := abelProfile_smooth F (abelCutoff_smooth _) hFc
  have hgr (q : ℝ) : star (g q)=g q := abelProfile_real F hFr q
  have hgs : Function.support g⊆Iic (Real.cosh R) := abelProfile_support F _ hFs
  have hradial : (2*Real.pi)*(∫ q in Ioi (1:ℝ),‖g q‖^2)≤A :=
    hprofile _ ha (shortRadius_cosh_sub_one_le_one R hR.le hR4)
  have hpacket (i : ι) : radialKernelOperator N g hg R hR.le hgs (energyInclusion N (u i))=
      (shortPacketMultiplier R (e i):ℂ) • energyInclusion N (u i) := by
    rw [hu i]
    change abelKernelOperator N F (abelCutoff_smooth _) hFc R hR.le hFs (v i)=_
    rw [abelKernelOperator_eq_coshWavePacket N F (abelCutoff_smooth _) hFc hFr R hR.le hFs]
    exact shortPacket_eigen N R hR (he i) (hgraph i)
  have hlower (i : ι) : c*R/2≤‖(shortPacketMultiplier R (e i):ℂ)‖ := by
    simp only [Complex.norm_real,Real.norm_eq_abs]
    have hm : c*R≤∫ t,shortTimeWeight R t := hmass R hR
    exact (by linarith : c*R/2≤(∫ t,shortTimeWeight R t)/2).trans
      ((shortPacketMultiplier_lower E R (e i) hR hR1 hsmall (he i) (heE i)).trans (le_abs_self _))
  have hcard := cuspidal_packet_finset_card N hN u (by simpa only [hu] using hv)
    (fun i => by simpa only [hu] using hcusp i) E Y L hY hsize henergy hcore
    g hg hgr R hR.le hgs (fun i => (shortPacketMultiplier R (e i):ℂ))
    (c*R/2) (by positivity) hlower hpacket s
  have hmA : (energyMultiplicity I L R:ℝ)*((2*Real.pi)*∫ q in Ioi (1:ℝ),‖g q‖^2)≤
      (D*(Y+3)^8)*A :=
    (mul_le_mul_of_nonneg_left hradial (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hmult hA.le)
  have hbound : (s.card:ℝ)*((c*R/2)^2/2)≤(D*A*(Q*40))*K^4*(E+1)^4 := by
    calc
      _ ≤ _ := hcard
      _ ≤ (D*(Y+3)^8*A)*(Q*40) := mul_le_mul_of_nonneg_right hmA (by positivity)
      _ = (D*A*(Q*40))*(Y+3)^8 := by ring
      _ ≤ (D*A*(Q*40))*(K^4*(E+1)^4) := mul_le_mul_of_nonneg_left hY8 (by positivity)
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_right hbound (by positivity : 0≤128*(E+1)^2)
  have hcancel : ((c*R/2)^2/2)*(128*(E+1)^2)=c^2 := by
    dsimp [R]
    field_simp [ne_of_gt (show 0<E+1 by positivity)]
    norm_num
  have hfinal : (s.card:ℝ)*c^2≤128*(D*A*(Q*40))*K^4*(E+1)^6 := by
    calc
      _ = ((s.card:ℝ)*((c*R/2)^2/2))*(128*(E+1)^2) := by rw [mul_assoc,hcancel]
      _ ≤ _ := hscaled
      _ = _ := by ring
  have hdiv : (s.card:ℝ)≤128*(D*A*(Q*40))*K^4*(E+1)^6/c^2 :=
    (le_div_iff₀ (sq_pos_of_pos hc)).mpr hfinal
  apply hdiv.trans
  calc
    _ = (128*(D*A*(Q*40))*K^4/c^2)*(E+1)^6 := by ring
    _ ≤ B*(E+1)^6 := by dsimp [B]; nlinarith [show 0≤(E+1)^6 by positivity]

/-- One constant works for every energy cutoff in any actual orthonormal
cuspidal eigenfamily, including a family with unbounded eigenvalues. -/
theorem cuspidal_spectral_band_polynomial (N : ℕ) (hN : 0<N) :
    ∃ B : ℝ,0<B ∧ ∀ (ι : Type u) (v : ι → AutomorphicSpace N),
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      ∀ e : ι → ℝ,(∀ i,0≤e i) →
      (∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) →
      ∀ E : ℝ,0≤E → {i | e i≤E}.Finite ∧
        (Nat.card {i // e i≤E}:ℝ)≤B*(E+1)^6 := by
  obtain ⟨B,hB,hcount⟩ := cuspidal_eigenfamily_polynomial_bound N hN
  refine ⟨B,hB,?_⟩
  intro ι v hv hcusp e he hgraph E hE
  let J := {i // e i≤E}
  have hON : Orthonormal ℂ (fun i : J => v i.val) := hv.comp _ Subtype.val_injective
  have hfinite := cuspidal_bounded_eigenfamily_finite N hN E hE
    (fun i : J => v i.val) hON (fun i => hcusp i.val)
    (fun i : J => e i.val) (fun i => he i.val) (fun i => i.property)
    (fun i => hgraph i.val)
  let : Finite J := Set.finite_univ_iff.mp hfinite
  let : Fintype J := Fintype.ofFinite J
  refine ⟨Set.finite_coe_iff.mp (show Finite J from inferInstance),?_⟩
  have h := hcount J E hE (fun i : J => v i.val) hON (fun i => hcusp i.val)
    (fun i : J => e i.val) (fun i => he i.val) (fun i => i.property)
    (fun i => hgraph i.val) Finset.univ
  simpa only [Finset.card_univ,Nat.card_eq_fintype_card] using h

#print axioms shortRadius_cosh_sub_one_le_one
#print axioms cuspidal_eigenfamily_polynomial_bound
#print axioms cuspidal_spectral_band_polynomial

end QuantitativeMaass
