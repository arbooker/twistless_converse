module

public import QuantitativeMaassTimeCuspidalTraceV1
public import QuantitativeArithmeticMaassHeckeResolventV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap

namespace QuantitativeMaass

/-- Apply the genuine Hecke operator to a specified invariant representative.
This avoids composing arbitrary almost-everywhere representatives with branches. -/
theorem heckeOperator_coeFn_of_representative (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (v : AutomorphicSpace N) (f : ℍ → ℂ) (hf : Measurable f)
    (hinv : ∀ γ : gamma N,∀ z,f (γ•z)=f z)
    (hrep : v.val=ᵐ[quotientMeasure N]f) :
    (HeckeL2.operator N p hN hpN a b hab v).val=ᵐ[quotientMeasure N]
      normalizedCuspHecke N p f := by
  have hm : MemLp f 2 (quotientMeasure N) := (Lp.memLp v.val).ae_eq hrep
  let u : AutomorphicL2.representatives (gamma N) (quotientMeasure N) := ⟨f,hf,hinv,hm⟩
  have hu : AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) u=v := by
    apply Subtype.ext
    apply Lp.ext
    exact hm.coeFn_toLp.trans hrep.symm
  rw [← hu,HeckeL2.operator_on_representatives]
  rw [show normalizedCuspHecke N p f=
    (HeckeL2.heckeRepresentative N p hN hpN a b hab u).val from
      normalizedCuspHecke_eq_representative N p hN hpN hNp a b hab u]
  exact (HeckeL2.heckeRepresentative N p hN hpN a b hab u).property.2.2.coeFn_toLp

/-- Actual Hecke and every admissible time packet commute. The resolvent
commutation used here was proved on compact Poincare seeds and the closed form. -/
theorem heckeOperator_wavePacket_commute (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : ℝ → ℂ) (hf : Wave.ShiftedWaveWeight f) :
    Commute (HeckeL2.operator N p hN hpN a b hab) (Wave.shiftedQuotientWavePacket N f hf) := by
  let T := HeckeL2.operator N p hN hpN a b hab
  have ht (t : ℝ) (v : AutomorphicSpace N) :
      T (Wave.shiftedQuotientWave N t v)=Wave.shiftedQuotientWave N t (T v) :=
    DFunLike.congr_fun (QuantitativeArithmeticMaassHecke.hecke_shiftedWave_commute N p hN hpN a b hab t) v
  apply ContinuousLinearMap.ext
  intro v
  change T (∫ t,f t • Wave.shiftedQuotientWave N t v)=
    ∫ t,f t • Wave.shiftedQuotientWave N t (T v)
  rw [← T.integral_comp_comm (Wave.shiftedQuotientWave_packet_integrable N hf v)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by change T (f t • Wave.shiftedQuotientWave N t v)=_; rw [map_smul,ht])

/-- Any genuine continuous invariant column model commuting with Hecke has
its literal finite-branch action on columns, at every centre. -/
theorem hecke_column_of_commute (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (c : ℍ → AutomorphicSpace N) (hc : Continuous c)
    (hci : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun z => inner ℂ (c z) v))
    (hcomm : Commute (HeckeL2.operator N p hN hpN a b hab) A) (x : ℍ) :
    HeckeL2.operator N p hN hpN a b hab (c x)=
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) • ∑ j : Option (ZMod p),c (cuspBranchGL N p j • x) := by
  let T := HeckeL2.operator N p hN hpN a b hab
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (HeckeL2.operator_selfAdjoint N p hN hpN a b hab)
  apply ext_inner_right ℂ
  intro v
  let fv := fun z => inner ℂ (c z) v
  have hfc : Continuous fv := hc.inner continuous_const
  have hfi : ∀ γ : gamma N,∀ z,fv (γ•z)=fv z := fun γ z => by dsimp [fv];rw [hci]
  have hm : MemLp fv 2 (quotientMeasure N) := (Lp.memLp (A v).val).ae_eq (hrep v)
  let u : AutomorphicL2.representatives (gamma N) (quotientMeasure N) := ⟨fv,hfc.measurable,hfi,hm⟩
  have hn : normalizedCuspHecke N p fv=(HeckeL2.heckeRepresentative N p hN hpN a b hab u).val :=
    normalizedCuspHecke_eq_representative N p hN hpN hNp a b hab u
  have hnc : Continuous (normalizedCuspHecke N p fv) := by
    unfold normalizedCuspHecke cuspHeckeSum
    have hsum : Continuous (fun z => ∑ j : Option (ZMod p),fv (cuspBranchGL N p j • z)) := by
      apply continuous_finsetSum
      intro j _
      exact hfc.comp (continuous_const_smul (cuspBranchGL N p j))
    exact hsum.const_smul ((Real.sqrt (p:ℝ))⁻¹:ℝ)
  have hni : ∀ γ : gamma N,∀ z,normalizedCuspHecke N p fv (γ•z)=normalizedCuspHecke N p fv z := by
    rw [hn]
    exact (HeckeL2.heckeRepresentative N p hN hpN a b hab u).property.2.1
  have he : (fun z => inner ℂ (T (c z)) v)=ᵐ[quotientMeasure N]normalizedCuspHecke N p fv := by
    have hp := heckeOperator_coeFn_of_representative N p hN hpN hNp a b hab
      (A v) fv hfc.measurable hfi (hrep v)
    have htv : T (A v)=A (T v) := DFunLike.congr_fun hcomm v
    change (T (A v)).val=ᵐ[quotientMeasure N]normalizedCuspHecke N p fv at hp
    rw [htv] at hp
    filter_upwards [hrep (T v),hp] with z hz ht
    exact (hsym (c z) v).trans (hz.symm.trans ht)
  have hall := continuous_invariant_eq_of_ae N _ _
    ((T.continuous.comp hc).inner continuous_const) hnc
    (fun γ z => by simp only [Function.comp_apply,hci]) hni he
  have hx : inner ℂ (T (c x)) v=normalizedCuspHecke N p fv x := congrFun hall x
  change inner ℂ (T (c x)) v=_
  rw [hx]
  rw [inner_smul_left (∑ j : Option (ZMod p),c (cuspBranchGL N p j • x)) v
    ((((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)),sum_inner]
  simp only [Complex.conj_ofReal,normalizedCuspHecke,cuspHeckeSum,fv,Complex.real_smul]

/-- The original time Abel column has the literal normalized p+1 Hecke
branch sum. This is a statement about the actual Hilbert Hecke operator. -/
theorem timeAbelColumn_hecke (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (x : ℍ) :
    HeckeL2.operator N p hN hpN a b hab (timeAbelColumn N f hc he R hR hs x)=
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) • ∑ j : Option (ZMod p),
        timeAbelColumn N f hc he R hR hs (cuspBranchGL N p j • x) := by
  apply hecke_column_of_commute N p hN hpN hNp a b hab
    (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc))
  · exact oneSidedAbelColumn_continuous N _ _ _ _ _
  · exact oneSidedAbelColumn_invariant N _ _ _ _ _
  · exact timeAbelColumn_packet_coeFn N f hc he hr R hR hs
  · exact heckeOperator_wavePacket_commute N p hN hpN a b hab f _

/-- The first actual Hecke-weighted square kernel, globally in the centre.
Higher words and their quantitative geometry still require separate estimates. -/
theorem timeSquare_hecke_kernel (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (x : ℍ) :
    inner ℂ (HeckeL2.operator N p hN hpN a b hab (timeAbelColumn N f hc he R hR hs x))
      (timeAbelColumn N f hc he R hR hs x)=
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) * ∑ j : Option (ZMod p),
        radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) x (cuspBranchGL N p j • x) := by
  rw [timeAbelColumn_hecke N p hN hpN hNp a b hab f hc he hr R hR hs]
  rw [inner_smul_left (∑ j : Option (ZMod p),timeAbelColumn N f hc he R hR hs (cuspBranchGL N p j • x))
    (timeAbelColumn N f hc he R hR hs x) ((((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)),sum_inner]
  simp only [Complex.conj_ofReal,timeSquare_kernel_cross N f hc he hr R hR hs]

/-- Iterate the literal normalized finite correspondence on functions.
No quotient operator or formal spectral moment is used in this definition. -/
def heckeBranchIterate (N p : ℕ) [Fact p.Prime] : ℕ → (ℍ → ℂ) → ℍ → ℂ
  | 0,g => g
  | n+1,g => normalizedCuspHecke N p (heckeBranchIterate N p n g)

/-- Every power of the actual Hecke operator has the literal iterated
finite-branch square-kernel formula, globally at every pair of centres. -/
theorem timeSquare_hecke_power_kernel (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (n : ℕ) (x y : ℍ) :
    inner ℂ (((HeckeL2.operator N p hN hpN a b hab)^n) (timeAbelColumn N f hc he R hR hs x))
      (timeAbelColumn N f hc he R hR hs y)=
      heckeBranchIterate N p n
        (fun z => radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) y z) x := by
  let T := HeckeL2.operator N p hN hpN a b hab
  let c := timeAbelColumn N f hc he R hR hs
  let α : ℂ := (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)
  have hcol (z : ℍ) : T (c z)=α • ∑ j : Option (ZMod p),c (cuspBranchGL N p j • z) :=
    timeAbelColumn_hecke N p hN hpN hNp a b hab f hc he hr R hR hs z
  have hscalar (w : AutomorphicSpace N) : inner ℂ (α • w) (c y)=α*inner ℂ w (c y) := by
    rw [inner_smul_left w (c y) α]
    simp only [α,Complex.conj_ofReal]
  change inner ℂ ((T^n) (c x)) (c y)=_
  induction n generalizing x with
  | zero =>
    simpa only [pow_zero,one_apply_eq_self,heckeBranchIterate] using
      timeSquare_kernel_cross N f hc he hr R hR hs y x
  | succ n ih =>
    rw [pow_succ]
    change inner ℂ ((T^n) (T (c x))) (c y)=_
    rw [hcol,map_smul,map_sum,hscalar,sum_inner]
    simp_rw [ih]
    simp only [heckeBranchIterate,normalizedCuspHecke,cuspHeckeSum,α,Complex.real_smul]

#print axioms timeSquare_hecke_power_kernel

#print axioms heckeOperator_coeFn_of_representative
#print axioms heckeOperator_wavePacket_commute
#print axioms hecke_column_of_commute
#print axioms timeAbelColumn_hecke
#print axioms timeSquare_hecke_kernel

end QuantitativeMaass
