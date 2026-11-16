module

public import QuantitativeMaassPacketDiagonalV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology ContDiff SchwartzMap FourierTransform

namespace QuantitativeMaass

local instance (N : ℕ) : DecidableEq (gamma N) := Classical.decEq _

/-- The actual nonidentity diagonal sum; the projective group counts scalar
representatives only once. Summability follows below from finite propagation. -/
def radialNonidentity (N : ℕ) (g : ℝ → ℂ) (x : ℍ) : ℂ :=
  ∑' γ : gamma N,if γ=1 then 0 else g (Real.cosh (dist (γ•x) x))

/-- One explicit finite orbit set, chosen before the radial test or centre. -/
def diagonalOrbitSet (N : ℕ) (o : ℍ) (D : ℝ) : Finset (gamma N) :=
  (compact_orbit_point_finite (G:=gamma N) (Metric.closedBall o D)
    (isCompact_closedBall o D) o).toFinset

theorem mem_diagonalOrbitSet (N : ℕ) (o : ℍ) (D : ℝ) (γ : gamma N) :
    γ∈diagonalOrbitSet N o D ↔ dist (γ•o) o≤D := by
  simp only [diagonalOrbitSet,Set.Finite.mem_toFinset,Metric.mem_closedBall,Set.mem_ofPred_eq]

theorem diagonalOrbitSet_card_bound (N : ℕ) [NeZero N] (o : ℍ) (D : ℝ) :
    (diagonalOrbitSet N o D).card≤energyMultiplicity o 0 D := by
  apply radial_support_overlap N o 0 D o
  intro γ hγ
  change dist (γ•o) o≤D+0
  simpa only [add_zero] using (mem_diagonalOrbitSet N o D γ).mp hγ

/-- Every displacement relevant anywhere in the L-ball lies in one set of
translates at the base point, with radius R+2L. -/
theorem displacement_in_diagonalOrbitSet (N : ℕ) (o x : ℍ) (L R : ℝ)
    (hx : dist x o≤L) (γ : gamma N) (hγ : dist (γ•x) x≤R) :
    γ∈diagonalOrbitSet N o (R+2*L) := by
  apply (mem_diagonalOrbitSet N o (R+2*L) γ).mpr
  have h1 := dist_triangle (γ•o) (γ•x) o
  have h2 := dist_triangle (γ•x) x o
  rw [congruence_action_dist,dist_comm o x] at h1
  linarith

/-- Exact finite nonidentity sum, uniformly valid on a fixed ball of centres. -/
theorem radialNonidentity_eq_finite (N : ℕ) (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (o x : ℍ) (L : ℝ) (hx : dist x o≤L) :
    radialNonidentity N g x=∑ γ∈(diagonalOrbitSet N o (R+2*L)).erase 1,
      g (Real.cosh (dist (γ•x) x)) := by
  classical
  unfold radialNonidentity
  rw [tsum_eq_sum (s:=(diagonalOrbitSet N o (R+2*L)).erase 1) (fun γ hγ => ?_)]
  · apply Finset.sum_congr rfl
    intro γ hγ
    exact ite_eq_right (Finset.mem_erase.mp hγ).1
  · by_cases he : γ=1
    · simp only [he,ite_true]
    · rw [ite_eq_right he]
      by_contra hn
      have hh : dist (γ•x) x≤R := by
        have hb := Real.cosh_le_cosh.mp (hs hn)
        simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] using hb
      exact hγ (Finset.mem_erase.mpr ⟨he,displacement_in_diagonalOrbitSet N o x L R hx γ hh⟩)

/-- The literal diagonal separates into its identity and nonidentity terms. -/
theorem radialPoincareKernel_diagonal_split (N : ℕ) (g : ℝ → ℂ)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ) :
    radialPoincareKernel N g x x=g 1+radialNonidentity N g x := by
  classical
  have hc : HasCompactSupport (upperFunction (radialFunction g x)) :=
    (isCompact_closedBall x R).of_isClosed_subset isClosed_closure
      (radialFunction_support g x R hR hs)
  have hsum : Summable (fun γ : gamma N => upperFunction (radialFunction g x) (γ•x)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support _ hc x)
  simp only [radialFunction_upper] at hsum
  have hh := hsum.tsum_eq_add_tsum_ite 1
  simpa only [radialPoincareKernel,poincareSum,radialFunction_upper,
    one_smul,dist_self,Real.cosh_zero,radialNonidentity] using hh

/-- A continuous physical profile gives a continuous nonidentity remainder. -/
theorem radialNonidentity_continuous (N : ℕ) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) : Continuous (radialNonidentity N g) := by
  have he : radialNonidentity N g=(fun x => radialPoincareKernel N g x x-g 1) := by
    funext x
    rw [radialPoincareKernel_diagonal_split N g R hR hs]
    abel
  rw [he]
  exact ((radialPoincareKernel_joint_continuous_physical N g hg R hR hs).comp
    (continuous_id.prodMk continuous_id)).sub continuous_const

/-- Nonidentity terms are locally integrable on the actual quotient. -/
theorem radialNonidentity_integrableOn_compact (N : ℕ) [NeZero N] (g : ℝ → ℂ)
    (hg : ContinuousOn g (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) (S : Set ℍ) (hS : IsCompact S) :
    IntegrableOn (radialNonidentity N g) S (quotientMeasure N) :=
  (radialNonidentity_continuous N g hg R hR hs).continuousOn.integrableOn_compact hS

/-- An explicit lattice factor bounds the actual nonidentity sum when a
physical-profile bound is available. This is not a sharp oscillatory estimate. -/
theorem radialNonidentity_norm_bound (N : ℕ) [NeZero N] (g : ℝ → ℂ)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R))
    (o x : ℍ) (L : ℝ) (hx : dist x o≤L) (C : ℝ) (hC : 0≤C)
    (hb : ∀ q,1≤q → ‖g q‖≤C) :
    ‖radialNonidentity N g x‖≤(energyMultiplicity o 0 (R+2*L):ℝ)*C := by
  classical
  rw [radialNonidentity_eq_finite N g R hR hs o x L hx]
  calc
    _ ≤ ∑ γ∈(diagonalOrbitSet N o (R+2*L)).erase 1,
        ‖g (Real.cosh (dist (γ•x) x))‖ := norm_sum_le _ _
    _ ≤ ∑ _γ∈(diagonalOrbitSet N o (R+2*L)).erase 1,C :=
      Finset.sum_le_sum (fun γ _ => hb _ (Real.one_le_cosh _))
    _ = (((diagonalOrbitSet N o (R+2*L)).erase 1).card:ℝ)*C := by simp
    _ ≤ _ := by
      have hh : ((diagonalOrbitSet N o (R+2*L)).erase 1).card≤energyMultiplicity o 0 (R+2*L) :=
        Finset.card_erase_le.trans (diagonalOrbitSet_card_bound N o (R+2*L))
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hC

/-- The true quotient square energy equals the spherical identity term plus
its explicitly defined nonidentity group sum. -/
theorem timeSquare_energy_split (N : ℕ) [NeZero N]
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) :
    ∀ᵐ x ∂quotientMeasure N,
      ((∫ y,‖radialPoincareKernel N (abelProfile (evenCoshLift f)) x y‖^2
        ∂quotientMeasure N : ℝ):ℂ)=
      abelProfile (evenCoshLift (timeConvolution f f)) 1+
        radialNonidentity N (abelProfile (evenCoshLift (timeConvolution f f))) x := by
  filter_upwards [timeSquare_kernel_diagonal_ae N f hc he hr R hR hs] with x hx
  rw [hx]
  apply radialPoincareKernel_diagonal_split N _ (R+R) (add_nonneg hR hR)
  exact abelProfile_support _ _ (evenCoshLift_support_of_time_support _ _ (add_nonneg hR hR)
    (timeConvolution_support f f R R hs hs))

/-- The actual moving-window geometric error, as a literal nonidentity sum. -/
def windowGeometricRemainder (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R) (a b : ℝ) (x : ℍ) : ℂ :=
  radialNonidentity N (abelProfile (evenCoshLift (timeConvolution
    (windowTimeSchwartz K hc R hR a b) (windowTimeSchwartz K hc R hR a b)))) x

theorem windowTimeSquare_energy_split (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    ∀ᵐ x ∂quotientMeasure N,
      ((∫ y,‖radialPoincareKernel N
        (abelProfile (evenCoshLift (windowTimeSchwartz K hc R hR a b))) x y‖^2
        ∂quotientMeasure N : ℝ):ℂ)=windowIdentityContribution K hc R hR a b+
          windowGeometricRemainder N K hc R hR a b x := by
  obtain ⟨B,hB,hs⟩ := symmetricWindowTimeTest_uniform_support K hc
  exact timeSquare_energy_split N (windowTimeSchwartz K hc R hR a b)
    (symmetricWindowTimeTest_compact K hc R a b hR)
    (symmetricWindowTimeTest_even K he R a b)
    (symmetricWindowTimeTest_real K he R a b) (B*R) (mul_nonneg hB.le hR.le) (hs R hR a b)

/-- The original uniform spherical main term now bounds the actual quotient
energy error up to the literal nonidentity sum; no bound on that sum is assumed. -/
theorem exists_uniform_window_energy_error :
    ∃ (K : SchwartzMap ℝ ℝ) (C : ℝ)
      (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))),
      0<C ∧ (∀ x,0≤K x) ∧ Function.Even K ∧ (∫ x,K x)=1 ∧
      ∀ (N : ℕ) [NeZero N] (t ε δ R : ℝ) (hR : 0<R),1≤t → ε∈Icc (0:ℝ) 1 →
        0≤δ → 2*δ≤ε → 1≤R → 1/R≤δ → ∀ᵐ x ∂quotientMeasure N,
        ‖((∫ y,‖radialPoincareKernel N
          (abelProfile (evenCoshLift (windowTimeSchwartz K hc R hR (t+δ) (t+ε-δ)))) x y‖^2
          ∂quotientMeasure N : ℝ):ℂ)-((t*ε/(2*Real.pi):ℝ):ℂ)‖ ≤
          C*(t*δ+1)+‖windowGeometricRemainder N K hc R hR (t+δ) (t+ε-δ) x‖ := by
  obtain ⟨K,C,hc,hC,hK,he,hm,hbound⟩ := exists_uniform_window_identity_main
  refine ⟨K,C,hc,hC,hK,he,hm,?_⟩
  intro N _ t ε δ R hR ht hε hδ hδε hR1 hRδ
  filter_upwards [windowTimeSquare_energy_split N K he hc R hR (t+δ) (t+ε-δ)] with x hx
  rw [hx,add_sub_right_comm]
  exact (norm_add_le _ _).trans (add_le_add
    (hbound t ε δ R hR ht hε hδ hδε hR1 hRδ) le_rfl)

#print axioms mem_diagonalOrbitSet
#print axioms diagonalOrbitSet_card_bound
#print axioms displacement_in_diagonalOrbitSet
#print axioms radialNonidentity_eq_finite
#print axioms radialPoincareKernel_diagonal_split
#print axioms radialNonidentity_continuous
#print axioms radialNonidentity_integrableOn_compact
#print axioms radialNonidentity_norm_bound
#print axioms timeSquare_energy_split
#print axioms windowTimeSquare_energy_split
#print axioms exists_uniform_window_energy_error

end QuantitativeMaass
