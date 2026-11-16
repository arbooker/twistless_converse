module

public import AsymptoticClassicalDiscriminantLevelV1
public import AsymptoticClassicalTriangularSlashV1
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.MulAction
public import QuantitativeMaassAffineCovarianceV1
public import QuantitativeMaassFriedrichsCoreV1
public import QuantitativeMaassHeckeActionV1
public import QuantitativeMaassPoincareGraphLinearV1

/-! Consolidated chapter: QuantitativeArithmeticMaassHecke. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticMaassHeckeAffineSeedV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open QuantitativeMaass MaassDifferential UpperHalfPlane
open AsymptoticClassicalDiscriminant

theorem upperFunction_affine (u : Point → ℂ) (a b : ℝ) (ha : 0<a) :
    upperFunction (u ∘ affineChart a b)=
      (upperFunction u) ∘ (fun z : ℍ => triangularGL a b 1 ha (by norm_num) • z) := by
  funext z
  rw [Function.comp_apply,triangularGL_action]
  simp [upperFunction,affineChart,affine,Function.comp_apply]

def affineSeed (u : SmoothUpperSeed) (a b : ℝ) (ha : 0<a) : SmoothUpperSeed where
  toFun := u.toFun ∘ affineChart a b
  smooth := affine_pullback_smooth u.smooth ha b
  compact := by
    rw [upperFunction_affine u.toFun a b ha]
    exact u.compact.comp_homeomorph (Homeomorph.smul (triangularGL a b 1 ha (by norm_num)))

theorem affineSeed_laplacian (u : SmoothUpperSeed) (a b : ℝ) (ha : 0<a) :
    upperFunction (affineSeed u a b ha).laplacian.toFun=
      upperFunction (affineSeed u.laplacian a b ha).toFun := by
  funext z
  exact hyperbolic_affine u.smooth ha b z.re z.im z.im_pos

theorem poincare_affineSeed_laplacian (N : ℕ) (u : SmoothUpperSeed)
    (a b : ℝ) (ha : 0<a) :
    poincareSeedVector N (affineSeed u a b ha).laplacian=
      poincareSeedVector N (affineSeed u.laplacian a b ha) :=
  poincareSeedVector_congr N (affineSeed_laplacian u a b ha)

#print axioms affineSeed
#print axioms poincare_affineSeed_laplacian

end QuantitativeArithmeticMaassHecke
end
end

/-! ## QuantitativeArithmeticMaassHeckeSeedSumV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open QuantitativeMaass MaassDifferential UpperHalfPlane

def seedSum {ι : Type*} (S : Finset ι) (u : ι → SmoothUpperSeed) : SmoothUpperSeed where
  toFun Z := ∑ i∈S, (u i).toFun Z
  smooth := ContDiffOn.sum (fun i _ => (u i).smooth)
  compact := by
    have he : upperFunction (fun Z => ∑ i∈S, (u i).toFun Z)=
        ∑ i∈S, upperFunction (u i).toFun := by
      funext z
      simp only [upperFunction,Finset.sum_apply]
    rw [he]
    exact HasCompactSupport.finset_sum (fun i _ => (u i).compact)

theorem seedSum_laplacian {ι : Type*} (S : Finset ι) (u : ι → SmoothUpperSeed) :
    upperFunction (seedSum S u).laplacian.toFun=
      upperFunction (seedSum S (fun i => (u i).laplacian)).toFun := by
  funext z
  exact hyperbolic_finset_sum S (fun i => (u i).toFun) (fun i _ => (u i).smooth)
    (z.re,z.im) z.im_pos

theorem poincare_seedSum (N : ℕ) {ι : Type*} (S : Finset ι) (u : ι → SmoothUpperSeed) :
    poincareSeedVector N (seedSum S u)=∑ i∈S, poincareSeedVector N (u i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,← poincareSeedVector_zero N]
    apply poincareSeedVector_congr
    funext z
    simp [upperFunction,seedSum,SmoothUpperSeed.zero]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,← ih,← poincareSeedVector_add]
    apply poincareSeedVector_congr
    funext z
    simp [upperFunction,seedSum,SmoothUpperSeed.add,Finset.sum_insert hi]

/-- The inverse branches of the normalized prime Hecke correspondence,
acting on compact smooth seeds rather than automorphic functions. -/
def inverseHeckeSeed (p : ℕ) (hp : 0<p) (u : SmoothUpperSeed) : SmoothUpperSeed :=
  ((affineSeed u (p : ℝ)⁻¹ 0 (by positivity)).add
    (seedSum Finset.univ (fun a : Fin p => affineSeed u p (-(a.val : ℝ))
      (by exact_mod_cast hp)))).smul (((Real.sqrt p)⁻¹ : ℝ) : ℂ)

theorem inverseHeckeSeed_laplacian (N p : ℕ) (hp : 0<p) (u : SmoothUpperSeed) :
    poincareSeedVector N (inverseHeckeSeed p hp u).laplacian=
      poincareSeedVector N (inverseHeckeSeed p hp u.laplacian) := by
  unfold inverseHeckeSeed
  rw [poincareSeedVector_laplacian_smul,poincareSeedVector_laplacian_add,
    poincareSeedVector_smul,poincareSeedVector_add,poincare_affineSeed_laplacian]
  congr 2
  have hs := poincareSeedVector_congr N
    (seedSum_laplacian Finset.univ (fun a : Fin p => affineSeed u p (-(a.val : ℝ))
      (by exact_mod_cast hp)))
  rw [hs,poincare_seedSum,poincare_seedSum]
  exact Finset.sum_congr rfl (fun a _ => poincare_affineSeed_laplacian N u p _ _)

#print axioms inverseHeckeSeed_laplacian

end QuantitativeArithmeticMaassHecke
end
end

/-! ## QuantitativeArithmeticMaassHeckeAffinePairingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open QuantitativeMaass MaassDifferential UpperHalfPlane MeasureTheory
open AsymptoticClassicalDiscriminant

theorem inverse_affineSeed_action (u : SmoothUpperSeed) (a b : ℝ) (ha : 0<a) (z : ℍ) :
    upperFunction (affineSeed u a⁻¹ (-b/a) (inv_pos.mpr ha)).toFun
      (triangularGL a b 1 ha (by norm_num) • z)=upperFunction u.toFun z := by
  rw [triangularGL_action]
  simp only [div_one]
  change u.toFun (a⁻¹*(affine a ha b z).re+-b/a,a⁻¹*(affine a ha b z).im)=u.toFun (z.re,z.im)
  congr 1
  ext
  · simp only [affine,UpperHalfPlane.mk_re,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    field_simp
    ring_nf
    rfl
  · rw [affine_im,← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]

/-- Hyperbolic change of variables transfers a Hecke branch onto the
inverse affine pullback of its compact seed, with no boundary terms. -/
theorem affine_seed_pairing (u : SmoothUpperSeed) (v : ℍ → ℂ)
    (a b : ℝ) (ha : 0<a) :
    (∫ z : ℍ, star (upperFunction u.toFun z)*v (triangularGL a b 1 ha (by norm_num) • z))=
      ∫ z : ℍ, star (upperFunction (affineSeed u a⁻¹ (-b/a) (inv_pos.mpr ha)).toFun z)*v z := by
  let g := triangularGL a b 1 ha (by norm_num)
  have h := (measurePreserving_smul g (volume : Measure ℍ)).integral_comp
    (Homeomorph.smul g).measurableEmbedding
    (fun z => star (upperFunction (affineSeed u a⁻¹ (-b/a) (inv_pos.mpr ha)).toFun z)*v z)
  simpa only [inverse_affineSeed_action,g] using h

#print axioms affine_seed_pairing

end QuantitativeArithmeticMaassHecke
end
end

/-! ## QuantitativeArithmeticMaassHeckePowerBoundV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A dyadic moment bound uses only symmetry, not completeness or a spectral
resolution. It will control the Hecke action in the energy norm. -/
theorem symmetric_dyadic_bound (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (x : E) (hx : ‖x‖≤1) (n : ℕ) :
    ‖T x‖^(2^n)≤‖(T^(2^n)) x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : ‖(T^(2^n)) x‖^2=(inner ℂ x ((T^(2^n)) ((T^(2^n)) x))).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans
        (congrArg Complex.re ((hT.pow (2^n)) x ((T^(2^n)) x)))
    have hb := re_inner_le_norm (𝕜 := ℂ) x ((T^(2^n)) ((T^(2^n)) x))
    have hm := mul_le_mul_of_nonneg_right hx (norm_nonneg ((T^(2^n)) ((T^(2^n)) x)))
    rw [one_mul] at hm
    have hs : ‖(T^(2^n)) x‖^2≤‖(T^(2^(n+1))) x‖ := by
      rw [he]
      have heq : (T^(2^n)) ((T^(2^n)) x)=(T^(2^(n+1))) x := by
        rw [← Module.End.mul_apply,← pow_add]
        congr 2
        omega
      exact heq ▸ hb.trans hm
    have hi : (‖T x‖^(2^n))^2≤‖(T^(2^n)) x‖^2 :=
      pow_le_pow_left₀ (by positivity) ih 2
    rw [← pow_mul,← pow_succ] at hi
    exact hi.trans hs

/-- A symmetric operator on a possibly incomplete inner-product space is
a contraction if each individual power orbit is bounded. The orbit bound
may depend on the vector. -/
theorem symmetric_contraction_of_bounded_powers (T : E →ₗ[ℂ] E)
    (hT : T.IsSymmetric) (hb : ∀ x : E, ∃ C : ℝ, ∀ n : ℕ, ‖(T^n) x‖≤C)
    (x : E) : ‖T x‖≤‖x‖ := by
  have hunit (y : E) (hy : ‖y‖≤1) : ‖T y‖≤1 := by
    by_contra h
    have hh : 1<‖T y‖ := lt_of_not_ge h
    obtain ⟨C,hC⟩ := hb y
    obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt C hh
    have hnat : n≤2^n := n.lt_two_pow_self.le
    have hpow : ‖T y‖^n≤‖T y‖^(2^n) := pow_right_mono₀ hh.le hnat
    exact (not_lt_of_ge ((hpow.trans (symmetric_dyadic_bound T hT y hy n)).trans
      (hC (2^n)))) hn
  by_cases hx : x=0
  · simp [hx]
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx
  let c : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
  have hc : ‖c‖=‖x‖⁻¹ := by simp [c]
  have hy : ‖c•x‖≤1 := by rw [norm_smul,hc,inv_mul_cancel₀ hn.ne']
  have ht := hunit (c•x) hy
  rw [map_smul,norm_smul,hc] at ht
  have ht' := mul_le_mul_of_nonneg_left ht hn.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul,mul_one] using ht'

#print axioms symmetric_contraction_of_bounded_powers

end QuantitativeArithmeticMaassHecke
end
end

/-! ## QuantitativeArithmeticMaassHeckeEnergyCoreV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open QuantitativeMaass Set
open scoped InnerProductSpace

theorem closedGraph_preserved_of_seeds (N : ℕ)
    (T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hseed : ∀ u : SmoothUpperSeed,
      PoincareGraph N (T (poincareSeedVector N u)) (T (poincareSeedVector N u.laplacian))) :
    ∀ v∈poincareClosedGraph N, (T v.1,T v.2)∈poincareClosedGraph N := by
  apply closure_minimal
  · intro v hv
    obtain ⟨u,hu,hdu⟩ := (poincareLinearGraph_mem_iff N v).mp hv
    change (T v.1,T v.2)∈poincareClosedGraph N
    rw [hu,hdu]
    exact (poincareLinearGraph N).le_topologicalClosure
      ((poincareLinearGraph_mem_iff N _).mpr (hseed u))
  · exact (poincareClosedGraph_closed N).preimage
      ((T.continuous.comp continuous_fst).prodMk (T.continuous.comp continuous_snd))

variable (N : ℕ) (T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hgraph : ∀ v∈poincareClosedGraph N, (T v.1,T v.2)∈poincareClosedGraph N)

def differentialCoreMap : quotientLaplacianDomain N →ₗ[ℂ] quotientLaplacianDomain N where
  toFun x := ⟨T x.val, ((quotientLaplacian_graph_iff N _ _).mp
    (hgraph _ (quotientLaplacian_graph N x))).1⟩
  map_add' _ _ := Subtype.ext (map_add T _ _)
  map_smul' _ _ := Subtype.ext (map_smul T _ _)

def energyCoreMap : QuotientEnergyDomain N →ₗ[ℂ] QuotientEnergyDomain N :=
  differentialCoreMap N T hgraph

theorem energyCoreMap_value (x : QuotientEnergyDomain N) :
    energyDomainValue N (energyCoreMap N T hgraph x)=T (energyDomainValue N x) := rfl

theorem energyCoreMap_laplacian (x : QuotientEnergyDomain N) :
    energyDomainLaplacian N (energyCoreMap N T hgraph x)=T (energyDomainLaplacian N x) :=
  poincareClosedGraph_singleValued N (quotientLaplacian_graph N (differentialCoreMap N T hgraph x))
    (hgraph _ (quotientLaplacian_graph N x))

theorem energyCoreMap_symmetric (hT : IsSelfAdjoint T) :
    (energyCoreMap N T hgraph).IsSymmetric := by
  intro x y
  simp only [quotientEnergy_inner,energyCoreMap_value,energyCoreMap_laplacian]
  exact congrArg₂ (·+·) (hT.isSymmetric (energyDomainValue N x) (energyDomainValue N y))
    (hT.isSymmetric (energyDomainValue N x) (energyDomainLaplacian N y))

theorem energyCoreMap_pow_value (n : ℕ) (x : QuotientEnergyDomain N) :
    energyDomainValue N (((energyCoreMap N T hgraph)^n) x)=(T^n) (energyDomainValue N x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Module.End.mul_apply,energyCoreMap_value,ih,pow_succ']
    rfl

theorem energyCoreMap_pow_laplacian (n : ℕ) (x : QuotientEnergyDomain N) :
    energyDomainLaplacian N (((energyCoreMap N T hgraph)^n) x)=(T^n) (energyDomainLaplacian N x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Module.End.mul_apply,energyCoreMap_laplacian,ih,pow_succ']
    rfl

theorem contraction_power (hT : ∀ x, ‖T x‖≤‖x‖) (n : ℕ) (x : AutomorphicSpace N) :
    ‖(T^n) x‖≤‖x‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    exact (hT ((T^n) x)).trans ih

/-- The ambient contraction estimate and differential commutation bound
each power orbit in the actual energy norm, without assuming an energy bound. -/
theorem energyCoreMap_power_bounded (hT : ∀ x, ‖T x‖≤‖x‖)
    (x : QuotientEnergyDomain N) :
    ∃ C : ℝ, ∀ n : ℕ, ‖((energyCoreMap N T hgraph)^n) x‖≤C := by
  let a := ‖energyDomainValue N x‖
  let b := ‖energyDomainLaplacian N x‖
  have ha : 0≤a := norm_nonneg _
  have hb : 0≤b := norm_nonneg _
  refine ⟨Real.sqrt (a^2+a*b),fun n => ?_⟩
  have hv := contraction_power N T hT n (energyDomainValue N x)
  have hl := contraction_power N T hT n (energyDomainLaplacian N x)
  have he := quotientEnergy_norm_sq N (((energyCoreMap N T hgraph)^n) x)
  rw [energyCoreMap_pow_value,energyCoreMap_pow_laplacian] at he
  have hi := re_inner_le_norm (𝕜 := ℂ) ((T^n) (energyDomainValue N x))
    ((T^n) (energyDomainLaplacian N x))
  have hp := mul_le_mul hv hl (norm_nonneg _) ha
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hv 2
  have hbound : ‖((energyCoreMap N T hgraph)^n) x‖^2≤a^2+a*b := by
    exact he.trans_le (add_le_add hsq (hi.trans hp))
  have hs := Real.sq_sqrt (show 0≤a^2+a*b by positivity)
  nlinarith [Real.sqrt_nonneg (a^2+a*b),norm_nonneg (((energyCoreMap N T hgraph)^n) x)]

theorem energyCoreMap_norm_le (hs : IsSelfAdjoint T) (hc : ∀ x, ‖T x‖≤‖x‖)
    (x : QuotientEnergyDomain N) : ‖energyCoreMap N T hgraph x‖≤‖x‖ :=
  symmetric_contraction_of_bounded_powers _ (energyCoreMap_symmetric N T hgraph hs)
    (energyCoreMap_power_bounded N T hgraph hc) x

#print axioms energyCoreMap_norm_le

end QuantitativeArithmeticMaassHecke
end
end

/-! ## QuantitativeArithmeticMaassHeckeEnergyResolventV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open QuantitativeMaass UniformSpace Set
open scoped InnerProductSpace Topology

variable (N : ℕ) (T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (hgraph : ∀ v∈poincareClosedGraph N, (T v.1,T v.2)∈poincareClosedGraph N)

def energyMap : QuotientEnergySpace N →L[ℂ] QuotientEnergySpace N :=
  (Completion.toComplₗᵢ.toLinearMap.comp (energyCoreMap N T hgraph)).extendOfNorm
    Completion.toComplₗᵢ.toLinearMap

theorem energyMap_coe (hs : IsSelfAdjoint T) (hc : ∀ x, ‖T x‖≤‖x‖)
    (x : QuotientEnergyDomain N) :
    energyMap N T hgraph (x : QuotientEnergySpace N)=
      (energyCoreMap N T hgraph x : QuotientEnergySpace N) := by
  apply LinearMap.extendOfNorm_eq Completion.denseRange_coe
  refine ⟨1,fun y => ?_⟩
  change ‖(energyCoreMap N T hgraph y : QuotientEnergySpace N)‖≤
    1*‖(y : QuotientEnergySpace N)‖
  simpa only [Completion.norm_coe,one_mul]
    using energyCoreMap_norm_le N T hgraph hs hc y

theorem energyMap_intertwines (hs : IsSelfAdjoint T) (hc : ∀ x, ‖T x‖≤‖x‖) :
    (energyInclusion N).comp (energyMap N T hgraph)=T.comp (energyInclusion N) := by
  apply DFunLike.coe_injective
  apply Completion.denseRange_coe.equalizer
    ((energyInclusion N).comp (energyMap N T hgraph)).continuous
    (T.comp (energyInclusion N)).continuous
  funext x
  change energyInclusion N (energyMap N T hgraph (x : QuotientEnergySpace N))=
    T (energyInclusion N (x : QuotientEnergySpace N))
  rw [energyMap_coe N T hgraph hs hc,energyInclusion_coe,energyInclusion_coe,energyCoreMap_value]

theorem energyMap_selfAdjoint (hs : IsSelfAdjoint T) (hc : ∀ x, ‖T x‖≤‖x‖) :
    IsSelfAdjoint (energyMap N T hgraph) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hcore (u v : QuotientEnergyDomain N) :
      inner ℂ (energyMap N T hgraph (u : QuotientEnergySpace N)) (v : QuotientEnergySpace N)=
        inner ℂ (u : QuotientEnergySpace N) (energyMap N T hgraph (v : QuotientEnergySpace N)) := by
    rw [energyMap_coe N T hgraph hs hc,energyMap_coe N T hgraph hs hc,
      Completion.inner_coe,Completion.inner_coe]
    exact energyCoreMap_symmetric N T hgraph hs u v
  have hx (v : QuotientEnergyDomain N) :
      inner ℂ (energyMap N T hgraph x) (v : QuotientEnergySpace N)=
        inner ℂ x (energyMap N T hgraph (v : QuotientEnergySpace N)) := by
    exact congrFun ((Completion.denseRange_coe (α := QuotientEnergyDomain N)).equalizer
      ((energyMap N T hgraph).continuous.inner continuous_const)
      (continuous_id.inner continuous_const) (funext fun u => hcore u v)) x
  exact congrFun ((Completion.denseRange_coe (α := QuotientEnergyDomain N)).equalizer
    (continuous_const.inner continuous_id)
    (continuous_const.inner (energyMap N T hgraph).continuous) (funext hx)) y

include hgraph in
/-- Differential graph preservation suffices for commutation with the
Friedrichs resolvent. Energy boundedness has been proved above, not assumed. -/
theorem resolvent_commute_of_contraction (hs : IsSelfAdjoint T)
    (hc : ∀ x, ‖T x‖≤‖x‖) : Commute T (friedrichsResolvent N) := by
  have hJ := energyMap_intertwines N T hgraph hs hc
  have hJa := congrArg ContinuousLinearMap.adjoint hJ
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
    (energyMap_selfAdjoint N T hgraph hs hc).adjoint_eq,hs.adjoint_eq] at hJa
  change T.comp ((energyInclusion N).comp (energyInclusion N).adjoint)=
    ((energyInclusion N).comp (energyInclusion N).adjoint).comp T
  rw [← ContinuousLinearMap.comp_assoc,← hJ,ContinuousLinearMap.comp_assoc,hJa,
    ContinuousLinearMap.comp_assoc]

/-- A bounded self-adjoint operator commuting with the differential
expression on the smooth Poincare core commutes with the actual Friedrichs
resolvent. No essential self-adjointness assertion is required. -/
theorem resolvent_commute_of_seed_graph (hs : IsSelfAdjoint T)
    (hseed : ∀ u : SmoothUpperSeed,
      PoincareGraph N (T (poincareSeedVector N u)) (T (poincareSeedVector N u.laplacian))) :
    Commute T (friedrichsResolvent N) := by
  let c : ℝ := (‖T‖+1)⁻¹
  have hcpos : 0<c := inv_pos.mpr (by positivity)
  let S : AutomorphicSpace N →L[ℂ] AutomorphicSpace N := (c : ℂ) • T
  have hS : IsSelfAdjoint S := (by simp [IsSelfAdjoint] : IsSelfAdjoint (c : ℂ)).smul hs
  have hSc (x : AutomorphicSpace N) : ‖S x‖≤‖x‖ := by
    change ‖(c : ℂ) • T x‖≤‖x‖
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hcpos]
    have h := mul_le_mul_of_nonneg_left (T.le_opNorm x) hcpos.le
    have hcn : c*‖T‖≤1 := by
      dsimp [c]
      apply (inv_mul_le_iff₀ (by positivity : 0<‖T‖+1)).mpr
      linarith
    exact h.trans (by rw [← mul_assoc]; exact mul_le_of_le_one_left (norm_nonneg x) hcn)
  have hSs (u : SmoothUpperSeed) :
      PoincareGraph N (S (poincareSeedVector N u)) (S (poincareSeedVector N u.laplacian)) :=
    poincareGraph_smul N (c : ℂ) (hseed u)
  have he := (resolvent_commute_of_contraction N S
    (closedGraph_preserved_of_seeds N S hSs) hS hSc).eq
  apply DFunLike.coe_injective
  funext x
  have hx := congrArg (fun J : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => J x) he
  change (c : ℂ) • T (friedrichsResolvent N x)=friedrichsResolvent N ((c : ℂ) • T x) at hx
  rw [map_smul] at hx
  exact (smul_right_injective _ (Complex.ofReal_ne_zero.mpr hcpos.ne')) hx

#print axioms resolvent_commute_of_seed_graph

end QuantitativeArithmeticMaassHecke
end
end

/-! ## QuantitativeArithmeticMaassHeckeSeedPairingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open QuantitativeMaass MaassDifferential UpperHalfPlane MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticClassicalDiscriminant
open scoped InnerProductSpace

theorem seed_pairing_integrable (u : SmoothUpperSeed) (v : ℍ → ℂ) (hv : Continuous v) :
    Integrable (fun z : ℍ => star (upperFunction u.toFun z)*v z) :=
  ((upperFunction_continuous u.smooth).star.mul hv).integrable_of_hasCompactSupport
    ((u.compact.comp_left (star_zero ℂ)).mul_right)

theorem inner_seed_representative (N : ℕ) (u : SmoothUpperSeed)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    inner ℂ (poincareSeedVector N u) (AutomorphicL2.denseEmbedding _ _ f)=
      ∫ z : ℍ, star (upperFunction u.toFun z)*f.val z := by
  rw [poincareSeedVector,AutomorphicL2.denseEmbedding_inner]
  exact congruence_poincare_pairing_left N f.val f.property.1 f.property.2.1 f.property.2.2
    (upperFunction u.toFun) (upperFunction_continuous u.smooth) u.compact

theorem affine_continuous (a b : ℝ) (ha : 0<a) : Continuous (affine a ha b) := by
  have h : (fun z : ℍ => triangularGL a b 1 ha (by norm_num) • z)=affine a ha b := by
    funext z
    simp only [triangularGL_action,div_one]
  rw [← h]
  exact continuous_const_smul _

theorem affine_seed_pairing' (u : SmoothUpperSeed) (v : ℍ → ℂ)
    (a b : ℝ) (ha : 0<a) :
    (∫ z : ℍ, star (upperFunction u.toFun z)*v (affine a ha b z))=
      ∫ z : ℍ, star (upperFunction (affineSeed u a⁻¹ (-b/a) (inv_pos.mpr ha)).toFun z)*v z := by
  simpa only [triangularGL_action,div_one] using affine_seed_pairing u v a b ha

/-- The literal affine branch expression, with the unitary Hecke normalization. -/
def rawHeckeFunction (p : ℕ) (hp : 0<p) (v : ℍ → ℂ) (z : ℍ) : ℂ :=
  (((Real.sqrt p)⁻¹ : ℝ) : ℂ) *
    (v (affine p (by exact_mod_cast hp) 0 z)+
      ∑ a : Fin p, v (affine (p : ℝ)⁻¹ (by positivity) ((a.val : ℝ)/p) z))

/-- The inverse-branch seed is adjoint to the actual affine Hecke sum
for hyperbolic volume. All integral interchanges have compact-support bounds. -/
theorem inverseHeckeSeed_pairing (p : ℕ) (hp : 0<p) (u : SmoothUpperSeed)
    (v : ℍ → ℂ) (hv : Continuous v) :
    (∫ z : ℍ, star (upperFunction u.toFun z)*rawHeckeFunction p hp v z)=
      ∫ z : ℍ, star (upperFunction (inverseHeckeSeed p hp u).toFun z)*v z := by
  let c : ℂ := (((Real.sqrt p)⁻¹ : ℝ) : ℂ)
  let v0 : ℍ → ℂ := fun z => v (affine p (by exact_mod_cast hp) 0 z)
  let va (a : Fin p) : ℍ → ℂ := fun z =>
    v (affine (p : ℝ)⁻¹ (by positivity) ((a.val : ℝ)/p) z)
  let u0 := affineSeed u (p : ℝ)⁻¹ 0 (by positivity)
  let ua (a : Fin p) := affineSeed u p (-(a.val : ℝ)) (by exact_mod_cast hp)
  have hi0 := seed_pairing_integrable u v0 (hv.comp (affine_continuous _ _ _))
  have hia (a : Fin p) := seed_pairing_integrable u (va a) (hv.comp (affine_continuous _ _ _))
  have hj0 := seed_pairing_integrable u0 v hv
  have hja (a : Fin p) := seed_pairing_integrable (ua a) v hv
  have he0 : (∫ z : ℍ, star (upperFunction u.toFun z)*v0 z)=
      ∫ z : ℍ, star (upperFunction u0.toFun z)*v z := by
    simpa only [neg_zero,zero_div] using affine_seed_pairing' u v p 0 (by exact_mod_cast hp)
  have hea (a : Fin p) : (∫ z : ℍ, star (upperFunction u.toFun z)*va a z)=
      ∫ z : ℍ, star (upperFunction (ua a).toFun z)*v z := by
    have h := affine_seed_pairing' u v (p : ℝ)⁻¹ ((a.val : ℝ)/p) (by positivity)
    have he : -((a.val : ℝ)/p)/(p : ℝ)⁻¹=-(a.val : ℝ) := by
      field_simp
    simpa only [inv_inv,he] using h
  have hleft : (fun z : ℍ => star (upperFunction u.toFun z)*rawHeckeFunction p hp v z)=
      fun z => c*(star (upperFunction u.toFun z)*v0 z+
        ∑ a : Fin p, star (upperFunction u.toFun z)*va a z) := by
    funext z
    change star (upperFunction u.toFun z)*(c*(v0 z+∑ a : Fin p,va a z))=
      c*(star (upperFunction u.toFun z)*v0 z+∑ a : Fin p,star (upperFunction u.toFun z)*va a z)
    rw [← Finset.mul_sum]
    ring
  have hright : (fun z : ℍ => star (upperFunction (inverseHeckeSeed p hp u).toFun z)*v z)=
      fun z => c*(star (upperFunction u0.toFun z)*v z+
        ∑ a : Fin p, star (upperFunction (ua a).toFun z)*v z) := by
    funext z
    change star (c*(upperFunction u0.toFun z+∑ a : Fin p,upperFunction (ua a).toFun z))*v z=
      c*(star (upperFunction u0.toFun z)*v z+∑ a : Fin p,star (upperFunction (ua a).toFun z)*v z)
    rw [star_mul,star_add,star_sum,show star c=c from Complex.conj_ofReal _,← Finset.sum_mul]
    ring
  rw [hleft,hright,integral_const_mul,integral_const_mul,
    integral_add hi0 (integrable_finsetSum _ fun a _ => hia a),
    integral_add hj0 (integrable_finsetSum _ fun a _ => hja a),
    integral_finsetSum _ (fun a _ => hia a),integral_finsetSum _ (fun a _ => hja a),he0]
  congr 2
  exact Finset.sum_congr rfl (fun a _ => hea a)

#print axioms inner_seed_representative
#print axioms inverseHeckeSeed_pairing

end QuantitativeArithmeticMaassHecke
end
end

/-! ## QuantitativeArithmeticMaassHeckeSeedActionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMaassHecke

open QuantitativeMaass MaassDifferential UpperHalfPlane MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticClassicalDiscriminant
open AsymptoticClassicalCusp AsymptoticCongruenceLabels
open scoped InnerProductSpace

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (A B : ℤ) (hAB : (p : ℤ)*A+(N : ℤ)*B=1)

theorem heckeRepresentative_raw
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) (z : ℍ) :
    (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val z=
      rawHeckeFunction p (HeckeL2.hp p) f.val z := by
  rw [HeckeL2.heckeRepresentative_apply]
  have hd : dilationLabel p (HeckeL2.hp p) • z=
      affine p (by exact_mod_cast HeckeL2.hp p) 0 z := by
    change dilationReal p (HeckeL2.hp p) • z=_
    exact dilation_action p (HeckeL2.hp p) z
  simp only [rawHeckeFunction,hd,triangularGL_action,one_div]

/-- The bounded automorphic Hecke operator acts on a compact Poincare
seed by the finite sum of inverse affine branches. This is proved by
unfolding, hyperbolic change of variables, self-adjointness and density. -/
theorem hecke_on_poincareSeed (u : SmoothUpperSeed) :
    HeckeL2.operator N p hN hpN A B hAB (poincareSeedVector N u)=
      poincareSeedVector N (inverseHeckeSeed p (HeckeL2.hp p) u) := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun g => AsymptoticRationalBranches.action_continuous g.val⟩
  apply (poincareSeedVector_dense N).eq_of_inner_left (𝕜 := ℂ)
  intro v
  let vr : AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
    ⟨poincareSum (G := gamma N) (upperFunction v.toFun),poincareSeed_representative N v⟩
  have hv : Continuous vr.val := poincareSum_continuous (G := gamma N)
    (upperFunction v.toFun) v.compact (upperFunction_continuous v.smooth)
  calc
    inner ℂ (HeckeL2.operator N p hN hpN A B hAB (poincareSeedVector N u))
        (poincareSeedVector N v) =
      inner ℂ (poincareSeedVector N u)
        (HeckeL2.operator N p hN hpN A B hAB (poincareSeedVector N v)) :=
      (HeckeL2.operator_selfAdjoint N p hN hpN A B hAB).isSymmetric _ _
    _ = ∫ z : ℍ, star (upperFunction u.toFun z)*
        rawHeckeFunction p (HeckeL2.hp p) vr.val z := by
      change inner ℂ (poincareSeedVector N u)
        (HeckeL2.operator N p hN hpN A B hAB (AutomorphicL2.denseEmbedding _ _ vr))=_
      rw [HeckeL2.operator_on_representatives,inner_seed_representative]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => congrArg
        (star (upperFunction u.toFun z)*·) (heckeRepresentative_raw N p hN hpN A B hAB vr z))
    _ = ∫ z : ℍ, star (upperFunction (inverseHeckeSeed p (HeckeL2.hp p) u).toFun z)*vr.val z :=
      inverseHeckeSeed_pairing p (HeckeL2.hp p) u vr.val hv
    _ = inner ℂ (poincareSeedVector N (inverseHeckeSeed p (HeckeL2.hp p) u))
        (poincareSeedVector N v) := (inner_seed_representative N _ vr).symm

theorem hecke_preserves_seed_graph (u : SmoothUpperSeed) :
    PoincareGraph N (HeckeL2.operator N p hN hpN A B hAB (poincareSeedVector N u))
      (HeckeL2.operator N p hN hpN A B hAB (poincareSeedVector N u.laplacian)) :=
  ⟨inverseHeckeSeed p (HeckeL2.hp p) u,hecke_on_poincareSeed N p hN hpN A B hAB u,
    (hecke_on_poincareSeed N p hN hpN A B hAB u.laplacian).trans
      (inverseHeckeSeed_laplacian N p (HeckeL2.hp p) u).symm⟩

#print axioms hecke_on_poincareSeed
#print axioms hecke_preserves_seed_graph

end QuantitativeArithmeticMaassHecke
end
end
