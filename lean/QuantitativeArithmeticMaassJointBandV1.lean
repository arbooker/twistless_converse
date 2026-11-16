module

public import QuantitativeArithmeticMaassExceptionalBandsV1
public import QuantitativeNinaMaassNewResolventV1
public import QuantitativeArithmeticMaassHeckeResolventV1
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Module Set QuantitativeMaass QuantitativeNinaMaass
open AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeArithmeticMaassJointBand

/-- A full orthonormal joint eigenbasis, including repeated eigenvalues. -/
theorem joint_orthonormal_basis {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : I → Module.End ℂ E) (hT : ∀ i, (T i).IsSymmetric)
    (hc : Pairwise fun i j => Commute (T i) (T j)) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      ∀ j, ∃ μ : I → ℝ, ∀ i, T i (b j) = (μ i : ℂ) • b j := by
  classical
  let V : (I → ℂ) → Submodule ℂ E := fun χ => ⨅ i, Module.End.eigenspace (T i) (χ i)
  have hFull := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hc
  let : Fintype {χ // V χ ≠ ⊥} :=
    hFull.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hD : DirectSum.IsInternal (fun χ : {χ // V χ ≠ ⊥} => V χ.val) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (hFull.submodule_iSupIndep.comp Subtype.val_injective)
      ((iSup_ne_bot_subtype V).trans hFull.submodule_iSup_eq_top)
  have hO : OrthogonalFamily ℂ (fun χ : {χ // V χ ≠ ⊥} => V χ.val)
      (fun χ => (V χ.val).subtypeₗᵢ) := by
    intro χ ψ hχψ v w
    exact (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT)
      (fun h => hχψ (Subtype.ext h)) v w
  let b := hD.subordinateOrthonormalBasis rfl hO
  refine ⟨b, fun j => ?_⟩
  let χ := (hD.subordinateOrthonormalBasisIndex rfl j hO).val
  have hj : b j ∈ ⨅ i, Module.End.eigenspace (T i) (χ i) :=
    hD.subordinateOrthonormalBasis_subordinate rfl j hO
  have he (i : I) : T i (b j) = χ i • b j :=
    Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hj i)
  refine ⟨fun i => (χ i).re, fun i => ?_⟩
  have hr : ((χ i).re : ℂ) = χ i := by
    apply RCLike.conj_eq_iff_re.mp
    exact (hT i).conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (he i), b.toBasis.ne_zero j⟩)
  rw [hr]
  exact he i

/-- Compute a power trace in any full orthonormal eigenbasis, so that a
joint energy eigenbasis can replace the canonical Hecke eigenbasis. -/
theorem trace_power_of_eigenbasis {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : Module.End ℂ E) (e : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E)
    (τ : Fin (finrank ℂ E) → ℝ) (he : ∀ i, T (e i)=(τ i:ℂ) • e i) (d : ℕ) :
    (LinearMap.trace ℂ E (T^d)).re = ∑ i, (τ i)^d := by
  classical
  have hm : LinearMap.toMatrix e.toBasis e.toBasis T = Matrix.diagonal (fun i => (τ i:ℂ)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [OrthonormalBasis.coe_toBasis]
    rw [he j, map_smul]
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  rw [LinearMap.trace_eq_matrix_trace ℂ e.toBasis, ←LinearMap.toMatrix_pow, hm]
  simp [Matrix.diagonal_pow, Matrix.trace, ←Complex.ofReal_pow]

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance

/-- The actual good-prime map commutes with the actual resolvent on the
entire cusp parity band, without a newspace restriction. -/
theorem band_hecke_resolvent_commute {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) (a b σ : ℝ) :
    Commute (S.dilationTraceParityBandMap p (Fact.out : p.Prime).pos a b σ)
      (S.resolventParityBandMap a b σ) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change dilationTraceOperator N p hN (Fact.out : p.Prime).pos
    (friedrichsResolvent N (v.val.val : AutomorphicSpace N)) =
      friedrichsResolvent N (dilationTraceOperator N p hN (Fact.out : p.Prime).pos
        (v.val.val : AutomorphicSpace N))
  rw [←hecke_eq_dilationTraceOperator N p hN hpN A B hAB]
  exact DFunLike.congr_fun
    (QuantitativeArithmeticMaassHecke.hecke_resolvent_commute N p hN hpN A B hAB) _

/-- A full orthonormal basis of the actual cusp parity band, with actual
Hecke eigenrelations and principal Friedrichs parameters in that same band. -/
theorem full_band_joint_basis {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) (a b σ : ℝ) :
    ∃ e : OrthonormalBasis (Fin (finrank ℂ (S.parityBand a b σ))) ℂ (S.parityBand a b σ),
      ∃ r τ : Fin (finrank ℂ (S.parityBand a b σ)) → ℝ,
        (∀ i, 0≤r i ∧ r i∈Icc a b) ∧
        (∀ i, FriedrichsGraph N ((e i).val.val : AutomorphicSpace N)
          (((1/4+(r i)^2 : ℝ):ℂ) • ((e i).val.val : AutomorphicSpace N))) ∧
        ∀ i, HeckeL2.operator N p hN hpN A B hAB ((e i).val.val : AutomorphicSpace N)=
          (τ i : ℂ) • ((e i).val.val : AutomorphicSpace N) := by
  classical
  let H := S.dilationTraceParityBandMap p (Fact.out : p.Prime).pos a b σ
  let R := S.resolventParityBandMap a b σ
  have hH : H.IsSymmetric := by
    intro v w
    change inner ℂ (dilationTraceOperator N p hN (Fact.out : p.Prime).pos
      (v.val.val : AutomorphicSpace N)) (w.val.val : AutomorphicSpace N) =
        inner ℂ (v.val.val : AutomorphicSpace N)
          (dilationTraceOperator N p hN (Fact.out : p.Prime).pos (w.val.val : AutomorphicSpace N))
    rw [←hecke_eq_dilationTraceOperator N p hN hpN A B hAB]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (HeckeL2.operator_selfAdjoint N p hN hpN A B hAB) _ _
  have hR : R.IsSymmetric := by
    intro v w
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (friedrichsResolvent_isSelfAdjoint N)
      (v.val.val : AutomorphicSpace N) (w.val.val : AutomorphicSpace N)
  let T : Bool → Module.End ℂ (S.parityBand a b σ) := fun i => if i then H else R
  have hT : ∀ i, (T i).IsSymmetric := by intro i; cases i <;> assumption
  have hc : Pairwise fun i j => Commute (T i) (T j) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact (band_hecke_resolvent_commute S p hpN A B hAB a b σ).symm
    · exact band_hecke_resolvent_commute S p hpN A B hAB a b σ
    · exact (hij rfl).elim
  obtain ⟨e, he⟩ := joint_orthonormal_basis T hT hc
  choose μ hμ using he
  have hr (i : Fin (finrank ℂ (S.parityBand a b σ))) :
      ∃ r : ℝ, 0≤r ∧ r∈Icc a b ∧ FriedrichsGraph N
        ((e i).val.val : AutomorphicSpace N)
        (((1/4+r^2 : ℝ):ℂ) • ((e i).val.val : AutomorphicSpace N)) := by
    have hv : ((e i).val.val : AutomorphicSpace N) ≠ 0 := by
      intro hz
      exact e.toBasis.ne_zero i (Subtype.ext (Subtype.ext (Subtype.ext hz)))
    have hres : friedrichsResolvent N ((e i).val.val : AutomorphicSpace N)=
        (μ i false : ℂ) • ((e i).val.val : AutomorphicSpace N) :=
      congrArg (fun v : S.parityBand a b σ => (v.val.val : AutomorphicSpace N)) (hμ i false)
    have hg := resolvent_nonzero_eigen_graph N _ hv _ hres
    obtain ⟨r,hr,hw,hell⟩ := S.band_graph_eigen_parameter a b (e i).val.val
      (e i).val.property (by intro hz; exact e.toBasis.ne_zero i (Subtype.ext (Subtype.ext hz)))
      ((μ i false : ℂ)⁻¹-1) hg
    have hscalar := congrArg (fun z : ℂ => z • ((e i).val.val : AutomorphicSpace N)) hell
    exact ⟨r,hr,hw,(congrArg (FriedrichsGraph N ((e i).val.val : AutomorphicSpace N))
      hscalar).mpr hg⟩
  choose r hr hw hg using hr
  refine ⟨e,r,fun i => μ i true, fun i => ⟨hr i,hw i⟩,hg,fun i => ?_⟩
  rw [hecke_eq_dilationTraceOperator N p hN hpN A B hAB]
  exact congrArg (fun v : S.parityBand a b σ => (v.val.val : AutomorphicSpace N)) (hμ i true)

/-- The full band basis supplies exactly the physical orthonormal family
required by the geometric eigenmoment bound. -/
theorem full_band_joint_family {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) (a b σ : ℝ) :
    ∃ f : Fin (finrank ℂ (S.parityBand a b σ)) → AutomorphicSpace N,
      Orthonormal ℂ f ∧ (∀ i, f i∈localCuspidalSpace N hN) ∧
      ∃ r τ : Fin (finrank ℂ (S.parityBand a b σ)) → ℝ,
        (∀ i, 0≤r i ∧ r i∈Icc a b) ∧
        (∀ i, FriedrichsGraph N (f i) (((1/4+(r i)^2:ℝ):ℂ) • f i)) ∧
        ∀ i, HeckeL2.operator N p hN hpN A B hAB (f i)=(τ i:ℂ) • f i := by
  classical
  obtain ⟨e,r,τ,hr,hg,he⟩ := full_band_joint_basis S p hpN A B hAB a b σ
  refine ⟨fun i => ((e i).val.val : AutomorphicSpace N),?_,
    fun i => (e i).val.val.property,r,τ,hr,hg,he⟩
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℂ (e i) (e j)=_
  exact orthonormal_iff_ite.mp e.orthonormal i j

/-- Exact normalization linking the joint physical eigenbasis to the
finite trace used in the exceptional-band estimate. -/
theorem normalized_band_trace {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) (a b σ : ℝ)
    (e : OrthonormalBasis (Fin (finrank ℂ (S.parityBand a b σ))) ℂ (S.parityBand a b σ))
    (τ : Fin (finrank ℂ (S.parityBand a b σ)) → ℝ)
    (he : ∀ i, HeckeL2.operator N p hN hpN A B hAB ((e i).val.val : AutomorphicSpace N)=
      (τ i:ℂ) • ((e i).val.val : AutomorphicSpace N)) (d : ℕ) :
    (LinearMap.trace ℂ (S.parityBand a b σ)
      ((QuantitativeArithmeticMaassExceptionalBands.normalizedBandHecke S p a b σ)^d)).re =
        ∑ i, (Real.sqrt (p:ℝ)/((p:ℝ)+1)*τ i)^d := by
  apply trace_power_of_eigenbasis _ e
  intro i
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change ((QuantitativeArithmeticMaassExceptionalBands.normalizedBandHecke S p a b σ (e i)).val.val :
      AutomorphicSpace N) = _
  rw [QuantitativeArithmeticMaassExceptionalBands.normalizedBandHecke_actual S p hpN A B hAB,he]
  simp only [Complex.ofReal_mul, smul_smul, Submodule.coe_smul]

#print axioms joint_orthonormal_basis
#print axioms trace_power_of_eigenbasis
#print axioms band_hecke_resolvent_commute
#print axioms full_band_joint_basis
#print axioms full_band_joint_family
#print axioms normalized_band_trace

end QuantitativeArithmeticMaassJointBand
