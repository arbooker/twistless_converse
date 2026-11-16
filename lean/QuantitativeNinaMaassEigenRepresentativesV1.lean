module

public import QuantitativeMaassAbelColumnContinuityV1
public import QuantitativeArithmeticMaassCuspidalDiscretenessV1
public import QuantitativeMaassCuspContinuousConstantV1
public import QuantitativeMaassPacketCrossKernelV1
public import QuantitativeArithmeticMaassCuspidalEigenbasisV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeMaass QuantitativeArithmeticMaassCuspBand
open scoped Topology ContDiff MatrixGroups

/-!
Continuous representatives of the actual Friedrichs eigenvectors are
constructed from a genuine Abel packet with proved nonzero multiplier.
The cusp condition is then the literal vanishing constant term at every
positive height. Neither regularity nor a Fourier expansion is assumed.

Continuity alone is not the full smooth Fourier-Bessel expansion needed for
normalized Hecke coefficients. No newform decomposition or Euler-product
solution construction is asserted here.
-/

namespace QuantitativeNinaMaass

/-- A concrete sufficiently short packet has positive multiplier at every
nonnegative energy, including exceptional energies. -/
theorem eigen_packet_multiplier_pos (e : ℝ) (he : 0 ≤ e) :
    0 < shortPacketMultiplier (1 / (4 * (e + 1))) e := by
  let R : ℝ := 1 / (4 * (e + 1))
  have hd : 0 < 4 * (e + 1) := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hR4 : R ≤ 1 / 4 := by
    dsimp [R]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hR1 : R ≤ 1 := by linarith
  have hReq : R * (4 * (e + 1)) = 1 := div_mul_cancel₀ 1 hd.ne'
  have hsmall : 4 * R^2 * (e + 1) ≤ 1 := by
    calc
      _ = R * (R * (4 * (e + 1))) := by ring
      _ = R := by rw [hReq, mul_one]
      _ ≤ 1 := hR1
  exact (half_pos (shortTimeWeight_mass_pos R hR)).trans_le
    (shortPacketMultiplier_lower e R e hR hR1 hsmall he le_rfl)

/-- Every actual Friedrichs eigenvector has a continuous, pointwise
automorphic L2 representative. The representative is constructed by
dividing a genuine smoothing packet output by its nonzero multiplier. -/
theorem exists_continuous_eigen_representative (N : ℕ) [NeZero N]
    (v : AutomorphicSpace N) (e : ℝ) (he : 0 ≤ e)
    (hgraph : FriedrichsGraph N v ((e : ℂ) • v)) :
    ∃ f : AutomorphicL2.representatives (gamma N) (quotientMeasure N),
      Continuous f.val ∧ AutomorphicL2.denseEmbedding _ _ f = v := by
  let R : ℝ := 1 / (4 * (e + 1))
  have hR : 0 < R := by dsimp [R]; positivity
  let F := abelCutoff (Real.cosh R - 1)
  have hF : ContDiff ℝ ∞ F := abelCutoff_smooth _
  have hc : HasCompactSupport F :=
    abelCutoff_compact _ (sub_pos.mpr (Real.one_lt_cosh.mpr hR.ne'))
  have hs : Function.support F ⊆ Iic (Real.cosh R) := abelCutoff_radius_support R hR
  have hr (q : ℝ) : star (F q) = F q := by simp [F, abelCutoff]
  let c : ℂ := shortPacketMultiplier R e
  have hc0 : c ≠ 0 := by
    dsimp [c, R]
    exact_mod_cast (eigen_packet_multiplier_pos e he).ne'
  let u : ℍ → ℂ := fun x =>
    ∫ y, radialPoincareKernel N (abelProfile F) x y * v.val y ∂quotientMeasure N
  have hu : Continuous u :=
    oneSidedAbelKernel_output_continuous N F hF.contDiffOn hr R hR.le hs v
  have hi (γ : gamma N) (x : ℍ) : u (γ • x) = u x :=
    radialKernel_output_invariant N (abelProfile F) (abelProfile_smooth F hF hc)
      R hR.le (abelProfile_support F _ hs) v.val γ x
  have hpacket := coshWavePacket_coeFn N F hF hc hr R hR.le hs v
  rw [shortPacket_eigen N R hR he hgraph] at hpacket
  have hscale : ((c • v : AutomorphicSpace N).val : ℍ → ℂ) =ᵐ[quotientMeasure N]
      fun x => c * v.val x := Lp.coeFn_smul c v.val
  have hae : v.val =ᵐ[quotientMeasure N] fun x => c⁻¹ * u x := by
    filter_upwards [hpacket, hscale] with x hx hxscale
    change (c • v : AutomorphicSpace N).val x = u x at hx
    rw [← hx, hxscale, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hm : (fun x => c⁻¹ * u x) ∈
      AutomorphicL2.representatives (gamma N) (quotientMeasure N) := by
    refine ⟨(continuous_const.mul hu).measurable, ?_, ?_⟩
    · intro γ x
      exact congrArg (fun z : ℂ => c⁻¹ * z) (hi γ x)
    · exact (memLp_congr_ae hae).mp (Lp.memLp v.val)
  refine ⟨⟨_, hm⟩, continuous_const.mul hu, ?_⟩
  apply Subtype.ext
  apply Lp.ext
  exact hm.2.2.coeFn_toLp.trans hae.symm

/-- Equality of completed vectors loses no information on continuous,
pointwise automorphic representatives. -/
theorem continuous_representative_unique (N : ℕ)
    (f g : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hg : Continuous g.val)
    (he : AutomorphicL2.denseEmbedding _ _ f = AutomorphicL2.denseEmbedding _ _ g) :
    f = g := by
  have heLp : f.property.2.2.toLp f.val = g.property.2.2.toLp g.val :=
    congrArg Subtype.val he
  have hae : f.val =ᵐ[quotientMeasure N] g.val := by
    have hh := f.property.2.2.coeFn_toLp
    rw [heLp] at hh
    exact hh.symm.trans g.property.2.2.coeFn_toLp
  apply Subtype.ext
  exact continuous_invariant_eq_of_ae N f.val g.val hf hg f.property.2.1 g.property.2.1 hae

/-- A cuspidal Friedrichs eigenvector has a constructed continuous
representative with the literal constant term zero at every integral cusp
and every positive height. -/
theorem exists_continuous_cuspidal_eigen_representative (N : ℕ) (hN : 0 < N)
    (v : AutomorphicSpace N) (hv : v ∈ localCuspidalSpace N hN)
    (e : ℝ) (he : 0 ≤ e) (hgraph : FriedrichsGraph N v ((e : ℂ) • v)) :
    ∃ f : AutomorphicL2.representatives (gamma N) (quotientMeasure N),
      Continuous f.val ∧ AutomorphicL2.denseEmbedding _ _ f = v ∧
      ∀ s : SL(2,ℤ), ∀ y : ℝ, 0 < y → cuspConstant N s f.val y = 0 := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨f, hf, heq⟩ := exists_continuous_eigen_representative N v e he hgraph
  refine ⟨f, hf, heq, ?_⟩
  intro s y hy
  have hae : v.val =ᵐ[quotientMeasure N] f.val := by
    rw [← heq]
    exact f.property.2.2.coeFn_toLp
  exact localCuspidalSpace_continuous_constant_zero N hN v hv f.val hf
    f.property.2.1 hae s y hy

/-- Every algebraic combination of actual cusp eigenvectors has a continuous
automorphic representative. This regularity statement is independent of a
choice of spectral window or a counting theorem. -/
theorem exists_continuous_span_representative {κ : Type*} (N : ℕ) (hN : 0 < N)
    (basis : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (henergy : ∀ j, 0 ≤ e j)
    (hgraph : ∀ j, FriedrichsGraph N (basis j : AutomorphicSpace N)
      ((e j : ℂ) • (basis j : AutomorphicSpace N)))
    (S : Set κ) (x : localCuspidalSpace N hN)
    (hx : x ∈ Submodule.span ℂ (Set.range (fun j : S => basis j.val))) :
    ∃ f : AutomorphicL2.representatives (gamma N) (quotientMeasure N),
      Continuous f.val ∧ AutomorphicL2.denseEmbedding _ _ f = (x : AutomorphicSpace N) := by
  let : NeZero N := ⟨hN.ne'⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact exists_continuous_eigen_representative N (basis j.val) (e j.val)
      (henergy j.val) (hgraph j.val)
  | zero =>
    refine ⟨0, continuous_const, ?_⟩
    exact map_zero _
  | add y z _ _ hy hz =>
    obtain ⟨f, hf, hfy⟩ := hy
    obtain ⟨g, hg, hgz⟩ := hz
    refine ⟨f + g, hf.add hg, ?_⟩
    rw [map_add, hfy, hgz]
    rfl
  | smul c y _ hy =>
    obtain ⟨f, hf, hfy⟩ := hy
    refine ⟨c • f, hf.const_smul c, ?_⟩
    rw [map_smul, hfy]
    rfl

/-- A bounded operator that preserves cusp membership on continuous actual
representatives preserves it on the entire closed cusp space. The needed
density is proved with the constructed geometric energy basis, not assumed
as a separate regularity or spectral-completeness hypothesis. -/
theorem cuspidal_operator_mem_of_continuous (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (U : AutomorphicSpace M →L[ℂ] AutomorphicSpace N)
    (hU : ∀ f : AutomorphicL2.representatives (gamma M) (quotientMeasure M),
      Continuous f.val → AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace M hM →
        U (AutomorphicL2.denseEmbedding _ _ f) ∈ localCuspidalSpace N hN)
    (v : AutomorphicSpace M) (hv : v ∈ localCuspidalSpace M hM) :
    U v ∈ localCuspidalSpace N hN := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  obtain ⟨κ, basis, e, henergy, hgraph, _⟩ := exists_cuspidal_energy_basis M hM
  have hgen (j : κ) : U (basis j : AutomorphicSpace M) ∈ localCuspidalSpace N hN := by
    obtain ⟨f, hf, heq⟩ := exists_continuous_eigen_representative M
      (basis j : AutomorphicSpace M) (e j) (henergy j) (hgraph j)
    rw [← heq]
    apply hU f hf
    rw [heq]
    exact (basis j).property
  let L := U.comp (localCuspidalSpace M hM).subtypeL
  have hs := L.hasSum (basis.hasSum_repr ⟨v, hv⟩)
  apply (localCuspidalSpace_closed N hN).mem_of_tendsto hs
  apply Eventually.of_forall
  intro S
  apply Submodule.sum_mem
  intro j _
  change U ((basis.repr ⟨v, hv⟩ j) • (basis j : AutomorphicSpace M)) ∈ _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (hgen j)

#print axioms eigen_packet_multiplier_pos
#print axioms exists_continuous_eigen_representative
#print axioms continuous_representative_unique
#print axioms exists_continuous_cuspidal_eigen_representative
#print axioms exists_continuous_span_representative
#print axioms cuspidal_operator_mem_of_continuous

end QuantitativeNinaMaass
