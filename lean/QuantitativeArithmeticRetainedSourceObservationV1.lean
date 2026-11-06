module

public import QuantitativeArithmeticRetainedFilterExpressionV1
public import QuantitativeEulerEndpointSectorTerminalOriginalV1
public import QuantitativeSpectralObservabilityReconstructionV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedSourceObservation
open UpperHalfPlane ContinuousLinearMap QuantitativeHolomorphic AsymptoticSectorSigns
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFilterExpression QuantitativeArithmeticRetainedSectorReconstruction
open QuantitativeArithmeticRetainedPreparedReconstruction
open QuantitativeArithmeticRetainedRegularNormalization QuantitativeArithmeticRetainedRegularExtension
open QuantitativeArithmeticRetainedCylinderNormalization (bound)
open AsymptoticOrbitDiagonal
open AsymptoticRegularCompactBranch (Space)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (P : Parameters A) (hS : ∀p∈S,p.Prime) (hN : 0<N)

/-- Normalization only changes the terminal input coordinates. In particular,
the mixed regular extension is controlled by its own terminal restriction. -/
theorem reconstructed_terminal_norm (e : Sector N) (x : ℍ) (v : Space) :
    ‖regularAmbient A P hS hN e x v‖≤bound A P*
      ‖corner (AsymptoticCertificateOperators.highStrip P.ε) x
        (regularAmbient A P hS hN e x v)‖ := by
  let R := reconstruction A hS hN P (multiplier e) (ramifiedParameter e)
    (by omega : 2≤exponent A P+3) x
  let V := scaled A hS hN P (multiplier e) (ramifiedParameter e)
    (by omega : 2≤exponent A P+3) x
  let w := inverseSqrtCFC (V.adjoint.comp V) ((TerminalSpace A P x).subtypeL.adjoint v)
  let g := (bound A P)⁻¹ • w
  have he : regularAmbient A P hS hN e x v=R g := by
    change ((bound A P)⁻¹ • R) w=R ((bound A P)⁻¹ • w)
    rw [smul_apply,map_smul_of_tower]
  have hk := regular_contraction A P hS hN e x
  have ht := reconstruction_terminal A hS hN P (multiplier e) (ramifiedParameter e)
    (by omega : 2≤exponent A P+3) x (hk.trans (by norm_num)) g
  have hR : ‖R‖≤bound A P := by
    apply (opNorm_comp_le _ _).trans
    exact (mul_le_mul (AsymptoticRegularInclusion.inclusion_norm_le P.epsilon_pos x)
      (extension_norm_le A hS hN P (multiplier e) (ramifiedParameter e)
        (fun q _ => multiplier_norm e q) (fun p _ => ramifiedParameter_norm e p)
        (by omega : 2≤exponent A P+3) x hk)
      (norm_nonneg (extension A hS hN P (multiplier e) (ramifiedParameter e)
        (by omega : 2≤exponent A P+3) x)) zero_le_one).trans_eq (one_mul _)
  rw [he]
  change ‖R g‖≤bound A P*‖highProjection A P x (R g)‖
  rw [ht]
  exact R.le_of_opNorm_le hR g

theorem reconstructed_norm_on_terminal (e : Sector N) (x : ℍ) (v : Space)
    (hv : v∈TerminalSpace A P x) : ‖regularAmbient A P hS hN e x v‖=‖v‖ := by
  let T := TerminalSpace A P x
  have hproj : T.subtypeL.adjoint v=(⟨v,hv⟩ : T) := by
    rw [Submodule.adjoint_subtypeL]
    apply Subtype.ext
    exact T.starProjection_eq_self_iff.mpr hv
  simp only [regularAmbient,comp_apply]
  rw [hproj]
  exact normalized_norm A hS hN P (multiplier e) (ramifiedParameter e)
    (fun q _ => multiplier_norm e q) (fun p _ => ramifiedParameter_norm e p)
    (by omega : 2≤exponent A P+3) x (regular_contraction A P hS hN e x) ⟨v,hv⟩

theorem terminal_input_le (e : Sector N) (x : ℍ) (v : Space)
    (hv : v∈TerminalSpace A P x) : ‖v‖≤bound A P*
      ‖corner (AsymptoticCertificateOperators.highStrip P.ε) x
        (regularAmbient A P hS hN e x v)‖ := by
  rw [←reconstructed_norm_on_terminal A P hS hN e x v hv]
  exact reconstructed_terminal_norm A P hS hN e x v

open QuantitativeEulerDensityGenerators QuantitativeEulerEndpointPrepared
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction QuantitativeNewGap
open scoped Classical MatrixGroups

/-- The original Euler-row observability theorem transfers to mixed
reconstruction without an admissible-level certificate. Only the actual
upper-height, boundary and quotient tails remain. -/
theorem exists_original_observability [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (D₀ : Prepared N excluded threshold)
    (hN2 : 2≤N) (e : Sector N) (G : Finset SL(2,ℤ))
    (hG : Subgroup.closure (G : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N) :
    let U := regularAmbient A P hS hN e
    ∃ (W : Finset (List SL(2,ℤ))) (Bobs : ℝ),1≤Bobs ∧
      ∃ Bg : ℝ,1≤Bg ∧ ∃ D : ℝ,1≤D ∧ ∃ B : ℝ,1≤B ∧ ∃ K : ℝ,0≤K ∧
      ∀ C : ℝ,B≤C → ∀q : ℕ,[Fact q.Prime] → D₀.Good q →
      ∃ hqN : ¬q∣N,∀H : ℝ,max P.ε⁻¹ 4≤H →
      (∀i,sectorFamilyB N (NeZero.pos N) e G hG i≤H) →
      ∀x : ℍ,fundamentalGood N x → ∀v : Space,v∈TerminalSpace A P x →
      corner (AsymptoticCertificateOperators.highStrip P.ε\AsymptoticHyperbolicArea.terminal P.ε) x (U x v)=0 →
      corner (AsymptoticHyperbolicArea.terminal H) x (U x v)=0 →
      quotientTailStack N (fun i => H/sectorFamilyC N (NeZero.pos N) e G hG i) P.epsilon_pos
        (by omega : 1≤exponent A P+4) (sectorFamilySampled N (NeZero.pos N) e H P.epsilon_pos
          (by omega : 1≤exponent A P+4)) x (U x v)=0 →
      let Y := min P.ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let hZ := div_pos (lt_min P.epsilon_pos (by norm_num : (0:ℝ)<1/4)) (wideDistortion_pos Bg 2 (D*H))
      let L := (2*generatorTransportConstant D₀*C)*(q:ℝ)^4
      let hs := wideFreshRegion_compact L R R hZ
      ‖v‖^2≤(bound A P)^2*sectorObservationCost N (NeZero.pos N) e G hG W Bobs H P.ε (exponent A P+4)*
        (K*((wideDistortion L R R)^(exponent A P+4))^2*
          primeOldOriginalEnergy e q hqN hs P.epsilon_pos (exponent A P+4) x (U x v)+
          ‖sectorSampling N (NeZero.pos N) e H P.epsilon_pos (by omega : 1≤exponent A P+4) x (U x v)‖^2) := by
  dsimp only
  obtain ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,hobs⟩ :=
    exists_sector_terminal_original_observability D₀ hN2 e G hG P.epsilon_pos
  refine ⟨W,Bobs,hBobs,Bg,hBg,D,hD,B,hB,K,hK,?_⟩
  intro C hBC q hqPrime hgood
  obtain ⟨hqN,hobs⟩ := hobs C hBC q hgood
  refine ⟨hqN,?_⟩
  intro H hH hdata x hx v hv hboundary hupper htail
  have hn := terminal_input_le A P hS hN e x v hv
  rw [closed_terminal_corner_of_boundary_zero P.ε x (regularAmbient A P hS hN e x v) hboundary] at hn
  have hn2 := pow_le_pow_left₀ (norm_nonneg v) hn 2
  rw [mul_pow] at hn2
  have ho := hobs H hH hdata (exponent A P+4) (by omega) x hx (regularAmbient A P hS hN e x v) hupper htail
  have hh := mul_le_mul_of_nonneg_left ho (sq_nonneg (bound A P))
  exact hn2.trans (hh.trans_eq (by ring))

#print axioms reconstructed_terminal_norm
#print axioms reconstructed_norm_on_terminal
#print axioms terminal_input_le
#print axioms exists_original_observability
end QuantitativeArithmeticRetainedSourceObservation
