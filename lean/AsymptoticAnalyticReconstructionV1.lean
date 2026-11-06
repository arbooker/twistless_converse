module

public import AsymptoticWeightedFEV1
public import AsymptoticGeometricReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticAnalyticReconstruction

open MeasureTheory UpperHalfPlane Set Filter
open FinitenessCertificate FinitenessGlobalHeight FinitenessAnalyticReconstruction
open AsymptoticCertificateBranches AsymptoticCertificateOperators
open AsymptoticHyperbolicSlash AsymptoticWeightedBranches AsymptoticWeightedFE

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem lowPart_coeFn (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (m : ℕ) (F : ℂ → ℂ) (u : Space) (hu : u =ᵐ[volume] stripSection P.ε t m F)
    (v : Index A) :
    lowPart A hN P t m v u =ᵐ[volume]
      lowValue (level_pos A hN v) (inputShift A v) (outputShift A v)
        P.ε P.ρ (lowCell A P.ε v) t m F := by
  let g := AsymptoticFoldedLow.fold (level_pos A hN v) (inputShift A v) (outputShift A v)
  have hp : ∀ᵐ z ∂volume, ∀ n : ℤ,u (g n • z)=stripSection P.ε t m F (g n • z) :=
    ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (g n) (volume : Measure ℍ)).quasiMeasurePreserving.ae hu)
  have ho := AsymptoticFoldedLow.operator_coeFn (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShift_nonneg A v) (outputShift_lt_one A v).le (fun _ hz => hz.1) ht m u
  filter_upwards [ho,hp] with z hz hzp
  apply hz.trans
  apply tsum_congr
  intro n
  rw [hzp n]

theorem terminalPart_coeFn (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (m : ℕ) (F : ℂ → ℂ) (u : Space) (hu : u =ᵐ[volume] stripSection P.ε t m F)
    (v : Index A) :
    terminalPart A hN P ht m v u =ᵐ[volume]
      terminalValue (level_pos A hN v) (inputShift A v) (outputShift A v)
        P.ε (lowCell A P.ε v) t m F := by
  let g := AsymptoticFoldedLow.fold (level_pos A hN v) (inputShift A v) (outputShift A v)
  have hp : ∀ᵐ z ∂volume, ∀ n : ℤ,u (g n • z)=stripSection P.ε t m F (g n • z) :=
    ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (g n) (volume : Measure ℍ)).quasiMeasurePreserving.ae hu)
  have ho := AsymptoticFoldedTerminal.operator_coeFn (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
    (outputShift_nonneg A v) (outputShift_lt_one A v).le
    (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m u
  filter_upwards [ho,hp] with z hz hzp
  apply hz.trans
  apply tsum_congr
  intro n
  rw [hzp n]

theorem reconstruction_coeFn (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (F : ℂ → ℂ) (u : Space)
    (hu : u =ᵐ[volume] stripSection P.ε t m F) :
    (low A hN P χ t m u+terminal A hN P χ ht m u:Space) =ᵐ[volume]
      reconstructionValue A hN P χ t m F := by
  have he : low A hN P χ t m u+terminal A hN P χ ht m u=
      ∑ v : Index A,amplitude A χ v • (lowPart A hN P t m v u+terminalPart A hN P ht m v u) := by
    simp only [low,terminal,_root_.sum_apply,_root_.smul_apply,smul_add,Finset.sum_add_distrib]
  rw [he]
  apply (Lp.coeFn_finsetSum _ _).trans
  have hv : reconstructionValue A hN P χ t m F=
      ∑ v : Index A,fun z : ℍ => amplitude A χ v*
        (lowValue (level_pos A hN v) (inputShift A v) (outputShift A v)
          P.ε P.ρ (lowCell A P.ε v) t m F z+
        terminalValue (level_pos A hN v) (inputShift A v) (outputShift A v)
          P.ε (lowCell A P.ε v) t m F z) := by
    funext z
    simp only [reconstructionValue,Finset.sum_apply]
  rw [hv]
  apply eventuallyEq_sum
  intro v _
  filter_upwards [Lp.coeFn_smul (amplitude A χ v)
    (lowPart A hN P t m v u+terminalPart A hN P ht m v u),
    Lp.coeFn_add (lowPart A hN P t m v u) (terminalPart A hN P ht m v u),
    lowPart_coeFn A hN P (by omega : 1≤t) m F u hu v,
    terminalPart_coeFn A hN P ht m F u hu v] with z hsm ha hl hr
  rw [hsm]
  change amplitude A χ v*(lowPart A hN P t m v u+terminalPart A hN P ht m v u) z=_
  rw [ha]
  change amplitude A χ v*(lowPart A hN P t m v u z+terminalPart A hN P ht m v u z)=_
  rw [hl,hr]

/-- Terminal branches see only the terminal restriction, on all of L². -/
theorem terminal_high (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (u : Space) :
    terminal A hN P χ ht m u=terminal A hN P χ ht m (highProjection A P u) := by
  have hz : ∀ v : Index A,terminalPart A hN P ht m v (u-highProjection A P u)=0 := by
    intro v
    apply AsymptoticFoldedTerminal.operator_eq_zero_of_target
      (level_pos A hN v) (inputShift A v) (outputShift A v)
      (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
      (outputShift_nonneg A v) (outputShift_lt_one A v).le
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m
    filter_upwards [Lp.coeFn_sub u (highProjection A P u),
      AsymptoticRegionL2.projection_coeFn volume (highStrip P.ε) (highStrip_measurable P.ε) u]
      with z hsub hproj hhigh
    rw [hsub]
    change u z-highProjection A P u z=0
    have hh : highProjection A P u z=u z := hproj.trans (Set.indicator_of_mem hhigh _)
    rw [hh,sub_self]
  have he : terminal A hN P χ ht m (u-highProjection A P u)=0 := by
    simp only [terminal,_root_.sum_apply,_root_.smul_apply,hz,smul_zero,Finset.sum_const_zero]
  exact sub_eq_zero.mp (by simpa only [map_sub] using he)

/-- The analytic FE supplies the reconstruction equation for its actual
weighted L² representative. L² existence is kept explicit here and will
be obtained from the cylinder embedding. -/
theorem equation_of_FE (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (u : Space) (hu : u =ᵐ[volume] stripSection P.ε t m F) :
    u=highProjection A P u+low A hN P χ t m u+
      terminal A hN P χ ht m (highProjection A P u) := by
  rw [← terminal_high A hN P χ ht m u,add_assoc]
  apply Lp.ext
  filter_upwards [hu,reconstruction_coeFn A hN P χ ht m F u hu,
    AsymptoticRegionL2.projection_coeFn volume (highStrip P.ε) (highStrip_measurable P.ε) u,
    Lp.coeFn_add (highProjection A P u) (low A hN P χ t m u+terminal A hN P χ ht m u)]
    with z hz hr hh ha
  change u z=(highProjection A P u+(low A hN P χ t m u+terminal A hN P χ ht m u):Space) z
  rw [ha]
  change u z=highProjection A P u z+(low A hN P χ t m u+terminal A hN P χ ht m u:Space) z
  rw [hr,hz]
  have he : highProjection A P u z=(highStrip P.ε).indicator (stripSection P.ε t m F) z := by
    apply hh.trans
    classical
    by_cases hmem : z∈highStrip P.ε
    · rw [Set.indicator_of_mem hmem,Set.indicator_of_mem hmem,hz]
    · rw [Set.indicator_of_notMem hmem,Set.indicator_of_notMem hmem]
  rw [he]
  exact reconstruct A hN P χ t m F hp hFE z

theorem extension_of_FE (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (u : Space) (hu : u =ᵐ[volume] stripSection P.ε (P.s+3) m F)
    (hK : ‖low A hN P χ (P.s+3) m‖<1) :
    AsymptoticGeometricReconstruction.extension A hN P χ m
      (AsymptoticRegionL2.restrict volume (highStrip P.ε) (highStrip_measurable P.ε) u)=u :=
  AsymptoticGeometricReconstruction.extension_unique A hN P χ m hK u
    (equation_of_FE A hN P χ (by omega : 2≤P.s+3) m F hp hFE u hu)

#print axioms lowPart_coeFn
#print axioms terminalPart_coeFn
#print axioms reconstruction_coeFn
#print axioms terminal_high
#print axioms equation_of_FE
#print axioms extension_of_FE

end AsymptoticAnalyticReconstruction
