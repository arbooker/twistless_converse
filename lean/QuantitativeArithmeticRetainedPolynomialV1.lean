module

public import QuantitativeArithmeticRetainedPacketV1
public import QuantitativeEulerEndpointUnitSubcornerV1
public import QuantitativeEulerEndpointSubcornerMassV1
public import QuantitativeEulerEndpointRetainedNormalizedRecurrenceV1
public import QuantitativeEulerEndpointControlledPacketV1
public import QuantitativeEulerEndpointControlledParametersV1
public import QuantitativeEulerEndpointSupportOperationsV1
public import QuantitativeEulerEndpointPacketSupportV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedTerminalAlgebra
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeEulerEndpointRegularBase AsymptoticRegularTrace
open QuantitativeEulerEndpointUnitSubcorner QuantitativeEulerEndpointCanonicalHalf
open QuantitativeArithmeticRetainedRegularExtension AsymptoticSubgroupSupport MeasureTheory

variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)
local notation "s" => terminalRegion A P
local notation "hs" => terminal_measurable A P
local notation "hp" => unitProjection action_measurable s hs

def terminalSpace (x : Base) : ClosedSubmodule ℂ AsymptoticFiniteBranch.RegularSpace where
  toSubmodule := TerminalSpace A P x
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (TerminalSpace A P x))).isClosed

theorem terminal_space_projection (x : Base) :
    (terminalSpace A P x).toSubmodule.starProjection=rep A P 1 x := (rep_one A P x).symm

def half (F : Algebra A P) : UpperHalfPlane → ClosedSubmodule ℂ AsymptoticFiniteBranch.RegularSpace :=
  fun x => space action_measurable s hs 1 hp (lift action_measurable s hs F) (show Base from x)

def halfProjection (F : Algebra A P) (hF : IsSelfAdjoint F) : Algebra A P :=
  projection action_measurable s hs 1 hp (terminalSpace A P) (terminal_space_projection A P)
    (lift action_measurable s hs F)
    (by apply Subtype.ext; exact hF)

theorem half_projection (F : Algebra A P) (hF : IsSelfAdjoint F) : IsStarProjection (halfProjection A P F hF) :=
  projection_isStarProjection action_measurable s hs 1 hp (terminalSpace A P)
    (terminal_space_projection A P) _ _

theorem half_representation (F : Algebra A P) (hF : IsSelfAdjoint F) (x : Base) :
    rep A P (halfProjection A P F hF) x=(half A P F x).toSubmodule.starProjection := rfl

theorem half_regular (F : Algebra A P) (hF : IsSelfAdjoint F) :
    (∀ g k,Measurable (fun x : UpperHalfPlane => matrix (half A P F x).toSubmodule.starProjection g k)) ∧
      Covariant (fun x => (half A P F x).toSubmodule.starProjection) := by
  exact ⟨QuantitativeSpectralRegularAlgebra.representation_matrix_measurable
    _ _ action_measurable s hs (halfProjection A P F hF),
    QuantitativeSpectralRegularAlgebra.representation_covariant
    _ _ action_measurable s hs (halfProjection A P F hF)⟩

theorem half_le_terminal (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) (x : UpperHalfPlane) :
    (half A P F x).toSubmodule≤TerminalSpace A P x := by
  apply space_le_baseline action_measurable s hs 1 hp (lift action_measurable s hs F)
    (lift_nonneg action_measurable s hs F hF0) (terminalSpace A P) _ x
  intro y
  rw [terminal_space_projection]
  exact (QuantitativeSpectralRegularOrder.pointwise_le_iff action_measurable s hs F 1).mpr hF1 y

theorem half_supported (F : Algebra A P) (hF : IsSelfAdjoint F)
    (S : Subgroup AsymptoticRationalGroup.Group)
    (hFS : ∀ x,Supported S (rep A P F x)) (x : UpperHalfPlane) :
    Supported S (half A P F x).toSubmodule.starProjection := by
  apply QuantitativeSpectralCutRegularity.highAt_supported S (rep A P F x) (hFS x)
  have hF' : IsSelfAdjoint (lift action_measurable s hs F) := by
    apply Subtype.ext
    exact hF
  exact hF'.map (QuantitativeEulerEndpointCornerCut.evaluation action_measurable s hs 1 hp x)

theorem half_mass (F : Algebra A P) (hF : IsSelfAdjoint F) :
    tr A P (halfProjection A P F hF)=QuantitativeEulerEndpointPrepared.cornerMass (half A P F) :=
  QuantitativeEulerEndpointSubcornerMass.initial_trace_eq action_measurable s hs
    (halfProjection A P F hF) (half_projection A P F hF) measure (terminal_finite A P)

#print axioms half_projection
#print axioms half_regular
#print axioms half_le_terminal
#print axioms half_supported
#print axioms half_mass
end QuantitativeArithmeticRetainedTerminalAlgebra

namespace QuantitativeArithmeticRetainedPolynomial
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointPrepared
open QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeArithmeticRetainedPacket QuantitativeEulerEndpointUnitSubcorner
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointBlockGram
open QuantitativeEulerEndpointSoftUpdate MeasureTheory Polynomial AsymptoticRegularTrace
open scoped ENNReal

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ)
    (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))
variable (C : ℕ → ℝ) (hC : ∀ i x,‖QuantitativeArithmeticRetainedPacket.rows A P hR₀ e hs l i x‖≤C i)
local notation "t" => terminalRegion A P
local notation "ht" => terminal_measurable A P
local notation "hp" => unitProjection action_measurable t ht
local notation "𝔄" => Algebra A P
local notation "𝕌" => UnitCorner action_measurable t ht
local notation "val" => value action_measurable t ht
local notation "up" => lift action_measurable t ht
local notation "B" => rows A P hR₀ e hs l
local notation "n" => l.length+1
local notation "hmB" => fun i => And.left (rows_regular A P hR₀ e hs l i)
local notation "hcB" => fun i => And.right (rows_regular A P hR₀ e hs l i)
local notation "NB" => QuantitativeEulerEndpointNormalizedRows.row action_measurable t ht 1 B C n
local notation "NC" => QuantitativeEulerEndpointNormalizedRows.bound C n
local notation "hmNB" => QuantitativeEulerEndpointNormalizedRows.row_measurable action_measurable t ht 1 B hmB C n
local notation "hcNB" => QuantitativeEulerEndpointNormalizedRows.row_covariant action_measurable t ht 1 B hcB C n
local notation "hnNB" => QuantitativeEulerEndpointNormalizedRows.row_norm action_measurable t ht 1 hp B C hC n
local notation "hsNB" => QuantitativeEulerEndpointNormalizedRows.row_source action_measurable t ht 1 hp B C n

def unitGram : 𝕌 := gramSum action_measurable t ht 1 hp NB hmNB hcNB NC hnNB hsNB n

theorem value_unitGram : val (unitGram A P hR₀ e hs l C hC)=gram A P hR₀ e hs l C hC := by
  apply QuantitativeSpectralRegularOrder.representation_injective action_measurable t ht
  funext x
  change representation action_measurable t ht 1 hp (unitGram A P hR₀ e hs l C hC) x=rep A P (gram A P hR₀ e hs l C hC) x
  rw [unitGram,representation_gramSum,rep_gram]
  apply Finset.sum_congr rfl
  intro i _
  have he : NB i x=scaledRows A P hR₀ e hs l C i x := by
    change ((QuantitativeEulerEndpointBlockNormalization.factor C n : ℝ):ℂ) •
      (B i x*AsymptoticOrbitDiagonal.corner t x)=_
    have he : AsymptoticOrbitDiagonal.corner t x=
        (QuantitativeArithmeticRetainedRegularExtension.TerminalSpace A P x).starProjection :=
      (QuantitativeSpectralExceptionalRows.region_projection _ x).symm
    rw [he,QuantitativeArithmeticRetainedPacket.rows_source]
    rfl
  rw [he]

def next (F : 𝔄) (L : ℕ) (z : ℝ[X]) : 𝔄 :=
  aeval (update F (F*gram A P hR₀ e hs l C hC*F) L) z

def unitNext (F : 𝔄) (L : ℕ) (z : ℝ[X]) : 𝕌 :=
  aeval (update (up F) (up F*unitGram A P hR₀ e hs l C hC*up F) L) z

theorem value_unitNext (F : 𝔄) (L : ℕ) (z : ℝ[X]) :
    val (unitNext A P hR₀ e hs l C hC F L z)=next A P hR₀ e hs l C hC F L z := by
  rw [unitNext,value_aeval,value_update]
  have hm (a b : 𝕌) : val (a*b)=val a*val b := rfl
  simp only [hm,value_lift,value_unitGram,next]

/-- The retained polynomial recurrence on the entire terminal strip, with
exactly the registered combined Gram. The only hard input is its canonical-half packet contraction. -/
theorem exists_next (F : 𝔄) (hF0 : 0≤F) (hF1 : F≤1)
    (c : ℝ) (hc : 0<c) {d K : ℝ} (hd : 0<d) (hK : 0<K)
    (hcut : 2*d^2<K) (hbound : 1+d^2≤K) (target : ℝ)
    (htheta0 : 0≤Real.log (K/(QuantitativeEulerEndpointBlockNormalization.factor C n*c)^2)/Real.log (K/(2*d^2)))
    (htheta1 : Real.log (K/(QuantitativeEulerEndpointBlockNormalization.factor C n*c)^2)/Real.log (K/(2*d^2))≤1)
    (hchain : cornerMass (fun x => QuantitativeSpectralDeflationChain.chain (half A P F x)
      (fun i => B i x) c n)-target≤(l.map primeFactor).prod*(cornerMass (half A P F)-target))
    (L : ℕ) {J : ℕ} (hJ : 0<J) :
    ∃ z : ℝ[X], z.natDegree≤16*J^5+1 ∧
      (∑ i∈z.support,|z.coeff i|)≤(((16*J^5:ℕ):ℝ)+2)*3^(16*J^5) ∧
      QuantitativeEulerEndpointBernstein.ScalarSharpening z ∧
      0≤next A P hR₀ e hs l C hC F L z ∧ next A P hR₀ e hs l C hC F L z≤F ∧
      tr A P (next A P hR₀ e hs l C hC F L z-(next A P hR₀ e hs l C hC F L z)^2)≤
        4*P.ε⁻¹/(J:ℝ) ∧
      (∀ E : 𝔄,F*E=E → (∀ i : Fin n,∀ x,B i x*rep A P E x=0) →
        next A P hR₀ e hs l C hC F L z*E=E) ∧
      tr A P (next A P hR₀ e hs l C hC F L z)-target≤
        (1-(1-Real.exp (-(L:ℝ)*(d^2/32)))*(1-(l.map primeFactor).prod)*
          (1-Real.log (K/(QuantitativeEulerEndpointBlockNormalization.factor C n*c)^2)/Real.log (K/(2*d^2))))*
          (tr A P F-target)+(4+2*(L:ℝ))*tr A P (F-F^2)+
          P.ε⁻¹*(Real.log 2/Real.log (K/(2*d^2))) := by
  let q := halfProjection A P F (IsSelfAdjoint.of_nonneg hF0)
  have hq := half_projection A P F (IsSelfAdjoint.of_nonneg hF0)
  have hmass := half_mass A P F (IsSelfAdjoint.of_nonneg hF0)
  have hchain' : (trace measure (QuantitativeSpectralRegularPacket.projectionFamily
      (fun x : Base => half A P F x) B c n)).toReal-target≤
      (l.map primeFactor).prod*(QuantitativeSpectralFiniteCornerTrace.rootedTrace measure action_measurable t ht
        (terminal_finite A P) q-target) := by
    change cornerMass (fun x => QuantitativeSpectralDeflationChain.chain (half A P F x) (fun i => B i x) c n)-target≤
      (l.map primeFactor).prod*(tr A P q-target)
    rw [hmass]
    exact hchain
  obtain ⟨z,hdeg,hmassz,hscalar,hz0,hzF,hdef,hfixed,hrec⟩ :=
    QuantitativeEulerEndpointNormalizedRecurrence.exists_normalized_block_update_scalar
      action_measurable t ht 1 hp measure (terminal_finite A P)
      (terminalSpace A P) (terminal_space_projection A P) q hq
      (fun x : Base => half A P F x) (fun _ => rfl) B hmB hcB C hC
      action_preserving (up F) (lift_nonneg action_measurable t ht F hF0)
      (lift_le_one action_measurable t ht F hF1) (fun _ => rfl) n c hc hd hK hcut
      ((add_le_add (QuantitativeEulerEndpointNormalizedRows.bound_square_sum C n) (le_refl (d^2))).trans hbound)
      target (l.map primeFactor).prod (primeProduct_nonneg l)
      (QuantitativeEulerEndpointControlledPacket.primeProduct_le_one l) htheta0 htheta1 hchain' L hJ
  have hm (a b : 𝕌) : val (a*b)=val a*val b := rfl
  have hval := value_unitNext A P hR₀ e hs l C hC F L z
  have hτ (a : 𝕌) : rootedTrace action_measurable t ht 1 hp measure (terminal_finite A P) a=tr A P (val a) := rfl
  change 0≤unitNext A P hR₀ e hs l C hC F L z at hz0
  change unitNext A P hR₀ e hs l C hC F L z≤up F at hzF
  change rootedTrace action_measurable t ht 1 hp measure (terminal_finite A P)
    (unitNext A P hR₀ e hs l C hC F L z-(unitNext A P hR₀ e hs l C hC F L z)^2)≤_ at hdef
  change rootedTrace action_measurable t ht 1 hp measure (terminal_finite A P)
    (unitNext A P hR₀ e hs l C hC F L z)-target≤_ at hrec
  simp only [hτ,map_sub,pow_two,hm,hval,value_one,tr_one] at hdef
  have harea : (measure t).toReal=P.ε⁻¹ := by
    rw [terminal_area,ENNReal.toReal_ofReal (inv_nonneg.mpr P.epsilon_pos.le)]
  simp only [hτ,map_sub,pow_two,hm,hval,value_lift,harea] at hrec
  refine ⟨z,hdeg,hmassz,hscalar,?_,?_,?_,?_,?_⟩
  · rw [← hval]
    exact (value_le_iff action_measurable t ht 0 _).mpr hz0
  · rw [← hval]
    exact (value_le_iff action_measurable t ht _ (up F)).mpr hzF
  · simpa only [pow_two,map_sub] using hdef
  · intro E hFE hBE
    have hh := hfixed (up E) (by apply Subtype.ext; exact hFE) hBE
    have hh' := congrArg val hh
    change val (unitNext A P hR₀ e hs l C hC F L z*up E)=E at hh'
    simpa only [hm,hval,value_lift] using hh'
  · simpa only [pow_two,map_sub] using hrec

#print axioms value_unitGram
#print axioms value_unitNext
#print axioms exists_next
end QuantitativeArithmeticRetainedPolynomial

namespace QuantitativeArithmeticRetainedPolynomial
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeArithmeticRetainedPacket Polynomial
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBlocks
open QuantitativeEulerEndpointControlledIteration

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N R₀ Q hQ)
    (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))
variable (C : ℕ → ℝ) (hC : ∀ i x,‖QuantitativeArithmeticRetainedPacket.rows A P hR₀ e hs l i x‖≤C i)
local notation "r" => QuantitativeEulerEndpointBlockNormalization.factor C (l.length+1)
local notation "area" => P.ε⁻¹

def logCost (bounds : ℕ → ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  Real.log (2/(QuantitativeEulerEndpointBlockNormalization.factor bounds n*c)^2)
def effort (bounds : ℕ → ℝ) (b n j : ℕ) (c : ℝ) : ℝ :=
  QuantitativeEulerEndpointLocalEffort.effort n j (logCost bounds b c)

theorem logCost_nonneg (bounds : ℕ → ℝ) (n : ℕ) {c : ℝ} (hc : 0<c)
    (hu : QuantitativeEulerEndpointBlockNormalization.factor bounds n*c≤1) : 0≤logCost bounds n c := by
  have hr := QuantitativeEulerEndpointBlockNormalization.factor_pos bounds n
  have hrc : 0<QuantitativeEulerEndpointBlockNormalization.factor bounds n*c := mul_pos hr hc
  apply Real.log_nonneg
  apply (one_le_div (sq_pos_of_pos hrc)).mpr
  nlinarith

/-- The finite-horizon schedule pays the actual normalized threshold, the
attenuation and the propagated incoming defect on the full terminal strip.
No positivity assumption on signed trace excess is used. -/
theorem exists_scheduled_next (n j : ℕ) (hj : j≤n)
    (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) (target c : ℝ)
    (hc : 0<c) (hu : r*c≤1)
    (hchain : cornerMass (fun x => QuantitativeSpectralDeflationChain.chain (half A P F x)
      (fun i => rows A P hR₀ e hs l i x) c (l.length+1))-target≤
      (l.map primeFactor).prod*(cornerMass (half A P F)-target))
    (hdef : tr A P (F-F^2)≤4*area/(sharpness area (effort C (l.length+1) n j c):ℝ))
    {T : ℕ} (hT : 0<T) :
    let E := effort C (l.length+1) n j c
    ∃ z : ℝ[X], z.natDegree≤16*T^5+1 ∧
      (∑ i∈z.support,|z.coeff i|)≤(((16*T^5:ℕ):ℝ)+2)*3^(16*T^5) ∧
      QuantitativeEulerEndpointBernstein.ScalarSharpening z ∧
      0≤next A P hR₀ e hs l C hC F (power E) z ∧ next A P hR₀ e hs l C hC F (power E) z≤F ∧
      tr A P (next A P hR₀ e hs l C hC F (power E) z-(next A P hR₀ e hs l C hC F (power E) z)^2)≤4*area/(T:ℝ) ∧
      (∀ D : Algebra A P,F*D=D →
        (∀ i : Fin (l.length+1),∀ x,rows A P hR₀ e hs l i x*rep A P D x=0) →
        next A P hR₀ e hs l C hC F (power E) z*D=D) ∧
      max 0 (tr A P (next A P hR₀ e hs l C hC F (power E) z)-target)≤
        ((l.map primeFactor).prod+2*blockRelativeLoss n j)*max 0 (tr A P F-target)+
          (1+area*Real.log 2)*blockAdditiveLoss n j := by
  intro E
  have harea : 0≤area := inv_nonneg.mpr P.epsilon_pos.le
  have hM := logCost_nonneg C (l.length+1) hc hu
  have hE : 0<E := QuantitativeEulerEndpointLocalEffort.effort_pos n j hM
  have hratio : logCost C (l.length+1) c/E≤blockRelativeLoss n j :=
    QuantitativeEulerEndpointLocalEffort.effort_ratio n j hj hM
  have hinverse : 1/E≤blockAdditiveLoss n j :=
    QuantitativeEulerEndpointLocalEffort.effort_inverse n j hj hM
  have htheta0 : 0≤logCost C (l.length+1) c/E := div_nonneg hM hE.le
  have htheta1 : logCost C (l.length+1) c/E≤1 :=
    hratio.trans (QuantitativeEulerEndpointControlledParameters.relative_le_one n j hj)
  have htheta : Real.log (2/(r*c)^2)/Real.log (2/(2*(cut E)^2))=logCost C (l.length+1) c/E := by
    rw [cut_log]
    rfl
  obtain ⟨z,hdeg,hmass,hscalar,hz0,hzF,hzdef,hfixed,hrec⟩ :=
    exists_next A P hR₀ e hs l C hC F hF0 hF1 c hc (cut_pos E) (by norm_num : (0:ℝ)<2)
      (cut_conditions hE).1 (cut_conditions hE).2 target
      (by rw [htheta]; exact htheta0) (by rw [htheta]; exact htheta1) hchain (power E) hT
  refine ⟨z,hdeg,hmass,hscalar,hz0,hzF,hzdef,hfixed,?_⟩
  rw [htheta,cut_log] at hrec
  have he0 : 0≤Real.exp (-(power E:ℝ)*((cut E)^2/32)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(power E:ℝ)*((cut E)^2/32))≤1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity))
  have hcoef := coefficient_bounds (primeProduct_nonneg l)
    (QuantitativeEulerEndpointControlledPacket.primeProduct_le_one l) htheta0 htheta1 he0 he1
  have hrel : logCost C (l.length+1) c/E+Real.exp (-(power E:ℝ)*((cut E)^2/32))≤2*blockRelativeLoss n j := by
    have hh := (attenuation hE).trans (hinverse.trans (QuantitativeEulerEndpointControlledParameters.additive_le_relative n j))
    linarith
  have hamp : 0≤4+2*(power E:ℝ) := by positivity
  have hsharp := sharpness_error harea hE (le_refl area)
  have hpaid := (mul_le_mul_of_nonneg_left hdef hamp).trans hsharp
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hscale : 0≤1+area*Real.log 2 := by positivity
  have herror : (4+2*(power E:ℝ))*tr A P (F-F^2)+area*(Real.log 2/E)≤
      (1+area*Real.log 2)*blockAdditiveLoss n j := by
    have hh := mul_le_mul_of_nonneg_left hinverse hscale
    calc
      _ ≤ 1/E+area*(Real.log 2/E) := add_le_add hpaid le_rfl
      _ = (1+area*Real.log 2)*(1/E) := by ring
      _ ≤ _ := hh
  have herr0 : 0≤(1+area*Real.log 2)*blockAdditiveLoss n j :=
    mul_nonneg hscale (blockAdditiveLoss_nonneg n j)
  have hrec' : tr A P (next A P hR₀ e hs l C hC F (power E) z)-target≤
      (1-(1-Real.exp (-(power E:ℝ)*((cut E)^2/32)))*(1-(l.map primeFactor).prod)*
        (1-logCost C (l.length+1) c/E))*(tr A P F-target)+
        (1+area*Real.log 2)*blockAdditiveLoss n j := by linarith [hrec,herror]
  have hpos := positive_part_step hcoef.1 herr0 hrec'
  have hcoef' : 1-(1-Real.exp (-(power E:ℝ)*((cut E)^2/32)))*(1-(l.map primeFactor).prod)*
      (1-logCost C (l.length+1) c/E)≤(l.map primeFactor).prod+2*blockRelativeLoss n j := by
    linarith [hcoef.2]
  exact hpos.trans (add_le_add (mul_le_mul_of_nonneg_right hcoef' (le_max_left _ _)) le_rfl)

#print axioms logCost_nonneg
#print axioms exists_scheduled_next
end QuantitativeArithmeticRetainedPolynomial

namespace QuantitativeArithmeticRetainedPolynomial
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointPrepared
open QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeEulerEndpointUnitSubcorner
open QuantitativeArithmetic QuantitativeEulerDensityGenerators
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup QuantitativeHolomorphic Polynomial

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))
variable (C : ℕ → ℝ) (hC : ∀ i x,‖QuantitativeArithmeticRetainedPacket.rows A P hR₀ e hs l i x‖≤C i)
variable (r : EligiblePrime N) (hrQ : ¬r.val∣Q) (hrR : ∀p∈R₀,¬r.val∣p)
  (hrfixed : ∀ a : UnitResidue N,¬r.val∣(primeLift N a).q) (hr : r∉l)
local notation "t" => terminalRegion A P
local notation "ht" => terminal_measurable A P
local notation "hp" => unitProjection action_measurable t ht

include hrQ hrR hrfixed hr in
theorem combined_rows_supported (i : ℕ) (x : UpperHalfPlane) :
    Supported (integralGroup r.val) (QuantitativeArithmeticRetainedPacket.rows A P hR₀ e hs l i x) := by
  have hU := QuantitativeArithmeticRetainedIntegralSupport.normalized_supported r.val A hR₀ (NeZero.pos N) r.property.2 hrQ hrR P e x
  cases i with
  | zero =>
    exact supported_comp _ _ _
      (newBaselineDetector_supported N e r.val r.property.2 hrfixed hs
        P.epsilon_pos
        (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) x) hU
  | succ i =>
    exact supported_comp _ _ _
      (packetSequence_supported N (NeZero.pos N) (sign e.1) hs
        P.epsilon_pos
        (QuantitativeArithmeticRetainedPreparedReconstruction.exponent A P+4) l r hr i x) hU

include hrQ hrR hrfixed hr in
theorem combined_gram_supported (x : Base) :
    Supported (integralGroup r.val) (rep A P (QuantitativeArithmeticRetainedPacket.gram A P hR₀ e hs l C hC) x) := by
  rw [QuantitativeArithmeticRetainedPacket.rep_gram]
  apply Finset.sum_induction
  · intro a b ha hb
    exact supported_add _ _ _ ha hb
  · intro g h _
    rfl
  intro i _
  have hh : Supported (integralGroup r.val) (QuantitativeArithmeticRetainedPacket.scaledRows A P hR₀ e hs l C i x) :=
    supported_smul _ _ (combined_rows_supported A P hR₀ e hs l r hrQ hrR hrfixed hr i x) _
  exact supported_comp _ _ _ (supported_adjoint _ _ hh) hh

include hrQ hrR hrfixed hr in
/-- Every future eligible prime avoiding the fixed denominators and the current
block remains a support prime after the complete polynomial update. -/
theorem next_supported (F : Algebra A P)
    (hF : ∀ x,Supported (integralGroup r.val) (rep A P F x)) (L : ℕ) (z : ℝ[X]) (x : Base) :
    Supported (integralGroup r.val) (rep A P (next A P hR₀ e hs l C hC F L z) x) := by
  have hP (y : Base) : Supported (integralGroup r.val) (rep A P 1 y) := by
    rw [rep_one,QuantitativeSpectralExceptionalRows.region_projection]
    exact AsymptoticSubgroupSupport.supported_corner _ _ _
  have hG (y : Base) : Supported (integralGroup r.val)
      (QuantitativeEulerEndpointSubcorner.representation action_measurable t ht 1 hp (unitGram A P hR₀ e hs l C hC) y) := by
    change Supported (integralGroup r.val) (rep A P (value action_measurable t ht (unitGram A P hR₀ e hs l C hC)) y)
    rw [value_unitGram]
    exact combined_gram_supported A P hR₀ e hs l C hC r hrQ hrR hrfixed hr y
  have hh := QuantitativeEulerEndpointSupportAlgebra.update_polynomial_supported
    action_measurable t ht 1 hp (integralGroup r.val) hP
    (lift action_measurable t ht F) (unitGram A P hR₀ e hs l C hC) hF hG L z x
  change Supported (integralGroup r.val)
    (rep A P (value action_measurable t ht (unitNext A P hR₀ e hs l C hC F L z)) x) at hh
  rwa [value_unitNext] at hh

#print axioms combined_rows_supported
#print axioms combined_gram_supported
#print axioms next_supported
end QuantitativeArithmeticRetainedPolynomial
