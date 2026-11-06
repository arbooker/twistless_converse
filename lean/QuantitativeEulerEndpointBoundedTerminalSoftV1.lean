module

public import QuantitativeEulerEndpointTerminalHalfV1
public import QuantitativeEulerEndpointBoundedTerminalGramV1
public import QuantitativeEulerEndpointRetainedNormalizedRecurrenceV1
public import QuantitativeEulerEndpointControlledPacketV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedTerminal
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointRegularBase QuantitativeEulerEndpointPrepared
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointUnitSubcorner
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointBlockGram
open QuantitativeEulerEndpointSoftUpdate MeasureTheory Polynomial AsymptoticRegularTrace
open scoped ENNReal

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))
local notation "t" => terminalRegion A P
local notation "ht" => terminal_measurable A P
local notation "hp" => unitProjection action_measurable t ht
local notation "𝔄" => Algebra A P
local notation "𝕌" => UnitCorner action_measurable t ht
local notation "val" => value action_measurable t ht
local notation "up" => lift action_measurable t ht
local notation "B" => normalizedCombinedRows A P e hs l
variable (C : ℕ → ℝ)
  (hC : ∀ i x,‖normalizedCombinedRows A P e hs l i x‖≤C i)
local notation "n" => l.length+1
local notation "hmB" => fun i => And.left (normalized_combined_rows_regular A P e hs l i)
local notation "hcB" => fun i => And.right (normalized_combined_rows_regular A P e hs l i)
local notation "NB" => QuantitativeEulerEndpointNormalizedRows.row action_measurable t ht 1 B C n
local notation "NC" => QuantitativeEulerEndpointNormalizedRows.bound C n
local notation "hmNB" => QuantitativeEulerEndpointNormalizedRows.row_measurable action_measurable t ht 1 B hmB C n
local notation "hcNB" => QuantitativeEulerEndpointNormalizedRows.row_covariant action_measurable t ht 1 B hcB C n
local notation "hnNB" => QuantitativeEulerEndpointNormalizedRows.row_norm action_measurable t ht 1 hp B C hC n
local notation "hsNB" => QuantitativeEulerEndpointNormalizedRows.row_source action_measurable t ht 1 hp B C n

def unitGram : 𝕌 := gramSum action_measurable t ht 1 hp NB hmNB hcNB NC hnNB hsNB n

theorem value_unitGram : val (unitGram A P e hs l C hC)=gram A P e hs l C hC := by
  apply QuantitativeSpectralRegularOrder.representation_injective action_measurable t ht
  funext x
  change representation action_measurable t ht 1 hp (unitGram A P e hs l C hC) x=rep A P (gram A P e hs l C hC) x
  rw [unitGram,representation_gramSum,rep_gram]
  apply Finset.sum_congr rfl
  intro i _
  have he : NB i x=scaledRows A P e hs l C i x := by
    change ((QuantitativeEulerEndpointBlockNormalization.factor C n : ℝ):ℂ) •
      (B i x*AsymptoticOrbitDiagonal.corner t x)=_
    rw [normalized_combined_rows_source]
    rfl
  rw [he]

def next (F : 𝔄) (L : ℕ) (z : ℝ[X]) : 𝔄 :=
  aeval (update F (F*gram A P e hs l C hC*F) L) z

def unitNext (F : 𝔄) (L : ℕ) (z : ℝ[X]) : 𝕌 :=
  aeval (update (up F) (up F*unitGram A P e hs l C hC*up F) L) z

theorem value_unitNext (F : 𝔄) (L : ℕ) (z : ℝ[X]) :
    val (unitNext A P e hs l C hC F L z)=next A P e hs l C hC F L z := by
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
      0≤next A P e hs l C hC F L z ∧ next A P e hs l C hC F L z≤F ∧
      tr A P (next A P e hs l C hC F L z-(next A P e hs l C hC F L z)^2)≤
        4*(AsymptoticReconstructedCount.parameters A P).ε⁻¹/(J:ℝ) ∧
      (∀ E : 𝔄,F*E=E → (∀ i : Fin n,∀ x,B i x*rep A P E x=0) →
        next A P e hs l C hC F L z*E=E) ∧
      tr A P (next A P e hs l C hC F L z)-target≤
        (1-(1-Real.exp (-(L:ℝ)*(d^2/32)))*(1-(l.map primeFactor).prod)*
          (1-Real.log (K/(QuantitativeEulerEndpointBlockNormalization.factor C n*c)^2)/Real.log (K/(2*d^2))))*
          (tr A P F-target)+(4+2*(L:ℝ))*tr A P (F-F^2)+
          (AsymptoticReconstructedCount.parameters A P).ε⁻¹*(Real.log 2/Real.log (K/(2*d^2))) := by
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
  have hval := value_unitNext A P e hs l C hC F L z
  have hτ (a : 𝕌) : rootedTrace action_measurable t ht 1 hp measure (terminal_finite A P) a=tr A P (val a) := rfl
  change 0≤unitNext A P e hs l C hC F L z at hz0
  change unitNext A P e hs l C hC F L z≤up F at hzF
  change rootedTrace action_measurable t ht 1 hp measure (terminal_finite A P)
    (unitNext A P e hs l C hC F L z-(unitNext A P e hs l C hC F L z)^2)≤_ at hdef
  change rootedTrace action_measurable t ht 1 hp measure (terminal_finite A P)
    (unitNext A P e hs l C hC F L z)-target≤_ at hrec
  simp only [hτ,map_sub,pow_two,hm,hval,value_one,tr_one] at hdef
  have harea : (measure t).toReal=(AsymptoticReconstructedCount.parameters A P).ε⁻¹ := by
    rw [terminal_area,ENNReal.toReal_ofReal (inv_nonneg.mpr (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le)]
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
    change val (unitNext A P e hs l C hC F L z*up E)=E at hh'
    simpa only [hm,hval,value_lift] using hh'
  · simpa only [pow_two,map_sub] using hrec

#print axioms value_unitGram
#print axioms value_unitNext
#print axioms exists_next
end QuantitativeEulerEndpointBoundedTerminal
