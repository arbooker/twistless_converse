module

public import QuantitativeEulerEndpointLocalSpanV1
public import QuantitativeEulerEndpointWideGamma0WordsV1
public import QuantitativeEulerEndpointWideRingV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open AsymptoticRegularObservationRows AsymptoticRegularBranchFamily AsymptoticOrbitDecode
open AsymptoticFreshCompactDefects AsymptoticObservationStack
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

/-- This is the original ramified observation, with its original normalization. -/
theorem compactAction_ramified (p : ℕ) (hp : 0<p) (δ : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (ramifiedRow p hp δ)=bad p hp δ hs hε t x := by
  unfold bad AsymptoticRegularBranchFamily.family
  rw [Fintype.sum_sum_type]
  simp only [ramifiedBranches,Sum.elim_inl,Sum.elim_inr,one_smul,Fintype.sum_unique]
  change compactAction hs hε t x (ramifiedRow p hp δ)=
    (∑ a : Fin p, compact (ramified p hp a.val) hs hε t x)+
      (-δ) • compact identityBranch hs hε t x
  have hid := compactAction_branch hs hε t x identityBranch
  rw [identityBranch_label,map_one] at hid
  have hram (a : Fin p) : compactAction hs hε t x (symbol (ramifiedLabel p hp a))=
      compact (ramified p hp a.val) hs hε t x :=
    compactAction_branch hs hε t x (ramified p hp a.val)
  rw [ramifiedRow,map_sub,map_sum,map_smul]
  simp only [hram]
  rw [hid,sub_eq_add_neg]
  congr 1
  exact (_root_.neg_smul δ (compact identityBranch hs hε t x)).symm


/-- Four literal original energies on one common observation region. -/
def localOriginalEnergy {N : ℕ} [NeZero N] (p : ℕ) (hp : 0<p) (w δ : ℂ)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) : ℝ :=
  ‖twist N 1 (NeZero.pos N) Nat.zero_lt_one w hs hε t x v‖^2+
    ‖fixedPrimeStack N w hs hε t x v‖^2+
    ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN w
      hs hε t i x) v‖^2+‖bad p hp δ hs hε t x v‖^2

theorem localOriginalEnergy_nonneg {N : ℕ} [NeZero N] (p : ℕ) (hp : 0<p) (w δ : ℂ)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    0≤localOriginalEnergy p hp w δ q hqN hs hε t x v := by
  unfold localOriginalEnergy
  positivity

def WideLocalControl {N : ℕ} [NeZero N] {excluded : Finset ℕ} {threshold : ℕ}
    (P : Prepared N excluded threshold) (p : ℕ) (hp : 0<p) (w δ : ℂ)
    (A : Ring) (B K : ℝ) : Prop :=
  ∀ (C : ℝ), B≤C → ∀ (q : ℕ) [Fact q.Prime], P.Good q →
    ∃ hqN : ¬q∣N, ∀ {s : Set ℍ} (hs : IsCompact s)
      {ε R Y H : ℝ} (hε : 0<ε) (hY : 0<Y)
      (_hre : ∀ z∈s, |z.re|≤R) (_hlo : ∀ z∈s, Y≤z.im) (_him : ∀ z∈s, z.im≤H)
      (t : ℕ) (x : ℍ) (v : Space),
    let L := (2*generatorTransportConstant P*C)*(q : ℝ)^4
    ‖compactAction hs hε t x A v‖^2≤K*((wideDistortion L R H)^t)^2*
      localOriginalEnergy p hp w δ q hqN (wideFreshRegion_compact L R H hY) hε t x v

#print axioms compactAction_ramified
#print axioms localOriginalEnergy_nonneg
end QuantitativeEulerEndpointPrepared
