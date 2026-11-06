module

public import QuantitativeEulerEndpointPacketSoftUpdateV1
public import QuantitativeEulerEndpointBandCornerV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPacketIteration
open UpperHalfPlane MeasureTheory AsymptoticRegularTrace Polynomial
open AsymptoticRegularCompactBranch (Space)
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointRegularBase
open QuantitativeEulerEndpointPreparedHalf QuantitativeEulerEndpointSubcorner
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open scoped ENNReal

/-- A block carries its own observation region and regularization parameters. -/
structure Block (N : ℕ) where
  observation : Set ℍ
  compact : IsCompact observation
  t : ℕ
  primes : List (EligiblePrime N)
  c : ℝ
  d : ℝ
  K : ℝ
  steps : ℕ
  J : ℕ

variable (N : ℕ) (hN : 0<N) (w : ℂ) {ε : ℝ} (hε : 0<ε) (H : ℝ)
local notation "hs₀" => QuantitativeEulerEndpointBandCorner.ambient_compact hε H
local notation "s₀" => region (QuantitativeEulerEndpointBandCorner.ambient (ε:=ε) H)
local notation "p" => QuantitativeEulerEndpointBandCorner.projection hε H
local notation "hp" => QuantitativeEulerEndpointBandCorner.projection_isStarProjection hε H
local notation "𝔄" => Subcorner action_measurable s₀ (region_measurable hs₀) p hp
local notation "ρ" => representation action_measurable s₀ (region_measurable hs₀) p hp
local notation "τ" => rootedTrace action_measurable s₀ (region_measurable hs₀) p hp measure (region_finite hs₀)

def rows (b : Block N) := packetRows N hN w b.compact hε b.t b.primes

def factor (b : Block N) : ℝ := QuantitativeEulerEndpointBlockNormalization.factor
  (packetSequenceBound N hN w b.compact hε b.t b.primes) b.primes.length

def theta (b : Block N) : ℝ :=
  Real.log (b.K/(factor N hN w hε b*b.c)^2)/Real.log (b.K/(2*b.d^2))

def Scalars (b : Block N) : Prop :=
  0<b.c ∧ 0<b.d ∧ 0<b.K ∧ 2*b.d^2<b.K ∧ 1+b.d^2≤b.K ∧
    0≤theta N hN w hε b ∧ theta N hN w hε b≤1 ∧ 0<b.J

def next (b : Block N) (A : 𝔄) (z : ℝ[X]) : 𝔄 :=
  QuantitativeEulerEndpointPacketSoftUpdate.next hs₀ p hp N hN w b.compact hε b.t b.primes A b.steps z

def Step (b : Block N) (target : ℝ) (A : 𝔄) (z : ℝ[X]) : Prop :=
  z.natDegree≤16*b.J^5+1 ∧
  (∑ i∈z.support, |z.coeff i|)≤(((16*b.J^5:ℕ):ℝ)+2)*3^(16*b.J^5) ∧
  let Z := next N hN w hε H b A z
  0≤Z ∧ Z≤A ∧ τ (Z-Z^2)≤4*τ 1/(b.J:ℝ) ∧
  (∀ E : 𝔄, A*E=E → (∀ i : Fin b.primes.length, ∀ x, rows N hN w hε b i x*ρ E x=0) → Z*E=E) ∧
  τ Z-target≤(1-(1-Real.exp (-(b.steps:ℝ)*(b.d^2/32)))*(1-(b.primes.map primeFactor).prod)*
    (1-theta N hN w hε b))*(τ A-target)+
    (4+2*(b.steps:ℝ))*τ (A-A^2)+(measure s₀).toReal*(Real.log 2/Real.log (b.K/(2*b.d^2)))

theorem exists_step (b : Block N) (hb : Scalars N hN w hε b)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) (target : ℝ)
    (hchain : (trace measure (QuantitativeSpectralRegularPacket.projectionFamily
      (fun x : Base => half hs₀ p hp A x) (rows N hN w hε b) b.c b.primes.length)).toReal-target≤
      (b.primes.map primeFactor).prod*(cornerMass (half hs₀ p hp A)-target)) :
    ∃ z, Step N hN w hε H b target A z := by
  rcases hb with ⟨hc,hd,hK,hcut,hnorm,hθ0,hθ1,hJ⟩
  exact QuantitativeEulerEndpointPacketSoftUpdate.exists_packet_update
    hs₀ p hp (QuantitativeEulerEndpointBandCorner.space (ε:=ε) H)
    (QuantitativeEulerEndpointBandCorner.space_representation hε H)
    N hN w b.compact hε b.t b.primes A hA0 hA1 b.c hc hd hK hcut hnorm target hθ0 hθ1 hchain b.steps hJ

theorem next_supported (b : Block N) (A : 𝔄) (r : EligiblePrime N) (hr : r∉b.primes)
    (hA : ∀ x, Supported (integralGroup r.val) (ρ A x)) (z : ℝ[X]) :
    ∀ x, Supported (integralGroup r.val) (ρ (next N hN w hε H b A z) x) :=
  QuantitativeEulerEndpointPacketSoftUpdate.next_supported hs₀ p hp N hN w b.compact hε b.t b.primes A r hr
    (QuantitativeEulerEndpointBandCorner.projection_supported hε H (integralGroup r.val)) hA b.steps z

/-- Finite iteration of the actual original-prime polynomial updates. The
only contraction input is the hard packet bound, supplied by the prepared
variable-region theorem. All later-prime support, monotonicity, and exact
solution invariants are proved throughout the constructed sequence. -/
theorem exists_iteration (n : ℕ) (b : ℕ → Block N)
    (hb : ∀ j, j<n → Scalars N hN w hε (b j))
    (hdisjoint : ∀ i j, i<j → j<n → ∀ r∈(b j).primes, r∉(b i).primes)
    (F₀ : 𝔄) (hF0 : 0≤F₀) (hF1 : F₀≤1)
    (hsupport : ∀ j, j<n → ∀ r∈(b j).primes, ∀ x, Supported (integralGroup r.val) (ρ F₀ x))
    (target : ℝ)
    (hchain : ∀ j, j<n → ∀ A : 𝔄, 0≤A → A≤F₀ →
      (∀ r∈(b j).primes, ∀ x, Supported (integralGroup r.val) (ρ A x)) →
      (trace measure (QuantitativeSpectralRegularPacket.projectionFamily
        (fun x : Base => half hs₀ p hp A x) (rows N hN w hε (b j)) (b j).c (b j).primes.length)).toReal-target≤
        ((b j).primes.map primeFactor).prod*(cornerMass (half hs₀ p hp A)-target)) :
    ∃ (F : ℕ → 𝔄) (z : ℕ → ℝ[X]), F 0=F₀ ∧
      (∀ j, j≤n → 0≤F j ∧ F j≤F₀ ∧
        ∀ k, j≤k → k<n → ∀ r∈(b k).primes, ∀ x, Supported (integralGroup r.val) (ρ (F j) x)) ∧
      (∀ j, j<n → Step N hN w hε H (b j) target (F j) (z j) ∧
        F (j+1)=next N hN w hε H (b j) (F j) (z j)) ∧
      (∀ E : 𝔄, F₀*E=E →
        (∀ j, j<n → ∀ i : Fin (b j).primes.length, ∀ x, rows N hN w hε (b j) i x*ρ E x=0) →
        ∀ j, j≤n → F j*E=E) := by
  classical
  let Valid (j : ℕ) (A : 𝔄) : Prop := 0≤A ∧ A≤F₀ ∧
    ∀ k, j≤k → k<n → ∀ r∈(b k).primes, ∀ x, Supported (integralGroup r.val) (ρ A x)
  have hex (j : ℕ) (hj : j<n) (A : 𝔄) (hA : Valid j A) :
      ∃ z, Step N hN w hε H (b j) target A z :=
    exists_step N hN w hε H (b j) (hb j hj) A hA.1 (hA.2.1.trans hF1) target
      (hchain j hj A hA.1 hA.2.1 (hA.2.2 j le_rfl hj))
  let pick (j : ℕ) (A : 𝔄) : ℝ[X] :=
    if h : j<n ∧ Valid j A then Classical.choose (hex j h.1 A h.2) else 0
  have hpick (j : ℕ) (hj : j<n) (A : 𝔄) (hA : Valid j A) :
      Step N hN w hε H (b j) target A (pick j A) := by
    dsimp only [pick]
    rw [dite_eq_left ⟨hj,hA⟩]
    exact Classical.choose_spec (hex j hj A hA)
  let F : ℕ → 𝔄 := fun j => Nat.rec F₀ (fun k A => next N hN w hε H (b k) A (pick k A)) j
  have hzero : F 0=F₀ := rfl
  have hsucc (j : ℕ) : F (j+1)=next N hN w hε H (b j) (F j) (pick j (F j)) := rfl
  have hv : ∀ j, j≤n → Valid j (F j) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨hF0,le_rfl,fun k _ hk => hsupport k hk⟩
    | succ j ih =>
      intro hj
      have hjn : j<n := by omega
      have hvj := ih (by omega)
      have hstep := hpick j hjn (F j) hvj
      refine ⟨?_,?_,?_⟩
      · rw [hsucc]
        exact hstep.2.2.1
      · rw [hsucc]
        exact hstep.2.2.2.1.trans hvj.2.1
      · intro k hjk hkn r hr x
        rw [hsucc]
        exact next_supported N hN w hε H (b j) (F j) r
          (hdisjoint j k (by omega) hkn r hr)
          (hvj.2.2 k (by omega) hkn r hr) (pick j (F j)) x
  refine ⟨F,fun j => pick j (F j),hzero,hv,?_,?_⟩
  · intro j hj
    exact ⟨hpick j hj (F j) (hv j (by omega)),hsucc j⟩
  · intro E hE hrows j
    induction j with
    | zero => intro _; exact hE
    | succ j ih =>
      intro hj
      have hjn : j<n := by omega
      have hstep := hpick j hjn (F j) (hv j (by omega))
      rw [hsucc]
      exact hstep.2.2.2.2.2.1 E (ih (by omega)) (hrows j hjn)

#print axioms exists_step
#print axioms next_supported
#print axioms exists_iteration
end QuantitativeEulerEndpointPacketIteration
