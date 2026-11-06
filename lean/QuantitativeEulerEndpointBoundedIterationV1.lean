module

public import QuantitativeEulerEndpointBoundedIterationDataV1

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial
open QuantitativeEulerEndpointExponentialParameters
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable (n : ℕ) (b : ℕ → Block A P e)
local notation "area" => (AsymptoticReconstructedCount.parameters A P).ε⁻¹

structure Valid (j : ℕ) (F : Algebra A P) : Prop where
  nonneg : 0≤F
  le_one : F≤1
  defect : tr A P (F-F^2)≤4*area/(sharpnessAt A P e n b j:ℝ)
  support : ∀ k,j≤k → k<n → ∀ r∈(b k).primes,∀ x,
    Supported (integralGroup r.val) (rep A P F x)

/-- Finite construction from the identity in the entire terminal algebra.
One-step existence is an explicit input here; prepared geometry supplies it
in the concrete application. All inter-block induction invariants are proved. -/
theorem exists_iteration
    (hprimes : ∀ j,j<n → ∀ r∈(b j).primes,
      ¬r.val∣Q ∧ ∀ a : UnitResidue N,¬r.val∣(primeLift N a).q)
    (hdisjoint : ∀ i j,i<j → j<n → ∀ r∈(b j).primes,r∉(b i).primes)
    (target : ℝ)
    (hstep : ∀ j,j<n → ∀ F : Algebra A P,0≤F → F≤1 →
      (∀ r∈(b j).primes,∀ x,Supported (integralGroup r.val) (rep A P F x)) →
      (tr A P (F-F^2)≤4*area/(sharpnessAt A P e n b j:ℝ)) →
      ∃ z,Step A P e n b target j F z) :
    ∃ (F : ℕ → Algebra A P) (z : ℕ → ℝ[X]),F 0=1 ∧
      (∀ j,j≤n → Valid A P e n b j (F j)) ∧
      (∀ j,j<n → Step A P e n b target j (F j) (z j) ∧
        F (j+1)=nextAt A P e n b j (F j) (z j)) ∧
      (∀ D : Algebra A P,
        (∀ j,j<n → ∀ i : Fin ((b j).primes.length+1),∀ x,
          normalizedCombinedRows A P e (b j).compact (b j).primes i x*rep A P D x=0) →
        ∀ j,j≤n → F j*D=D) := by
  classical
  have hex (j : ℕ) (hj : j<n) (F : Algebra A P) (hv : Valid A P e n b j F) :
      ∃ z,Step A P e n b target j F z :=
    hstep j hj F hv.nonneg hv.le_one (hv.support j le_rfl hj) hv.defect
  let pick (j : ℕ) (F : Algebra A P) : ℝ[X] :=
    if h : j<n ∧ Valid A P e n b j F then Classical.choose (hex j h.1 F h.2) else 0
  have hpick (j : ℕ) (hj : j<n) (F : Algebra A P) (hv : Valid A P e n b j F) :
      Step A P e n b target j F (pick j F) := by
    dsimp only [pick]
    rw [dite_eq_left ⟨hj,hv⟩]
    exact Classical.choose_spec (hex j hj F hv)
  let F : ℕ → Algebra A P := fun j =>
    Nat.rec 1 (fun k F => nextAt A P e n b k F (pick k F)) j
  have hzero : F 0=1 := rfl
  have hsucc (j : ℕ) : F (j+1)=nextAt A P e n b j (F j) (pick j (F j)) := rfl
  have hv : ∀ j,j≤n → Valid A P e n b j (F j) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨?_,le_rfl,?_,?_⟩
      · change (0:Algebra A P)≤1
        simpa only [star_one,mul_one] using star_mul_self_nonneg (1:Algebra A P)
      · rw [hzero,one_pow,sub_self,map_zero]
        have ha : 0≤area := inv_nonneg.mpr (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le
        positivity
      · intro k _ _ r _ x
        rw [hzero,rep_one]
        exact reconstructed_terminal_supported A P r.val x
    | succ j ih =>
      intro hj
      have hjn : j<n := by omega
      have hvj := ih (by omega)
      have hs := hpick j hjn (F j) hvj
      refine ⟨?_,?_,?_,?_⟩
      · rw [hsucc]
        exact hs.nonneg
      · rw [hsucc]
        exact hs.le.trans hvj.le_one
      · rw [hsucc]
        exact hs.defect
      · intro k hjk hkn r hr x
        rw [hsucc]
        exact QuantitativeEulerEndpointBoundedTerminal.next_supported A P e (b j).compact (b j).primes (b j).bound (b j).norm_bound
          r (hprimes k hkn r hr).1 (hprimes k hkn r hr).2
          (hdisjoint j k (by omega) hkn r hr) (F j)
          (hvj.support k (by omega) hkn r hr) (power (effortAt A P e n b j)) (pick j (F j)) x
  refine ⟨F,fun j => pick j (F j),hzero,hv,?_,?_⟩
  · intro j hj
    exact ⟨hpick j hj (F j) (hv j hj.le),hsucc j⟩
  · intro D hrows j
    induction j with
    | zero => intro _; rw [hzero,one_mul]
    | succ j ih =>
      intro hj
      have hjn : j<n := by omega
      have hs := hpick j hjn (F j) (hv j (by omega))
      rw [hsucc]
      exact hs.fixed D (ih (by omega)) (hrows j hjn)

#print axioms exists_iteration
end QuantitativeEulerEndpointBoundedIteration
