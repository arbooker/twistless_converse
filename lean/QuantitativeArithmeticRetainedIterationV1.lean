module

public import QuantitativeArithmeticRetainedPolynomialV1
public import QuantitativeEulerEndpointFiniteScheduleV1

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra Polynomial
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBlocks
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)

/-- Actual observation region, prime list and threshold of a normalized terminal block. -/
structure Block where
  region : Set UpperHalfPlane
  compact : IsCompact region
  primes : List (EligiblePrime N)
  cutoff : ℝ
  bound : ℕ → ℝ
  norm_bound : ∀ i x,‖QuantitativeArithmeticRetainedPacket.rows A P hR₀ e compact primes i x‖≤bound i

variable (n : ℕ) (b : ℕ → Block A P hR₀ e)
local notation "area" => P.ε⁻¹

def effortAt (j : ℕ) : ℝ := QuantitativeArithmeticRetainedPolynomial.effort
  (b j).bound ((b j).primes.length+1) n j (b j).cutoff

def sharpnessAt (j : ℕ) : ℕ := sharpness area (effortAt A P hR₀ e n b j)

def nextAt (j : ℕ) (F : Algebra A P) (z : ℝ[X]) : Algebra A P :=
  QuantitativeArithmeticRetainedPolynomial.next A P hR₀ e (b j).compact (b j).primes (b j).bound (b j).norm_bound F
    (power (effortAt A P hR₀ e n b j)) z

/-- Checked properties retained from one scheduled polynomial update. -/
structure Step (target : ℝ) (j : ℕ) (F : Algebra A P) (z : ℝ[X]) : Prop where
  degree : z.natDegree≤16*(sharpnessAt A P hR₀ e n b (j+1))^5+1
  mass : (∑ i∈z.support,|z.coeff i|)≤
    (((16*(sharpnessAt A P hR₀ e n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P hR₀ e n b (j+1))^5)
  scalar : QuantitativeEulerEndpointBernstein.ScalarSharpening z
  nonneg : 0≤nextAt A P hR₀ e n b j F z
  le : nextAt A P hR₀ e n b j F z≤F
  defect : tr A P (nextAt A P hR₀ e n b j F z-(nextAt A P hR₀ e n b j F z)^2)≤
    4*area/(sharpnessAt A P hR₀ e n b (j+1):ℝ)
  fixed : ∀ D : Algebra A P,F*D=D →
    (∀ i : Fin ((b j).primes.length+1),∀ x,
      QuantitativeArithmeticRetainedPacket.rows A P hR₀ e (b j).compact (b j).primes i x*rep A P D x=0) →
    nextAt A P hR₀ e n b j F z*D=D
  excess : max 0 (tr A P (nextAt A P hR₀ e n b j F z)-target)≤
    (((b j).primes.map primeFactor).prod+2*blockRelativeLoss n j)*max 0 (tr A P F-target)+
      (1+area*Real.log 2)*blockAdditiveLoss n j

/-- The incoming sharpening pays the current block, and the outgoing
sharpening is chosen from the NEXT block's actual effort. -/
theorem exists_step (j : ℕ) (hj : j≤n) (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1)
    (target : ℝ) (hc : 0<(b j).cutoff)
    (hu : QuantitativeEulerEndpointBlockNormalization.factor
      (b j).bound ((b j).primes.length+1)*(b j).cutoff≤1)
    (hchain : cornerMass (fun x => QuantitativeSpectralDeflationChain.chain (half A P F x)
      (fun i => QuantitativeArithmeticRetainedPacket.rows A P hR₀ e (b j).compact (b j).primes i x)
      (b j).cutoff ((b j).primes.length+1))-target≤
      ((b j).primes.map primeFactor).prod*(cornerMass (half A P F)-target))
    (hdef : tr A P (F-F^2)≤4*area/(sharpnessAt A P hR₀ e n b j:ℝ)) :
    ∃ z,Step A P hR₀ e n b target j F z := by
  obtain ⟨z,hdeg,hmass,hscalar,hz0,hzF,hzdef,hfixed,hrec⟩ :=
    QuantitativeArithmeticRetainedPolynomial.exists_scheduled_next A P hR₀ e (b j).compact (b j).primes (b j).bound (b j).norm_bound
      n j hj F hF0 hF1 target (b j).cutoff hc hu hchain hdef
      (sharpness_pos area (effortAt A P hR₀ e n b (j+1)))
  exact ⟨z,hdeg,hmass,hscalar,hz0,hzF,hzdef,hfixed,hrec⟩

#print axioms exists_step
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra Polynomial
open QuantitativeEulerEndpointExponentialParameters
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup
open QuantitativeArithmetic QuantitativeEulerDensityGenerators

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)
variable (n : ℕ) (b : ℕ → Block A P hR₀ e)
local notation "area" => P.ε⁻¹

structure Valid (j : ℕ) (F : Algebra A P) : Prop where
  nonneg : 0≤F
  le_one : F≤1
  defect : tr A P (F-F^2)≤4*area/(sharpnessAt A P hR₀ e n b j:ℝ)
  support : ∀ k,j≤k → k<n → ∀ r∈(b k).primes,∀ x,
    Supported (integralGroup r.val) (rep A P F x)

/-- Finite construction from the identity in the entire terminal algebra.
One-step existence is an explicit input here; prepared geometry supplies it
in the concrete application. All inter-block induction invariants are proved. -/
theorem exists_iteration
    (hprimes : ∀ j,j<n → ∀ r∈(b j).primes,
      ¬r.val∣Q ∧ (∀p∈R₀,¬r.val∣p) ∧ ∀ a : UnitResidue N,¬r.val∣(primeLift N a).q)
    (hdisjoint : ∀ i j,i<j → j<n → ∀ r∈(b j).primes,r∉(b i).primes)
    (target : ℝ)
    (hstep : ∀ j,j<n → ∀ F : Algebra A P,0≤F → F≤1 →
      (∀ r∈(b j).primes,∀ x,Supported (integralGroup r.val) (rep A P F x)) →
      (tr A P (F-F^2)≤4*area/(sharpnessAt A P hR₀ e n b j:ℝ)) →
      ∃ z,Step A P hR₀ e n b target j F z) :
    ∃ (F : ℕ → Algebra A P) (z : ℕ → ℝ[X]),F 0=1 ∧
      (∀ j,j≤n → Valid A P hR₀ e n b j (F j)) ∧
      (∀ j,j<n → Step A P hR₀ e n b target j (F j) (z j) ∧
        F (j+1)=nextAt A P hR₀ e n b j (F j) (z j)) ∧
      (∀ D : Algebra A P,
        (∀ j,j<n → ∀ i : Fin ((b j).primes.length+1),∀ x,
          QuantitativeArithmeticRetainedPacket.rows A P hR₀ e (b j).compact (b j).primes i x*rep A P D x=0) →
        ∀ j,j≤n → F j*D=D) := by
  classical
  have hex (j : ℕ) (hj : j<n) (F : Algebra A P) (hv : Valid A P hR₀ e n b j F) :
      ∃ z,Step A P hR₀ e n b target j F z :=
    hstep j hj F hv.nonneg hv.le_one (hv.support j le_rfl hj) hv.defect
  let pick (j : ℕ) (F : Algebra A P) : ℝ[X] :=
    if h : j<n ∧ Valid A P hR₀ e n b j F then Classical.choose (hex j h.1 F h.2) else 0
  have hpick (j : ℕ) (hj : j<n) (F : Algebra A P) (hv : Valid A P hR₀ e n b j F) :
      Step A P hR₀ e n b target j F (pick j F) := by
    dsimp only [pick]
    rw [dite_eq_left ⟨hj,hv⟩]
    exact Classical.choose_spec (hex j hj F hv)
  let F : ℕ → Algebra A P := fun j =>
    Nat.rec 1 (fun k F => nextAt A P hR₀ e n b k F (pick k F)) j
  have hzero : F 0=1 := rfl
  have hsucc (j : ℕ) : F (j+1)=nextAt A P hR₀ e n b j (F j) (pick j (F j)) := rfl
  have hv : ∀ j,j≤n → Valid A P hR₀ e n b j (F j) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨?_,le_rfl,?_,?_⟩
      · change (0:Algebra A P)≤1
        simpa only [star_one,mul_one] using star_mul_self_nonneg (1:Algebra A P)
      · rw [hzero,one_pow,sub_self,map_zero]
        have ha : 0≤area := inv_nonneg.mpr P.epsilon_pos.le
        positivity
      · intro k _ _ r _ x
        rw [hzero,rep_one,QuantitativeSpectralExceptionalRows.region_projection]
        exact AsymptoticSubgroupSupport.supported_corner _ _ _
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
        exact QuantitativeArithmeticRetainedPolynomial.next_supported A P hR₀ e (b j).compact (b j).primes (b j).bound (b j).norm_bound
          r (hprimes k hkn r hr).1 (hprimes k hkn r hr).2.1 (hprimes k hkn r hr).2.2
          (hdisjoint j k (by omega) hkn r hr) (F j)
          (hvj.support k (by omega) hkn r hr) (power (effortAt A P hR₀ e n b j)) (pick j (F j)) x
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
end QuantitativeArithmeticRetainedIteration

namespace QuantitativeArithmeticRetainedIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeArithmeticRetainedTerminalAlgebra Polynomial Finset
open QuantitativeEulerEndpointBlocks

variable {N Q : ℕ} {R₀ : Finset ℕ} [NeZero N] {hQ : 0<Q}
  (A : Certificate N R₀ Q hQ) (P : Parameters A) (hR₀ : ∀p∈R₀,p.Prime) (e : Sector N)
variable (n : ℕ) (b : ℕ → Block A P hR₀ e) (target : ℝ)
  (F : ℕ → Algebra A P) (z : ℕ → ℝ[X])
local notation "area" => P.ε⁻¹

/-- The checked finite-horizon scalar bound applied to actual terminal
polynomial updates, with all sharpening and determinant errors already paid. -/
theorem finite_excess_bound
    (hsteps : ∀ j,j<n → Step A P hR₀ e n b target j (F j) (z j) ∧
      F (j+1)=nextAt A P hR₀ e n b j (F j) (z j))
    (bad : ℕ → ℝ) {C : ℝ} (hbad : ∀ j,0≤bad j)
    (hbudget : (∑ j∈range n,bad j)≤C)
    (hprime : ∀ j,j<n → ((b j).primes.map primeFactor).prod≤Real.exp (bad j)/4) :
    max 0 (tr A P (F n)-target)≤
      Real.exp (C+8)*(max 0 (tr A P (F 0)-target)+4*(1+area*Real.log 2))/(4:ℝ)^n := by
  have ha : 0≤area := inv_nonneg.mpr P.epsilon_pos.le
  have hB : 0≤1+area*Real.log 2 := by
    have hh : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hstep : ∀ j,j<n → max 0 (tr A P (F (j+1))-target)≤
      (Real.exp (bad j)/4+2*blockRelativeLoss n j)*max 0 (tr A P (F j)-target)+
        (1+area*Real.log 2)*blockAdditiveLoss n j := by
    intro j hj
    obtain ⟨hs,he⟩ := hsteps j hj
    have hrec := hs.excess
    rw [← he] at hrec
    exact hrec.trans (add_le_add
      (mul_le_mul_of_nonneg_right (add_le_add (hprime j hj) le_rfl) (le_max_left _ _)) le_rfl)
  simpa only [show (4:ℝ)*2=8 by norm_num] using
    finite_schedule_endpoint n (fun j => max 0 (tr A P (F j)-target)) bad
      (by norm_num : (0:ℝ)≤2) hB (fun _ _ => le_max_left _ _) hbad hbudget hstep

theorem finite_trace_bound (hzero : F 0=1) (htarget : 0≤target)
    (hsteps : ∀ j,j<n → Step A P hR₀ e n b target j (F j) (z j) ∧
      F (j+1)=nextAt A P hR₀ e n b j (F j) (z j))
    (bad : ℕ → ℝ) {C : ℝ} (hbad : ∀ j,0≤bad j)
    (hbudget : (∑ j∈range n,bad j)≤C)
    (hprime : ∀ j,j<n → ((b j).primes.map primeFactor).prod≤Real.exp (bad j)/4) :
    tr A P (F n)≤target+Real.exp (C+8)*(area+4*(1+area*Real.log 2))/(4:ℝ)^n := by
  have ha : 0≤area := inv_nonneg.mpr P.epsilon_pos.le
  have hstart : max 0 (tr A P (F 0)-target)≤area := by
    rw [hzero,tr_one]
    exact max_le ha (sub_le_self _ htarget)
  have hh := (finite_excess_bound A P hR₀ e n b target F z hsteps bad hbad hbudget hprime).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hstart le_rfl) (Real.exp_pos _).le) (by positivity))
  have hm := le_max_right 0 (tr A P (F n)-target)
  linarith

#print axioms finite_excess_bound
#print axioms finite_trace_bound
end QuantitativeArithmeticRetainedIteration
