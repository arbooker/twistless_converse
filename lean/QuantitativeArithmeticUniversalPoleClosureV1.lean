module
public import SmallLevelPoleGridTheoryV4
public import SmallLevelUniversalHigherPoleVectorV1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleClosure
open Complex QuantitativeArithmeticUniversalPoleVector
/-- A common analytic half-plane and three local rightmost-pole exclusions
imply global regularity away from one possible simple pole. -/
theorem pole_orders {ι : Type*} [Fintype ι] (G : ℂ → ι → ℂ) (k : ℂ)
    (hG : ∀ j s, MeromorphicNFAt (fun z => G z j) s)
    (B : ℝ) (hhalf : ∀ j z, B<z.re → AnalyticAt ℂ (fun w => G w j) z)
    (hstrict : ∀ s v, IsLeadingVector G s v →
      (∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (s+n)) → k.re<s.re → False)
    (hcentral : ∀ v, IsLeadingVector (fun z j => (z-k)*G z j) k v →
      (∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (k+n)) →
      (∃ j,meromorphicOrderAt (fun z => (z-k)*G z j) k<0) → False)
    (haway : ∀ s v, IsLeadingVector G s v →
      (∀ n : ℕ,0<n → s+n≠k → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (s+n)) →
      (∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) k) → s≠k →
      (∃ j,meromorphicOrderAt (fun z => G z j) s<0) → False) :
    (∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) k) ∧
      ∀ s : ℂ,s≠k → ∀ j,0≤meromorphicOrderAt (fun z => G z j) s := by
  have habove : ∀ s : ℂ,k.re<s.re → ∀ j,0≤meromorphicOrderAt (fun z => G z j) s := by
    intro s hs j
    by_contra! hj
    obtain ⟨n,hpole,hshift⟩ := SmallLevelPoleGrid.rightmost_pole
      (fun j z => G z j) ⟨j,hj⟩ B hhalf
    obtain ⟨v,hv⟩ := exists_leading_vector G (s+n) (fun j => (hG j _).meromorphicAt) hpole
    apply hstrict (s+n) v hv hshift
    simp only [Complex.add_re,Complex.natCast_re]
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith
  have hwshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (k+n) := by
    intro n hn
    apply habove
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    norm_num
    linarith
  have hweight : ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) k := by
    by_contra! hp
    have hrpole : ∃ j,meromorphicOrderAt (fun z => (z-k)*G z j) k<0 := by
      obtain ⟨j,hj⟩ := hp
      refine ⟨j,?_⟩
      have hloc : MeromorphicAt (fun z : ℂ => z-k) k :=
        (analyticAt_id.sub analyticAt_const).meromorphicAt
      change meromorphicOrderAt ((fun z : ℂ => z-k)*(fun z => G z j)) k<0
      rw [meromorphicOrderAt_mul hloc (hG j _).meromorphicAt,meromorphicOrderAt_id_sub_const]
      lift meromorphicOrderAt (fun z => G z j) k to ℤ using hj.ne_top with q hq
      have hq' : q< -1 := by
        change (q:WithTop ℤ)<((-1:ℤ):WithTop ℤ) at hj
        exact WithTop.coe_lt_coe.mp hj
      exact_mod_cast (show 1+q<0 by omega)
    obtain ⟨v,hv⟩ := exists_leading_vector (fun z j => (z-k)*G z j) k
      (fun j => (analyticAt_id.sub analyticAt_const).meromorphicAt.mul (hG j _).meromorphicAt) hrpole
    exact hcentral v hv hwshift hrpole
  refine ⟨hweight,?_⟩
  intro s hs j
  by_contra! hj
  obtain ⟨n,hsn,hpole,hshift⟩ := SmallLevelPoleGrid.rightmost_pole_away
    (fun j z => G z j) k hs ⟨j,hj⟩ B hhalf
  obtain ⟨v,hv⟩ := exists_leading_vector G (s+n) (fun j => (hG j _).meromorphicAt) hpole
  exact haway (s+n) v hv hshift hweight hsn hpole
#print axioms pole_orders
end QuantitativeArithmeticUniversalPoleClosure
