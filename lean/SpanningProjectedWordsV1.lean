module

public import SpanningPeriodicWordsV1
public import FiniteEndomorphismPowersV1
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

namespace SpanningProjectedWords

/-- The positive moduli in the two-generator tower. -/
def Tower (q₁ q₂ n : ℕ) : Prop := ∃ a b : ℕ, n=q₁^a*q₂^b

theorem tower_mul {q₁ q₂ n m : ℕ} (hn : Tower q₁ q₂ n) (hm : Tower q₁ q₂ m) :
    Tower q₁ q₂ (n*m) := by
  obtain ⟨a,b,rfl⟩ := hn
  obtain ⟨c,d,rfl⟩ := hm
  exact ⟨a+c,b+d,by simp [pow_add]; ring⟩

theorem tower_large {q₁ q₂ : ℕ} (h₁ : 2≤q₁) (i : ℕ) :
    ∃ n, Tower q₁ q₂ n ∧ i<n := by
  exact ⟨q₁^i, ⟨i,0,by simp⟩, Nat.lt_pow_self (by omega)⟩

theorem tower_pos {q₁ q₂ n : ℕ} (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hn : Tower q₁ q₂ n) : 0 < n := by
  obtain ⟨a,b,rfl⟩ := hn
  positivity

theorem tower_pow {q₁ q₂ n : ℕ} (hn : Tower q₁ q₂ n) (a : ℕ) :
    Tower q₁ q₂ (n^a) := by
  obtain ⟨b,c,rfl⟩ := hn
  exact ⟨b*a,c*a,by rw [mul_pow, ← pow_mul, ← pow_mul]⟩

theorem tower_powers {q₁ q₂ s t n : ℕ} (hn : Tower (q₁^s) (q₂^t) n) :
    Tower q₁ q₂ n := by
  obtain ⟨a,b,rfl⟩ := hn
  exact ⟨s*a,t*b,by rw [pow_mul,pow_mul]⟩

/-- A right digit action, expressed on the finite alphabet of covectors.
The composition law is the restriction identity for stationary trace lifts. -/
structure DigitAction (A : Type) (q₁ q₂ : ℕ) where
  digit : ℕ → ℕ → A → A
  compose : ∀ m n, Tower q₁ q₂ m → Tower q₁ q₂ n →
    ∀ j i, j<m → i<n → ∀ α,
      digit (m*n) (n*j+i) α = digit n i (digit m j α)

variable {A : Type} {q₁ q₂ : ℕ}

def DigitAction.rebase (F : DigitAction A q₁ q₂) (s t : ℕ) :
    DigitAction A (q₁^s) (q₂^t) where
  digit := F.digit
  compose m n hm hn := F.compose m n (tower_powers hm) (tower_powers hn)

/-- The covectors fixed by every leading-zero map. After taking
idempotent powers, this is the image of the projection Π in the paper. -/
def Stable (F : DigitAction A q₁ q₂) :=
  {α : A // ∀ n, Tower q₁ q₂ n → F.digit n 0 α=α}

theorem zero_mul (F : DigitAction A q₁ q₂) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {m n : ℕ} (hm : Tower q₁ q₂ m) (hn : Tower q₁ q₂ n) (α : A) :
    F.digit (m*n) 0 α = F.digit n 0 (F.digit m 0 α) := by
  simpa only [mul_zero, zero_add] using F.compose m n hm hn 0 0
    (tower_pos h₁ h₂ hm) (tower_pos h₁ h₂ hn) α

theorem zero_commute (F : DigitAction A q₁ q₂) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {m n : ℕ} (hm : Tower q₁ q₂ m) (hn : Tower q₁ q₂ n) (α : A) :
    F.digit m 0 (F.digit n 0 α) = F.digit n 0 (F.digit m 0 α) := by
  rw [← zero_mul F h₁ h₂ hn hm, Nat.mul_comm n m, zero_mul F h₁ h₂ hm hn]

theorem zero_pow (F : DigitAction A q₁ q₂) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {q : ℕ} (hq : Tower q₁ q₂ q) {n : ℕ} (hn : 0 < n) :
    F.digit (q^n) 0 = (F.digit q 0)^[n] := by
  have hp : ∀ a α, F.digit (q^(a+1)) 0 α = (F.digit q 0)^[a+1] α := by
    intro a
    induction a with
    | zero => intro α; simp
    | succ a ih =>
      intro α
      rw [pow_succ, zero_mul F h₁ h₂ (tower_pow hq (a+1)) hq, ih]
      simp only [Function.iterate_succ_apply']
  cases n with
  | zero => omega
  | succ a => exact funext (hp a)

/-- Idempotent bases exist by the elementary finite-map power lemma.
This imports no common-factor or concentration theorem. -/
theorem idempotent_bases [Fintype A] (F : DigitAction A q₁ q₂)
    (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    ∃ s t : ℕ, 0 < s ∧ 0 < t ∧
      (∀ α, F.digit (q₁^s) 0 (F.digit (q₁^s) 0 α) = F.digit (q₁^s) 0 α) ∧
      (∀ α, F.digit (q₂^t) 0 (F.digit (q₂^t) 0 α) = F.digit (q₂^t) 0 α) := by
  obtain ⟨s,hs,hids⟩ := FiniteEndomorphismPowers.exists_idempotent_iterate (F.digit q₁ 0)
  obtain ⟨t,ht,hidt⟩ := FiniteEndomorphismPowers.exists_idempotent_iterate (F.digit q₂ 0)
  refine ⟨s,t,hs,ht,?_,?_⟩
  · rwa [zero_pow F h₁ h₂ (show Tower q₁ q₂ q₁ from ⟨1,0,by simp⟩) hs]
  · rwa [zero_pow F h₁ h₂ (show Tower q₁ q₂ q₂ from ⟨0,1,by simp⟩) ht]

theorem fixed_on_tower (F : DigitAction A q₁ q₂) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (α : A) (hunit : F.digit 1 0 α = α)
    (hfirst : F.digit q₁ 0 α = α) (hsecond : F.digit q₂ 0 α = α) :
    ∀ n, Tower q₁ q₂ n → F.digit n 0 α = α := by
  have hp : ∀ q, Tower q₁ q₂ q → F.digit q 0 α = α →
      ∀ a, F.digit (q^a) 0 α = α := by
    intro q hq hqα a
    induction a with
    | zero => simpa using hunit
    | succ a ih => rw [pow_succ, zero_mul F h₁ h₂ (tower_pow hq a) hq, ih, hqα]
  intro n hn
  obtain ⟨a,b,rfl⟩ := hn
  have ht₁ : Tower q₁ q₂ q₁ := ⟨1,0,by simp⟩
  have ht₂ : Tower q₁ q₂ q₂ := ⟨0,1,by simp⟩
  rw [zero_mul F h₁ h₂ (tower_pow ht₁ a) (tower_pow ht₂ b),
    hp q₁ ht₁ hfirst a, hp q₂ ht₂ hsecond b]

/-- Commuting idempotent leading-zero maps give the common projection Π.
Every covector in its image is stable under all tower leading-zero maps. -/
def project (F : DigitAction A q₁ q₂) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hid₁ : ∀ α, F.digit q₁ 0 (F.digit q₁ 0 α) = F.digit q₁ 0 α)
    (hid₂ : ∀ α, F.digit q₂ 0 (F.digit q₂ 0 α) = F.digit q₂ 0 α)
    (α : A) : Stable F := by
  let β := F.digit (q₁*q₂) 0 α
  have ht₁ : Tower q₁ q₂ q₁ := ⟨1,0,by simp⟩
  have ht₂ : Tower q₁ q₂ q₂ := ⟨0,1,by simp⟩
  have hβ : β = F.digit q₂ 0 (F.digit q₁ 0 α) := zero_mul F h₁ h₂ ht₁ ht₂ α
  refine ⟨β, fixed_on_tower F h₁ h₂ β ?_ ?_ ?_⟩
  · have he := zero_mul F h₁ h₂ (tower_mul ht₁ ht₂) (show Tower q₁ q₂ 1 from ⟨0,0,by simp⟩) α
    simpa only [mul_one] using he.symm
  · rw [hβ, zero_commute F h₁ h₂ ht₁ ht₂, hid₁]
  · rw [hβ, hid₂]

theorem value_independent (F : DigitAction A q₁ q₂) (α : Stable F)
    {n m i : ℕ} (hn : Tower q₁ q₂ n) (hm : Tower q₁ q₂ m)
    (hin : i<n) (him : i<m) : F.digit n i α.val=F.digit m i α.val := by
  have h₁ := F.compose m n hm hn 0 i (by omega) hin α.val
  have h₂ := F.compose n m hn hm 0 i (by omega) him α.val
  simp only [mul_zero, zero_add, α.property m hm, α.property n hn] at h₁ h₂
  rw [Nat.mul_comm n m] at h₂
  exact h₁.symm.trans h₂

noncomputable def word (F : DigitAction A q₁ q₂) (h₁ : 2≤q₁)
    (α : Stable F) (i : ℕ) : A :=
  F.digit (Classical.choose (tower_large (q₂:=q₂) h₁ i)) i α.val

theorem word_eq (F : DigitAction A q₁ q₂) (h₁ : 2≤q₁) (α : Stable F)
    {n i : ℕ} (hn : Tower q₁ q₂ n) (hi : i<n) :
    word F h₁ α i=F.digit n i α.val := by
  exact value_independent F α (Classical.choose_spec (tower_large h₁ i)).1 hn
    (Classical.choose_spec (tower_large h₁ i)).2 hi

theorem word_zero (F : DigitAction A q₁ q₂) (h₁ : 2≤q₁) (α : Stable F) :
    word F h₁ α 0=α.val := by
  rw [word_eq F h₁ α (n:=1) ⟨0,0,by simp⟩ (by omega)]
  exact α.property 1 ⟨0,0,by simp⟩

theorem word_recursion (F : DigitAction A q₁ q₂) (h₁ : 2≤q₁)
    (α : Stable F) {q : ℕ} (hq : Tower q₁ q₂ q) (i : ℕ) (r : Fin q) :
    word F h₁ α (q*i+r.val)=F.digit q r.val (word F h₁ α i) := by
  obtain ⟨n,hn,hin⟩ := tower_large (q₂:=q₂) h₁ i
  have hbound : q*i+r.val<n*q := by
    have := r.isLt
    nlinarith
  rw [word_eq F h₁ α (tower_mul hn hq) hbound,
    F.compose n q hn hq i r.val hin r.isLt, word_eq F h₁ α hn hin]

/-- The actual projected words, rather than an assumed family of automatic
sequences, have a common eventual period by ordinary Cobham. -/
theorem projected_words_periodic [Fintype A] (F : DigitAction A q₁ q₂)
    (h₁ : 2≤q₁) (h₂ : 2≤q₂) (hi : IndependentBases.Independent q₁ q₂) :
    ∃ P i₀ : ℕ, 0 < P ∧ ∀ (α : Stable F) (i : ℕ),
      i₀ ≤ i → word F h₁ α (i + P) = word F h₁ α i := by
  classical
  let : Finite (Stable F) := Finite.of_injective (fun α : Stable F => α.val) Subtype.val_injective
  let : Fintype (Stable F) := Fintype.ofFinite _
  apply SpanningPeriodicWords.uniform_period h₁ h₂ hi (word F h₁)
    (fun α r => F.digit q₁ r.val α) (fun α r => F.digit q₂ r.val α)
  · exact fun α i r => word_recursion F h₁ α ⟨1,0,by simp⟩ i r
  · exact fun α i r => word_recursion F h₁ α ⟨0,1,by simp⟩ i r

#print axioms projected_words_periodic

/-- The initial subblock after the two idempotent leading zeros is exactly
the infinite projected word. -/
theorem projected_block (F : DigitAction A q₁ q₂) (h₁ : 2 ≤ q₁) (h₂ : 0 < q₂)
    (hid₁ : ∀ α, F.digit q₁ 0 (F.digit q₁ 0 α) = F.digit q₁ 0 α)
    (hid₂ : ∀ α, F.digit q₂ 0 (F.digit q₂ 0 α) = F.digit q₂ 0 α)
    (α : A) {n i : ℕ} (hn : Tower q₁ q₂ n) (hi : i < n) :
    F.digit ((q₁*q₂)*n) i α =
      word F h₁ (project F (by omega) h₂ hid₁ hid₂ α) i := by
  rw [word_eq F h₁ _ hn hi]
  have he := F.compose (q₁*q₂) n ⟨1,1,by simp⟩ hn 0 i
    (by positivity) hi α
  simpa only [project, mul_zero, zero_add] using he

/-- Uniform periodic zones for a finite digit action with idempotent bases.
The period is common to all covectors and all tower blocks. -/
theorem block_periodic [Fintype A] (F : DigitAction A q₁ q₂)
    (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂) (hi : IndependentBases.Independent q₁ q₂)
    (hid₁ : ∀ α, F.digit q₁ 0 (F.digit q₁ 0 α) = F.digit q₁ 0 α)
    (hid₂ : ∀ α, F.digit q₂ 0 (F.digit q₂ 0 α) = F.digit q₂ 0 α) :
    ∃ P i₀ : ℕ, 0 < P ∧ ∀ n, Tower q₁ q₂ n → ∀ α i,
      i₀ ≤ i → i+P < n →
      F.digit ((q₁*q₂)*n) (i+P) α = F.digit ((q₁*q₂)*n) i α := by
  obtain ⟨P,i₀,hP,hperiod⟩ := projected_words_periodic F h₁ h₂ hi
  refine ⟨P,i₀,hP,?_⟩
  intro n hn α i hi₀ hin
  rw [projected_block F h₁ (by omega) hid₁ hid₂ α hn hin,
    projected_block F h₁ (by omega) hid₁ hid₂ α hn (by omega)]
  exact hperiod _ i hi₀

/-- No idempotence hypothesis is needed initially: take positive powers of
the bases, form Π, and apply ordinary Cobham to the projected words. -/
theorem powered_block_periodic [Fintype A] (F : DigitAction A q₁ q₂)
    (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂) (hi : IndependentBases.Independent q₁ q₂) :
    ∃ s t P i₀ : ℕ, 0 < s ∧ 0 < t ∧ 0 < P ∧
      ∀ n, Tower (q₁^s) (q₂^t) n → ∀ α i, i₀ ≤ i → i+P < n →
      F.digit ((q₁^s*q₂^t)*n) (i+P) α = F.digit ((q₁^s*q₂^t)*n) i α := by
  obtain ⟨s,t,hs,ht,hids,hidt⟩ := idempotent_bases F (by omega) (by omega)
  have hp₁ : 2 ≤ q₁^s := h₁.trans (Nat.le_self_pow hs.ne' _)
  have hp₂ : 2 ≤ q₂^t := h₂.trans (Nat.le_self_pow ht.ne' _)
  obtain ⟨P,i₀,hP,hperiod⟩ := block_periodic (F.rebase s t) hp₁ hp₂
    (IndependentBases.independent_powers hi hs ht) hids hidt
  exact ⟨s,t,P,i₀,hs,ht,hP,hperiod⟩

#print axioms powered_block_periodic

end SpanningProjectedWords
