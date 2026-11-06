module

/- Elementary finite-kernel automatic-sequence constructions, including
finite digit automata and closure under shifts and prefix recursions. -/
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace AutomaticSequences

variable {A : Type*}

/-- The actual base-k kernel of an infinite sequence. -/
def kernel (k : ℕ) (x : ℕ → A) : Set (ℕ → A) :=
  {y | ∃ e r : ℕ, r < k ^ e ∧ y = fun n => x (k ^ e * n + r)}

/-- We use the standard finite-kernel formulation of automaticity. -/
def Automatic (k : ℕ) (x : ℕ → A) : Prop := (kernel k x).Finite

/-- A single descent keeps the shift in the same fixed finite interval. -/
theorem shift_step {k s : ℕ} (hk : 2 ≤ k)
    (step : Fin k → A → A) (x : ℕ → A)
    (hx : ∀ t, s ≤ t →
      x t = step ⟨(t-s) % k, Nat.mod_lt _ (by omega)⟩ (x ((t-s)/k)))
    {d r : ℕ} (hd : d ≤ s) (hr : r < k) :
    ∃ d' ≤ s, ∃ g : A → A, ∀ n, s ≤ n →
      x (k*n+r-d) = g (x (n-d')) := by
  have hk0 : 0 < k := by omega
  let q := k*s+r-d-s
  have hlarge : d+s ≤ k*s+r := by nlinarith
  have hq : q + d + s = k*s+r := by dsimp [q]; omega
  have hqbound : q < k*(s+1) := by nlinarith
  have hdiv : q/k ≤ s := by
    have : q/k < s+1 := (Nat.div_lt_iff_lt_mul hk0).mpr (by
      simpa [Nat.mul_comm] using hqbound)
    omega
  refine ⟨s-q/k, Nat.sub_le _ _, step ⟨q%k, Nat.mod_lt _ hk0⟩, ?_⟩
  intro n hn
  have hns : n-s+s = n := Nat.sub_add_cancel hn
  have hbase : k*n+r = k*(n-s)+(k*s+r) := by
    calc
      k*n+r = k*((n-s)+s)+r := by rw [hns]
      _ = k*(n-s)+(k*s+r) := by ring
  have hnonneg : s ≤ k*n+r-d := by omega
  have harg : k*n+r-d-s = k*(n-s)+q := by omega
  rw [hx _ hnonneg]
  have hmod : (k*n+r-d-s)%k = q%k := by
    rw [harg]
    simp
  have hquot : (k*n+r-d-s)/k = n-(s-q/k) := by
    rw [harg, Nat.mul_add_div hk0]
    simpa only [Nat.sub_sub_self hdiv] using
      (Nat.sub_add_sub_cancel hn (Nat.sub_le s (q/k)))
  simp only [hmod, hquot]

/-- Every kernel element has a bounded-shift, letter-coding description
outside the fixed prefix of length s. -/
theorem kernel_normal_form {k s : ℕ} (hk : 2 ≤ k)
    (step : Fin k → A → A) (x : ℕ → A)
    (hx : ∀ t, s ≤ t →
      x t = step ⟨(t-s) % k, Nat.mod_lt _ (by omega)⟩ (x ((t-s)/k))) :
    ∀ e r, r < k^e → ∃ d ≤ s, ∃ f : A → A,
      ∀ n, s ≤ n → x (k^e*n+r) = f (x (n-d)) := by
  intro e
  induction e with
  | zero =>
    intro r hr
    have : r = 0 := by simpa using hr
    subst r
    refine ⟨0, Nat.zero_le _, id, ?_⟩
    simp
  | succ e ih =>
    intro r hr
    have hk0 : 0 < k := by omega
    have hpow : 0 < k^e := pow_pos hk0 e
    have ht : r/k^e < k := by
      apply (Nat.div_lt_iff_lt_mul hpow).mpr
      simpa [pow_succ, Nat.mul_comm] using hr
    obtain ⟨d, hd, f, hf⟩ := ih (r%k^e) (Nat.mod_lt _ hpow)
    obtain ⟨d', hd', g, hg⟩ := shift_step hk step x hx hd ht
    refine ⟨d', hd', f ∘ g, ?_⟩
    intro n hn
    have harg : k^(e+1)*n+r = k^e*(k*n+r/k^e)+r%k^e := by
      have heq := Nat.mod_add_div r (k^e)
      rw [pow_succ]
      nlinarith
    have hkn : n ≤ k*n := Nat.le_mul_of_pos_left n hk0
    have hknr : s ≤ k*n+r/k^e := le_trans hn (le_trans hkn (Nat.le_add_right _ _))
    rw [harg, hf _ hknr, hg _ hn]
    rfl

/-- A finite-alphabet prefix-substitution equation forces automaticity.
No automaticity theorem is assumed here. -/
theorem automatic_of_prefix_equation [Fintype A] {k s : ℕ} (hk : 2 ≤ k)
    (step : Fin k → A → A) (x : ℕ → A)
    (hx : ∀ t, s ≤ t →
      x t = step ⟨(t-s) % k, Nat.mod_lt _ (by omega)⟩ (x ((t-s)/k))) :
    Automatic k x := by
  classical
  let realize : ((Fin s → A) × Fin (s+1) × (A → A)) → (ℕ → A) :=
    fun v n => if h : n < s then v.1 ⟨n,h⟩ else v.2.2 (x (n-v.2.1.val))
  apply (Set.finite_range realize).subset
  rintro y ⟨e, r, hr, rfl⟩
  obtain ⟨d, hd, f, hf⟩ := kernel_normal_form hk step x hx e r hr
  refine ⟨(fun j => x (k^e*j.val+r), ⟨d, by omega⟩, f), ?_⟩
  funext n
  dsimp [realize]
  split_ifs with hn
  · rfl
  · exact (hf n (by omega)).symm

/-- The infinite concatenation U sigma(U) sigma^2(U) ... constructed
recursively by its exact prefix equation. The block identity below identifies
this recursion with the concatenation, rather than merely postulating it. -/
def envelope (k s : ℕ) (hk : 0 < k) (hs : 0 < s)
    (seed : Fin s → A) (step : Fin k → A → A) (n : ℕ) : A :=
  if h : n < s then seed ⟨n,h⟩
  else step ⟨(n-s)%k, Nat.mod_lt _ hk⟩
    (envelope k s hk hs seed step ((n-s)/k))
termination_by n
decreasing_by
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt (by omega) hs)

theorem envelope_prefix_equation (k s : ℕ) (hk : 0 < k) (hs : 0 < s)
    (seed : Fin s → A) (step : Fin k → A → A) (n : ℕ) (hn : s ≤ n) :
    envelope k s hk hs seed step n =
      step ⟨(n-s)%k, Nat.mod_lt _ hk⟩
        (envelope k s hk hs seed step ((n-s)/k)) := by
  rw [envelope]
  simp only [dite_eq_right (by omega : ¬ n < s)]

/-- BKK Lemma1.2(ii), in finite-kernel form. -/
theorem automatic_envelope [Fintype A] (k s : ℕ) (hk : 2 ≤ k) (hs : 0 < s)
    (seed : Fin s → A) (step : Fin k → A → A) :
    Automatic k (envelope k s (by omega) hs seed step) := by
  apply automatic_of_prefix_equation hk step
  intro n hn
  exact envelope_prefix_equation k s (by omega) hs seed step n hn

/-- Starting position of the r-th substituted seed block. -/
def blockStart (k s : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => s+k*blockStart k s r

/-- Values in sigma^r(U), with irrelevant total extension beyond its length. -/
def blockValue (k s : ℕ) (hk : 0 < k) (hs : 0 < s)
    (seed : Fin s → A) (step : Fin k → A → A) : ℕ → ℕ → A
  | 0, t => seed ⟨t%s, Nat.mod_lt _ hs⟩
  | r+1, t => step ⟨t%k, Nat.mod_lt _ hk⟩
      (blockValue k s hk hs seed step r (t/k))

/-- Successive blocks abut: the r-th block has exactly s*k^r letters. -/
theorem blockStart_succ (k s r : ℕ) :
    blockStart k s (r+1) = blockStart k s r + s*k^r := by
  induction r with
  | zero => simp [blockStart]
  | succ r ih =>
    calc
      blockStart k s (r+1+1) = s+k*blockStart k s (r+1) := rfl
      _ = s+k*(blockStart k s r + s*k^r) := by rw [ih]
      _ = blockStart k s (r+1) + s*k^(r+1) := by
        simp only [blockStart, pow_succ]
        ring

/-- Semantic identification with U sigma(U) sigma^2(U) ... . -/
theorem envelope_on_block (k s : ℕ) (hk : 2 ≤ k) (hs : 0 < s)
    (seed : Fin s → A) (step : Fin k → A → A) :
    ∀ r t, t < s*k^r →
      envelope k s (by omega) hs seed step (blockStart k s r+t) =
        blockValue k s (by omega) hs seed step r t := by
  have hk0 : 0 < k := by omega
  intro r
  induction r with
  | zero =>
    intro t ht
    have ht' : t < s := by simpa using ht
    simp [blockStart, blockValue, envelope, ht', Nat.mod_eq_of_lt ht']
  | succ r ih =>
    intro t ht
    have hidx : s ≤ blockStart k s (r+1)+t := by
      simp only [blockStart]
      omega
    have htdiv : t/k < s*k^r := by
      apply (Nat.div_lt_iff_lt_mul hk0).mpr
      simpa [pow_succ, Nat.mul_assoc] using ht
    have hsub : blockStart k s (r+1)+t-s = k*blockStart k s r+t := by
      simp only [blockStart]
      omega
    rw [envelope_prefix_equation k s hk0 hs seed step _ hidx]
    simp only [hsub, Nat.mul_add_mod, Nat.mul_add_div hk0]
    rw [ih _ htdiv]
    rfl

/-- Every position lies in a substituted seed block: the concatenation
identification covers the entire infinite sequence. -/
theorem exists_block (k s : ℕ) (hk : 0 < k) (hs : 0 < s) (n : ℕ) :
    ∃ r t, t < s*k^r ∧ n = blockStart k s r+t := by
  induction n with
  | zero => exact ⟨0, 0, by simpa using hs, rfl⟩
  | succ n ih =>
    obtain ⟨r, t, ht, hn⟩ := ih
    by_cases hnext : t+1 < s*k^r
    · exact ⟨r, t+1, hnext, by omega⟩
    · refine ⟨r+1, 0, by simpa using Nat.mul_pos hs (pow_pos hk (r+1)), ?_⟩
      rw [blockStart_succ]
      omega

/-! The finite-kernel result is connected explicitly to finite automata,
so `Automatic` is not merely an uninterpreted predicate. Digits here are
read least-significant first; their numerical value is specified below. -/

universe u

/-- A genuine finite-state digit automaton with output. -/
structure DigitAutomaton (k : ℕ) (A : Type u) where
  State : Type u
  finite : Finite State
  start : State
  next : State → Fin k → State
  output : State → A

def DigitAutomaton.run {k : ℕ} (M : DigitAutomaton k A) :
    M.State → List (Fin k) → A
  | q, [] => M.output q
  | q, d::ds => M.run (M.next q d) ds

/-- Value of a base-k digit string written least-significant first. -/
def digitValue (k : ℕ) : List (Fin k) → ℕ
  | [] => 0
  | d::ds => d.val+k*digitValue k ds

theorem self_mem_kernel (k : ℕ) (x : ℕ → A) : x ∈ kernel k x := by
  refine ⟨0, 0, by simp, ?_⟩
  funext n
  simp

theorem decimation_mem_kernel {k : ℕ} {x y : ℕ → A}
    (hy : y ∈ kernel k x) (d : Fin k) :
    (fun n => y (k*n+d.val)) ∈ kernel k x := by
  obtain ⟨e, r, hr, rfl⟩ := hy
  refine ⟨e+1, k^e*d.val+r, ?_, ?_⟩
  · calc
      k^e*d.val+r < k^e*d.val+k^e := Nat.add_lt_add_left hr _
      _ = k^e*(d.val+1) := by ring
      _ ≤ k^e*k := Nat.mul_le_mul_left _ (by omega)
      _ = k^(e+1) := (pow_succ _ _).symm
  · funext n
    apply congrArg x
    rw [pow_succ]
    ring

def kernelAutomaton {k : ℕ} {x : ℕ → A} (h : Automatic k x) :
    DigitAutomaton k A where
  State := ↥(kernel k x)
  finite := h.to_subtype
  start := ⟨x, self_mem_kernel k x⟩
  next := fun q d => ⟨fun n => q.val (k*n+d.val), decimation_mem_kernel q.property d⟩
  output := fun q => q.val 0

theorem kernelAutomaton_run {k : ℕ} {x : ℕ → A} (h : Automatic k x)
    (q : (kernelAutomaton h).State) (ds : List (Fin k)) :
    (kernelAutomaton h).run q ds = q.val (digitValue k ds) := by
  induction ds generalizing q with
  | nil => rfl
  | cons d ds ih =>
    rw [DigitAutomaton.run, ih]
    change q.val (k*digitValue k ds+d.val) = q.val (d.val+k*digitValue k ds)
    rw [Nat.add_comm]

/-- Every natural number really has an input representation. -/
theorem exists_digits (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    ∃ ds : List (Fin k), digitValue k ds = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      exact ⟨[], rfl⟩
    · obtain ⟨ds, hds⟩ := ih (n/k) (Nat.div_lt_self (by omega) hk)
      refine ⟨⟨n%k, Nat.mod_lt _ (by omega)⟩::ds, ?_⟩
      simp only [digitValue, hds]
      exact Nat.mod_add_div n k

/-- Actual finite-state computation of the BKK envelope, not an assumed
equivalence between finite kernels and an opaque automaticity predicate. -/
theorem envelope_has_finite_automaton [Fintype A]
    (k s : ℕ) (hk : 2 ≤ k) (hs : 0 < s)
    (seed : Fin s → A) (step : Fin k → A → A) :
    ∃ M : DigitAutomaton k A, ∀ ds,
      M.run M.start ds =
        envelope k s (by omega) hs seed step (digitValue k ds) := by
  let h := automatic_envelope k s hk hs seed step
  refine ⟨kernelAutomaton h, ?_⟩
  intro ds
  exact kernelAutomaton_run h (kernelAutomaton h).start ds

/-- State transformations reverse the direction of digit reading, with
no infinite state space introduced. -/
def DigitAutomaton.reverse {k : ℕ} (M : DigitAutomaton k A) :
    DigitAutomaton k A where
  State := M.State → M.State
  finite := by
    classical
    have := M.finite
    let : Fintype M.State := Fintype.ofFinite M.State
    infer_instance
  start := id
  next := fun f d => f ∘ (fun q => M.next q d)
  output := fun f => M.output (f M.start)

theorem DigitAutomaton.run_eq_foldl {k : ℕ} (M : DigitAutomaton k A)
    (q : M.State) (ds : List (Fin k)) :
    M.run q ds = M.output (ds.foldl M.next q) := by
  induction ds generalizing q with
  | nil => rfl
  | cons d ds ih => exact ih (M.next q d)

theorem DigitAutomaton.reverse_run_aux {k : ℕ} (M : DigitAutomaton k A)
    (f : M.State → M.State) (ds : List (Fin k)) :
    M.reverse.run f ds = M.output (f (ds.reverse.foldl M.next M.start)) := by
  induction ds generalizing f with
  | nil => rfl
  | cons d ds ih =>
    change M.reverse.run (f ∘ (fun q => M.next q d)) ds = _
    rw [ih]
    simp [List.reverse_cons, List.foldl_append]

theorem DigitAutomaton.reverse_run {k : ℕ} (M : DigitAutomaton k A)
    (ds : List (Fin k)) :
    M.reverse.run M.reverse.start ds = M.run M.start ds.reverse := by
  exact (DigitAutomaton.reverse_run_aux M id ds).trans
    (DigitAutomaton.run_eq_foldl M M.start ds.reverse).symm

/-- The standard, most-significant-digit-first automaton formulation of
the envelope lemma. The input ds has value digitValue k ds.reverse. -/
theorem envelope_has_msb_automaton [Fintype A]
    (k s : ℕ) (hk : 2 ≤ k) (hs : 0 < s)
    (seed : Fin s → A) (step : Fin k → A → A) :
    ∃ M : DigitAutomaton k A, ∀ ds,
      M.run M.start ds =
        envelope k s (by omega) hs seed step (digitValue k ds.reverse) := by
  obtain ⟨M, hM⟩ := envelope_has_finite_automaton k s hk hs seed step
  refine ⟨M.reverse, ?_⟩
  intro ds
  rw [DigitAutomaton.reverse_run, hM]

/-- There is an MSB-first input for every index, including zero. -/
theorem exists_msb_digits (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    ∃ ds : List (Fin k), digitValue k ds.reverse = n := by
  obtain ⟨ds, hds⟩ := exists_digits k hk n
  exact ⟨ds.reverse, by simpa using hds⟩

end AutomaticSequences

#print axioms AutomaticSequences.automatic_envelope
#print axioms AutomaticSequences.envelope_on_block
#print axioms AutomaticSequences.exists_block
#print axioms AutomaticSequences.envelope_has_finite_automaton
#print axioms AutomaticSequences.exists_digits
#print axioms AutomaticSequences.envelope_has_msb_automaton
#print axioms AutomaticSequences.exists_msb_digits
