module

public import SpanningFixedCandidatesV1
public import SpanningRationalClosureV1
public import SpanningFinalReductionV1

@[expose] public section

namespace SpanningBoundedAxis

open scoped BigOperators
open Module GridAdmissibleGap SpanningActualKernel SpanningLinearKernels
  SpanningFiniteDimensions SpanningLevelArithmetic SpanningTraceAlgebra SpanningWindows

theorem bounded_axis {N:ℕ} (hN:Admissible N) : SpanningFinalReduction.BoundedAxis N := by
  classical
  intro B p L hB hp _hpN hdiv hbound
  let H := dimension (K:=ℚ) N (L:Set ℕ) B
  obtain ⟨S,hS,hprime⟩ := SpanningFixedCandidates.prime_set (N+B+p) (H+1)
  let P := ∏c∈S,c
  let Z := H*P
  have hroot : (0:ℝ)<Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN.1)
  have hBreal : (0:ℝ)<B := by exact_mod_cast hB
  obtain ⟨a,ha⟩ := pow_unbounded_of_one_lt ((Z:ℝ)*Real.sqrt N/(B:ℝ))
    (show (1:ℝ)<p by exact_mod_cast hp.one_lt)
  let Q := B*p^a
  have hQ : 0<Q := Nat.mul_pos hB (Nat.pow_pos hp.pos)
  let : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have hBQ : B∣Q := dvd_mul_right B (p^a)
  have hwindow : (Z:ℝ)<radius N Q 1 := by
    simp only [radius,level,one_pow,Nat.lcm_one_right]
    apply (lt_div_iff₀ hroot).mpr
    have he := (div_lt_iff₀ hBreal).mp ha
    dsimp [Q]
    push_cast
    nlinarith [he]
  let V := augmentedSubmodule (K:=ℚ) N (L:Set ℕ) Q
  have hdim : finrank ℚ V≤H := hbound a
  by_cases hzero : finrank ℚ V=0
  · let : Subsingleton V := (Module.finrank_eq_zero_iff_of_free ℚ V).mp hzero
    refine ⟨Q,hQ,hBQ,?_⟩
    intro f hf
    exact congrArg (fun x:V => (x:ℤ→ℚ)) (Subsingleton.elim (⟨f,hf⟩:V) 0)
  have hpos : 0<finrank ℚ V := Nat.pos_of_ne_zero hzero
  have hcpos : ∀c:S,0<c.val := fun c => (hprime c.val c.property).1.pos
  have hcp : Pairwise (fun c d:S => Nat.Coprime c.val d.val) := by
    intro c d hne
    exact (Nat.coprime_primes (hprime c.val c.property).1 (hprime d.val d.property).1).mpr
      (fun he => hne (Subtype.ext he))
  have hcN : ∀c:S,Nat.Coprime N c.val := by
    intro c
    exact (SpanningFixedCandidates.prime_coprime_of_large (hprime c.val c.property).1
      hN.1 (by have h:=(hprime c.val c.property).2; omega)).symm
  have hcQ : ∀c:S,Nat.Coprime c.val Q := by
    intro c
    have hb : Nat.Coprime c.val B := SpanningFixedCandidates.prime_coprime_of_large
      (hprime c.val c.property).1 hB (by have h:=(hprime c.val c.property).2; omega)
    have hcp' : Nat.Coprime c.val p := SpanningFixedCandidates.prime_coprime_of_large
      (hprime c.val c.property).1 hp.pos (by have h:=(hprime c.val c.property).2; omega)
    exact hb.mul_right (hcp'.pow_right a)
  have hcard : finrank ℚ V<Fintype.card S := by
    rw [Fintype.card_coe,hS]
    omega
  have hsize : finrank ℚ V*(∏c:S,c.val)≤Z := by
    have he : (∏c:S,c.val)=P := by
      simpa only [id_eq,Finset.univ_eq_attach] using (Finset.prod_attach S id)
    rw [he]
    exact Nat.mul_le_mul_right _ hdim
  obtain ⟨c,d,hcd,hci,hdi⟩ := SpanningTwoAdditionSelection.exists_two_injective
    (algebraMap ℚ ℂ) hQ (Complex.isPrimitiveRoot_exp Q (Nat.ne_of_gt hQ)) V
    hcard hpos (fun f hf => hf.1.1) (fun f hf n hn => by
      have hleg := legal_interval hwindow (by omega : -(Z:ℤ)≤n) (by exact_mod_cast hn)
      have he := hf.1.2 1 (one_dvd Q) n hleg
      simpa [trace] using he)
    (fun c:S => c.val) hcpos hcQ hcp hsize
  have hc2 := (hprime c.val c.property).1.two_le
  have hd2 := (hprime d.val d.property).1.two_le
  obtain ⟨Q',hQ',hQQ',hz⟩ := SpanningRationalClosure.two_rational_injections_force_zero
    hN hQ hc2 hd2 (IndependentBases.independent_of_coprime hc2 hd2 (hcp hcd))
    (hcN c) (hcN d) (fun ell hell => (hdiv ell hell).trans hBQ) hci hdi
  exact ⟨Q',hQ',hBQ.trans hQQ',hz⟩

#print axioms bounded_axis

end SpanningBoundedAxis
