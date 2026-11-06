module

public import GridParametersV1

@[expose] public section

namespace GridBufferedDetection

open GridParameters GridSelectedWindows GridSpecialWindows GridPrimeParts GridAdmissibleGap
  GridSupportedDetection GridLabelDetection GridCarrier CompleteRowCosets
  SpanningActualKernel SpanningWindows SpanningTraceAlgebra

def BufferedZero {K : Type*} [AddCommMonoid K] (N Q : ℕ) (b : ℝ) (f : ℤ → K) : Prop :=
  ∀q:ℕ,0<q → q∣Q → ∀u:ℤ,Legal (radius N Q q) u →
    b≤radius N Q q-1-(u:ℝ) → trace q (Q/q) f u=0

theorem coset_zero_of_buffer {K : Type*} [AddCommMonoid K] {N Q q D : ℕ}
    {b : ℝ} {f : ℤ → K} (hq : 0<q) (hD : 0<D) (he : q*D=Q)
    (hcyc : Cyclic Q f) (hz : BufferedZero N Q b f) (u : ℤ)
    (hu : Legal (radius N Q q) u) (hb : b≤radius N Q q-1-(u:ℝ)) : cosetSum Q D u f=0 := by
  have hqd : Q/q=D := by rw [←he,Nat.mul_div_cancel_left _ hq]
  have ht := hz q hq ⟨D,he.symm⟩ u hu hb
  rw [hqd] at ht
  have hcos := trace_coset_sum hq hD u f (by simpa only [he] using hcyc)
  rw [he] at hcos
  exact hcos.symm.trans ht

/-- Complete arithmetic-grid support detector, with an explicit rational
buffer and no external mathematical inputs. -/
theorem exists_buffered_grid {N G : ℕ} (hN : Admissible N) (hG : 0<G) (hNG : N∣G) :
    ∃H R:ℕ,0<H ∧ 0<R ∧ ∀(v:ℕ)(hv0:0<v),H∣v → 16*R≤v →
      ∀{K : Type} [AddCommMonoid K] (f : ℤ → K),
      Cyclic (G*v) f →
      (∀j:Fin (G*v),j∉Set.range (gridIndex hG hv0 (v/(8*R))) → f j.val=0) →
      BufferedZero N (G*v) (3*(v:ℝ)/(40*R)-1) f → f=0 := by
  obtain ⟨r,H,R,hH,hR,hr⟩ := exists_grid_parameters hG
  refine ⟨H,R,hH,hR,?_⟩
  intro v hv0 hHv hv K _ f hcyc hsupport hrows
  let w := fun a:Fin G => v/r a
  let c := fun a:Fin G => labelModulus a/labelOrder a
  have hrv : ∀a,r a∣v := fun a => (hr a).2.2.1.trans hHv
  have hwv : ∀a,v=r a*w a := fun a => (Nat.mul_div_cancel' (hrv a)).symm
  have hest := fun a => quotient_estimates (hr a).1 (hr a).2.2.2.1 hv (hrv a)
  have hJv : 2*(v/(8*R))<v := (hest ⟨0,hG⟩).2.2
  apply grid_detect_of_rows hG hv0 hJv r w c
    (fun a _ => (hest a).1) (fun a _ => hwv a)
    (fun a _ => by
      have he := row_factorization hG a (hwv a)
      exact ⟨primePart G (fun p => ¬p∣labelOrder a)*r a,by rw [←he]; ring⟩)
    (fun a _ => (hest a).2.1)
    (fun a _ => ((hr a).2.1.of_dvd_right (part_dvd G _)).symm)
    (fun a _ => (hr a).2.2.2.2) f hcyc hsupport
  · intro a ha t
    have hwin := selected_window hN hG hNG a ha (hr a).1 (hr a).2.1
      (hr a).2.2.2.1 hv (hwv a) t.val (offset_bound hR t)
    have hmp : 0<labelModulus a := Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hG) _)
    have hdp : 0<primePart G (fun p => ¬p∣labelOrder a) :=
      Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hG) _)
    apply coset_zero_of_buffer (Nat.mul_pos hdp (hr a).1) (Nat.mul_pos hmp (hest a).1)
      (row_factorization hG a (hwv a)) hcyc hrows
    · exact hwin.1
    · exact hwin.2
  · intro t
    have hwin := special_window hN.1 hG (q:=1) (by omega) hNG (one_dvd G)
      hR hv t.val (offset_bound hR t)
    have hz := hrows 1 (by omega) (one_dvd _) t.val hwin.1 hwin.2
    simpa [trace] using hz
  · intro a haa t
    have h2G : 2∣G := ⟨a.val,haa.symm⟩
    have hwin := special_window hN.1 hG (q:=2) (by omega) hNG h2G
      hR hv t.val (offset_bound hR t)
    have hz := hrows 2 (by omega) (h2G.trans (dvd_mul_right G v)) t.val hwin.1 hwin.2
    have hdiv : G*v/2=a.val*v := by
      have he : G*v=2*(a.val*v) := by nlinarith [congrArg (fun x:ℕ => x*v) haa]
      rw [he,Nat.mul_div_cancel_left _ (by omega : 0<2)]
    simpa [trace,Finset.sum_range_succ,hdiv,Nat.cast_mul,add_comm] using hz

#print axioms exists_buffered_grid

end GridBufferedDetection
