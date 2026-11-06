module

/- Complete rows are sums of primitive rows, via actual gcd fibers. -/
public import SpanningWindowsV1

@[expose] public section

namespace SpanningPrimitiveComplete
open Finset SpanningTraceAlgebra SpanningWindows
variable {F : Type*} [AddCommMonoid F]

theorem fiber_sum (d e B : ℕ) (hd : 0<d) (u : ℤ) (v : ℤ → F) :
    (∑ a∈(range (d*e)).filter (fun a => Nat.gcd (d*e) a=d),v (u+a*B))=
      primitive e (d*B) v u := by
  symm
  unfold primitive
  apply sum_bij (fun b _ => d*b)
  · intro b hb
    obtain ⟨hb,hcop⟩ := mem_filter.mp hb
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hd),?_⟩
    rw [Nat.gcd_mul_left,hcop.symm.gcd_eq_one,Nat.mul_one]
  · intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro a ha
    obtain ⟨ha,hg⟩ := mem_filter.mp ha
    have hda : d∣a := by rw [← hg]; exact Nat.gcd_dvd_right _ _
    obtain ⟨b,rfl⟩ := hda
    refine ⟨b,mem_filter.mpr ⟨mem_range.mpr ?_,?_⟩,rfl⟩
    · exact Nat.lt_of_mul_lt_mul_left (mem_range.mp ha)
    · rw [Nat.gcd_mul_left] at hg
      have h1 : Nat.gcd e b=1 := by
        apply Nat.eq_of_mul_eq_mul_left hd
        simpa using hg
      exact (show Nat.Coprime e b from h1).symm
  · intro b _
    congr 1
    push_cast
    ring

theorem complete_of_primitive_at (q B : ℕ) (hq : 0<q) (u : ℤ) (v : ℤ → F)
    (hv : ∀ d, d∣q → 0<d → primitive (q/d) (d*B) v u=0) :
    trace q B v u=0 := by
  let D := (range q).image (Nat.gcd q)
  have he : (∑ d∈D,∑ a∈(range q).filter (fun a => Nat.gcd q a=d),v (u+a*B))=
      trace q B v u := sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem _ ha) _
  rw [← he]
  apply sum_eq_zero
  intro d hd
  obtain ⟨a,_ha,rfl⟩ := mem_image.mp hd
  have hdiv := Nat.gcd_dvd_left q a
  have hpos := Nat.gcd_pos_of_pos_left a hq
  have hprod : Nat.gcd q a*(q/Nat.gcd q a)=q := Nat.mul_div_cancel' hdiv
  have hf := fiber_sum (Nat.gcd q a) (q/Nat.gcd q a) B hpos u v
  rw [hprod] at hf
  exact hf.trans (hv _ hdiv hpos)

#print axioms complete_of_primitive_at

theorem quotient_stride {Q q d : ℕ} (hq : 0<q) (_hd : 0<d)
    (hdq : d∣q) (hqQ : q∣Q) : Q/(q/d)=d*(Q/q) := by
  have he : d*(q/d)=q := Nat.mul_div_cancel' hdq
  have hQ : q*(Q/q)=Q := Nat.mul_div_cancel' hqQ
  have hep : 0<q/d := by nlinarith
  have hprod : (q/d)*(d*(Q/q))=Q := by nlinarith [he]
  calc
    Q/(q/d)=((q/d)*(d*(Q/q)))/(q/d) := congrArg (fun x => x/(q/d)) hprod.symm
    _ = d*(Q/q) := Nat.mul_div_cancel_left _ hep

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

theorem complete_kernel_of_primitive {radius : ℕ → ℕ → R} {Q : ℕ}
    (hQ : 0<Q) (hmono : ∀ d q, d∣q → radius Q q≤radius Q d)
    {v : ℤ → F} (hv : PrimitiveKernel radius Q v) : CompleteKernel radius Q v := by
  refine ⟨hv.1,?_⟩
  intro q hq u hu
  have hq0 := Nat.pos_of_dvd_of_pos hq hQ
  apply complete_of_primitive_at q (Q/q) hq0 u v
  intro d hd hd0
  have he : q/d∣q := Nat.div_dvd_of_dvd hd
  have hh := hv.2 (q/d) (he.trans hq) u (legal_mono (hmono _ _ he) hu)
  rw [quotient_stride hq0 hd0 hd hq] at hh
  exact hh

#print axioms complete_kernel_of_primitive

theorem trace_eq_primitive_of_proper (q B : ℕ) (hq : 0<q) (u : ℤ) (v : ℤ → F)
    (hv : ∀ d, d∣q → 1<d → primitive (q/d) (d*B) v u=0) :
    trace q B v u=primitive q B v u := by
  let D := (range q).image (Nat.gcd q)
  have h1 : 1∈D := by
    by_cases he : q=1
    · subst q
      exact mem_image.mpr ⟨0,mem_range.mpr (by omega),rfl⟩
    · exact mem_image.mpr ⟨1,mem_range.mpr (by omega),Nat.gcd_one_right q⟩
  have he : (∑ d∈D,∑ a∈(range q).filter (fun a => Nat.gcd q a=d),v (u+a*B))=
      trace q B v u := sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem _ ha) _
  rw [← he,sum_eq_single 1]
  · simpa using fiber_sum 1 q B (by omega) u v
  · intro d hd hd1
    obtain ⟨a,_,rfl⟩ := mem_image.mp hd
    have hdiv := Nat.gcd_dvd_left q a
    have hpos := Nat.gcd_pos_of_pos_left a hq
    have hprod : Nat.gcd q a*(q/Nat.gcd q a)=q := Nat.mul_div_cancel' hdiv
    have hf := fiber_sum (Nat.gcd q a) (q/Nat.gcd q a) B hpos u v
    rw [hprod] at hf
    exact hf.trans (hv _ hdiv (by omega))
  · exact fun h => False.elim (h h1)

theorem primitive_kernel_of_complete {radius : ℕ → ℕ → R} {Q : ℕ}
    (hQ : 0<Q) (hmono : ∀ d q, d∣q → radius Q q≤radius Q d)
    {v : ℤ → F} (hv : CompleteKernel radius Q v) : PrimitiveKernel radius Q v := by
  refine ⟨hv.1,?_⟩
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq u hu
    have hq0 := Nat.pos_of_dvd_of_pos hq hQ
    have he := trace_eq_primitive_of_proper q (Q/q) hq0 u v (by
      intro d hd hd1
      have hd0 : 0<d := by omega
      have hlt : q/d<q := Nat.div_lt_self hq0 hd1
      have hdiv : q/d∣q := Nat.div_dvd_of_dvd hd
      have hh := ih (q/d) hlt (hdiv.trans hq) u (legal_mono (hmono _ _ hdiv) hu)
      rw [quotient_stride hq0 hd0 hd hq] at hh
      exact hh)
    exact he.symm.trans (hv.2 q hq u hu)

theorem kernel_equivalence {radius : ℕ → ℕ → R} {Q : ℕ}
    (hQ : 0<Q) (hmono : ∀ d q, d∣q → radius Q q≤radius Q d) (v : ℤ → F) :
    PrimitiveKernel radius Q v ↔ CompleteKernel radius Q v :=
  ⟨complete_kernel_of_primitive hQ hmono,primitive_kernel_of_complete hQ hmono⟩

#print axioms kernel_equivalence

end SpanningPrimitiveComplete
