module

/- Identify the sliced finite sum with sum_r tau^r mu_q(w_r). -/
public import SpanningSlicedAdditionV1
public import Mathlib.Data.Int.ModEq

@[expose] public section

namespace SpanningAdditionCoordinates

open Finset SpanningTraceAlgebra SpanningCyclicCoordinates SpanningSlicedAddition
variable {F : Type*} [AddCommMonoid F]

theorem residue_cast {q : ℕ} (hq : 0<q) (j : ℤ) :
    ((residue hq j).val:ℤ)=j%q := by
  dsimp [residue]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt hq))

theorem residue_progression_injective {q B : ℕ} (hq : 0<q) (hc : Nat.Coprime q B) (n : ℤ) :
    Function.Injective (fun a : Fin q => residue hq (n+(a:ℕ)*B)) := by
  intro a b hab
  have he := congrArg (fun r : Fin q => (r.val:ℤ)) hab
  rw [residue_cast,residue_cast] at he
  have hm : Int.ModEq q ((a:ℕ)*B) ((b:ℕ)*B) :=
    Int.ModEq.add_left_cancel' n he
  have hh := hm.cancel_right_div_gcd (show (0:ℤ)<q by exact_mod_cast hq)
  have heq : Int.ModEq q (a:ℕ) (b:ℕ) := by simpa [Int.gcd_natCast_natCast,hc] using hh
  change (a:ℕ)%(q:ℤ)=(b:ℕ)%(q:ℤ) at heq
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast a.isLt),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast b.isLt)] at heq
  exact Fin.ext (by exact_mod_cast heq)

/-- On B-periodic vectors, t is an inverse of q modulo B. -/
def inverseAddition (q : ℕ) (t : ℤ) (w : ℕ → ℤ → F) : ℤ → F :=
  fun n => ∑ r∈range q, w r (t*(n-r))

omit [AddCommMonoid F] in
theorem cyclic_eq_of_dvd {B : ℕ} {v : ℤ → F} (hv : Cyclic B v) {i j : ℤ}
    (hd : (B:ℤ)∣j-i) : v i=v j := by
  obtain ⟨a,ha⟩ := hd
  have he : j=i+a*B := by rw [mul_comm a,←ha]; ring
  rw [he,cyclic_shift_int hv]

theorem quotient_congr_inverse {q B : ℕ} {t z : ℤ}
    (ht : (q:ℤ)*t+(B:ℤ)*z=1) (n : ℤ) (a : ℕ) :
    (B:ℤ)∣t*(n-((n+a*B)%(q:ℤ)))-(n+a*B)/(q:ℤ) := by
  let j := (n+a*B)/(q:ℤ)
  have he : (q:ℤ)*j+(n+a*B)%(q:ℤ)=n+a*B := Int.mul_ediv_add_emod _ _
  refine ⟨-z*j-t*a,?_⟩
  calc
    t*(n-(n+a*B)%(q:ℤ))-j=(t*q-1)*j-t*a*B := by
      have hn : n-(n+a*B)%(q:ℤ)=q*j-a*B := by omega
      rw [hn]; ring
    _ = B*(-z*j-t*a) := by
      have ht' : t*(q:ℤ)-1= -(B:ℤ)*z := by nlinarith [ht]
      rw [ht']; ring

theorem addition_eq_inverse {q B : ℕ} (hq : 0<q) (hc : Nat.Coprime q B)
    {t z : ℤ} (ht : (q:ℤ)*t+(B:ℤ)*z=1) (w : ℕ → ℤ → F)
    (hw : ∀ r<q, Cyclic B (w r)) : addition q B w=inverseAddition q t w := by
  funext n
  let f : Fin q → Fin q := fun a => residue hq (n+(a:ℕ)*B)
  have hf : Function.Injective f := residue_progression_injective hq hc n
  have hsurj := Finite.surjective_of_injective hf
  unfold addition inverseAddition
  apply sum_bij (fun a ha => (f ⟨a,mem_range.mp ha⟩).val)
  · intro a ha
    exact mem_range.mpr (f ⟨a,mem_range.mp ha⟩).isLt
  · intro a ha b hb hab
    have he := hf (Fin.ext hab)
    exact congrArg Fin.val he
  · intro b hb
    obtain ⟨a,ha⟩ := hsurj ⟨b,mem_range.mp hb⟩
    exact ⟨a.val,mem_range.mpr a.isLt,congrArg Fin.val ha⟩
  · intro a ha
    let r := f ⟨a,mem_range.mp ha⟩
    change w r.val ((n+a*B)/(q:ℤ))=w r.val (t*(n-r.val))
    apply cyclic_eq_of_dvd (hw r.val r.isLt)
    have hr : (r.val:ℤ)=(n+a*B)%(q:ℤ) := residue_cast hq _
    rw [hr]
    exact quotient_congr_inverse ht n a

theorem inverse_exists {q B : ℕ} (hc : Nat.Coprime q B) :
    ∃t z : ℤ, (q:ℤ)*t+(B:ℤ)*z=1 := by
  refine ⟨Nat.gcdA q B,Nat.gcdB q B,?_⟩
  rw [←Nat.gcd_eq_gcd_ab,hc]
  rfl

#print axioms addition_eq_inverse

theorem addition_injective_of_inverse {q B : ℕ} (hq : 0<q) (hc : Nat.Coprime q B)
    {t z : ℤ} (ht : (q:ℤ)*t+(B:ℤ)*z=1) {V : Set (ℤ → F)}
    (hcyc : ∀v∈V, Cyclic B v)
    (hinj : ∀w : ℕ → ℤ → F, (∀r<q, w r∈V) → inverseAddition q t w=0 → ∀r<q, w r=0) :
    AdditionInjective q B V := by
  intro w hw hz
  apply hinj w hw
  rw [←addition_eq_inverse hq hc ht w (fun r hr => hcyc _ (hw r hr))]
  exact hz

#print axioms addition_injective_of_inverse

#print axioms residue_progression_injective
#print axioms quotient_congr_inverse

end SpanningAdditionCoordinates
