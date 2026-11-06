module

/- Finite scale-invariant colorings from automatic kernels.
This replaces redundant-digit normalization in the planned Krebs proof.
-/
public import AutomaticSequencesV1
public import EventuallyPeriodicV1
public import Mathlib.Tactic

@[expose] public section

namespace CobhamColoring

open AutomaticSequences

variable {A : Type*}

def extendedKernel (k : ℕ) (x : ℕ → A) : Set (ℕ → A) :=
  {g | ∃ e r, r<2*k^e ∧ g = fun n => x (k^e*n+r)}

theorem extendedKernel_finite {k : ℕ} (hk : 0<k) {x : ℕ → A}
    (hx : Automatic k x) : (extendedKernel k x).Finite := by
  apply ((hx.prod (Set.finite_univ : (Set.univ : Set (Fin 2)).Finite)).image
    (fun p n => p.1 (n+p.2.val))).subset
  rintro g ⟨e,r,hr,rfl⟩
  have hd : r/k^e<2 := (Nat.div_lt_iff_lt_mul (pow_pos hk e)).mpr hr
  refine ⟨((fun n => x (k^e*n+r%k^e)),⟨r/k^e,hd⟩),
    ⟨⟨e,r%k^e,Nat.mod_lt _ (pow_pos hk e),rfl⟩,Set.mem_univ _⟩,?_⟩
  funext n
  dsimp
  congr 1
  have he := Nat.mod_add_div r (k^e)
  nlinarith

structure ScalingColoring (k : ℕ) (x : ℕ → A) where
  State : Type
  finite : Finite State
  color : ℕ → State
  same : ∀ a b, color a=color b → ∀ e r, r<2*k^e →
    x (k^e*a+r)=x (k^e*b+r)

noncomputable def scalingColoring {A : Type} [Fintype A] {k : ℕ}
    (hk : 0<k) {x : ℕ → A} (hx : Automatic k x) : ScalingColoring k x := by
  classical
  let E := ↥(extendedKernel k x)
  let : Fintype E := (extendedKernel_finite hk hx).fintype
  refine ⟨E → A,inferInstance,(fun n y => y.val n),?_⟩
  intro a b he e r hr
  exact congrFun he ⟨_,e,r,hr,rfl⟩

/-- Beyond a finite prefix, every color encountered has an infinite fiber. -/
theorem eventually_infinite_fibers {C : Type*} [Finite C] (f : ℕ → C) :
    ∃ M, ∀ n, M≤n → {j | f j=f n}.Infinite := by
  classical
  let E := ⋃ c : C, if h : {j | f j=c}.Finite then {j | f j=c} else ∅
  have hE : E.Finite := by
    apply Set.finite_iUnion
    intro c
    split_ifs with h
    · exact h
    · exact Set.finite_empty
  obtain ⟨M,hM⟩ := hE.bddAbove
  refine ⟨M+1,?_⟩
  intro n hn hfin
  have hmem : n ∈ E := by
    apply Set.mem_iUnion.mpr
    refine ⟨f n,?_⟩
    simp only [dite_eq_left hfin,Set.mem_ofPred_eq]
  have := hM hmem
  omega

theorem repeated_pair {C D : Type*} [Finite C] (f : ℕ → C) (g : ℕ → D)
    (d : D) (hd : {j | g j=d}.Infinite) :
    ∃ a b, a<b ∧ g a=d ∧ g b=d ∧ f a=f b := by
  classical
  by_contra! h
  have hi : Set.InjOn f {j | g j=d} := by
    intro a ha b hb he
    rcases lt_trichotomy a b with hab | hab | hab
    · exact False.elim (h a b hab ha hb he)
    · exact hab
    · exact False.elim (h b a hab hb ha he.symm)
  exact hd ((Set.toFinite (f '' {j | g j=d})).of_finite_image hi)

/-- All infinite second-color fibers have a same-first-color pair below
one fixed bound. No density or simultaneous-base approximation is used. -/
theorem bounded_repeated_pairs {C D : Type*} [Finite C] [Finite D]
    (f : ℕ → C) (g : ℕ → D) :
    ∃ X, 0<X ∧ ∀ d, {j | g j=d}.Infinite →
      ∃ a b, a<b ∧ a<X ∧ b<X ∧ g a=d ∧ g b=d ∧ f a=f b := by
  classical
  let S := {d : D // {j | g j=d}.Infinite}
  let : Fintype S := Fintype.ofFinite S
  have hh := fun s : S => repeated_pair f g s.val s.property
  choose a b h using hh
  let M := Finset.univ.sup b
  refine ⟨M+1,by omega,?_⟩
  intro d hd
  let s : S := ⟨d,hd⟩
  have hb : b s≤M := Finset.le_sup (f:=b) (Finset.mem_univ s)
  exact ⟨a s,b s,(h s).1,by have := (h s).1; omega,by omega,(h s).2⟩

#print axioms scalingColoring
#print axioms bounded_repeated_pairs

end CobhamColoring
