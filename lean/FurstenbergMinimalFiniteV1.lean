module

public import FurstenbergMinimalV1
public import Mathlib.NumberTheory.PowModTotient

set_option autoImplicit false

@[expose] public section

namespace FurstenbergMinimal

open Set SpanningExceptionalSet SpanningProjectedWords FurstenbergZero
open IndependentBases

/-- Multipliers congruent to one fix the corresponding torsion subgroup. -/
theorem fixes_torsion {n d : ℕ} (hn : n % d = 1) {θ : Circle}
    (hθ : d • θ = 0) : n • θ = θ := by
  conv_lhs => rw [← Nat.mod_add_div n d]
  rw [add_nsmul, hn, one_nsmul, mul_comm d, mul_smul, hθ, smul_zero, add_zero]

/-- A powered minimal subset of an infinite minimal set remains infinite. -/
theorem powered_minimal_infinite {q₁ q₂ s : ℕ} (h₁ : 2 ≤ q₁) (hs : 0 < s)
    {M B : Set Circle} (hM : Minimal (Admissible q₁ q₂) M) (hInf : M.Infinite)
    (hB : Minimal (Admissible (q₁^s) (q₂^s)) B) (hBM : B ⊆ M) : B.Infinite := by
  intro hfin
  obtain ⟨x,hx⟩ := hB.prop.2.1
  have hpow : 2 ≤ q₁^s := h₁.trans (le_self_pow₀ (by omega) hs.ne')
  obtain ⟨d,hd,hxd⟩ := torsion_of_finite_invariant hfin hpow
    (fun y hy => hB.prop.2.2 _ ⟨1,0,by simp⟩ y hy) hx
  exact hInf (finite_of_torsion hM (hBM hx) hd hxd)

/-- Arbitrarily fine rational grids occur inside an infinite minimal set.
Only the total set is assumed minimal; no nested choice of subsets is needed. -/
theorem grid_in_minimal {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {M : Set Circle}
    (hM : Minimal (Admissible q₁ q₂) M) (hInf : M.Infinite)
    {d : ℕ} (hd : 1 < d) (hc₁ : q₁.Coprime d) (hc₂ : q₂.Coprime d) :
    ∃ x : Circle, ∀ θ : Circle, d • θ = 0 → x-θ ∈ M := by
  let s := Nat.totient d
  have hs : 0 < s := Nat.totient_pos.mpr (by omega)
  have hpowered : Admissible (q₁^s) (q₂^s) M :=
    ⟨hM.prop.1,hM.prop.2.1,fun n hn x hx => hM.prop.2.2 n (tower_powers hn) x hx⟩
  obtain ⟨B,hBM,hB⟩ := exists_minimal hpowered
  have hBI := powered_minimal_infinite h₁ hs hM hInf hB hBM
  obtain ⟨x,hx⟩ := hB.prop.2.1
  refine ⟨x,fun θ hθ => hBM ?_⟩
  exact translate_mem_of_infinite
    (h₁.trans (le_self_pow₀ (by omega) hs.ne'))
    (h₂.trans (le_self_pow₀ (by omega) hs.ne')) (independent_powers hi hs hs) hB hBI
    (fixes_torsion (Nat.pow_totient_mod_eq_one hd hc₁) hθ)
    (fixes_torsion (Nat.pow_totient_mod_eq_one hd hc₂) hθ) hx

/-- A closed set containing translated rational grids of arbitrarily fine
mesh is the whole circle. This is a real-lift proof, using the integer ceiling. -/
theorem full_of_grids {A : Set Circle} (hA : IsClosed A)
    (hgrids : ∀ T : ℕ, ∃ d : ℕ, T < d ∧ ∃ x : Circle,
      ∀ θ : Circle, d • θ = 0 → x-θ ∈ A) : A = univ := by
  let S : Set ℝ := ((↑) : ℝ → Circle) ⁻¹' A
  have hS : IsClosed S := hA.preimage (AddCircle.continuous_mk' 1)
  have hall : ∀ y : ℝ, (y:Circle) ∈ A := by
    intro y
    apply hS.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨T,hT⟩ := exists_nat_gt (1/ε)
    obtain ⟨d,hd,x,hx⟩ := hgrids T
    have hdpos : 0 < (d:ℝ) := by exact_mod_cast (show 0<d by omega)
    have hsmall : 1/(d:ℝ) < ε := by
      have hT' : (T:ℝ) < d := by exact_mod_cast hd
      apply (div_lt_iff₀ hdpos).mpr
      have he := (div_lt_iff₀ hε).mp (hT.trans hT')
      nlinarith
    obtain ⟨u,hu⟩ := QuotientAddGroup.mk_surjective x
    let z : ℤ := ⌈(d:ℝ)*(y-u)⌉
    let t : ℝ := u+(z:ℝ)/(d:ℝ)
    have hlo : y ≤ t := by
      have hc := Int.le_ceil ((d:ℝ)*(y-u))
      have he : (d:ℝ)*((z:ℝ)/(d:ℝ)) = z := by field_simp
      dsimp [t]
      change (d:ℝ)*(y-u) ≤ (z:ℝ) at hc
      nlinarith
    have hup : t < y+1/(d:ℝ) := by
      have hc := Int.ceil_lt_add_one ((d:ℝ)*(y-u))
      have he : (d:ℝ)*((z:ℝ)/(d:ℝ)) = z := by field_simp
      have he' : (d:ℝ)*(1/(d:ℝ)) = 1 := by field_simp
      dsimp [t]
      change (z:ℝ) < (d:ℝ)*(y-u)+1 at hc
      nlinarith
    refine ⟨t,?_,?_⟩
    · have hθ : d • (((-(z:ℝ)/(d:ℝ)):ℝ):Circle) = 0 := by
        rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
        change (((d:ℝ)*(-(z:ℝ)/(d:ℝ)):ℝ):Circle)=0
        have he : (d:ℝ)*(-(z:ℝ)/(d:ℝ)) = -(z:ℝ) := by field_simp
        rw [he]
        apply (AddCircle.coe_eq_zero_iff 1).mpr
        exact ⟨-z,by simp⟩
      have hh := hx _ hθ
      rw [← hu, ← AddCircle.coe_sub] at hh
      have he : u - -(z:ℝ)/(d:ℝ) = t := by dsimp [t]; ring
      rw [he] at hh
      exact hh
    · rw [Real.dist_eq, abs_of_nonpos (by linarith : y-t ≤ 0)]
      linarith
  apply eq_univ_of_forall
  intro x
  obtain ⟨y,rfl⟩ := QuotientAddGroup.mk_surjective x
  exact hall y

/-- Furstenberg's minimal-set lemma: every minimal nonempty closed invariant
set on the circle is finite. -/
theorem minimal_finite {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {M : Set Circle}
    (hM : Minimal (Admissible q₁ q₂) M) : M.Finite := by
  by_contra hInf
  have hfull : M = univ := by
    apply full_of_grids hM.prop.1
    intro T
    let d := q₁*q₂*(T+1)+1
    have hprod : 2 ≤ q₁*q₂ := by nlinarith
    have hlarge := Nat.le_mul_of_pos_left (T+1) (show 0<q₁*q₂ by omega)
    have hlarge' := Nat.le_mul_of_pos_right (q₁*q₂) (show 0<T+1 by omega)
    have hd : T < d := by dsimp [d]; omega
    have hd1 : 1 < d := by dsimp [d]; omega
    have hc₁ : q₁.Coprime d := by
      dsimp [d]
      rw [mul_assoc, Nat.coprime_mul_left_add_right]
      exact Nat.coprime_one_right _
    have hc₂ : q₂.Coprime d := by
      dsimp [d]
      rw [mul_comm q₁ q₂, mul_assoc, Nat.coprime_mul_left_add_right]
      exact Nat.coprime_one_right _
    obtain ⟨x,hx⟩ := grid_in_minimal h₁ h₂ hi hM hInf hd1 hc₁ hc₂
    exact ⟨d,hd,x,hx⟩
  have hz : (0:Circle) ∈ M := hfull.symm ▸ mem_univ _
  exact hInf (finite_of_torsion hM hz (by decide : 0<1) (by simp))

#print axioms grid_in_minimal
#print axioms full_of_grids
#print axioms minimal_finite

end FurstenbergMinimal
