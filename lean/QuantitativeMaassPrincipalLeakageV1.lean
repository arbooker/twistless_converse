module

public import QuantitativeMaassShellSummationV1
public import QuantitativeMaassWindowFloorTailV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open AsymptoticCongruenceStrip
open scoped SchwartzMap

namespace QuantitativeMaass

universe u

/-- Actual total principal spectral leakage of a trimmed window. One constant
is chosen before the orthonormal cusp eigenfamily, kernel, centre and scales. -/
theorem principal_trimmed_window_leakage (N : ℕ) (hN : 0<N) :
    ∃ C : ℝ,0<C ∧ ∀ (ι : Type u) (v : ι → AutomorphicSpace N),
      Orthonormal ℂ v → (∀ i,v i∈localCuspidalSpace N hN) →
      ∀ e : ι → ℝ,(∀ i,0≤e i) →
      (∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i)) →
      ∀ K : SchwartzMap ℝ ℝ,(∀ x,0≤K x) →
      ∀ t ε δ R : ℝ,0<t → ε≤1 → 0<δ → δ≤1 → 0<R →
        let f := fun i : {i // 1/4≤e i ∧ Real.sqrt (e i-1/4)∉Icc t (t+ε)} =>
          (smoothedWindow K R (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ)))
            (Real.sqrt (e i.val-1/4)))^2
        Summable f ∧ (∑' i,f i)≤C*(∫ u,|u|^2*K u)^2*(t+2)/(R*δ)^4 := by
  classical
  obtain ⟨B,hB,hcount⟩ := principal_shell_linear N hN
  have hZ : 0≤cubicShellMass := tsum_nonneg (fun n => by positivity)
  refine ⟨81*B*(cubicShellMass+1),by positivity,?_⟩
  intro ι v hv hcusp e he hgraph K hK t ε δ R ht hε hδ hδ1 hR
  let J := {i // 1/4≤e i ∧ Real.sqrt (e i-1/4)∉Icc t (t+ε)}
  let r : J → ℝ := fun i => Real.sqrt (e i.val-1/4)
  let j : J → ℕ := fun i => ⌊|r i-t|⌋₊
  let f : J → ℝ := fun i =>
    (smoothedWindow K R (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) (r i))^2
  let T : ℕ → Set ι := fun n => {i | 1/4≤e i ∧ |Real.sqrt (e i-1/4)-t|∈Icc (n:ℝ) (n+1)}
  have hb (n : ℕ) : (T n).Finite ∧ (Nat.card (T n):ℝ)≤B*(t+n+2) :=
    hcount ι v hv hcusp e he hgraph t n ht.le (Nat.cast_nonneg n)
  have hsub (n : ℕ) : {i : J | j i=n}⊆Subtype.val ⁻¹' T n := by
    intro i hi
    have hl := Nat.floor_le (abs_nonneg (r i-t))
    have hu := Nat.lt_floor_add_one |r i-t|
    change j i=n at hi
    change (j i:ℝ)≤|r i-t| at hl
    change |r i-t|<(j i:ℝ)+1 at hu
    rw [hi] at hl hu
    exact ⟨i.property.1,hl,hu.le⟩
  have hfin (n : ℕ) : {i : J | j i=n}.Finite :=
    ((hb n).1.preimage Subtype.val_injective.injOn).subset (hsub n)
  have hcard (n : ℕ) : (Nat.card {i : J // j i=n}:ℝ)≤B*(t+n+2) := by
    let : Fintype (T n) := (hb n).1.fintype
    let F : {i : J // j i=n} → T n := fun i => ⟨i.val.val,hsub n i.property⟩
    have hinj : Function.Injective F := by
      intro a b hab
      have hval : a.val.val=b.val.val := congrArg (fun x : T n => x.val) hab
      exact Subtype.ext (Subtype.ext hval)
    have hh : (Nat.card {i : J // j i=n}:ℝ)≤(Nat.card (T n):ℝ) := by
      exact_mod_cast Nat.card_le_card_of_injective F hinj
    exact hh.trans (hb n).2
  let A : ℝ := 81*(∫ u,|u|^2*K u)^2/(R*δ)^4
  have hpoint (i : J) : f i≤A/((j i:ℝ)+1)^4 :=
    shrunken_squaredWindow_floor_tail K hK t ε δ R (r i) ht (Real.sqrt_nonneg _)
      hε hδ hδ1 hR i.property.2
  have hh := linear_shell_weight_sum j f (fun i => sq_nonneg _) B A t hB.le (by positivity)
    ht.le hfin hcard hpoint
  refine ⟨hh.1,hh.2.trans ?_⟩
  change B*(t+2)*A*cubicShellMass≤_
  calc
    _ ≤ B*(t+2)*A*(cubicShellMass+1) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by dsimp only [A]; ring

#print axioms principal_trimmed_window_leakage

end QuantitativeMaass
