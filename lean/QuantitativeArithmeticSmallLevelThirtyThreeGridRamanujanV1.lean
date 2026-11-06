module

public import QuantitativeArithmeticSmallLevelThirtyThreeGridCoherentFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessNormalizedTwistProduct

def gridTaylorSpecs : Fin 72→ℕ×ℤ :=
  ![(1,1),(1,-1),(1,2),(1,-2),(1,3),(1,-3),(1,4),(1,-4),(1,6),(1,-6),(1,11),(1,-11),(1,12),(1,-12),(1,22),(1,-22),(1,33),(1,-33),(1,44),(1,-44),(1,66),(1,-66),(1,132),(1,-132),(2,1),(2,-1),(2,3),(2,-3),(2,11),(2,-11),(2,33),(2,-33),(3,1),(3,-1),(3,2),(3,-2),(3,4),(3,-4),(3,11),(3,-11),(3,22),(3,-22),(3,44),(3,-44),(6,1),(6,-1),(6,11),(6,-11),(11,1),(11,-1),(11,2),(11,-2),(11,3),(11,-3),(11,4),(11,-4),(11,6),(11,-6),(11,12),(11,-12),(22,1),(22,-1),(22,3),(22,-3),(33,1),(33,-1),(33,2),(33,-2),(33,4),(33,-4),(66,1),(66,-1)]
def gridTaylorQ (i : Fin 72) : ℕ := (gridTaylorSpecs i).1
def gridTaylorT (i : Fin 72) : ℤ := (gridTaylorSpecs i).2
def gridTaylorL (i : Fin 72) : ℕ := Nat.lcm 33 ((gridTaylorQ i)^2)
def gridTaylorD (i : Fin 72) : ℤ := (66:ℤ)^2/(gridTaylorL i:ℤ)
def gridTaylorPartner (i : Fin 72) : ℤ := -(gridTaylorD i/gridTaylorT i)

theorem gridTaylorSpecs_valid : ∀ i : Fin 72,
    0<gridTaylorQ i ∧ gridTaylorQ i∣66 ∧ gridTaylorT i≠0 ∧
      (gridTaylorL i:ℤ)*gridTaylorD i=(66:ℤ)^2 ∧ gridTaylorT i∣gridTaylorD i := by decide

def gridTaylorCoefficient (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 72) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar (2*m) (gridTaylorL i) ((gridTaylorT i:ℝ)/66)
    (root 33 f (gridTaylorQ i)*ε*I^(2*m)) n s

def gridTaylorError (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 72) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError (2*m) (fullCoefficients (twisted f (gridTaylorQ i)) (2*m))
    (gridTaylorL i) ((gridTaylorT i:ℝ)/66) (root 33 f (gridTaylorQ i)*ε*I^(2*m)) (M+1)) s

theorem grid_ramanujan_rows_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (i : Fin 72) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  have hv:=gridTaylorSpecs_valid i
  have hr : (gridTaylorT i:ℝ)/66≠0:=div_ne_zero (by exact_mod_cast hv.2.2.1) (by norm_num)
  have hL : 0<gridTaylorL i:=Nat.lcm_pos (by decide) (pow_pos hv.1 _)
  obtain ⟨B,hB⟩:=grid_ramanujan_taylor_of_laws m hf hlaw (gridTaylorQ i) hv.1 _ hr
  refine ⟨B,?_⟩
  intro M
  constructor
  · intro s hs
    unfold gridTaylorError gridTaylorL
    apply (hB (M+1)).1 s
    change B-((M+1:ℕ):ℝ)<s.re
    change B-((M:ℝ)+1)<s.re at hs
    simpa only [Nat.cast_add,Nat.cast_one] using hs
  · intro s hs
    have hm:=(hB (M+1)).2 s hs
    rw [ramanujanTaylorSum_split] at hm
    rw [show Nat.lcm 33 ((gridTaylorQ i)^2)=gridTaylorL i from rfl] at hm
    have htrans:=ramanujanAdditive_grid (2*m) f (by decide : 0<66) hv.1 hv.2.1 (gridTaylorT i) s
    norm_num only [Nat.cast_ofNat] at htrans
    rw [htrans] at hm
    have hp:=fricke_grid_partner (by decide : 0<66) hL hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
    norm_num only [Nat.cast_ofNat] at hp
    rw [hp] at hm
    have hgrid (t : ℤ) (w : ℂ) :
        ramanujanAdditive (2*m) f (gridTaylorQ i) ((t:ℝ)/66) w=
          ∑ j∈FinitenessRamanujanSum.residues (gridTaylorQ i),
            grid (2*m) f 66 (t+(j:ℤ)*(66/gridTaylorQ i:ℕ)) w := by
      simpa only [Nat.cast_ofNat] using
        ramanujanAdditive_grid (2*m) f (by decide : 0<66) hv.1 hv.2.1 t w
    simp_rw [hgrid] at hm
    simp only [Nat.cast_add,Nat.cast_one] at hm
    unfold gridTaylorCoefficient gridTaylorError gridTaylorPartner gridSum
    linear_combination hm

/-- All selected Ramanujan rows share a half-plane and the specified sign. -/
theorem grid_ramanujan_system_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∀ i : Fin 72, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 66 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  choose b hb using grid_ramanujan_rows_of_laws m hf hlaw
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 72) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

#print axioms gridTaylorSpecs_valid
#print axioms grid_ramanujan_rows_of_laws
#print axioms grid_ramanujan_system_of_laws
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
