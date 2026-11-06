module

public import SmallLevelTwentySixGridCoherentFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessNormalizedTwistProduct

def gridTaylorSpecs : Fin 71→ℕ×ℤ :=
  ![(3,-130),(3,-65),(3,-50),(3,-40),(3,-26),(3,-25),(3,-20),(3,-13),(3,-10),(3,10),(3,13),(3,20),(3,25),(3,26),(3,40),(3,50),(3,65),(3,130),(4,-25),(4,-15),(4,-13),(4,-5),(4,5),(4,13),(4,15),(4,25),(4,39),(4,45),(6,-26),(6,-25),(6,-20),(6,-13),(6,-10),(6,-2),(6,2),(6,10),(6,13),(6,20),(6,25),(6,26),(10,-6),(10,6),(12,-5),(12,-1),(12,1),(12,5),(13,-180),(13,-90),(13,-20),(13,-10),(13,10),(13,20),(13,30),(13,90),(13,180),(26,-90),(26,-10),(26,10),(26,90),(39,-20),(39,-10),(39,10),(39,20),(52,-45),(52,-5),(52,5),(52,45),(78,-10),(78,10),(156,-5),(156,5)]
def gridTaylorQ (i : Fin 71) : ℕ := (gridTaylorSpecs i).1
def gridTaylorT (i : Fin 71) : ℤ := (gridTaylorSpecs i).2
def gridTaylorL (i : Fin 71) : ℕ := Nat.lcm 26 ((gridTaylorQ i)^2)
def gridTaylorD (i : Fin 71) : ℤ := (780:ℤ)^2/(gridTaylorL i:ℤ)
def gridTaylorPartner (i : Fin 71) : ℤ := -(gridTaylorD i/gridTaylorT i)

theorem gridTaylorSpecs_valid : ∀ i : Fin 71,
    0<gridTaylorQ i ∧ gridTaylorQ i∣780 ∧ gridTaylorT i≠0 ∧
      (gridTaylorL i:ℤ)*gridTaylorD i=(780:ℤ)^2 ∧ gridTaylorT i∣gridTaylorD i := by decide

def gridTaylorCoefficient (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 71) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar (2*m) (gridTaylorL i) ((gridTaylorT i:ℝ)/780)
    (root 26 f (gridTaylorQ i)*ε*I^(2*m)) n s

def gridTaylorError (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 71) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError (2*m) (fullCoefficients (twisted f (gridTaylorQ i)) (2*m))
    (gridTaylorL i) ((gridTaylorT i:ℝ)/780) (root 26 f (gridTaylorQ i)*ε*I^(2*m)) (M+1)) s

theorem grid_ramanujan_rows_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (i : Fin 71) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  have hv:=gridTaylorSpecs_valid i
  have hr : (gridTaylorT i:ℝ)/780≠0:=div_ne_zero (by exact_mod_cast hv.2.2.1) (by norm_num)
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
    rw [show Nat.lcm 26 ((gridTaylorQ i)^2)=gridTaylorL i from rfl] at hm
    have htrans:=ramanujanAdditive_grid (2*m) f (by decide : 0<780) hv.1 hv.2.1 (gridTaylorT i) s
    norm_num only [Nat.cast_ofNat] at htrans
    rw [htrans] at hm
    have hp:=fricke_grid_partner (by decide : 0<780) hL hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
    norm_num only [Nat.cast_ofNat] at hp
    rw [hp] at hm
    have hgrid (t : ℤ) (w : ℂ) :
        ramanujanAdditive (2*m) f (gridTaylorQ i) ((t:ℝ)/780) w=
          ∑ j∈FinitenessRamanujanSum.residues (gridTaylorQ i),
            grid (2*m) f 780 (t+(j:ℤ)*(780/gridTaylorQ i:ℕ)) w := by
      simpa only [Nat.cast_ofNat] using
        ramanujanAdditive_grid (2*m) f (by decide : 0<780) hv.1 hv.2.1 t w
    simp_rw [hgrid] at hm
    simp only [Nat.cast_add,Nat.cast_one] at hm
    unfold gridTaylorCoefficient gridTaylorError gridTaylorPartner gridSum
    linear_combination hm

/-- All selected Ramanujan rows share a half-plane and the specified sign. -/
theorem grid_ramanujan_system_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∀ i : Fin 71, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 780 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  choose b hb using grid_ramanujan_rows_of_laws m hf hlaw
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 71) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
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
end SmallLevelTwentySixGrid
