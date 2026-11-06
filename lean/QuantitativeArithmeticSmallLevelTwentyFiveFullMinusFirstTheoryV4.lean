module

public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModelTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveFullMinusLeadingTheoryV4
public import SmallLevelUniversalFactoredFirstShiftV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.FullMinusFirst. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveFullMinusFirstSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FullMinusFirst
open Complex Matrix Filter QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

def physicalRow (i : Fin 4450) : Row := CuspMinusLaurent.physicalPart (AuxMinusLaurent.actual i.val)
def sourceRow (i : Fin 4450) : SourceRow := .physical (physicalRow i)
abbrev RowIndex := Fin 4450 ⊕ Fin 68

def leadingMatrix (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : Matrix RowIndex (Fin 1050) ℂ :=
  augmentedMatrix sourceRow AuxMinusLaurent.freeCoordinate m f ε s

def shiftMatrix (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix RowIndex (Fin 1050) ℂ :=
  augmentedShiftMatrix (κ := Fin 68) sourceRow m f ε n s

theorem original_germs
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(-1)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge AuxMinusLaurent.basis
      AuxMinusLaurent.freeCoordinate m f z (gridVector 1050 (2*m) f z)) :
    ∃ (B : ℝ) (H : ℕ → ℂ → RowIndex → ℂ),
      (∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z) ∧
      ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
        (fun z => ∑ j, leadingMatrix m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
          (fun z => H n z i+∑ a∈Finset.range n, ∑ j,
            shiftMatrix m f ε a z i j*G (z+((a:ℂ)+1)) j) := by
  classical
  have hp (i : Fin 4450) : normalizedPoly (rawSourcePoly (-1) (.physical (physicalRow i)))=AuxMinusLaurent.source i.val := by
    have h := AuxMinusLaurent.all_actual_source ⟨i.val,by omega⟩
    rw [FullMinusLeading.source_physical i] at h
    exact h
  have hq (i : Fin 4450) : normalizedPoly (rawTailPoly (.physical (physicalRow i)))=AuxMinusLaurent.tail i.val := by
    have h := AuxMinusLaurent.all_actual_tail ⟨i.val,by omega⟩
    rw [FullMinusLeading.source_physical i] at h
    exact h
  obtain ⟨B,H,hH,hrow⟩ := selected_physical_germs AuxMinusLaurent.basis
    AuxMinusLaurent.freeCoordinate AuxMinusLaurent.basis_periodic physicalRow (-1)
    (fun i => AuxMinusLaurent.source i.val) (fun i => AuxMinusLaurent.tail i.val) hp hq
    (fun i => AuxMinusLaurent.all_source_zero ⟨i.val,by omega⟩)
    (fun i => AuxMinusLaurent.all_tail_zero ⟨i.val,by omega⟩)
    hm hf ε hε hlaw (by simpa using hχ) BG G (fun j z => (hG j z).meromorphicAt) hGF
  have hg := continued_free_zero AuxMinusLaurent.basis AuxMinusLaurent.freeCoordinate
    AuxMinusLaurent.basis_free_coordinate m f BG G hG hGF
  have ha (z : ℂ) (v : Fin 1050 → ℂ) (i : RowIndex) :
      (∑ j,leadingMatrix m f ε z i j*v j)=augmentedLeading sourceRow AuxMinusLaurent.freeCoordinate m f ε z v i :=
    congrFun (augmentedMatrix_mulVec sourceRow AuxMinusLaurent.freeCoordinate m f ε z v) i
  have hc (n : ℕ) (z : ℂ) (v : Fin 1050 → ℂ) (i : RowIndex) :
      (∑ j,shiftMatrix m f ε n z i j*v j)=augmentedShifted sourceRow m f ε n z v i :=
    congrFun (augmentedShiftMatrix_mulVec (κ := Fin 68) sourceRow m f ε n z v) i
  refine ⟨B,(fun n z => Sum.elim (H n z) (fun _ => 0)),?_,?_⟩
  · intro n i z hz
    cases i with
    | inl i => exact hH n i z hz
    | inr i => exact analyticAt_const
  · intro n i x hx
    cases i with
    | inl i =>
      simpa only [ha,hc,augmentedLeading,augmentedShifted,Sum.elim_inl,sourceRow,
        sourceLeading,sourceShifted] using hrow n i x hx
    | inr i =>
      filter_upwards [] with z
      simp only [ha,hc,augmentedLeading,augmentedShifted,Sum.elim_inr,hg,
        Finset.sum_const_zero,add_zero]
#print axioms original_germs
end QuantitativeArithmeticSmallLevelTwentyFive.FullMinusFirst
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveFullMinusFirstSyzygyV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FullMinusFirst
open Complex Matrix QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector

theorem original_first_shift_allowed
    {ρ : Type*} {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(-1)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge AuxMinusLaurent.basis
      AuxMinusLaurent.freeCoordinate m f z (gridVector 1050 (2*m) f z))
    (L : ℂ → Matrix ρ RowIndex ℂ)
    (hL : ∀ z r i, AnalyticAt ℂ (fun w => L w r i) z)
    (hLA : ∀ z, L z*leadingMatrix m f ε z=0)
    (s : ℂ) (v : Fin 1050 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ,0<n → (s+n)≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hweight : ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)) :
    (L (s-1)*shiftMatrix m f ε 0 (s-1))*ᵥv=0 := by
  obtain ⟨B,H,hH,hrow⟩ := original_germs hm hf ε hε hlaw hχ BG G hG hGF
  exact IsLeadingVector.allowed_first_shift B G (leadingMatrix m f ε) (shiftMatrix m f ε)
    H L hG (fun n z i j => augmentedShiftMatrix_analytic sourceRow m f ε n z i j)
    hH hL hLA hrow s ((2*m:ℕ):ℂ) v hv hshift hweight
    (fun n z hz i j => augmentedShift_zero_at_weight sourceRow m f ε (-1)
      (by simpa using hχ) n z hz i j)

theorem original_regularized_first_shift
    {ρ : Type*} {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(-1)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge AuxMinusLaurent.basis
      AuxMinusLaurent.freeCoordinate m f z (gridVector 1050 (2*m) f z))
    (L : ℂ → Matrix ρ RowIndex ℂ)
    (hL : ∀ z r i, AnalyticAt ℂ (fun w => L w r i) z)
    (hLA : ∀ z, L z*leadingMatrix m f ε z=0)
    (s : ℂ) (v : Fin 1050 → ℂ)
    (hv : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*G z j) s v)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (D : ℂ → Matrix ρ (Fin 1050) ℂ)
    (hD : ∀ r j,AnalyticAt ℂ (fun z => D z r j) s)
    (hfactor : ∀ z r j,(L (z-1)*shiftMatrix m f ε 0 (z-1)) r j=
      (z-((2*m:ℕ):ℂ))*D z r j) : D s*ᵥv=0 := by
  obtain ⟨B,H,hH,hrow⟩ := original_germs hm hf ε hε hlaw hχ BG G hG hGF
  exact IsLeadingVector.factored_first_shift B G (leadingMatrix m f ε) (shiftMatrix m f ε)
    H L hG (fun n z i j => augmentedShiftMatrix_analytic sourceRow m f ε n z i j)
    hH hL hLA hrow s hshift (fun z => z-((2*m:ℕ):ℂ)) D hD hfactor v hv
#print axioms original_first_shift_allowed
#print axioms original_regularized_first_shift
end QuantitativeArithmeticSmallLevelTwentyFive.FullMinusFirst
end
end
