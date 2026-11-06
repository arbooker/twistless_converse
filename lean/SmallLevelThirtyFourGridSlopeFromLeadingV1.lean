module
public import SmallLevelThirtyFourGridTheoryV4
public import SmallLevelThirtyFourUnitMMMTheoryV4
public import SmallLevelThirtyFourUnitMMPTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex

def slopeFromLeading {r : ℕ} (J : Fin r→GridSource) (L : Fin r→ℂ)
    (w : Fin 510→ℂ) (i : Fin r) : ℂ :=
  match J i with
  | .word j => (gridGroupDerivative j:ℂ)*(w (gridGroupIndex j)-L i)
  | .taylor j => taylorSlope j*(gridSample (gridTaylorQ j) (gridTaylorT j) w-L i)
  | .entire _ => 0
  | .hecke _ => 0
  | .infinity _ => 0

theorem slopeFromLeading_actual {r : ℕ} (J : Fin r→GridSource)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 510→ℂ) (i : Fin r) :
    slopeFromLeading J (fun j => gridLeadingRows m f ε s w (J j)) w i=
      slopeRows m f ε 1 s w (J i) := by
  cases h : J i with
  | word j =>
    simp only [slopeFromLeading,h,gridLeadingRows,gridGroupLeading,slopeRows,pow_one]
    ring
  | taylor j =>
    simp only [slopeFromLeading,h,gridLeadingRows,gridRamanujanLeading,slopeRows,pow_one]
    ring
  | entire j => simp only [slopeFromLeading,h,slopeRows]
  | hecke j => simp only [slopeFromLeading,h,slopeRows]
  | infinity j => simp only [slopeFromLeading,h,slopeRows]

#print axioms slopeFromLeading_actual
end SmallLevelThirtyFourGrid

namespace SmallLevelThirtyFourUnitMMM
open Complex SmallLevelThirtyFourGrid SmallLevelPrimeRates

def sourceSlopeRows (X Y Z W a b : ℂ) (w : Fin 510→ℂ) : Fin 546→ℂ :=
  slopeFromLeading selectedSource (sourceRows X Y Z W a b w) w

theorem scaled_sourceSlopeRows_actual (m : ℕ) (f : ℕ→ℂ) (ε u v s : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 510→ℂ) (i : Fin 546) :
    sourceSlopeRows (u*parameter 2 m s) (parameter 3 m s) (v*parameter 17 m s)
      (parameter 5 m s) (badParameter f 3) (badParameter f 5) w i=
      slopeRows m f ε 1 s w (selectedSource i) := by
  have he : sourceRows (u*parameter 2 m s) (parameter 3 m s) (v*parameter 17 m s)
      (parameter 5 m s) (badParameter f 3) (badParameter f 5) w=
      (fun j => gridLeadingRows m f ε s w (selectedSource j)) :=
    funext (fun j => scaled_sourceRows_actual m f ε u v s hu hv hη h₂ h₁₇ w j)
  unfold sourceSlopeRows
  rw [he]
  exact slopeFromLeading_actual selectedSource m f ε s w i

#print axioms scaled_sourceSlopeRows_actual
end SmallLevelThirtyFourUnitMMM

namespace SmallLevelThirtyFourUnitMMP
open Complex SmallLevelThirtyFourGrid SmallLevelPrimeRates

def sourceSlopeRows (X Y Z W a b : ℂ) (w : Fin 510→ℂ) : Fin 546→ℂ :=
  slopeFromLeading selectedSource (sourceRows X Y Z W a b w) w

theorem scaled_sourceSlopeRows_actual (m : ℕ) (f : ℕ→ℂ) (ε u v s : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 510→ℂ) (i : Fin 546) :
    sourceSlopeRows (u*parameter 2 m s) (parameter 3 m s) (v*parameter 17 m s)
      (parameter 5 m s) (badParameter f 3) (badParameter f 5) w i=
      slopeRows m f ε 1 s w (selectedSource i) := by
  have he : sourceRows (u*parameter 2 m s) (parameter 3 m s) (v*parameter 17 m s)
      (parameter 5 m s) (badParameter f 3) (badParameter f 5) w=
      (fun j => gridLeadingRows m f ε s w (selectedSource j)) :=
    funext (fun j => scaled_sourceRows_actual m f ε u v s hu hv hη h₂ h₁₇ w j)
  unfold sourceSlopeRows
  rw [he]
  exact slopeFromLeading_actual selectedSource m f ε s w i

#print axioms scaled_sourceSlopeRows_actual
end SmallLevelThirtyFourUnitMMP
