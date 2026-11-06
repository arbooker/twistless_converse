module

public import QuantitativeArithmeticOriginalHeckeGridV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySevenPhysicalReconstructionV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySevenHeckeSource. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceModelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
open SmallLevelAdditive QuantitativeArithmeticOriginalHeckeGrid
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

structure Spec where
  source : ℕ
  Q : ℕ
  p : ℕ
  j : ℤ
  sample : Fin p → ℕ
  first : ℕ
  second : ℕ

def Valid (point : ℕ → ℚ) (r : Spec) : Prop :=
  0<r.Q ∧ r.p.Prime ∧ r.p∣r.Q ∧ (r.p=2 ∨ r.p=3 ∨ r.p=5 ∨ r.p=7) ∧
  (∀ t : Fin r.p, point (r.sample t)=((r.j+(t.val:ℤ)*(r.Q/r.p:ℕ))%(r.Q:ℤ):ℤ)/(r.Q:ℚ)) ∧
  point r.first=(((r.p:ℤ)*r.j)%(r.Q:ℤ):ℤ)/(r.Q:ℚ) ∧
  point r.second=(((r.p:ℤ)^2*r.j)%(r.Q:ℤ):ℤ)/(r.Q:ℚ)

def leading (r : Spec) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) (v : ℕ → ℂ) : ℂ :=
  (∑ t : Fin r.p, v (r.sample t))-
    ((Real.sqrt r.p:ℂ)*f r.p)*(r.p:ℂ)^((m:ℂ)-s)*v r.first+
    if r.p∣27 then 0 else ((r.p:ℂ)^((m:ℂ)-s))^2*v r.second

def rate (p : ℕ) (x y z w : ℂ) : ℂ := if p=2 then x else if p=3 then y else if p=5 then z else w
def eigenvalue (p : ℕ) (a b c : ℂ) : ℂ := if p=2 then a else if p=3 then 0 else if p=5 then b else c

def formalLeading (r : Spec) (x y z w a b c : ℂ) (v : ℕ → ℂ) : ℂ :=
  (∑ t : Fin r.p, v (r.sample t))-
    eigenvalue r.p a b c*(rate r.p x y z w)⁻¹*v r.first+
    if r.p=3 then 0 else ((rate r.p x y z w)⁻¹)^2*v r.second

theorem point_grid (point : ℕ → ℚ) (Q : ℕ) (hQ : 0<Q) (n : ℕ) (j : ℤ)
    (h : point n=((j%(Q:ℤ):ℤ):ℚ)/(Q:ℚ)) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    original (2*m) f (point n:ℝ) s=grid (2*m) f Q j s := by
  have he : (point n:ℝ)=((j%(Q:ℤ):ℤ):ℝ)/(Q:ℝ) := by exact_mod_cast h
  rw [he,← grid_mod (2*m) f hQ j s]
  rfl

theorem leading_grid (point : ℕ → ℚ) (r : Spec) (hr : Valid point r)
    (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    leading r m f s (fun n => original (2*m) f (point n:ℝ) s)=
      heckeLeading 27 r.Q m f r.p r.j s := by
  rcases hr with ⟨hQ,_,_,_,hs,h1,h2⟩
  have hsum : (∑ t : Fin r.p, original (2*m) f (point (r.sample t):ℝ) s)=
      ∑ t∈Finset.range r.p, grid (2*m) f r.Q (r.j+(t:ℤ)*(r.Q/r.p:ℕ)) s := by
    simp_rw [point_grid point r.Q hQ _ _ (hs _)]
    exact Fin.sum_univ_eq_sum_range (fun t : ℕ => grid (2*m) f r.Q (r.j+(t:ℤ)*(r.Q/r.p:ℕ)) s) r.p
  unfold leading heckeLeading
  dsimp only []
  rw [hsum,point_grid point r.Q hQ _ _ h1,point_grid point r.Q hQ _ _ h2]

theorem original_leading (point : ℕ → ℚ) (r : Spec) (hr : Valid point r)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      leading r m f s (fun n => original (2*m) f (point n:ℝ) s)=0 := by
  obtain ⟨B,hB⟩ := original_hecke_grid 27 r.Q hr.1 hm hf hr.2.1 hr.2.2.1
  exact ⟨B,fun s hs => (leading_grid point r hr m f s).trans (hB r.j s hs)⟩

theorem inverse_primeRate (p : ℕ) (hp : 0<p) (m : ℕ) (s : ℂ) :
    (primeRate p m s)⁻¹=(p:ℂ)^((m:ℂ)-s) := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp0]
  simp only [primeRate,Complex.ofReal_natCast]
  rw [← Complex.exp_neg,← Complex.natCast_log]
  congr 1
  ring

theorem physical_formal (r : Spec) (hp : r.p=2 ∨ r.p=3 ∨ r.p=5 ∨ r.p=7)
    (m : ℕ) (f : ℕ → ℂ) (h3 : f 3=0) (s : ℂ) (v : ℕ → ℂ) :
    formalLeading r (primeRate 2 m s) (primeRate 3 m s) (primeRate 5 m s) (primeRate 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7) v=leading r m f s v := by
  have h2 : (primeRate 2 m s)⁻¹=(2:ℂ)^((m:ℂ)-s) := by simpa using inverse_primeRate 2 (by decide) m s
  have h5 : (primeRate 5 m s)⁻¹=(5:ℂ)^((m:ℂ)-s) := by simpa using inverse_primeRate 5 (by decide) m s
  have h7 : (primeRate 7 m s)⁻¹=(7:ℂ)^((m:ℂ)-s) := by simpa using inverse_primeRate 7 (by decide) m s
  rcases hp with h|h|h|h <;>
    simp [formalLeading,leading,eigenvalue,rate,h,h2,h5,h7,h3]


#print axioms original_leading
#print axioms physical_formal
end QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceOriginalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
open SmallLevelAdditive QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

def physicalRow (point : ℕ → ℚ) (source : ℕ) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  eval (primeRate 2 m s) (primeRate 3 m s) (primeRate 5 m s) (primeRate 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7)
      (fun n => original (2*m) f (point n:ℝ) s) (inputs source)

/-- A checked coordinate specification and a checked sparse row identity
identify a genuine original Hecke equation, including at f₂=0. -/
theorem original_source (point : ℕ → ℚ) (r : Spec) (hr : Valid point r)
    (hrow : ∀ x y z w a b c : ℂ, ∀ v : ℕ → ℂ,
      eval x y z w a b c v (inputs r.source)=formalLeading r x y z w a b c v)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → physicalRow point r.source m f s=0 := by
  have h3 : f 3=0 := FinitenessOriginalTwistLocal.bad_parameter_zero hf.toEulerData (by decide) (by decide)
  obtain ⟨B,hB⟩ := original_leading point r hr hm hf
  refine ⟨B,?_⟩
  intro s hs
  unfold physicalRow
  rw [hrow,physical_formal r hr.2.2.2.1 m f h3]
  exact hB s hs
#print axioms original_source
end QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenSourcePointsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
open QuantitativeArithmeticSevenLaurentRows
def pointPart0 : ℕ → ℚ
  | 0 => (25/27:ℚ)
  | 1 => (26/27:ℚ)
  | 2 => (0/1:ℚ)
  | 3 => (1/2:ℚ)
  | 4 => (1/54:ℚ)
  | 5 => (68/135:ℚ)
  | 6 => (1/9:ℚ)
  | 7 => (23/45:ℚ)
  | 8 => (8/27:ℚ)
  | 9 => (139/270:ℚ)
  | 10 => (7/90:ℚ)
  | 11 => (11/135:ℚ)
  | 12 => (7/18:ℚ)
  | 13 => (4/45:ℚ)
  | 14 => (11/27:ℚ)
  | 15 => (5/54:ℚ)
  | 16 => (4/9:ℚ)
  | 17 => (25/54:ℚ)
  | 18 => (4/27:ℚ)
  | 19 => (7/15:ℚ)
  | 20 => (1/6:ℚ)
  | 21 => (64/135:ℚ)
  | 22 => (7/27:ℚ)
  | 23 => (43/90:ℚ)
  | 24 => (13/27:ℚ)
  | 25 => (131/270:ℚ)
  | 26 => (19/27:ℚ)
  | 27 => (22/45:ℚ)
  | 28 => (8/9:ℚ)
  | 29 => (67/135:ℚ)
  | 30 => (53/54:ℚ)
  | 31 => (14/27:ℚ)
  | _ => 0
def pointPart1 : ℕ → ℚ
  | 0 => (1/27:ℚ)
  | 1 => (5/9:ℚ)
  | 2 => (1/18:ℚ)
  | 3 => (31/54:ℚ)
  | 4 => (8/135:ℚ)
  | 5 => (2/3:ℚ)
  | 6 => (1/15:ℚ)
  | 7 => (23/27:ℚ)
  | 8 => (19/270:ℚ)
  | 9 => (137/270:ℚ)
  | 10 => (17/18:ℚ)
  | 11 => (131/135:ℚ)
  | 12 => (29/54:ℚ)
  | 13 => (263/270:ℚ)
  | 14 => (17/27:ℚ)
  | 15 => (44/45:ℚ)
  | 16 => (1/45:ℚ)
  | 17 => (4/135:ℚ)
  | 18 => (1/3:ℚ)
  | 19 => (1/30:ℚ)
  | 20 => (47/90:ℚ)
  | 21 => (20/27:ℚ)
  | 22 => (71/135:ℚ)
  | 23 => (5/6:ℚ)
  | 24 => (8/15:ℚ)
  | 25 => (49/54:ℚ)
  | 26 => (16/27:ℚ)
  | 27 => (41/45:ℚ)
  | 28 => (11/18:ℚ)
  | 29 => (124/135:ℚ)
  | 30 => (83/90:ℚ)
  | 31 => (251/270:ℚ)
  | _ => 0
def pointPart2 : ℕ → ℚ
  | 0 => (14/15:ℚ)
  | 1 => (127/135:ℚ)
  | 2 => (23/54:ℚ)
  | 3 => (11/270:ℚ)
  | 4 => (2/45:ℚ)
  | 5 => (7/9:ℚ)
  | 6 => (7/135:ℚ)
  | 7 => (47/54:ℚ)
  | 8 => (2/27:ℚ)
  | 9 => (7/54:ℚ)
  | 10 => (128/135:ℚ)
  | 11 => (2/9:ℚ)
  | 12 => (43/45:ℚ)
  | 13 => (259/270:ℚ)
  | 14 => (2/135:ℚ)
  | 15 => (29/30:ℚ)
  | 16 => (10/27:ℚ)
  | 17 => (7/270:ℚ)
  | 18 => (133/270:ℚ)
  | 19 => (1/135:ℚ)
  | 20 => (1/90:ℚ)
  | 21 => (133/135:ℚ)
  | 22 => (89/90:ℚ)
  | 23 => (134/135:ℚ)
  | 24 => (1/270:ℚ)
  | 25 => (269/270:ℚ)
  | 26 => (3/5:ℚ)
  | 27 => (2/5:ℚ)
  | 28 => (1/10:ℚ)
  | 29 => (9/10:ℚ)
  | 30 => (2/15:ℚ)
  | 31 => (13/18:ℚ)
  | _ => 0
def pointPart3 : ℕ → ℚ
  | 0 => (13/15:ℚ)
  | 1 => (5/18:ℚ)
  | 2 => (5/27:ℚ)
  | 3 => (4/5:ℚ)
  | 4 => (22/27:ℚ)
  | 5 => (1/5:ℚ)
  | 6 => (91/270:ℚ)
  | 7 => (181/270:ℚ)
  | 8 => (89/270:ℚ)
  | 9 => (179/270:ℚ)
  | 10 => (46/135:ℚ)
  | 11 => (91/135:ℚ)
  | 12 => (44/135:ℚ)
  | 13 => (89/135:ℚ)
  | 14 => (31/90:ℚ)
  | 15 => (61/90:ℚ)
  | 16 => (29/90:ℚ)
  | 17 => (59/90:ℚ)
  | 18 => (47/135:ℚ)
  | 19 => (92/135:ℚ)
  | 20 => (43/135:ℚ)
  | 21 => (88/135:ℚ)
  | 22 => (19/54:ℚ)
  | 23 => (37/54:ℚ)
  | 24 => (17/54:ℚ)
  | 25 => (35/54:ℚ)
  | 26 => (16/45:ℚ)
  | 27 => (31/45:ℚ)
  | 28 => (14/45:ℚ)
  | 29 => (29/45:ℚ)
  | 30 => (11/30:ℚ)
  | 31 => (7/10:ℚ)
  | _ => 0
def pointPart4 : ℕ → ℚ
  | 0 => (3/10:ℚ)
  | 1 => (19/30:ℚ)
  | 2 => (17/45:ℚ)
  | 3 => (32/45:ℚ)
  | 4 => (13/45:ℚ)
  | 5 => (28/45:ℚ)
  | 6 => (11/15:ℚ)
  | 7 => (4/15:ℚ)
  | 8 => (41/54:ℚ)
  | 9 => (13/54:ℚ)
  | 10 => (13/30:ℚ)
  | 11 => (23/30:ℚ)
  | 12 => (7/30:ℚ)
  | 13 => (17/30:ℚ)
  | 14 => (11/54:ℚ)
  | 15 => (109/270:ℚ)
  | 16 => (163/270:ℚ)
  | 17 => (217/270:ℚ)
  | 18 => (53/270:ℚ)
  | 19 => (107/270:ℚ)
  | 20 => (161/270:ℚ)
  | 21 => (43/54:ℚ)
  | 22 => (28/135:ℚ)
  | 23 => (82/135:ℚ)
  | 24 => (109/135:ℚ)
  | 25 => (26/135:ℚ)
  | 26 => (53/135:ℚ)
  | 27 => (107/135:ℚ)
  | 28 => (19/90:ℚ)
  | 29 => (37/90:ℚ)
  | 30 => (73/90:ℚ)
  | 31 => (17/90:ℚ)
  | _ => 0
def pointPart5 : ℕ → ℚ
  | 0 => (53/90:ℚ)
  | 1 => (71/90:ℚ)
  | 2 => (29/135:ℚ)
  | 3 => (56/135:ℚ)
  | 4 => (83/135:ℚ)
  | 5 => (52/135:ℚ)
  | 6 => (79/135:ℚ)
  | 7 => (106/135:ℚ)
  | 8 => (19/45:ℚ)
  | 9 => (37/45:ℚ)
  | 10 => (8/45:ℚ)
  | 11 => (26/45:ℚ)
  | 12 => (7/45:ℚ)
  | 13 => (34/45:ℚ)
  | 14 => (11/45:ℚ)
  | 15 => (38/45:ℚ)
  | 16 => (23/135:ℚ)
  | 17 => (113/135:ℚ)
  | 18 => (22/135:ℚ)
  | 19 => (112/135:ℚ)
  | 20 => (31/270:ℚ)
  | 21 => (61/270:ℚ)
  | 22 => (121/270:ℚ)
  | 23 => (151/270:ℚ)
  | 24 => (211/270:ℚ)
  | 25 => (241/270:ℚ)
  | 26 => (29/270:ℚ)
  | 27 => (59/270:ℚ)
  | 28 => (119/270:ℚ)
  | 29 => (149/270:ℚ)
  | 30 => (209/270:ℚ)
  | 31 => (239/270:ℚ)
  | _ => 0
def pointPart6 : ℕ → ℚ
  | 0 => (16/135:ℚ)
  | 1 => (31/135:ℚ)
  | 2 => (61/135:ℚ)
  | 3 => (76/135:ℚ)
  | 4 => (121/135:ℚ)
  | 5 => (14/135:ℚ)
  | 6 => (59/135:ℚ)
  | 7 => (74/135:ℚ)
  | 8 => (104/135:ℚ)
  | 9 => (119/135:ℚ)
  | 10 => (11/90:ℚ)
  | 11 => (41/90:ℚ)
  | 12 => (49/90:ℚ)
  | 13 => (79/90:ℚ)
  | 14 => (17/135:ℚ)
  | 15 => (32/135:ℚ)
  | 16 => (62/135:ℚ)
  | 17 => (77/135:ℚ)
  | 18 => (122/135:ℚ)
  | 19 => (13/135:ℚ)
  | 20 => (58/135:ℚ)
  | 21 => (73/135:ℚ)
  | 22 => (103/135:ℚ)
  | 23 => (118/135:ℚ)
  | 24 => (13/90:ℚ)
  | 25 => (23/90:ℚ)
  | 26 => (67/90:ℚ)
  | 27 => (77/90:ℚ)
  | 28 => (41/135:ℚ)
  | 29 => (94/135:ℚ)
  | 30 => (37/270:ℚ)
  | 31 => (73/270:ℚ)
  | _ => 0
def pointPart7 : ℕ → ℚ
  | 0 => (127/270:ℚ)
  | 1 => (199/270:ℚ)
  | 2 => (253/270:ℚ)
  | 3 => (17/270:ℚ)
  | 4 => (71/270:ℚ)
  | 5 => (143/270:ℚ)
  | 6 => (197/270:ℚ)
  | 7 => (233/270:ℚ)
  | 8 => (19/135:ℚ)
  | 9 => (37/135:ℚ)
  | 10 => (98/135:ℚ)
  | 11 => (116/135:ℚ)
  | 12 => (38/135:ℚ)
  | 13 => (101/135:ℚ)
  | 14 => (34/135:ℚ)
  | 15 => (97/135:ℚ)
  | 16 => (41/270:ℚ)
  | 17 => (101/270:ℚ)
  | 18 => (191/270:ℚ)
  | 19 => (221/270:ℚ)
  | 20 => (49/270:ℚ)
  | 21 => (79/270:ℚ)
  | 22 => (169/270:ℚ)
  | 23 => (229/270:ℚ)
  | 24 => (86/135:ℚ)
  | 25 => (49/135:ℚ)
  | 26 => (13/270:ℚ)
  | 27 => (43/270:ℚ)
  | 28 => (67/270:ℚ)
  | 29 => (97/270:ℚ)
  | 30 => (103/270:ℚ)
  | 31 => (157/270:ℚ)
  | _ => 0
def pointPart8 : ℕ → ℚ
  | 0 => (187/270:ℚ)
  | 1 => (193/270:ℚ)
  | 2 => (223/270:ℚ)
  | 3 => (247/270:ℚ)
  | 4 => (23/270:ℚ)
  | 5 => (47/270:ℚ)
  | 6 => (77/270:ℚ)
  | 7 => (83/270:ℚ)
  | 8 => (113/270:ℚ)
  | 9 => (167/270:ℚ)
  | 10 => (173/270:ℚ)
  | 11 => (203/270:ℚ)
  | 12 => (227/270:ℚ)
  | 13 => (257/270:ℚ)
  | 14 => (121/126:ℚ)
  | 15 => (13/14:ℚ)
  | 16 => (349/378:ℚ)
  | 17 => (32/63:ℚ)
  | 18 => (97/189:ℚ)
  | 19 => (65/126:ℚ)
  | 20 => (5/63:ℚ)
  | 21 => (16/189:ℚ)
  | 22 => (89/189:ℚ)
  | 23 => (10/21:ℚ)
  | 24 => (181/378:ℚ)
  | 25 => (61/126:ℚ)
  | 26 => (92/189:ℚ)
  | 27 => (31/63:ℚ)
  | 28 => (4/63:ℚ)
  | 29 => (13/189:ℚ)
  | 30 => (184/189:ℚ)
  | 31 => (41/42:ℚ)
  | _ => 0
def pointPart9 : ℕ → ℚ
  | 0 => (185/189:ℚ)
  | 1 => (5/189:ℚ)
  | 2 => (2/63:ℚ)
  | 3 => (13/378:ℚ)
  | 4 => (197/378:ℚ)
  | 5 => (11/21:ℚ)
  | 6 => (100/189:ℚ)
  | 7 => (173/189:ℚ)
  | 8 => (58/63:ℚ)
  | 9 => (176/189:ℚ)
  | 10 => (59/63:ℚ)
  | 11 => (5/126:ℚ)
  | 12 => (8/189:ℚ)
  | 13 => (1/21:ℚ)
  | 14 => (20/21:ℚ)
  | 15 => (181/189:ℚ)
  | 16 => (1/63:ℚ)
  | 17 => (4/189:ℚ)
  | 18 => (365/378:ℚ)
  | 19 => (61/63:ℚ)
  | 20 => (187/378:ℚ)
  | 21 => (94/189:ℚ)
  | 22 => (1/42:ℚ)
  | 23 => (2/189:ℚ)
  | 24 => (5/378:ℚ)
  | 25 => (62/63:ℚ)
  | 26 => (373/378:ℚ)
  | 27 => (95/189:ℚ)
  | 28 => (191/378:ℚ)
  | 29 => (29/378:ℚ)
  | 30 => (1/14:ℚ)
  | 31 => (193/378:ℚ)
  | _ => 0
def pointPart10 : ℕ → ℚ
  | 0 => (185/378:ℚ)
  | 1 => (1/378:ℚ)
  | 2 => (377/378:ℚ)
  | 3 => (1/189:ℚ)
  | 4 => (188/189:ℚ)
  | 5 => (1/126:ℚ)
  | 6 => (125/126:ℚ)
  | 7 => (187/189:ℚ)
  | 8 => (2/21:ℚ)
  | 9 => (19/21:ℚ)
  | 10 => (5/7:ℚ)
  | 11 => (2/7:ℚ)
  | 12 => (1/7:ℚ)
  | 13 => (6/7:ℚ)
  | 14 => (4/7:ℚ)
  | 15 => (3/7:ℚ)
  | 16 => (127/378:ℚ)
  | 17 => (253/378:ℚ)
  | 18 => (125/378:ℚ)
  | 19 => (251/378:ℚ)
  | 20 => (64/189:ℚ)
  | 21 => (127/189:ℚ)
  | 22 => (62/189:ℚ)
  | 23 => (125/189:ℚ)
  | 24 => (43/126:ℚ)
  | 25 => (85/126:ℚ)
  | 26 => (41/126:ℚ)
  | 27 => (83/126:ℚ)
  | 28 => (65/189:ℚ)
  | 29 => (128/189:ℚ)
  | 30 => (61/189:ℚ)
  | 31 => (124/189:ℚ)
  | _ => 0
def pointPart11 : ℕ → ℚ
  | 0 => (22/63:ℚ)
  | 1 => (43/63:ℚ)
  | 2 => (20/63:ℚ)
  | 3 => (41/63:ℚ)
  | 4 => (5/14:ℚ)
  | 5 => (29/42:ℚ)
  | 6 => (13/42:ℚ)
  | 7 => (9/14:ℚ)
  | 8 => (23/63:ℚ)
  | 9 => (44/63:ℚ)
  | 10 => (19/63:ℚ)
  | 11 => (40/63:ℚ)
  | 12 => (8/21:ℚ)
  | 13 => (13/21:ℚ)
  | 14 => (17/42:ℚ)
  | 15 => (31/42:ℚ)
  | 16 => (11/42:ℚ)
  | 17 => (25/42:ℚ)
  | 18 => (16/21:ℚ)
  | 19 => (5/21:ℚ)
  | 20 => (17/21:ℚ)
  | 21 => (4/21:ℚ)
  | 22 => (32/189:ℚ)
  | 23 => (158/189:ℚ)
  | 24 => (31/189:ℚ)
  | 25 => (157/189:ℚ)
  | 26 => (11/63:ℚ)
  | 27 => (53/63:ℚ)
  | 28 => (10/63:ℚ)
  | 29 => (52/63:ℚ)
  | 30 => (55/378:ℚ)
  | 31 => (109/378:ℚ)
  | _ => 0
def pointPart12 : ℕ → ℚ
  | 0 => (163/378:ℚ)
  | 1 => (271/378:ℚ)
  | 2 => (325/378:ℚ)
  | 3 => (53/378:ℚ)
  | 4 => (107/378:ℚ)
  | 5 => (215/378:ℚ)
  | 6 => (269/378:ℚ)
  | 7 => (323/378:ℚ)
  | 8 => (55/189:ℚ)
  | 9 => (82/189:ℚ)
  | 10 => (109/189:ℚ)
  | 11 => (136/189:ℚ)
  | 12 => (163/189:ℚ)
  | 13 => (26/189:ℚ)
  | 14 => (53/189:ℚ)
  | 15 => (80/189:ℚ)
  | 16 => (107/189:ℚ)
  | 17 => (134/189:ℚ)
  | 18 => (19/126:ℚ)
  | 19 => (37/126:ℚ)
  | 20 => (55/126:ℚ)
  | 21 => (73/126:ℚ)
  | 22 => (109/126:ℚ)
  | 23 => (17/126:ℚ)
  | 24 => (53/126:ℚ)
  | 25 => (71/126:ℚ)
  | 26 => (89/126:ℚ)
  | 27 => (107/126:ℚ)
  | 28 => (29/189:ℚ)
  | 29 => (3/14:ℚ)
  | 30 => (83/189:ℚ)
  | 31 => (110/189:ℚ)
  | _ => 0
def pointPart13 : ℕ → ℚ
  | 0 => (137/189:ℚ)
  | 1 => (164/189:ℚ)
  | 2 => (11/14:ℚ)
  | 3 => (25/189:ℚ)
  | 4 => (52/189:ℚ)
  | 5 => (79/189:ℚ)
  | 6 => (106/189:ℚ)
  | 7 => (160/189:ℚ)
  | 8 => (37/63:ℚ)
  | 9 => (46/63:ℚ)
  | 10 => (55/63:ℚ)
  | 11 => (8/63:ℚ)
  | 12 => (17/63:ℚ)
  | 13 => (26/63:ℚ)
  | 14 => (16/63:ℚ)
  | 15 => (19/42:ℚ)
  | 16 => (25/63:ℚ)
  | 17 => (34/63:ℚ)
  | 18 => (37/42:ℚ)
  | 19 => (5/42:ℚ)
  | 20 => (29/63:ℚ)
  | 21 => (23/42:ℚ)
  | 22 => (38/63:ℚ)
  | 23 => (47/63:ℚ)
  | 24 => (43/378:ℚ)
  | 25 => (85/378:ℚ)
  | 26 => (169/378:ℚ)
  | 27 => (211/378:ℚ)
  | 28 => (295/378:ℚ)
  | 29 => (337/378:ℚ)
  | 30 => (41/378:ℚ)
  | 31 => (83/378:ℚ)
  | _ => 0
def pointPart14 : ℕ → ℚ
  | 0 => (167/378:ℚ)
  | 1 => (209/378:ℚ)
  | 2 => (293/378:ℚ)
  | 3 => (335/378:ℚ)
  | 4 => (22/189:ℚ)
  | 5 => (43/189:ℚ)
  | 6 => (85/189:ℚ)
  | 7 => (148/189:ℚ)
  | 8 => (169/189:ℚ)
  | 9 => (20/189:ℚ)
  | 10 => (41/189:ℚ)
  | 11 => (104/189:ℚ)
  | 12 => (146/189:ℚ)
  | 13 => (167/189:ℚ)
  | 14 => (29/126:ℚ)
  | 15 => (113/126:ℚ)
  | 16 => (13/126:ℚ)
  | 17 => (97/126:ℚ)
  | 18 => (23/189:ℚ)
  | 19 => (44/189:ℚ)
  | 20 => (86/189:ℚ)
  | 21 => (149/189:ℚ)
  | 22 => (170/189:ℚ)
  | 23 => (19/189:ℚ)
  | 24 => (40/189:ℚ)
  | 25 => (103/189:ℚ)
  | 26 => (145/189:ℚ)
  | 27 => (166/189:ℚ)
  | 28 => (50/63:ℚ)
  | 29 => (13/63:ℚ)
  | 30 => (31/126:ℚ)
  | 31 => (59/126:ℚ)
  | _ => 0
def pointPart15 : ℕ → ℚ
  | 0 => (101/126:ℚ)
  | 1 => (115/126:ℚ)
  | 2 => (11/126:ℚ)
  | 3 => (25/126:ℚ)
  | 4 => (67/126:ℚ)
  | 5 => (95/126:ℚ)
  | 6 => (68/189:ℚ)
  | 7 => (122/189:ℚ)
  | 8 => (67/189:ℚ)
  | 9 => (121/189:ℚ)
  | 10 => (11/189:ℚ)
  | 11 => (74/189:ℚ)
  | 12 => (116/189:ℚ)
  | 13 => (179/189:ℚ)
  | 14 => (10/189:ℚ)
  | 15 => (73/189:ℚ)
  | 16 => (115/189:ℚ)
  | 17 => (178/189:ℚ)
  | 18 => (19/378:ℚ)
  | 19 => (37/378:ℚ)
  | 20 => (73/378:ℚ)
  | 21 => (145/378:ℚ)
  | 22 => (199/378:ℚ)
  | 23 => (235/378:ℚ)
  | 24 => (289/378:ℚ)
  | 25 => (307/378:ℚ)
  | 26 => (361/378:ℚ)
  | 27 => (17/378:ℚ)
  | 28 => (71/378:ℚ)
  | 29 => (89/378:ℚ)
  | 30 => (143/378:ℚ)
  | 31 => (179/378:ℚ)
  | _ => 0
def pointPart16 : ℕ → ℚ
  | 0 => (233/378:ℚ)
  | 1 => (305/378:ℚ)
  | 2 => (341/378:ℚ)
  | 3 => (359/378:ℚ)
  | 4 => (37/189:ℚ)
  | 5 => (46/189:ℚ)
  | 6 => (118/189:ℚ)
  | 7 => (172/189:ℚ)
  | 8 => (17/189:ℚ)
  | 9 => (71/189:ℚ)
  | 10 => (143/189:ℚ)
  | 11 => (152/189:ℚ)
  | 12 => (79/126:ℚ)
  | 13 => (103/126:ℚ)
  | 14 => (23/126:ℚ)
  | 15 => (47/126:ℚ)
  | 16 => (38/189:ℚ)
  | 17 => (47/189:ℚ)
  | 18 => (101/189:ℚ)
  | 19 => (155/189:ℚ)
  | 20 => (34/189:ℚ)
  | 21 => (88/189:ℚ)
  | 22 => (142/189:ℚ)
  | 23 => (151/189:ℚ)
  | 24 => (113/378:ℚ)
  | 25 => (155/378:ℚ)
  | 26 => (239/378:ℚ)
  | 27 => (281/378:ℚ)
  | 28 => (97/378:ℚ)
  | 29 => (139/378:ℚ)
  | 30 => (223/378:ℚ)
  | 31 => (265/378:ℚ)
  | _ => 0
def pointPart17 : ℕ → ℚ
  | 0 => (50/189:ℚ)
  | 1 => (113/189:ℚ)
  | 2 => (76/189:ℚ)
  | 3 => (139/189:ℚ)
  | 4 => (58/189:ℚ)
  | 5 => (131/189:ℚ)
  | 6 => (59/189:ℚ)
  | 7 => (130/189:ℚ)
  | 8 => (25/378:ℚ)
  | 9 => (31/378:ℚ)
  | 10 => (61/378:ℚ)
  | 11 => (67/378:ℚ)
  | 12 => (79/378:ℚ)
  | 13 => (103/378:ℚ)
  | 14 => (115/378:ℚ)
  | 15 => (121/378:ℚ)
  | 16 => (151/378:ℚ)
  | 17 => (157/378:ℚ)
  | 18 => (205/378:ℚ)
  | 19 => (229/378:ℚ)
  | 20 => (241/378:ℚ)
  | 21 => (247/378:ℚ)
  | 22 => (277/378:ℚ)
  | 23 => (283/378:ℚ)
  | 24 => (313/378:ℚ)
  | 25 => (319/378:ℚ)
  | 26 => (331/378:ℚ)
  | 27 => (355/378:ℚ)
  | 28 => (367/378:ℚ)
  | 29 => (11/378:ℚ)
  | 30 => (23/378:ℚ)
  | 31 => (47/378:ℚ)
  | _ => 0
def pointPart18 : ℕ → ℚ
  | 0 => (59/378:ℚ)
  | 1 => (65/378:ℚ)
  | 2 => (95/378:ℚ)
  | 3 => (101/378:ℚ)
  | 4 => (131/378:ℚ)
  | 5 => (137/378:ℚ)
  | 6 => (149/378:ℚ)
  | 7 => (173/378:ℚ)
  | 8 => (221/378:ℚ)
  | 9 => (227/378:ℚ)
  | 10 => (257/378:ℚ)
  | 11 => (263/378:ℚ)
  | 12 => (275/378:ℚ)
  | 13 => (299/378:ℚ)
  | 14 => (311/378:ℚ)
  | 15 => (317/378:ℚ)
  | 16 => (347/378:ℚ)
  | 17 => (353/378:ℚ)
  | 18 => (34/945:ℚ)
  | 19 => (17/945:ℚ)
  | 20 => (4/315:ℚ)
  | 21 => (979/1890:ℚ)
  | 22 => (69/70:ℚ)
  | 23 => (317/630:ℚ)
  | 24 => (68/945:ℚ)
  | 25 => (1/630:ℚ)
  | 26 => (1/315:ℚ)
  | 27 => (2/315:ℚ)
  | 28 => (127/630:ℚ)
  | 29 => (253/630:ℚ)
  | 30 => (379/630:ℚ)
  | _ => 0
def point (n : ℕ) : ℚ := (if n<288 then (if n<128 then (if n<64 then (if n<32 then pointPart0 (n-0) else pointPart1 (n-32)) else (if n<96 then pointPart2 (n-64) else pointPart3 (n-96))) else (if n<192 then (if n<160 then pointPart4 (n-128) else pointPart5 (n-160)) else (if n<224 then pointPart6 (n-192) else (if n<256 then pointPart7 (n-224) else pointPart8 (n-256))))) else (if n<448 then (if n<352 then (if n<320 then pointPart9 (n-288) else pointPart10 (n-320)) else (if n<384 then pointPart11 (n-352) else (if n<416 then pointPart12 (n-384) else pointPart13 (n-416)))) else (if n<512 then (if n<480 then pointPart14 (n-448) else pointPart15 (n-480)) else (if n<544 then pointPart16 (n-512) else (if n<576 then pointPart17 (n-544) else pointPart18 (n-576))))))
end QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

def spec0 : Spec := ⟨103,270,2,3,![84,7],48,68⟩
theorem valid0 : Valid point spec0 := by
  dsimp only [Valid,spec0]
  decide +kernel
theorem row0 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 103)=formalLeading spec0 x y z w a b c v := by
  dsimp only [formalLeading,spec0]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec0,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec1 : Spec := ⟨105,270,2,6,![48,52],68,13⟩
theorem valid1 : Valid point spec1 := by
  dsimp only [Valid,spec1]
  decide +kernel
theorem row1 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 105)=formalLeading spec1 x y z w a b c v := by
  dsimp only [formalLeading,spec1]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec1,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec2 : Spec := ⟨109,270,2,2,![83,41],78,49⟩
theorem valid2 : Valid point spec2 := by
  dsimp only [Valid,spec2]
  decide +kernel
theorem row2 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 109)=formalLeading spec2 x y z w a b c v := by
  dsimp only [formalLeading,spec2]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec2,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec3 : Spec := ⟨113,270,5,18,![38,135,19,37,96],50,37⟩
theorem valid3 : Valid point spec3 := by
  dsimp only [Valid,spec3]
  decide +kernel
theorem row3 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 113)=formalLeading spec3 x y z w a b c v := by
  dsimp only [formalLeading,spec3]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec3,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec4 : Spec := ⟨119,270,2,18,![38,141],94,135⟩
theorem valid4 : Valid point spec4 := by
  dsimp only [Valid,spec4]
  decide +kernel
theorem row4 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 119)=formalLeading spec4 x y z w a b c v := by
  dsimp only [formalLeading,spec4]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec4,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec5 : Spec := ⟨120,270,2,25,![15,58],98,80⟩
theorem valid5 : Valid point spec5 := by
  dsimp only [Valid,spec5]
  decide +kernel
theorem row5 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 120)=formalLeading spec5 x y z w a b c v := by
  dsimp only [formalLeading,spec5]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec5,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec6 : Spec := ⟨122,270,2,27,![92,90],101,91⟩
theorem valid6 : Valid point spec6 := by
  dsimp only [Valid,spec6]
  decide +kernel
theorem row6 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 122)=formalLeading spec6 x y z w a b c v := by
  dsimp only [formalLeading,spec6]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec6,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec7 : Spec := ⟨123,270,2,4,![78,9],49,36⟩
theorem valid7 : Valid point spec7 := by
  dsimp only [Valid,spec7]
  decide +kernel
theorem row7 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 123)=formalLeading spec7 x y z w a b c v := by
  dsimp only [formalLeading,spec7]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec7,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec8 : Spec := ⟨125,270,2,35,![73,46],22,31⟩
theorem valid8 : Valid point spec8 := by
  dsimp only [Valid,spec8]
  decide +kernel
theorem row8 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 125)=formalLeading spec8 x y z w a b c v := by
  dsimp only [formalLeading,spec8]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec8,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec9 : Spec := ⟨127,270,2,36,![94,129],135,56⟩
theorem valid9 : Valid point spec9 := by
  dsimp only [Valid,spec9]
  decide +kernel
theorem row9 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 127)=formalLeading spec9 x y z w a b c v := by
  dsimp only [formalLeading,spec9]
  (norm_num [eval,monomial,inputs,inputPart3,formalLeading,spec9,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec10 : Spec := ⟨131,270,2,40,![18,121],8,58⟩
theorem valid10 : Valid point spec10 := by
  dsimp only [Valid,spec10]
  decide +kernel
theorem row10 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 131)=formalLeading spec10 x y z w a b c v := by
  dsimp only [formalLeading,spec10]
  (norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec10,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec11 : Spec := ⟨132,270,2,50,![98,119],80,53⟩
theorem valid11 : Valid point spec11 := by
  dsimp only [Valid,spec11]
  decide +kernel
theorem row11 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 132)=formalLeading spec11 x y z w a b c v := by
  dsimp only [formalLeading,spec11]
  (norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec11,eigenvalue,rate,Fin.sum_univ_succ]; ring)

def spec12 : Spec := ⟨133,270,2,55,![142,26],14,100⟩
theorem valid12 : Valid point spec12 := by
  dsimp only [Valid,spec12]
  decide +kernel
theorem row12 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 133)=formalLeading spec12 x y z w a b c v := by
  dsimp only [formalLeading,spec12]
  (norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec12,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec13 : Spec := ⟨134,270,2,70,![22,136],31,32⟩
theorem valid13 : Valid point spec13 := by
  dsimp only [Valid,spec13]
  decide +kernel
theorem row13 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 134)=formalLeading spec13 x y z w a b c v := by
  dsimp only [formalLeading,spec13]
  (norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec13,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec14 : Spec := ⟨137,270,2,7,![81,54],70,197⟩
theorem valid14 : Valid point spec14 := by
  dsimp only [Valid,spec14]
  decide +kernel
theorem row14 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 137)=formalLeading spec14 x y z w a b c v := by
  dsimp only [formalLeading,spec14]
  (norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec14,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec15 : Spec := ⟨138,270,2,72,![135,139],56,38⟩
theorem valid15 : Valid point spec15 := by
  dsimp only [Valid,spec15]
  decide +kernel
theorem row15 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 138)=formalLeading spec15 x y z w a b c v := by
  dsimp only [formalLeading,spec15]
  (norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec15,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec16 : Spec := ⟨140,270,2,128,![21,45],74,196⟩
theorem valid16 : Valid point spec16 := by
  dsimp only [Valid,spec16]
  decide +kernel
theorem row16 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 140)=formalLeading spec16 x y z w a b c v := by
  dsimp only [formalLeading,spec16]
  (norm_num [eval,monomial,inputs,inputPart4,formalLeading,spec16,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec17 : Spec := ⟨199,378,2,5,![312,274],289,494⟩
theorem valid17 : Valid point spec17 := by
  dsimp only [Valid,spec17]
  decide +kernel
theorem row17 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 199)=formalLeading spec17 x y z w a b c v := by
  dsimp only [formalLeading,spec17]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec17,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec18 : Spec := ⟨200,378,2,18,![301,437],328,373⟩
theorem valid18 : Valid point spec18 := by
  dsimp only [Valid,spec18]
  decide +kernel
theorem row18 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 200)=formalLeading spec18 x y z w a b c v := by
  dsimp only [formalLeading,spec18]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec18,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec19 : Spec := ⟨201,378,2,36,![328,369],373,364⟩
theorem valid19 : Valid point spec19 := by
  dsimp only [Valid,spec19]
  decide +kernel
theorem row19 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 201)=formalLeading spec19 x y z w a b c v := by
  dsimp only [formalLeading,spec19]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec19,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec20 : Spec := ⟨203,378,2,45,![435,365],371,279⟩
theorem valid20 : Valid point spec20 := by
  dsimp only [Valid,spec20]
  decide +kernel
theorem row20 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 203)=formalLeading spec20 x y z w a b c v := by
  dsimp only [formalLeading,spec20]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec20,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec21 : Spec := ⟨204,378,2,54,![332,359],331,334⟩
theorem valid21 : Valid point spec21 := by
  dsimp only [Valid,spec21]
  decide +kernel
theorem row21 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 204)=formalLeading spec21 x y z w a b c v := by
  dsimp only [formalLeading,spec21]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec21,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec22 : Spec := ⟨206,378,2,72,![373,357],364,370⟩
theorem valid22 : Valid point spec22 := by
  dsimp only [Valid,spec22]
  decide +kernel
theorem row22 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 206)=formalLeading spec22 x y z w a b c v := by
  dsimp only [formalLeading,spec22]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec22,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec23 : Spec := ⟨208,378,2,81,![413,330],335,333⟩
theorem valid23 : Valid point spec23 := by
  dsimp only [Valid,spec23]
  decide +kernel
theorem row23 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 208)=formalLeading spec23 x y z w a b c v := by
  dsimp only [formalLeading,spec23]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec23,eigenvalue,rate,Fin.sum_univ_succ]; ring)

def spec24 : Spec := ⟨210,378,2,90,![371,367],279,302⟩
theorem valid24 : Valid point spec24 := by
  dsimp only [Valid,spec24]
  decide +kernel
theorem row24 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 210)=formalLeading spec24 x y z w a b c v := by
  dsimp only [formalLeading,spec24]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec24,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec25 : Spec := ⟨212,378,2,144,![364,434],370,293⟩
theorem valid25 : Valid point spec25 := by
  dsimp only [Valid,spec25]
  decide +kernel
theorem row25 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 212)=formalLeading spec25 x y z w a b c v := by
  dsimp only [formalLeading,spec25]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec25,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec26 : Spec := ⟨214,378,2,184,![282,314],286,493⟩
theorem valid26 : Valid point spec26 := by
  dsimp only [Valid,spec26]
  decide +kernel
theorem row26 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 214)=formalLeading spec26 x y z w a b c v := by
  dsimp only [formalLeading,spec26]
  (norm_num [eval,monomial,inputs,inputPart6,formalLeading,spec26,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec27 : Spec := ⟨226,270,2,123,![203,76],59,169⟩
theorem valid27 : Valid point spec27 := by
  dsimp only [Valid,spec27]
  decide +kernel
theorem row27 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 226)=formalLeading spec27 x y z w a b c v := by
  dsimp only [formalLeading,spec27]
  (norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec27,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec28 : Spec := ⟨229,270,2,12,![68,204],13,170⟩
theorem valid28 : Valid point spec28 := by
  dsimp only [Valid,spec28]
  decide +kernel
theorem row28 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 229)=formalLeading spec28 x y z w a b c v := by
  dsimp only [formalLeading,spec28]
  (norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec28,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec29 : Spec := ⟨232,378,2,15,![299,433],276,380⟩
theorem valid29 : Valid point spec29 := by
  dsimp only [Valid,spec29]
  decide +kernel
theorem row29 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 232)=formalLeading spec29 x y z w a b c v := by
  dsimp only [formalLeading,spec29]
  (norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec29,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec30 : Spec := ⟨239,270,2,66,![174,218],27,47⟩
theorem valid30 : Valid point spec30 := by
  dsimp only [Valid,spec30]
  decide +kernel
theorem row30 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 239)=formalLeading spec30 x y z w a b c v := by
  dsimp only [formalLeading,spec30]
  (norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec30,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec31 : Spec := ⟨240,270,2,111,![157,59],169,125⟩
theorem valid31 : Valid point spec31 := by
  dsimp only [Valid,spec31]
  decide +kernel
theorem row31 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 240)=formalLeading spec31 x y z w a b c v := by
  dsimp only [formalLeading,spec31]
  (norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec31,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec32 : Spec := ⟨255,270,2,114,![168,62],175,123⟩
theorem valid32 : Valid point spec32 := by
  dsimp only [Valid,spec32]
  decide +kernel
theorem row32 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 255)=formalLeading spec32 x y z w a b c v := by
  dsimp only [formalLeading,spec32]
  (norm_num [eval,monomial,inputs,inputPart7,formalLeading,spec32,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec33 : Spec := ⟨256,270,2,24,![13,160],170,122⟩
theorem valid33 : Valid point spec33 := by
  dsimp only [Valid,spec33]
  decide +kernel
theorem row33 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 256)=formalLeading spec33 x y z w a b c v := by
  dsimp only [formalLeading,spec33]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec33,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec34 : Spec := ⟨257,270,2,33,![202,133],174,27⟩
theorem valid34 : Valid point spec34 := by
  dsimp only [Valid,spec34]
  decide +kernel
theorem row34 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 257)=formalLeading spec34 x y z w a b c v := by
  dsimp only [formalLeading,spec34]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec34,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec35 : Spec := ⟨261,270,2,39,![216,125],132,171⟩
theorem valid35 : Valid point spec35 := by
  dsimp only [Valid,spec35]
  decide +kernel
theorem row35 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 261)=formalLeading spec35 x y z w a b c v := by
  dsimp only [formalLeading,spec35]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec35,eigenvalue,rate,Fin.sum_univ_succ]; ring)

def spec36 : Spec := ⟨263,270,2,42,![172,113],124,133⟩
theorem valid36 : Valid point spec36 := by
  dsimp only [Valid,spec36]
  decide +kernel
theorem row36 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 263)=formalLeading spec36 x y z w a b c v := by
  dsimp only [formalLeading,spec36]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec36,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec37 : Spec := ⟨264,270,2,48,![170,111],122,131⟩
theorem valid37 : Valid point spec37 := by
  dsimp only [Valid,spec37]
  decide +kernel
theorem row37 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 264)=formalLeading spec37 x y z w a b c v := by
  dsimp only [formalLeading,spec37]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec37,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec38 : Spec := ⟨267,270,2,8,![49,229],36,192⟩
theorem valid38 : Valid point spec38 := by
  dsimp only [Valid,spec38]
  decide +kernel
theorem row38 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 267)=formalLeading spec38 x y z w a b c v := by
  dsimp only [formalLeading,spec38]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec38,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec39 : Spec := ⟨268,270,2,11,![67,213],11,178⟩
theorem valid39 : Valid point spec39 := by
  dsimp only [Valid,spec39]
  decide +kernel
theorem row39 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 268)=formalLeading spec39 x y z w a b c v := by
  dsimp only [formalLeading,spec39]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec39,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec40 : Spec := ⟨269,270,2,14,![70,189],197,150⟩
theorem valid40 : Valid point spec40 := by
  dsimp only [Valid,spec40]
  decide +kernel
theorem row40 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 269)=formalLeading spec40 x y z w a b c v := by
  dsimp only [formalLeading,spec40]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec40,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec41 : Spec := ⟨270,270,2,64,![207,225],21,74⟩
theorem valid41 : Valid point spec41 := by
  dsimp only [Valid,spec41]
  decide +kernel
theorem row41 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 270)=formalLeading spec41 x y z w a b c v := by
  dsimp only [formalLeading,spec41]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec41,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec42 : Spec := ⟨271,270,2,67,![252,237],29,87⟩
theorem valid42 : Valid point spec42 := by
  dsimp only [Valid,spec42]
  decide +kernel
theorem row42 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 271)=formalLeading spec42 x y z w a b c v := by
  dsimp only [formalLeading,spec42]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec42,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec43 : Spec := ⟨272,270,2,68,![238,267],5,83⟩
theorem valid43 : Valid point spec43 := by
  dsimp only [Valid,spec43]
  decide +kernel
theorem row43 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 272)=formalLeading spec43 x y z w a b c v := by
  dsimp only [formalLeading,spec43]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec43,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec44 : Spec := ⟨273,270,2,71,![228,214],54,70⟩
theorem valid44 : Valid point spec44 := by
  dsimp only [Valid,spec44]
  decide +kernel
theorem row44 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 273)=formalLeading spec44 x y z w a b c v := by
  dsimp only [formalLeading,spec44]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec44,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec45 : Spec := ⟨274,270,2,121,![182,74],196,155⟩
theorem valid45 : Valid point spec45 := by
  dsimp only [Valid,spec45]
  decide +kernel
theorem row45 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 274)=formalLeading spec45 x y z w a b c v := by
  dsimp only [formalLeading,spec45]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec45,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec46 : Spec := ⟨275,270,2,124,![208,77],61,177⟩
theorem valid46 : Valid point spec46 := by
  dsimp only [Valid,spec46]
  decide +kernel
theorem row46 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 275)=formalLeading spec46 x y z w a b c v := by
  dsimp only [formalLeading,spec46]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec46,eigenvalue,rate,Fin.sum_univ_succ]; ring)
def spec47 : Spec := ⟨276,270,2,127,![224,43],65,201⟩
theorem valid47 : Valid point spec47 := by
  dsimp only [Valid,spec47]
  decide +kernel
theorem row47 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 276)=formalLeading spec47 x y z w a b c v := by
  dsimp only [formalLeading,spec47]
  (norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec47,eigenvalue,rate,Fin.sum_univ_succ]; ring)

def spec48 : Spec := ⟨277,270,3,7,![81,253,256],10,140⟩
theorem valid48 : Valid point spec48 := by
  dsimp only [Valid,spec48]
  decide +kernel
theorem row48 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 277)=formalLeading spec48 x y z w a b c v := by
  dsimp only [formalLeading,spec48]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec48,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec49 : Spec := ⟨278,270,3,8,![49,249,221],13,135⟩
theorem valid49 : Valid point spec49 := by
  dsimp only [Valid,spec49]
  decide +kernel
theorem row49 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 278)=formalLeading spec49 x y z w a b c v := by
  dsimp only [formalLeading,spec49]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec49,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec50 : Spec := ⟨279,270,3,11,![67,241,242],202,126⟩
theorem valid50 : Valid point spec50 := by
  dsimp only [Valid,spec50]
  decide +kernel
theorem row50 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 279)=formalLeading spec50 x y z w a b c v := by
  dsimp only [formalLeading,spec50]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec50,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec51 : Spec := ⟨280,270,3,14,![70,165,239],172,19⟩
theorem valid51 : Valid point spec51 := by
  dsimp only [Valid,spec51]
  decide +kernel
theorem row51 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 280)=formalLeading spec51 x y z w a b c v := by
  dsimp only [formalLeading,spec51]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec51,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec52 : Spec := ⟨282,270,3,16,![36,154,234],170,56⟩
theorem valid52 : Valid point spec52 := by
  dsimp only [Valid,spec52]
  decide +kernel
theorem row52 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 282)=formalLeading spec52 x y z w a b c v := by
  dsimp only [formalLeading,spec52]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec52,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec53 : Spec := ⟨284,270,3,19,![40,143,225],156,129⟩
theorem valid53 : Valid point spec53 := by
  dsimp only [Valid,spec53]
  decide +kernel
theorem row53 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 284)=formalLeading spec53 x y z w a b c v := by
  dsimp only [formalLeading,spec53]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec53,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec54 : Spec := ⟨285,270,3,22,![11,163,237],174,134⟩
theorem valid54 : Valid point spec54 := by
  dsimp only [Valid,spec54]
  decide +kernel
theorem row54 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 285)=formalLeading spec54 x y z w a b c v := by
  dsimp only [formalLeading,spec54]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec54,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec55 : Spec := ⟨286,270,3,28,![197,198,200],124,64⟩
theorem valid55 : Valid point spec55 := by
  dsimp only [Valid,spec55]
  decide +kernel
theorem row55 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 286)=formalLeading spec55 x y z w a b c v := by
  dsimp only [formalLeading,spec55]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec55,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec56 : Spec := ⟨287,270,3,38,![232,21,152],168,135⟩
theorem valid56 : Valid point spec56 := by
  dsimp only [Valid,spec56]
  decide +kernel
theorem row56 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 287)=formalLeading spec56 x y z w a b c v := by
  dsimp only [formalLeading,spec56]
  norm_num [eval,monomial,inputs,inputPart8,formalLeading,spec56,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec57 : Spec := ⟨290,270,3,41,![240,25,243],203,126⟩
theorem valid57 : Valid point spec57 := by
  dsimp only [Valid,spec57]
  decide +kernel
theorem row57 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 290)=formalLeading spec57 x y z w a b c v := by
  dsimp only [formalLeading,spec57]
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec57,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec58 : Spec := ⟨292,270,3,43,![251,82,258],23,138⟩
theorem valid58 : Valid point spec58 := by
  dsimp only [Valid,spec58]
  decide +kernel
theorem row58 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 292)=formalLeading spec58 x y z w a b c v := by
  dsimp only [formalLeading,spec58]
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec58,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec59 : Spec := ⟨293,270,3,47,![261,41,268],52,141⟩
theorem valid59 : Valid point spec59 := by
  dsimp only [Valid,spec59]
  decide +kernel
theorem row59 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 293)=formalLeading spec59 x y z w a b c v := by
  dsimp only [formalLeading,spec59]
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec59,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec60 : Spec := ⟨294,270,3,49,![244,9,247],204,129⟩
theorem valid60 : Valid point spec60 := by
  dsimp only [Valid,spec60]
  decide +kernel
theorem row60 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 294)=formalLeading spec60 x y z w a b c v := by
  dsimp only [formalLeading,spec60]
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec60,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec61 : Spec := ⟨296,270,3,52,![153,54,235],171,134⟩
theorem valid61 : Valid point spec61 := by
  dsimp only [Valid,spec61]
  decide +kernel
theorem row61 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 296)=formalLeading spec61 x y z w a b c v := by
  dsimp only [formalLeading,spec61]
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec61,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec62 : Spec := ⟨298,270,3,83,![263,266,45],62,139⟩
theorem valid62 : Valid point spec62 := by
  dsimp only [Valid,spec62]
  decide +kernel
theorem row62 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 298)=formalLeading spec62 x y z w a b c v := by
  dsimp only [formalLeading,spec62]
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec62,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec63 : Spec := ⟨319,378,2,10,![289,502],494,457⟩
theorem valid63 : Valid point spec63 := by
  dsimp only [Valid,spec63]
  decide +kernel
theorem row63 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 319)=formalLeading spec63 x y z w a b c v := by
  dsimp only [formalLeading,spec63]
  norm_num [eval,monomial,inputs,inputPart9,formalLeading,spec63,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec64 : Spec := ⟨320,378,2,12,![290,484],284,427⟩
theorem valid64 : Valid point spec64 := by
  dsimp only [Valid,spec64]
  decide +kernel
theorem row64 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 320)=formalLeading spec64 x y z w a b c v := by
  dsimp only [formalLeading,spec64]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec64,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec65 : Spec := ⟨321,378,2,13,![291,530],285,397⟩
theorem valid65 : Valid point spec65 := by
  dsimp only [Valid,spec65]
  decide +kernel
theorem row65 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 321)=formalLeading spec65 x y z w a b c v := by
  dsimp only [formalLeading,spec65]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec65,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec66 : Spec := ⟨322,378,2,16,![300,562],277,374⟩
theorem valid66 : Valid point spec66 := by
  dsimp only [Valid,spec66]
  decide +kernel
theorem row66 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 322)=formalLeading spec66 x y z w a b c v := by
  dsimp only [formalLeading,spec66]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec66,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec67 : Spec := ⟨323,378,2,30,![276,405],380,354⟩
theorem valid67 : Valid point spec67 := by
  dsimp only [Valid,spec67]
  decide +kernel
theorem row67 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 323)=formalLeading spec67 x y z w a b c v := by
  dsimp only [formalLeading,spec67]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec67,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec68 : Spec := ⟨324,378,2,92,![517,539],282,286⟩
theorem valid68 : Valid point spec68 := by
  dsimp only [Valid,spec68]
  decide +kernel
theorem row68 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 324)=formalLeading spec68 x y z w a b c v := by
  dsimp only [formalLeading,spec68]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec68,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec69 : Spec := ⟨325,378,2,93,![478,439],283,313⟩
theorem valid69 : Valid point spec69 := by
  dsimp only [Valid,spec69]
  decide +kernel
theorem row69 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 325)=formalLeading spec69 x y z w a b c v := by
  dsimp only [formalLeading,spec69]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec69,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec70 : Spec := ⟨326,378,2,94,![529,567],309,324⟩
theorem valid70 : Valid point spec70 := by
  dsimp only [Valid,spec70]
  decide +kernel
theorem row70 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 326)=formalLeading spec70 x y z w a b c v := by
  dsimp only [formalLeading,spec70]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec70,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec71 : Spec := ⟨327,378,2,95,![578,534],315,323⟩
theorem valid71 : Valid point spec71 := by
  dsimp only [Valid,spec71]
  decide +kernel
theorem row71 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 327)=formalLeading spec71 x y z w a b c v := by
  dsimp only [formalLeading,spec71]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec71,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec72 : Spec := ⟨328,378,2,96,![430,485],273,304⟩
theorem valid72 : Valid point spec72 := by
  dsimp only [Valid,spec72]
  decide +kernel
theorem row72 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 328)=formalLeading spec72 x y z w a b c v := by
  dsimp only [formalLeading,spec72]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec72,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec73 : Spec := ⟨329,378,2,97,![540,522],274,289⟩
theorem valid73 : Valid point spec73 := by
  dsimp only [Valid,spec73]
  decide +kernel
theorem row73 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 329)=formalLeading spec73 x y z w a b c v := by
  dsimp only [formalLeading,spec73]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec73,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec74 : Spec := ⟨330,378,2,102,![428,465],433,276⟩
theorem valid74 : Valid point spec74 := by
  dsimp only [Valid,spec74]
  decide +kernel
theorem row74 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 330)=formalLeading spec74 x y z w a b c v := by
  dsimp only [formalLeading,spec74]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec74,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec75 : Spec := ⟨331,378,2,173,![583,303],295,377⟩
theorem valid75 : Valid point spec75 := by
  dsimp only [Valid,spec75]
  decide +kernel
theorem row75 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 331)=formalLeading spec75 x y z w a b c v := by
  dsimp only [formalLeading,spec75]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec75,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec76 : Spec := ⟨332,378,2,174,![436,270],296,379⟩
theorem valid76 : Valid point spec76 := by
  dsimp only [Valid,spec76]
  decide +kernel
theorem row76 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 332)=formalLeading spec76 x y z w a b c v := by
  dsimp only [formalLeading,spec76]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec76,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec77 : Spec := ⟨333,378,2,176,![533,306],297,396⟩
theorem valid77 : Valid point spec77 := by
  dsimp only [Valid,spec77]
  decide +kernel
theorem row77 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 333)=formalLeading spec77 x y z w a b c v := by
  dsimp only [formalLeading,spec77]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec77,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec78 : Spec := ⟨334,378,2,177,![479,307],298,426⟩
theorem valid78 : Valid point spec78 := by
  dsimp only [Valid,spec78]
  decide +kernel
theorem row78 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 334)=formalLeading spec78 x y z w a b c v := by
  dsimp only [formalLeading,spec78]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec78,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec79 : Spec := ⟨335,378,2,179,![511,286],493,456⟩
theorem valid79 : Valid point spec79 := by
  dsimp only [Valid,spec79]
  decide +kernel
theorem row79 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 335)=formalLeading spec79 x y z w a b c v := by
  dsimp only [formalLeading,spec79]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec79,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec80 : Spec := ⟨336,378,3,5,![312,580,586],299,435⟩
theorem valid80 : Valid point spec80 := by
  dsimp only [Valid,spec80]
  decide +kernel
theorem row80 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 336)=formalLeading spec80 x y z w a b c v := by
  dsimp only [formalLeading,spec80]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec80,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec81 : Spec := ⟨337,378,3,8,![305,488,551],284,373⟩
theorem valid81 : Valid point spec81 := by
  dsimp only [Valid,spec81]
  decide +kernel
theorem row81 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 337)=formalLeading spec81 x y z w a b c v := by
  dsimp only [formalLeading,spec81]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec81,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec82 : Spec := ⟨338,378,3,10,![289,486,549],276,371⟩
theorem valid82 : Valid point spec82 := by
  dsimp only [Valid,spec82]
  decide +kernel
theorem row82 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 338)=formalLeading spec82 x y z w a b c v := by
  dsimp only [formalLeading,spec82]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec82,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec83 : Spec := ⟨339,378,3,13,![291,541,543],464,358⟩
theorem valid83 : Valid point spec83 := by
  dsimp only [Valid,spec83]
  decide +kernel
theorem row83 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 339)=formalLeading spec83 x y z w a b c v := by
  dsimp only [formalLeading,spec83]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec83,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec84 : Spec := ⟨340,378,3,15,![299,527,410],435,356⟩
theorem valid84 : Valid point spec84 := by
  dsimp only [Valid,spec84]
  decide +kernel
theorem row84 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 340)=formalLeading spec84 x y z w a b c v := by
  dsimp only [formalLeading,spec84]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec84,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec85 : Spec := ⟨341,378,3,16,![300,521,401],427,364⟩
theorem valid85 : Valid point spec85 := by
  dsimp only [Valid,spec85]
  decide +kernel
theorem row85 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 341)=formalLeading spec85 x y z w a b c v := by
  dsimp only [formalLeading,spec85]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec85,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec86 : Spec := ⟨342,378,3,20,![494,495,395],380,279⟩
theorem valid86 : Valid point spec86 := by
  dsimp only [Valid,spec86]
  decide +kernel
theorem row86 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 342)=formalLeading spec86 x y z w a b c v := by
  dsimp only [formalLeading,spec86]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec86,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec87 : Spec := ⟨343,378,3,26,![285,546,547],477,365⟩
theorem valid87 : Valid point spec87 := by
  dsimp only [Valid,spec87]
  decide +kernel
theorem row87 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 343)=formalLeading spec87 x y z w a b c v := by
  dsimp only [formalLeading,spec87]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec87,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec88 : Spec := ⟨344,378,3,29,![317,537,539],462,357⟩
theorem valid88 : Valid point spec88 := by
  dsimp only [Valid,spec88]
  decide +kernel
theorem row88 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 344)=formalLeading spec88 x y z w a b c v := by
  dsimp only [formalLeading,spec88]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec88,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec89 : Spec := ⟨345,378,3,32,![277,421,534],430,370⟩
theorem valid89 : Valid point spec89 := by
  dsimp only [Valid,spec89]
  decide +kernel
theorem row89 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 345)=formalLeading spec89 x y z w a b c v := by
  dsimp only [formalLeading,spec89]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec89,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec90 : Spec := ⟨346,378,3,52,![397,278,523],429,371⟩
theorem valid90 : Valid point spec90 := by
  dsimp only [Valid,spec90]
  decide +kernel
theorem row90 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 346)=formalLeading spec90 x y z w a b c v := by
  dsimp only [formalLeading,spec90]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec90,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec91 : Spec := ⟨348,378,3,55,![382,280,505],404,358⟩
theorem valid91 : Valid point spec91 := by
  dsimp only [Valid,spec91]
  decide +kernel
theorem row91 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 348)=formalLeading spec91 x y z w a b c v := by
  dsimp only [formalLeading,spec91]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec91,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec92 : Spec := ⟨349,378,3,57,![402,281,525],431,356⟩
theorem valid92 : Valid point spec92 := by
  dsimp only [Valid,spec92]
  decide +kernel
theorem row92 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 349)=formalLeading spec92 x y z w a b c v := by
  dsimp only [formalLeading,spec92]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec92,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec93 : Spec := ⟨350,378,3,58,![412,282,531],436,364⟩
theorem valid93 : Valid point spec93 := by
  dsimp only [Valid,spec93]
  decide +kernel
theorem row93 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 350)=formalLeading spec93 x y z w a b c v := by
  dsimp only [formalLeading,spec93]
  norm_num [eval,monomial,inputs,inputPart10,formalLeading,spec93,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec94 : Spec := ⟨352,378,3,59,![576,320,590],479,366⟩
theorem valid94 : Valid point spec94 := by
  dsimp only [Valid,spec94]
  decide +kernel
theorem row94 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 352)=formalLeading spec94 x y z w a b c v := by
  dsimp only [formalLeading,spec94]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec94,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec95 : Spec := ⟨353,378,3,61,![554,308,568],281,431⟩
theorem valid95 : Valid point spec95 := by
  dsimp only [Valid,spec95]
  decide +kernel
theorem row95 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 353)=formalLeading spec95 x y z w a b c v := by
  dsimp only [formalLeading,spec95]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec95,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec96 : Spec := ⟨354,378,3,65,![577,316,591],275,437⟩
theorem valid96 : Valid point spec96 := by
  dsimp only [Valid,spec96]
  decide +kernel
theorem row96 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 354)=formalLeading spec96 x y z w a b c v := by
  dsimp only [formalLeading,spec96]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec96,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec97 : Spec := ⟨355,378,3,67,![555,319,569],484,369⟩
theorem valid97 : Valid point spec97 := by
  dsimp only [Valid,spec97]
  decide +kernel
theorem row97 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 355)=formalLeading spec97 x y z w a b c v := by
  dsimp only [formalLeading,spec97]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec97,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec98 : Spec := ⟨356,378,3,68,![532,274,423],433,365⟩
theorem valid98 : Valid point spec98 := by
  dsimp only [Valid,spec98]
  decide +kernel
theorem row98 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 356)=formalLeading spec98 x y z w a b c v := by
  dsimp only [formalLeading,spec98]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec98,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec99 : Spec := ⟨358,378,3,69,![526,275,411],437,359⟩
theorem valid99 : Valid point spec99 := by
  dsimp only [Valid,spec99]
  decide +kernel
theorem row99 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 358)=formalLeading spec99 x y z w a b c v := by
  dsimp only [formalLeading,spec99]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec99,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec100 : Spec := ⟨359,378,3,71,![508,292,391],409,357⟩
theorem valid100 : Valid point spec100 := by
  dsimp only [Valid,spec100]
  decide +kernel
theorem row100 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 359)=formalLeading spec100 x y z w a b c v := by
  dsimp only [formalLeading,spec100]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec100,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec101 : Spec := ⟨361,378,3,74,![516,294,396],424,370⟩
theorem valid101 : Valid point spec101 := by
  dsimp only [Valid,spec101]
  decide +kernel
theorem row101 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 361)=formalLeading spec101 x y z w a b c v := by
  dsimp only [formalLeading,spec101]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec101,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec102 : Spec := ⟨363,378,3,97,![540,542,272],465,358⟩
theorem valid102 : Valid point spec102 := by
  dsimp only [Valid,spec102]
  decide +kernel
theorem row102 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 363)=formalLeading spec102 x y z w a b c v := by
  dsimp only [formalLeading,spec102]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec102,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec103 : Spec := ⟨365,378,3,106,![398,492,493],379,293⟩
theorem valid103 : Valid point spec103 := by
  dsimp only [Valid,spec103]
  decide +kernel
theorem row103 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 365)=formalLeading spec103 x y z w a b c v := by
  dsimp only [formalLeading,spec103]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec103,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec104 : Spec := ⟨366,378,3,118,![550,487,288],298,372⟩
theorem valid104 : Valid point spec104 := by
  dsimp only [Valid,spec104]
  decide +kernel
theorem row104 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 366)=formalLeading spec104 x y z w a b c v := by
  dsimp only [formalLeading,spec104]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec104,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec105 : Spec := ⟨367,378,3,121,![559,565,314],270,434⟩
theorem valid105 : Valid point spec105 := by
  dsimp only [Valid,spec105]
  decide +kernel
theorem row105 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 367)=formalLeading spec105 x y z w a b c v := by
  dsimp only [formalLeading,spec105]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec105,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec106 : Spec := ⟨380,270,2,16,![36,183],192,207⟩
theorem valid106 : Valid point spec106 := by
  dsimp only [Valid,spec106]
  decide +kernel
theorem row106 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 380)=formalLeading spec106 x y z w a b c v := by
  dsimp only [formalLeading,spec106]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec106,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec107 : Spec := ⟨381,270,2,22,![11,255],178,108⟩
theorem valid107 : Valid point spec107 := by
  dsimp only [Valid,spec107]
  decide +kernel
theorem row107 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 381)=formalLeading spec107 x y z w a b c v := by
  dsimp only [formalLeading,spec107]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec107,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec108 : Spec := ⟨382,270,2,32,![192,265],207,21⟩
theorem valid108 : Valid point spec108 := by
  dsimp only [Valid,spec108]
  decide +kernel
theorem row108 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 382)=formalLeading spec108 x y z w a b c v := by
  dsimp only [formalLeading,spec108]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec108,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec109 : Spec := ⟨383,270,2,62,![193,230],208,61⟩
theorem valid109 : Valid point spec109 := by
  dsimp only [Valid,spec109]
  decide +kernel
theorem row109 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 383)=formalLeading spec109 x y z w a b c v := by
  dsimp only [formalLeading,spec109]
  norm_num [eval,monomial,inputs,inputPart11,formalLeading,spec109,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec110 : Spec := ⟨384,270,2,73,![223,200],213,11⟩
theorem valid110 : Valid point spec110 := by
  dsimp only [Valid,spec110]
  decide +kernel
theorem row110 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 384)=formalLeading spec110 x y z w a b c v := by
  dsimp only [formalLeading,spec110]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec110,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec111 : Spec := ⟨385,270,2,103,![254,201],214,54⟩
theorem valid111 : Valid point spec111 := by
  dsimp only [Valid,spec111]
  decide +kernel
theorem row111 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 385)=formalLeading spec111 x y z w a b c v := by
  dsimp only [formalLeading,spec111]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec111,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec112 : Spec := ⟨386,270,2,107,![147,196],155,166⟩
theorem valid112 : Valid point spec112 := by
  dsimp only [Valid,spec112]
  decide +kernel
theorem row112 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 386)=formalLeading spec112 x y z w a b c v := by
  dsimp only [formalLeading,spec112]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec112,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec113 : Spec := ⟨387,270,2,113,![264,61],177,107⟩
theorem valid113 : Valid point spec113 := by
  dsimp only [Valid,spec113]
  decide +kernel
theorem row113 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 387)=formalLeading spec113 x y z w a b c v := by
  dsimp only [formalLeading,spec113]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec113,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec114 : Spec := ⟨388,270,2,119,![188,65],201,214⟩
theorem valid114 : Valid point spec114 := by
  dsimp only [Valid,spec114]
  decide +kernel
theorem row114 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 388)=formalLeading spec114 x y z w a b c v := by
  dsimp only [formalLeading,spec114]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec114,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec115 : Spec := ⟨389,270,3,31,![180,182,184],110,51⟩
theorem valid115 : Valid point spec115 := by
  dsimp only [Valid,spec115]
  decide +kernel
theorem row115 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 389)=formalLeading spec115 x y z w a b c v := by
  dsimp only [formalLeading,spec115]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec115,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec116 : Spec := ⟨390,270,3,37,![222,224,145],157,140⟩
theorem valid116 : Valid point spec116 := by
  dsimp only [Valid,spec116]
  decide +kernel
theorem row116 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 390)=formalLeading spec116 x y z w a b c v := by
  dsimp only [formalLeading,spec116]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec116,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec117 : Spec := ⟨391,270,3,59,![187,189,191],113,79⟩
theorem valid117 : Valid point spec117 := by
  dsimp only [Valid,spec117]
  decide +kernel
theorem row117 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 391)=formalLeading spec117 x y z w a b c v := by
  dsimp only [formalLeading,spec117]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec117,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec118 : Spec := ⟨392,270,5,7,![81,181,66,246,258],73,121⟩
theorem valid118 : Valid point spec118 := by
  dsimp only [Valid,spec118]
  decide +kernel
theorem row118 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 392)=formalLeading spec118 x y z w a b c v := by
  dsimp only [formalLeading,spec118]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec118,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec119 : Spec := ⟨393,270,5,16,![36,22,208,109,235],8,24⟩
theorem valid119 : Valid point spec119 := by
  dsimp only [Valid,spec119]
  decide +kernel
theorem row119 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 393)=formalLeading spec119 x y z w a b c v := by
  dsimp only [formalLeading,spec119]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec119,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec120 : Spec := ⟨394,270,5,20,![72,233,21,107,215],80,39⟩
theorem valid120 : Valid point spec120 := by
  dsimp only [Valid,spec120]
  decide +kernel
theorem row120 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 394)=formalLeading spec120 x y z w a b c v := by
  dsimp only [formalLeading,spec120]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec120,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec121 : Spec := ⟨395,270,5,23,![260,262,25,119,191],66,73⟩
theorem valid121 : Valid point spec121 := by
  dsimp only [Valid,spec121]
  decide +kernel
theorem row121 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 395)=formalLeading spec121 x y z w a b c v := by
  dsimp only [formalLeading,spec121]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec121,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec122 : Spec := ⟨396,270,5,29,![186,263,41,242,57],44,119⟩
theorem valid122 : Valid point spec122 := by
  dsimp only [Valid,spec122]
  decide +kernel
theorem row122 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 396)=formalLeading spec122 x y z w a b c v := by
  dsimp only [formalLeading,spec122]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec122,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec123 : Spec := ⟨403,378,2,20,![494,449],457,472⟩
theorem valid123 : Valid point spec123 := by
  dsimp only [Valid,spec123]
  decide +kernel
theorem row123 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 403)=formalLeading spec123 x y z w a b c v := by
  dsimp only [formalLeading,spec123]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec123,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec124 : Spec := ⟨404,378,2,24,![284,409],427,430⟩
theorem valid124 : Valid point spec124 := by
  dsimp only [Valid,spec124]
  decide +kernel
theorem row124 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 404)=formalLeading spec124 x y z w a b c v := by
  dsimp only [formalLeading,spec124]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec124,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec125 : Spec := ⟨405,378,2,29,![317,394],412,548⟩
theorem valid125 : Valid point spec125 := by
  dsimp only [Valid,spec125]
  decide +kernel
theorem row125 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 405)=formalLeading spec125 x y z w a b c v := by
  dsimp only [formalLeading,spec125]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec125,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec126 : Spec := ⟨406,378,2,32,![277,584],374,340⟩
theorem valid126 : Valid point spec126 := by
  dsimp only [Valid,spec126]
  decide +kernel
theorem row126 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 406)=formalLeading spec126 x y z w a b c v := by
  dsimp only [formalLeading,spec126]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec126,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec127 : Spec := ⟨407,378,2,39,![464,438],477,429⟩
theorem valid127 : Valid point spec127 := by
  dsimp only [Valid,spec127]
  decide +kernel
theorem row127 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 407)=formalLeading spec127 x y z w a b c v := by
  dsimp only [formalLeading,spec127]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec127,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec128 : Spec := ⟨408,378,2,46,![466,503],517,282⟩
theorem valid128 : Valid point spec128 := by
  dsimp only [Valid,spec128]
  decide +kernel
theorem row128 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 408)=formalLeading spec128 x y z w a b c v := by
  dsimp only [formalLeading,spec128]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec128,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec129 : Spec := ⟨409,378,2,47,![575,518],529,309⟩
theorem valid129 : Valid point spec129 := by
  dsimp only [Valid,spec129]
  decide +kernel
theorem row129 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 409)=formalLeading spec129 x y z w a b c v := by
  dsimp only [formalLeading,spec129]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec129,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec130 : Spec := ⟨410,378,2,48,![427,524],430,273⟩
theorem valid130 : Valid point spec130 := by
  dsimp only [Valid,spec130]
  decide +kernel
theorem row130 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 410)=formalLeading spec130 x y z w a b c v := by
  dsimp only [formalLeading,spec130]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec130,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec131 : Spec := ⟨411,378,2,50,![419,538],544,294⟩
theorem valid131 : Valid point spec131 := by
  dsimp only [Valid,spec131]
  decide +kernel
theorem row131 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 411)=formalLeading spec131 x y z w a b c v := by
  dsimp only [formalLeading,spec131]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec131,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec132 : Spec := ⟨412,378,2,51,![407,363],428,433⟩
theorem valid132 : Valid point spec132 := by
  dsimp only [Valid,spec132]
  decide +kernel
theorem row132 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 412)=formalLeading spec132 x y z w a b c v := by
  dsimp only [formalLeading,spec132]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec132,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec133 : Spec := ⟨413,378,2,60,![380,347],354,363⟩
theorem valid133 : Valid point spec133 := by
  dsimp only [Valid,spec133]
  decide +kernel
theorem row133 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 413)=formalLeading spec133 x y z w a b c v := by
  dsimp only [formalLeading,spec133]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec133,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec134 : Spec := ⟨414,378,2,78,![477,410],429,381⟩
theorem valid134 : Valid point spec134 := by
  dsimp only [Valid,spec134]
  decide +kernel
theorem row134 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 414)=formalLeading spec134 x y z w a b c v := by
  dsimp only [formalLeading,spec134]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec134,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec135 : Spec := ⟨415,378,2,88,![467,566],533,297⟩
theorem valid135 : Valid point spec135 := by
  dsimp only [Valid,spec135]
  decide +kernel
theorem row135 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 415)=formalLeading spec135 x y z w a b c v := by
  dsimp only [formalLeading,spec135]
  norm_num [eval,monomial,inputs,inputPart12,formalLeading,spec135,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec136 : Spec := ⟨416,378,2,89,![509,547],278,497⟩
theorem valid136 : Valid point spec136 := by
  dsimp only [Valid,spec136]
  decide +kernel
theorem row136 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 416)=formalLeading spec136 x y z w a b c v := by
  dsimp only [formalLeading,spec136]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec136,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec137 : Spec := ⟨417,378,2,101,![579,474],530,285⟩
theorem valid137 : Valid point spec137 := by
  dsimp only [Valid,spec137]
  decide +kernel
theorem row137 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 417)=formalLeading spec137 x y z w a b c v := by
  dsimp only [formalLeading,spec137]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec137,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec138 : Spec := ⟨418,378,2,113,![536,535],545,516⟩
theorem valid138 : Valid point spec138 := by
  dsimp only [Valid,spec138]
  decide +kernel
theorem row138 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 418)=formalLeading spec138 x y z w a b c v := by
  dsimp only [formalLeading,spec138]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec138,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec139 : Spec := ⟨424,378,2,139,![541,417],547,278⟩
theorem valid139 : Valid point spec139 := by
  dsimp only [Valid,spec139]
  decide +kernel
theorem row139 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 424)=formalLeading spec139 x y z w a b c v := by
  dsimp only [formalLeading,spec139]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec139,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec140 : Spec := ⟨425,378,2,76,![528,543],546,523⟩
theorem valid140 : Valid point spec140 := by
  dsimp only [Valid,spec140]
  decide +kernel
theorem row140 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 425)=formalLeading spec140 x y z w a b c v := by
  dsimp only [formalLeading,spec140]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec140,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec141 : Spec := ⟨431,378,2,34,![520,542],532,486⟩
theorem valid141 : Valid point spec141 := by
  dsimp only [Valid,spec141]
  decide +kernel
theorem row141 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 431)=formalLeading spec141 x y z w a b c v := by
  dsimp only [formalLeading,spec141]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec141,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec142 : Spec := ⟨432,378,2,142,![521,570],534,315⟩
theorem valid142 : Valid point spec142 := by
  dsimp only [Valid,spec142]
  decide +kernel
theorem row142 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 432)=formalLeading spec142 x y z w a b c v := by
  dsimp only [formalLeading,spec142]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec142,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec143 : Spec := ⟨433,378,2,143,![510,475],522,274⟩
theorem valid143 : Valid point spec143 := by
  dsimp only [Valid,spec143]
  decide +kernel
theorem row143 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 433)=formalLeading spec143 x y z w a b c v := by
  dsimp only [formalLeading,spec143]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec143,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec144 : Spec := ⟨434,378,2,156,![429,481],381,355⟩
theorem valid144 : Valid point spec144 := by
  dsimp only [Valid,spec144]
  decide +kernel
theorem row144 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 434)=formalLeading spec144 x y z w a b c v := by
  dsimp only [formalLeading,spec144]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec144,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec145 : Spec := ⟨437,378,2,157,![561,295],377,343⟩
theorem valid145 : Valid point spec145 := by
  dsimp only [Valid,spec145]
  decide +kernel
theorem row145 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 437)=formalLeading spec145 x y z w a b c v := by
  dsimp only [formalLeading,spec145]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec145,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec146 : Spec := ⟨438,378,2,163,![384,297],396,416⟩
theorem valid146 : Valid point spec146 := by
  dsimp only [Valid,spec146]
  decide +kernel
theorem row146 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 438)=formalLeading spec146 x y z w a b c v := by
  dsimp only [formalLeading,spec146]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec146,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec147 : Spec := ⟨439,378,2,169,![442,493],456,469⟩
theorem valid147 : Valid point spec147 := by
  dsimp only [Valid,spec147]
  decide +kernel
theorem row147 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 439)=formalLeading spec147 x y z w a b c v := by
  dsimp only [formalLeading,spec147]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec147,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec148 : Spec := ⟨440,378,2,178,![278,572],497,461⟩
theorem valid148 : Valid point spec148 := by
  dsimp only [Valid,spec148]
  decide +kernel
theorem row148 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 440)=formalLeading spec148 x y z w a b c v := by
  dsimp only [formalLeading,spec148]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec148,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec149 : Spec := ⟨441,378,3,11,![573,581,587],482,368⟩
theorem valid149 : Valid point spec149 := by
  dsimp only [Valid,spec149]
  decide +kernel
theorem row149 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 441)=formalLeading spec149 x y z w a b c v := by
  dsimp only [formalLeading,spec149]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec149,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec150 : Spec := ⟨442,378,3,19,![498,501,385],402,431⟩
theorem valid150 : Valid point spec150 := by
  dsimp only [Valid,spec150]
  decide +kernel
theorem row150 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 442)=formalLeading spec150 x y z w a b c v := by
  dsimp only [formalLeading,spec150]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec150,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec151 : Spec := ⟨443,378,3,23,![574,582,588],526,437⟩
theorem valid151 : Valid point spec151 := by
  dsimp only [Valid,spec151]
  decide +kernel
theorem row151 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 443)=formalLeading spec151 x y z w a b c v := by
  dsimp only [formalLeading,spec151]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec151,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec152 : Spec := ⟨444,378,3,41,![446,448,450],346,287⟩
theorem valid152 : Valid point spec152 := by
  dsimp only [Valid,spec152]
  decide +kernel
theorem row152 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 444)=formalLeading spec152 x y z w a b c v := by
  dsimp only [formalLeading,spec152]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec152,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec153 : Spec := ⟨445,378,3,53,![387,511,513],408,368⟩
theorem valid153 : Valid point spec153 := by
  dsimp only [Valid,spec153]
  decide +kernel
theorem row153 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 445)=formalLeading spec153 x y z w a b c v := by
  dsimp only [formalLeading,spec153]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec153,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec154 : Spec := ⟨446,378,3,73,![500,502,386],405,367⟩
theorem valid154 : Valid point spec154 := by
  dsimp only [Valid,spec154]
  decide +kernel
theorem row154 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 446)=formalLeading spec154 x y z w a b c v := by
  dsimp only [formalLeading,spec154]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec154,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec155 : Spec := ⟨447,378,3,85,![441,443,445],345,310⟩
theorem valid155 : Valid point spec155 := by
  dsimp only [Valid,spec155]
  decide +kernel
theorem row155 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 447)=formalLeading spec155 x y z w a b c v := by
  dsimp only [formalLeading,spec155]
  norm_num [eval,monomial,inputs,inputPart13,formalLeading,spec155,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec156 : Spec := ⟨448,378,3,103,![557,563,571],525,431⟩
theorem valid156 : Valid point spec156 := by
  dsimp only [Valid,spec156]
  decide +kernel
theorem row156 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 448)=formalLeading spec156 x y z w a b c v := by
  dsimp only [formalLeading,spec156]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec156,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec157 : Spec := ⟨449,378,3,107,![388,512,515],411,437⟩
theorem valid157 : Valid point spec157 := by
  dsimp only [Valid,spec157]
  decide +kernel
theorem row157 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 449)=formalLeading spec157 x y z w a b c v := by
  dsimp only [formalLeading,spec157]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec157,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec158 : Spec := ⟨452,270,3,13,![250,254,257],216,138⟩
theorem valid158 : Valid point spec158 := by
  dsimp only [Valid,spec158]
  decide +kernel
theorem row158 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 452)=formalLeading spec158 x y z w a b c v := by
  dsimp only [formalLeading,spec158]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec158,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec159 : Spec := ⟨453,270,3,77,![262,265,269],219,141⟩
theorem valid159 : Valid point spec159 := by
  dsimp only [Valid,spec159]
  decide +kernel
theorem row159 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 453)=formalLeading spec159 x y z w a b c v := by
  dsimp only [formalLeading,spec159]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec159,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec160 : Spec := ⟨454,270,5,8,![49,193,212,46,179],18,53⟩
theorem valid160 : Valid point spec160 := by
  dsimp only [Valid,spec160]
  decide +kernel
theorem row160 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 454)=formalLeading spec160 x y z w a b c v := by
  dsimp only [formalLeading,spec160]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec160,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec161 : Spec := ⟨455,270,5,10,![32,207,198,248,177],98,0⟩
theorem valid161 : Valid point spec161 := by
  dsimp only [Valid,spec161]
  decide +kernel
theorem row161 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 455)=formalLeading spec161 x y z w a b c v := by
  dsimp only [formalLeading,spec161]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec161,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec162 : Spec := ⟨456,270,5,11,![67,137,188,266,268],142,4⟩
theorem valid162 : Valid point spec162 := by
  dsimp only [Valid,spec162]
  decide +kernel
theorem row162 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 456)=formalLeading spec162 x y z w a b c v := by
  dsimp only [formalLeading,spec162]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec162,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec163 : Spec := ⟨457,270,5,14,![70,238,194,117,39],22,8⟩
theorem valid163 : Valid point spec163 := by
  dsimp only [Valid,spec163]
  decide +kernel
theorem row163 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 457)=formalLeading spec163 x y z w a b c v := by
  dsimp only [formalLeading,spec163]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec163,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec164 : Spec := ⟨458,270,5,17,![227,228,17,105,231],120,35⟩
theorem valid164 : Valid point spec164 := by
  dsimp only [Valid,spec164]
  decide +kernel
theorem row164 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 458)=formalLeading spec164 x y z w a b c v := by
  dsimp only [formalLeading,spec164]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec164,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec165 : Spec := ⟨459,270,5,22,![11,236,24,115,201],14,32⟩
theorem valid165 : Valid point spec165 := by
  dsimp only [Valid,spec165]
  decide +kernel
theorem row165 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 459)=formalLeading spec165 x y z w a b c v := by
  dsimp only [formalLeading,spec165]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec165,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec166 : Spec := ⟨460,270,5,25,![15,245,82,256,185],17,120⟩
theorem valid166 : Valid point spec166 := by
  dsimp only [Valid,spec166]
  decide +kernel
theorem row166 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 460)=formalLeading spec166 x y z w a b c v := by
  dsimp only [formalLeading,spec166]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec166,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec167 : Spec := ⟨461,270,5,31,![180,120,9,257,259],35,71⟩
theorem valid167 : Valid point spec167 := by
  dsimp only [Valid,spec167]
  decide +kernel
theorem row167 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 461)=formalLeading spec167 x y z w a b c v := by
  dsimp only [formalLeading,spec167]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec167,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec168 : Spec := ⟨462,270,5,37,![222,102,44,225,226],119,66⟩
theorem valid168 : Valid point spec168 := by
  dsimp only [Valid,spec168]
  decide +kernel
theorem row168 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 462)=formalLeading spec168 x y z w a b c v := by
  dsimp only [formalLeading,spec168]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec168,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec169 : Spec := ⟨469,378,2,26,![285,389],397,420⟩
theorem valid169 : Valid point spec169 := by
  dsimp only [Valid,spec169]
  decide +kernel
theorem row169 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 469)=formalLeading spec169 x y z w a b c v := by
  dsimp only [formalLeading,spec169]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec169,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec170 : Spec := ⟨470,378,2,31,![553,415],376,342⟩
theorem valid170 : Valid point spec170 := by
  dsimp only [Valid,spec170]
  decide +kernel
theorem row170 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 470)=formalLeading spec170 x y z w a b c v := by
  dsimp only [formalLeading,spec170]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec170,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec171 : Spec := ⟨471,378,2,33,![482,424],378,352⟩
theorem valid171 : Valid point spec171 := by
  dsimp only [Valid,spec171]
  decide +kernel
theorem row171 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 471)=formalLeading spec171 x y z w a b c v := by
  dsimp only [formalLeading,spec171]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec171,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec172 : Spec := ⟨472,378,2,37,![499,545],516,491⟩
theorem valid172 : Valid point spec172 := by
  dsimp only [Valid,spec172]
  decide +kernel
theorem row172 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 472)=formalLeading spec172 x y z w a b c v := by
  dsimp only [formalLeading,spec172]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec172,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec173 : Spec := ⟨473,378,2,40,![457,563],472,399⟩
theorem valid173 : Valid point spec173 := by
  dsimp only [Valid,spec173]
  decide +kernel
theorem row173 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 473)=formalLeading spec173 x y z w a b c v := by
  dsimp only [formalLeading,spec173]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec173,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec174 : Spec := ⟨474,378,2,43,![440,492],453,468⟩
theorem valid174 : Valid point spec174 := by
  dsimp only [Valid,spec174]
  decide +kernel
theorem row174 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 474)=formalLeading spec174 x y z w a b c v := by
  dsimp only [formalLeading,spec174]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec174,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec175 : Spec := ⟨475,378,2,55,![382,487],392,415⟩
theorem valid175 : Valid point spec175 := by
  dsimp only [Valid,spec175]
  decide +kernel
theorem row175 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 475)=formalLeading spec175 x y z w a b c v := by
  dsimp only [formalLeading,spec175]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec175,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec176 : Spec := ⟨476,378,2,58,![412,565],548,492⟩
theorem valid176 : Valid point spec176 := by
  dsimp only [Valid,spec176]
  decide +kernel
theorem row176 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 476)=formalLeading spec176 x y z w a b c v := by
  dsimp only [formalLeading,spec176]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec176,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec177 : Spec := ⟨477,378,2,59,![576,351],550,518⟩
theorem valid177 : Valid point spec177 := by
  dsimp only [Valid,spec177]
  decide +kernel
theorem row177 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 477)=formalLeading spec177 x y z w a b c v := by
  dsimp only [formalLeading,spec177]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec177,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec178 : Spec := ⟨478,378,2,61,![554,343],350,487⟩
theorem valid178 : Valid point spec178 := by
  dsimp only [Valid,spec178]
  decide +kernel
theorem row178 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 478)=formalLeading spec178 x y z w a b c v := by
  dsimp only [formalLeading,spec178]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec178,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec179 : Spec := ⟨479,378,2,62,![376,339],342,351⟩
theorem valid179 : Valid point spec179 := by
  dsimp only [Valid,spec179]
  decide +kernel
theorem row179 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 479)=formalLeading spec179 x y z w a b c v := by
  dsimp only [formalLeading,spec179]
  norm_num [eval,monomial,inputs,inputPart14,formalLeading,spec179,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec180 : Spec := ⟨480,378,2,64,![374,337],340,349⟩
theorem valid180 : Valid point spec180 := by
  dsimp only [Valid,spec180]
  decide +kernel
theorem row180 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 480)=formalLeading spec180 x y z w a b c v := by
  dsimp only [formalLeading,spec180]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec180,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec181 : Spec := ⟨481,378,2,65,![577,341],348,551⟩
theorem valid181 : Valid point spec181 := by
  dsimp only [Valid,spec181]
  decide +kernel
theorem row181 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 481)=formalLeading spec181 x y z w a b c v := by
  dsimp only [formalLeading,spec181]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec181,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec182 : Spec := ⟨482,378,2,67,![555,349],488,401⟩
theorem valid182 : Valid point spec182 := by
  dsimp only [Valid,spec182]
  decide +kernel
theorem row182 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 482)=formalLeading spec182 x y z w a b c v := by
  dsimp only [formalLeading,spec182]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec182,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec183 : Spec := ⟨483,378,2,68,![532,586],486,395⟩
theorem valid183 : Valid point spec183 := by
  dsimp only [Valid,spec183]
  decide +kernel
theorem row183 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 483)=formalLeading spec183 x y z w a b c v := by
  dsimp only [formalLeading,spec183]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec183,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec184 : Spec := ⟨484,378,2,71,![508,551],521,534⟩
theorem valid184 : Valid point spec184 := by
  dsimp only [Valid,spec184]
  decide +kernel
theorem row184 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 484)=formalLeading spec184 x y z w a b c v := by
  dsimp only [formalLeading,spec184]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec184,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec185 : Spec := ⟨485,378,2,79,![556,401],421,375⟩
theorem valid185 : Valid point spec185 := by
  dsimp only [Valid,spec185]
  decide +kernel
theorem row185 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 485)=formalLeading spec185 x y z w a b c v := by
  dsimp only [formalLeading,spec185]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec185,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec186 : Spec := ⟨486,378,2,80,![472,390],399,423⟩
theorem valid186 : Valid point spec186 := by
  dsimp only [Valid,spec186]
  decide +kernel
theorem row186 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 486)=formalLeading spec186 x y z w a b c v := by
  dsimp only [formalLeading,spec186]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec186,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec187 : Spec := ⟨487,378,2,100,![544,504],294,490⟩
theorem valid187 : Valid point spec187 := by
  dsimp only [Valid,spec187]
  decide +kernel
theorem row187 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 487)=formalLeading spec187 x y z w a b c v := by
  dsimp only [formalLeading,spec187]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec187,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec188 : Spec := ⟨488,378,2,109,![383,469],394,412⟩
theorem valid188 : Valid point spec188 := by
  dsimp only [Valid,spec188]
  decide +kernel
theorem row188 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 488)=formalLeading spec188 x y z w a b c v := by
  dsimp only [formalLeading,spec188]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec188,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec189 : Spec := ⟨489,378,2,110,![392,589],415,376⟩
theorem valid189 : Valid point spec189 := by
  dsimp only [Valid,spec189]
  decide +kernel
theorem row189 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 489)=formalLeading spec189 x y z w a b c v := by
  dsimp only [formalLeading,spec189]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec189,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec190 : Spec := ⟨490,378,2,137,![581,396],416,454⟩
theorem valid190 : Valid point spec190 := by
  dsimp only [Valid,spec190]
  decide +kernel
theorem row190 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 490)=formalLeading spec190 x y z w a b c v := by
  dsimp only [formalLeading,spec190]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec190,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec191 : Spec := ⟨491,378,2,145,![501,461],474,530⟩
theorem valid191 : Valid point spec191 := by
  dsimp only [Valid,spec191]
  decide +kernel
theorem row191 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 491)=formalLeading spec191 x y z w a b c v := by
  dsimp only [formalLeading,spec191]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec191,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec192 : Spec := ⟨492,378,2,149,![582,456],469,394⟩
theorem valid192 : Valid point spec192 := by
  dsimp only [Valid,spec192]
  decide +kernel
theorem row192 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 492)=formalLeading spec192 x y z w a b c v := by
  dsimp only [formalLeading,spec192]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec192,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec193 : Spec := ⟨493,378,2,152,![546,514],523,496⟩
theorem valid193 : Valid point spec193 := by
  dsimp only [Valid,spec193]
  decide +kernel
theorem row193 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 493)=formalLeading spec193 x y z w a b c v := by
  dsimp only [formalLeading,spec193]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec193,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec194 : Spec := ⟨494,378,2,158,![421,592],375,341⟩
theorem valid194 : Valid point spec194 := by
  dsimp only [Valid,spec194]
  decide +kernel
theorem row194 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 494)=formalLeading spec194 x y z w a b c v := by
  dsimp only [formalLeading,spec194]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec194,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec195 : Spec := ⟨496,378,2,38,![471,585],528,546⟩
theorem valid195 : Valid point spec195 := by
  dsimp only [Valid,spec195]
  decide +kernel
theorem row195 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 496)=formalLeading spec195 x y z w a b c v := by
  dsimp only [formalLeading,spec195]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec195,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec196 : Spec := ⟨497,378,2,167,![448,497],461,474⟩
theorem valid196 : Valid point spec196 := by
  dsimp only [Valid,spec196]
  decide +kernel
theorem row196 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 497)=formalLeading spec196 x y z w a b c v := by
  dsimp only [formalLeading,spec196]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec196,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec197 : Spec := ⟨498,378,3,25,![552,560,566],483,369⟩
theorem valid197 : Valid point spec197 := by
  dsimp only [Valid,spec197]
  decide +kernel
theorem row197 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 498)=formalLeading spec197 x y z w a b c v := by
  dsimp only [formalLeading,spec197]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec197,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec198 : Spec := ⟨500,378,7,16,![300,98,342,278,492,522,470],8,72⟩
theorem valid198 : Valid point spec198 := by
  dsimp only [Valid,spec198]
  decide +kernel
theorem row198 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 500)=formalLeading spec198 x y z w a b c v := by
  dsimp only [formalLeading,spec198]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec198,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec199 : Spec := ⟨503,270,2,19,![40,209],232,236⟩
theorem valid199 : Valid point spec199 := by
  dsimp only [Valid,spec199]
  decide +kernel
theorem row199 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 503)=formalLeading spec199 x y z w a b c v := by
  dsimp only [formalLeading,spec199]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec199,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec200 : Spec := ⟨504,270,2,26,![211,148],153,165⟩
theorem valid200 : Valid point spec200 := by
  dsimp only [Valid,spec200]
  decide +kernel
theorem row200 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 504)=formalLeading spec200 x y z w a b c v := by
  dsimp only [formalLeading,spec200]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec200,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec201 : Spec := ⟨505,270,2,28,![197,144],150,163⟩
theorem valid201 : Valid point spec201 := by
  dsimp only [Valid,spec201]
  decide +kernel
theorem row201 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 505)=formalLeading spec201 x y z w a b c v := by
  dsimp only [formalLeading,spec201]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec201,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec202 : Spec := ⟨506,270,2,34,![206,246],238,5⟩
theorem valid202 : Valid point spec202 := by
  dsimp only [Valid,spec202]
  decide +kernel
theorem row202 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 506)=formalLeading spec202 x y z w a b c v := by
  dsimp only [formalLeading,spec202]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec202,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec203 : Spec := ⟨507,270,2,98,![249,231],234,194⟩
theorem valid203 : Valid point spec203 := by
  dsimp only [Valid,spec203]
  decide +kernel
theorem row203 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 507)=formalLeading spec203 x y z w a b c v := by
  dsimp only [formalLeading,spec203]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec203,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec204 : Spec := ⟨510,378,2,25,![552,400],419,544⟩
theorem valid204 : Valid point spec204 := by
  dsimp only [Valid,spec204]
  decide +kernel
theorem row204 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 510)=formalLeading spec204 x y z w a b c v := by
  dsimp only [formalLeading,spec204]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec204,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec205 : Spec := ⟨511,378,2,52,![397,564],420,459⟩
theorem valid205 : Valid point spec205 := by
  dsimp only [Valid,spec205]
  decide +kernel
theorem row205 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 511)=formalLeading spec205 x y z w a b c v := by
  dsimp only [formalLeading,spec205]
  norm_num [eval,monomial,inputs,inputPart15,formalLeading,spec205,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec206 : Spec := ⟨512,378,2,53,![387,489],398,422⟩
theorem valid206 : Valid point spec206 := by
  dsimp only [Valid,spec206]
  decide +kernel
theorem row206 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 512)=formalLeading spec206 x y z w a b c v := by
  dsimp only [formalLeading,spec206]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec206,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec207 : Spec := ⟨513,378,2,57,![402,355],362,438⟩
theorem valid207 : Valid point spec207 := by
  dsimp only [Valid,spec207]
  decide +kernel
theorem row207 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 513)=formalLeading spec207 x y z w a b c v := by
  dsimp only [formalLeading,spec207]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec207,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec208 : Spec := ⟨514,378,2,83,![447,395],414,475⟩
theorem valid208 : Valid point spec208 := by
  dsimp only [Valid,spec208]
  decide +kernel
theorem row208 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 514)=formalLeading spec208 x y z w a b c v := by
  dsimp only [formalLeading,spec208]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec208,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec209 : Spec := ⟨515,378,2,85,![441,416],454,470⟩
theorem valid209 : Valid point spec209 := by
  dsimp only [Valid,spec209]
  decide +kernel
theorem row209 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 515)=formalLeading spec209 x y z w a b c v := by
  dsimp only [formalLeading,spec209]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec209,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec210 : Spec := ⟨516,378,2,103,![557,460],473,520⟩
theorem valid210 : Valid point spec210 := by
  dsimp only [Valid,spec210]
  decide +kernel
theorem row210 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 516)=formalLeading spec210 x y z w a b c v := by
  dsimp only [formalLeading,spec210]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec210,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec211 : Spec := ⟨517,378,2,170,![454,515],470,535⟩
theorem valid211 : Valid point spec211 := by
  dsimp only [Valid,spec211]
  decide +kernel
theorem row211 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 517)=formalLeading spec211 x y z w a b c v := by
  dsimp only [formalLeading,spec211]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec211,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec212 : Spec := ⟨518,270,2,59,![187,239],198,215⟩
theorem valid212 : Valid point spec212 := by
  dsimp only [Valid,spec212]
  decide +kernel
theorem row212 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 518)=formalLeading spec212 x y z w a b c v := by
  dsimp only [formalLeading,spec212]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec212,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec213 : Spec := ⟨524,378,2,11,![573,294],490,452⟩
theorem valid213 : Valid point spec213 := by
  dsimp only [Valid,spec213]
  decide +kernel
theorem row213 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 524)=formalLeading spec213 x y z w a b c v := by
  dsimp only [formalLeading,spec213]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec213,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec214 : Spec := ⟨525,378,2,73,![500,549],495,460⟩
theorem valid214 : Valid point spec214 := by
  dsimp only [Valid,spec214]
  decide +kernel
theorem row214 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 525)=formalLeading spec214 x y z w a b c v := by
  dsimp only [formalLeading,spec214]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec214,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec215 : Spec := ⟨526,378,2,87,![462,425],436,296⟩
theorem valid215 : Valid point spec215 := by
  dsimp only [Valid,spec215]
  decide +kernel
theorem row215 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 526)=formalLeading spec215 x y z w a b c v := by
  dsimp only [formalLeading,spec215]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec215,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec216 : Spec := ⟨527,378,7,7,![4,554,558,442,542,566,570],73,57⟩
theorem valid216 : Valid point spec216 := by
  dsimp only [Valid,spec216]
  decide +kernel
theorem row216 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 527)=formalLeading spec216 x y z w a b c v := by
  dsimp only [formalLeading,spec216]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec216,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec217 : Spec := ⟨528,378,7,10,![289,374,550,468,545,53,461],98,8⟩
theorem valid217 : Valid point spec217 := by
  dsimp only [Valid,spec217]
  decide +kernel
theorem row217 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 528)=formalLeading spec217 x y z w a b c v := by
  dsimp only [formalLeading,spec217]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec217,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec218 : Spec := ⟨529,378,7,20,![494,516,340,24,518,474,519],80,58⟩
theorem valid218 : Valid point spec218 := by
  dsimp only [Valid,spec218]
  decide +kernel
theorem row218 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 529)=formalLeading spec218 x y z w a b c v := by
  dsimp only [formalLeading,spec218]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec218,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec219 : Spec := ⟨530,378,7,22,![490,528,348,282,46,460,295],14,39⟩
theorem valid219 : Valid point spec219 := by
  dsimp only [Valid,spec219]
  decide +kernel
theorem row219 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 530)=formalLeading spec219 x y z w a b c v := by
  dsimp only [formalLeading,spec219]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec219,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec220 : Spec := ⟨534,270,2,29,![186,151],162,212⟩
theorem valid220 : Valid point spec220 := by
  dsimp only [Valid,spec220]
  decide +kernel
theorem row220 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 534)=formalLeading spec220 x y z w a b c v := by
  dsimp only [formalLeading,spec220]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec220,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec221 : Spec := ⟨536,378,2,66,![378,345],352,361⟩
theorem valid221 : Valid point spec221 := by
  dsimp only [Valid,spec221]
  decide +kernel
theorem row221 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 536)=formalLeading spec221 x y z w a b c v := by
  dsimp only [formalLeading,spec221]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec221,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec222 : Spec := ⟨537,270,2,13,![250,199],211,153⟩
theorem valid222 : Valid point spec222 := by
  dsimp only [Valid,spec222]
  decide +kernel
theorem row222 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 537)=formalLeading spec222 x y z w a b c v := by
  dsimp only [formalLeading,spec222]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec222,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec223 : Spec := ⟨538,270,2,38,![232,266],236,195⟩
theorem valid223 : Valid point spec223 := by
  dsimp only [Valid,spec223]
  decide +kernel
theorem row223 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 538)=formalLeading spec223 x y z w a b c v := by
  dsimp only [formalLeading,spec223]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec223,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec224 : Spec := ⟨539,270,2,41,![240,117],220,151⟩
theorem valid224 : Valid point spec224 := by
  dsimp only [Valid,spec224]
  decide +kernel
theorem row224 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 539)=formalLeading spec224 x y z w a b c v := by
  dsimp only [formalLeading,spec224]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec224,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec225 : Spec := ⟨540,270,2,43,![251,109],116,248⟩
theorem valid225 : Valid point spec225 := by
  dsimp only [Valid,spec225]
  decide +kernel
theorem row225 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 540)=formalLeading spec225 x y z w a b c v := by
  dsimp only [formalLeading,spec225]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec225,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec226 : Spec := ⟨543,378,7,8,![305,376,548,454,58,547,475],18,32⟩
theorem valid226 : Valid point spec226 := by
  dsimp only [Valid,spec226]
  decide +kernel
theorem row226 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 543)=formalLeading spec226 x y z w a b c v := by
  dsimp only [formalLeading,spec226]
  norm_num [eval,monomial,inputs,inputPart16,formalLeading,spec226,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec227 : Spec := ⟨544,270,2,49,![244,115],249,234⟩
theorem valid227 : Valid point spec227 := by
  dsimp only [Valid,spec227]
  decide +kernel
theorem row227 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 544)=formalLeading spec227 x y z w a b c v := by
  dsimp only [formalLeading,spec227]
  norm_num [eval,monomial,inputs,inputPart17,formalLeading,spec227,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

def spec228 : Spec := ⟨545,378,2,22,![490,443],452,467⟩
theorem valid228 : Valid point spec228 := by
  dsimp only [Valid,spec228]
  decide +kernel
theorem row228 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 545)=formalLeading spec228 x y z w a b c v := by
  dsimp only [formalLeading,spec228]
  norm_num [eval,monomial,inputs,inputPart17,formalLeading,spec228,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec229 : Spec := ⟨548,378,2,23,![574,422],466,517⟩
theorem valid229 : Valid point spec229 := by
  dsimp only [Valid,spec229]
  decide +kernel
theorem row229 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 548)=formalLeading spec229 x y z w a b c v := by
  dsimp only [formalLeading,spec229]
  norm_num [eval,monomial,inputs,inputPart17,formalLeading,spec229,eigenvalue,rate,Fin.sum_univ_succ] <;> ring
def spec230 : Spec := ⟨549,378,2,41,![446,496],458,393⟩
theorem valid230 : Valid point spec230 := by
  dsimp only [Valid,spec230]
  decide +kernel
theorem row230 (x y z w a b c : ℂ) (v : ℕ → ℂ) :
    eval x y z w a b c v (inputs 549)=formalLeading spec230 x y z w a b c v := by
  dsimp only [formalLeading,spec230]
  norm_num [eval,monomial,inputs,inputPart17,formalLeading,spec230,eigenvalue,rate,Fin.sum_univ_succ] <;> ring

end QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenHeckeSourceBoundBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelTwentySevenHeckeSource

def indicesPart0 : List ℕ := [103,105,109,113,119,120,122,123,125,127,131,132]
theorem original_part0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart0, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec0 valid0 row0 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec1 valid1 row1 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec2 valid2 row2 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec3 valid3 row3 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec4 valid4 row4 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec5 valid5 row5 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec6 valid6 row6 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec7 valid7 row7 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec8 valid8 row8 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec9 valid9 row9 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec10 valid10 row10 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec11 valid11 row11 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart0,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part0

def indicesPart1 : List ℕ := [133,134,137,138,140,199,200,201,203,204,206,208]
theorem original_part1 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart1, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec12 valid12 row12 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec13 valid13 row13 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec14 valid14 row14 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec15 valid15 row15 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec16 valid16 row16 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec17 valid17 row17 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec18 valid18 row18 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec19 valid19 row19 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec20 valid20 row20 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec21 valid21 row21 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec22 valid22 row22 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec23 valid23 row23 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart1,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part1

def indicesPart2 : List ℕ := [210,212,214,226,229,232,239,240,255,256,257,261]
theorem original_part2 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart2, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec24 valid24 row24 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec25 valid25 row25 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec26 valid26 row26 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec27 valid27 row27 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec28 valid28 row28 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec29 valid29 row29 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec30 valid30 row30 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec31 valid31 row31 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec32 valid32 row32 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec33 valid33 row33 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec34 valid34 row34 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec35 valid35 row35 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart2,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part2

def indicesPart3 : List ℕ := [263,264,267,268,269,270,271,272,273,274,275,276]
theorem original_part3 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart3, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec36 valid36 row36 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec37 valid37 row37 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec38 valid38 row38 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec39 valid39 row39 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec40 valid40 row40 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec41 valid41 row41 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec42 valid42 row42 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec43 valid43 row43 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec44 valid44 row44 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec45 valid45 row45 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec46 valid46 row46 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec47 valid47 row47 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart3,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part3

def indicesPart4 : List ℕ := [277,278,279,280,282,284,285,286,287,290,292,293]
theorem original_part4 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart4, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec48 valid48 row48 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec49 valid49 row49 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec50 valid50 row50 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec51 valid51 row51 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec52 valid52 row52 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec53 valid53 row53 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec54 valid54 row54 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec55 valid55 row55 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec56 valid56 row56 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec57 valid57 row57 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec58 valid58 row58 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec59 valid59 row59 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart4,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part4

def indicesPart5 : List ℕ := [294,296,298,319,320,321,322,323,324,325,326,327]
theorem original_part5 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart5, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec60 valid60 row60 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec61 valid61 row61 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec62 valid62 row62 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec63 valid63 row63 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec64 valid64 row64 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec65 valid65 row65 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec66 valid66 row66 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec67 valid67 row67 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec68 valid68 row68 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec69 valid69 row69 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec70 valid70 row70 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec71 valid71 row71 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart5,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part5

def indicesPart6 : List ℕ := [328,329,330,331,332,333,334,335,336,337,338,339]
theorem original_part6 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart6, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec72 valid72 row72 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec73 valid73 row73 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec74 valid74 row74 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec75 valid75 row75 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec76 valid76 row76 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec77 valid77 row77 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec78 valid78 row78 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec79 valid79 row79 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec80 valid80 row80 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec81 valid81 row81 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec82 valid82 row82 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec83 valid83 row83 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart6,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part6

def indicesPart7 : List ℕ := [340,341,342,343,344,345,346,348,349,350,352,353]
theorem original_part7 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart7, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec84 valid84 row84 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec85 valid85 row85 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec86 valid86 row86 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec87 valid87 row87 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec88 valid88 row88 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec89 valid89 row89 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec90 valid90 row90 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec91 valid91 row91 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec92 valid92 row92 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec93 valid93 row93 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec94 valid94 row94 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec95 valid95 row95 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart7,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part7

def indicesPart8 : List ℕ := [354,355,356,358,359,361,363,365,366,367,380,381]
theorem original_part8 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart8, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec96 valid96 row96 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec97 valid97 row97 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec98 valid98 row98 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec99 valid99 row99 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec100 valid100 row100 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec101 valid101 row101 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec102 valid102 row102 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec103 valid103 row103 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec104 valid104 row104 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec105 valid105 row105 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec106 valid106 row106 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec107 valid107 row107 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart8,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part8

def indicesPart9 : List ℕ := [382,383,384,385,386,387,388,389,390,391,392,393]
theorem original_part9 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart9, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec108 valid108 row108 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec109 valid109 row109 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec110 valid110 row110 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec111 valid111 row111 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec112 valid112 row112 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec113 valid113 row113 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec114 valid114 row114 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec115 valid115 row115 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec116 valid116 row116 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec117 valid117 row117 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec118 valid118 row118 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec119 valid119 row119 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart9,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part9

def indicesPart10 : List ℕ := [394,395,396,403,404,405,406,407,408,409,410,411]
theorem original_part10 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart10, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec120 valid120 row120 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec121 valid121 row121 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec122 valid122 row122 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec123 valid123 row123 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec124 valid124 row124 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec125 valid125 row125 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec126 valid126 row126 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec127 valid127 row127 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec128 valid128 row128 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec129 valid129 row129 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec130 valid130 row130 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec131 valid131 row131 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart10,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part10

def indicesPart11 : List ℕ := [412,413,414,415,416,417,418,424,425,431,432,433]
theorem original_part11 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart11, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec132 valid132 row132 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec133 valid133 row133 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec134 valid134 row134 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec135 valid135 row135 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec136 valid136 row136 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec137 valid137 row137 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec138 valid138 row138 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec139 valid139 row139 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec140 valid140 row140 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec141 valid141 row141 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec142 valid142 row142 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec143 valid143 row143 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart11,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part11

def indicesPart12 : List ℕ := [434,437,438,439,440,441,442,443,444,445,446,447]
theorem original_part12 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart12, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec144 valid144 row144 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec145 valid145 row145 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec146 valid146 row146 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec147 valid147 row147 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec148 valid148 row148 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec149 valid149 row149 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec150 valid150 row150 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec151 valid151 row151 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec152 valid152 row152 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec153 valid153 row153 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec154 valid154 row154 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec155 valid155 row155 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart12,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part12

def indicesPart13 : List ℕ := [448,449,452,453,454,455,456,457,458,459,460,461]
theorem original_part13 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart13, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec156 valid156 row156 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec157 valid157 row157 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec158 valid158 row158 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec159 valid159 row159 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec160 valid160 row160 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec161 valid161 row161 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec162 valid162 row162 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec163 valid163 row163 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec164 valid164 row164 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec165 valid165 row165 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec166 valid166 row166 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec167 valid167 row167 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart13,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part13

def indicesPart14 : List ℕ := [462,469,470,471,472,473,474,475,476,477,478,479]
theorem original_part14 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart14, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec168 valid168 row168 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec169 valid169 row169 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec170 valid170 row170 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec171 valid171 row171 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec172 valid172 row172 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec173 valid173 row173 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec174 valid174 row174 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec175 valid175 row175 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec176 valid176 row176 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec177 valid177 row177 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec178 valid178 row178 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec179 valid179 row179 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart14,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part14

def indicesPart15 : List ℕ := [480,481,482,483,484,485,486,487,488,489,490,491]
theorem original_part15 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart15, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec180 valid180 row180 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec181 valid181 row181 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec182 valid182 row182 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec183 valid183 row183 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec184 valid184 row184 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec185 valid185 row185 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec186 valid186 row186 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec187 valid187 row187 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec188 valid188 row188 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec189 valid189 row189 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec190 valid190 row190 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec191 valid191 row191 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart15,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part15

def indicesPart16 : List ℕ := [492,493,494,496,497,498,500,503,504,505,506,507]
theorem original_part16 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart16, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec192 valid192 row192 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec193 valid193 row193 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec194 valid194 row194 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec195 valid195 row195 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec196 valid196 row196 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec197 valid197 row197 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec198 valid198 row198 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec199 valid199 row199 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec200 valid200 row200 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec201 valid201 row201 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec202 valid202 row202 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec203 valid203 row203 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart16,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part16

def indicesPart17 : List ℕ := [510,511,512,513,514,515,516,517,518,524,525,526]
theorem original_part17 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart17, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec204 valid204 row204 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec205 valid205 row205 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec206 valid206 row206 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec207 valid207 row207 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec208 valid208 row208 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec209 valid209 row209 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec210 valid210 row210 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec211 valid211 row211 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec212 valid212 row212 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec213 valid213 row213 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec214 valid214 row214 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec215 valid215 row215 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart17,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part17

def indicesPart18 : List ℕ := [527,528,529,530,534,536,537,538,539,540,543,544]
theorem original_part18 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart18, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec216 valid216 row216 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec217 valid217 row217 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec218 valid218 row218 hm hf
  obtain ⟨B3,h3⟩ := original_source point spec219 valid219 row219 hm hf
  obtain ⟨B4,h4⟩ := original_source point spec220 valid220 row220 hm hf
  obtain ⟨B5,h5⟩ := original_source point spec221 valid221 row221 hm hf
  obtain ⟨B6,h6⟩ := original_source point spec222 valid222 row222 hm hf
  obtain ⟨B7,h7⟩ := original_source point spec223 valid223 row223 hm hf
  obtain ⟨B8,h8⟩ := original_source point spec224 valid224 row224 hm hf
  obtain ⟨B9,h9⟩ := original_source point spec225 valid225 row225 hm hf
  obtain ⟨B10,h10⟩ := original_source point spec226 valid226 row226 hm hf
  obtain ⟨B11,h11⟩ := original_source point spec227 valid227 row227 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 B11))))))))))),?_⟩
  intro s hs i hi
  simp only [indicesPart18,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
  · exact h3 s (lt_of_le_of_lt (by simp) hs)
  · exact h4 s (lt_of_le_of_lt (by simp) hs)
  · exact h5 s (lt_of_le_of_lt (by simp) hs)
  · exact h6 s (lt_of_le_of_lt (by simp) hs)
  · exact h7 s (lt_of_le_of_lt (by simp) hs)
  · exact h8 s (lt_of_le_of_lt (by simp) hs)
  · exact h9 s (lt_of_le_of_lt (by simp) hs)
  · exact h10 s (lt_of_le_of_lt (by simp) hs)
  · exact h11 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part18

def indicesPart19 : List ℕ := [545,548,549]
theorem original_part19 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indicesPart19, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_source point spec228 valid228 row228 hm hf
  obtain ⟨B1,h1⟩ := original_source point spec229 valid229 row229 hm hf
  obtain ⟨B2,h2⟩ := original_source point spec230 valid230 row230 hm hf
  refine ⟨(max B0 (max B1 B2)),?_⟩
  intro s hs i hi
  simp only [indicesPart19,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact h0 s (lt_of_le_of_lt (by simp) hs)
  · exact h1 s (lt_of_le_of_lt (by simp) hs)
  · exact h2 s (lt_of_le_of_lt (by simp) hs)
#print axioms original_part19

end QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySevenHeckeSourcesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
def indices : List ℕ := indicesPart0 ++ indicesPart1 ++ indicesPart2 ++ indicesPart3 ++ indicesPart4 ++ indicesPart5 ++ indicesPart6 ++ indicesPart7 ++ indicesPart8 ++ indicesPart9 ++ indicesPart10 ++ indicesPart11 ++ indicesPart12 ++ indicesPart13 ++ indicesPart14 ++ indicesPart15 ++ indicesPart16 ++ indicesPart17 ++ indicesPart18 ++ indicesPart19
/-- All 231 selected Hecke rows hold simultaneously on a right half-plane,
from the original level-27 hypotheses; no eigenvalue nonvanishing is required. -/
theorem original_hecke_sources {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 27 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ∀ i ∈ indices, physicalRow point i m f s=0 := by
  obtain ⟨B0,h0⟩ := original_part0 hm hf
  obtain ⟨B1,h1⟩ := original_part1 hm hf
  obtain ⟨B2,h2⟩ := original_part2 hm hf
  obtain ⟨B3,h3⟩ := original_part3 hm hf
  obtain ⟨B4,h4⟩ := original_part4 hm hf
  obtain ⟨B5,h5⟩ := original_part5 hm hf
  obtain ⟨B6,h6⟩ := original_part6 hm hf
  obtain ⟨B7,h7⟩ := original_part7 hm hf
  obtain ⟨B8,h8⟩ := original_part8 hm hf
  obtain ⟨B9,h9⟩ := original_part9 hm hf
  obtain ⟨B10,h10⟩ := original_part10 hm hf
  obtain ⟨B11,h11⟩ := original_part11 hm hf
  obtain ⟨B12,h12⟩ := original_part12 hm hf
  obtain ⟨B13,h13⟩ := original_part13 hm hf
  obtain ⟨B14,h14⟩ := original_part14 hm hf
  obtain ⟨B15,h15⟩ := original_part15 hm hf
  obtain ⟨B16,h16⟩ := original_part16 hm hf
  obtain ⟨B17,h17⟩ := original_part17 hm hf
  obtain ⟨B18,h18⟩ := original_part18 hm hf
  obtain ⟨B19,h19⟩ := original_part19 hm hf
  refine ⟨(max B0 (max B1 (max B2 (max B3 (max B4 (max B5 (max B6 (max B7 (max B8 (max B9 (max B10 (max B11 (max B12 (max B13 (max B14 (max B15 (max B16 (max B17 (max B18 B19))))))))))))))))))),?_⟩
  intro s hs i hi
  simp only [indices,List.mem_append,or_assoc] at hi
  rcases hi with hi0 | hi1 | hi2 | hi3 | hi4 | hi5 | hi6 | hi7 | hi8 | hi9 | hi10 | hi11 | hi12 | hi13 | hi14 | hi15 | hi16 | hi17 | hi18 | hi19
  · exact h0 s (lt_of_le_of_lt (by simp) hs) i hi0
  · exact h1 s (lt_of_le_of_lt (by simp) hs) i hi1
  · exact h2 s (lt_of_le_of_lt (by simp) hs) i hi2
  · exact h3 s (lt_of_le_of_lt (by simp) hs) i hi3
  · exact h4 s (lt_of_le_of_lt (by simp) hs) i hi4
  · exact h5 s (lt_of_le_of_lt (by simp) hs) i hi5
  · exact h6 s (lt_of_le_of_lt (by simp) hs) i hi6
  · exact h7 s (lt_of_le_of_lt (by simp) hs) i hi7
  · exact h8 s (lt_of_le_of_lt (by simp) hs) i hi8
  · exact h9 s (lt_of_le_of_lt (by simp) hs) i hi9
  · exact h10 s (lt_of_le_of_lt (by simp) hs) i hi10
  · exact h11 s (lt_of_le_of_lt (by simp) hs) i hi11
  · exact h12 s (lt_of_le_of_lt (by simp) hs) i hi12
  · exact h13 s (lt_of_le_of_lt (by simp) hs) i hi13
  · exact h14 s (lt_of_le_of_lt (by simp) hs) i hi14
  · exact h15 s (lt_of_le_of_lt (by simp) hs) i hi15
  · exact h16 s (lt_of_le_of_lt (by simp) hs) i hi16
  · exact h17 s (lt_of_le_of_lt (by simp) hs) i hi17
  · exact h18 s (lt_of_le_of_lt (by simp) hs) i hi18
  · exact h19 s (lt_of_le_of_lt (by simp) hs) i hi19
#print axioms original_hecke_sources
end QuantitativeArithmeticSmallLevelTwentySevenHeckeSource
end
end
