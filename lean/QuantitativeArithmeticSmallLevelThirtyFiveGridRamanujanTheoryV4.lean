module

public import Mathlib.Data.Rat.Cast.CharZero
public import QuantitativeArithmeticRamifiedFullTraceV1
public import SmallLevelTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open Complex Set MeasureTheory SmallLevelTaylor FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct

/-- Original 53 F rows followed by the 36 shifted q=1 Fricke rows.
The latter share exactly the same globally chosen original Fricke sign. -/
def taylorSpecs : Fin 89 → ℕ×ℤ := ![(3,1),(3,-1),(3,2),(3,-2),(3,4),(3,-4),(3,5),(3,-5),(3,7),(3,-7),(3,10),(3,-10),(5,1),(5,-1),(5,2),(5,-2),(5,3),(5,-3),(5,4),(5,-4),(5,6),(5,-6),(5,9),(5,-9),(5,12),(5,-12),(5,14),(5,-14),(7,1),(7,-1),(7,2),(7,-2),(7,3),(7,-3),(7,4),(7,5),(7,-5),(7,9),(7,-9),(7,10),(10,1),(10,-1),(15,1),(15,-1),(15,2),(15,-2),(15,4),(15,-4),(21,1),(21,-1),(30,1),(30,-1),(35,1),(1,420),(1,210),(1,252),(1,315),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,9),(1,10),(1,12),(1,14),(1,15),(1,18),(1,20),(1,21),(1,28),(1,30),(1,35),(1,36),(1,42),(1,45),(1,60),(1,63),(1,70),(1,84),(1,90),(1,105),(1,126),(1,140),(1,180),(1,-2),(1,-1)]

def taylorInputIds : Fin 89 → ℕ := ![1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1433,1434,1435,1436,1437,1438,1467,1468,1469,1470,1471,1472,1473,1475,1476,1479,1480,1481,1504,1505,1530,1531,1532,1533,1534,1535,1543,1544,1556,1557,1561,0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,64,65]
def entireSpecs : Fin 11 → ℕ := ![1,3,5,7,10,14,15,21,30,42,210]
def entireInputIds : Fin 11 → ℕ := ![4,1395,1420,1466,1503,1516,1529,1542,1555,1579,1598]
def heckeSpecs : Fin 66 → ℕ×ℤ := ![(2,2),(2,4),(2,5),(2,7),(2,8),(2,9),(2,10),(2,11),(2,14),(2,15),(2,16),(2,17),(2,18),(2,19),(2,20),(2,22),(2,23),(2,25),(2,26),(2,30),(2,31),(2,37),(2,43),(2,45),(2,48),(2,49),(2,50),(2,51),(2,52),(2,53),(2,54),(2,55),(2,56),(2,57),(2,63),(2,68),(2,74),(2,80),(2,86),(2,87),(2,88),(2,89),(2,95),(2,97),(3,3),(3,6),(3,7),(3,10),(3,11),(3,12),(3,13),(3,16),(3,17),(3,18),(3,22),(3,23),(3,27),(3,28),(3,29),(3,31),(3,33),(3,47),(3,58),(3,59),(5,11),(5,17)]
def heckeInputIds : Fin 66 → ℕ := ![1603,1605,1606,1608,1609,1610,1611,1612,1615,1616,1617,1618,1619,1620,1621,1623,1624,1626,1627,1631,1632,1638,1644,1646,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1664,1669,1675,1681,1687,1688,1689,1690,1696,1698,1709,1712,1713,1716,1717,1718,1719,1722,1723,1724,1728,1729,1733,1734,1735,1737,1739,1753,1764,1765,1787,1793]
def ordinaryTaylorIndex (i : Fin 53) : Fin 89 := ⟨i.val,by omega⟩
def frickeTaylorIndex (i : Fin 36) : Fin 89 := ⟨53+i.val,by omega⟩

def rowQ (i : Fin 89) : ℕ := (taylorSpecs i).1
def rowT (i : Fin 89) : ℤ := (taylorSpecs i).2
def rowL (i : Fin 89) : ℕ := Nat.lcm 35 ((rowQ i)^2)
def rowD (i : Fin 89) : ℤ := (210:ℤ)^2/(rowL i:ℤ)
def rowPartner (i : Fin 89) : ℤ := -(rowD i/rowT i)

/-- Kernel-checked finite arithmetic certificate; no native evaluation. -/
theorem taylorSpecs_valid : ∀ i : Fin 89,
    0<rowQ i ∧ rowQ i∣210 ∧ rowT i≠0 ∧
      (rowL i:ℤ)*rowD i=(210:ℤ)^2 ∧ rowT i∣rowD i := by decide

def rowCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 89) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (rowL i) ((rowT i:ℝ)/210) (root 35 f (rowQ i)*ε*I^k) n s

def rowError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 89) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f (rowQ i)) k)
    (rowL i) ((rowT i:ℝ)/210) (root 35 f (rowQ i)*ε*I^k) (M+1)) s

/-- All 89 actual Taylor rows of the level-35 system, with one sign and one
common initial half-plane for all rows and all Taylor orders. This is the
analytic closed-grid input, not yet the determinant or pole-removal proof. -/
theorem original_taylor_system {k : ℕ} (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∃ B : ℝ, ∀ i : Fin 89, ∀ M : ℕ,
      AnalyticOnNhd ℂ (rowError k f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum k f 210 (rowQ i) (rowT i) s-
          rowCoefficient k f ε i 0 s*gridSum k f 210 (rowQ i) (rowPartner i) s=
        rowError k f ε i M s+
          ∑ n∈Finset.range M, rowCoefficient k f ε i (n+1) s*
            gridSum k f 210 (rowQ i) (rowPartner i) (s+((n:ℂ)+1)) := by
  obtain ⟨ε,hε,hrows⟩ := original_closed_grid_taylor_rows (by decide : 0<35) hk hf
  have hi (i : Fin 89) := hrows 210 (rowQ i) (by decide) (taylorSpecs_valid i).1
    (taylorSpecs_valid i).2.1 (rowT i) (rowD i) (taylorSpecs_valid i).2.2.1
    (taylorSpecs_valid i).2.2.2.1 (taylorSpecs_valid i).2.2.2.2
  choose b hb using hi
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 89) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨ε,hε,B,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

theorem rowCoefficient_analytic (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (i : Fin 89) (n : ℕ) (s : ℂ) : AnalyticAt ℂ (rowCoefficient k f ε i n) s := by
  apply taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<35) (pow_pos (taylorSpecs_valid i).1 2)
  · exact div_ne_zero (by exact_mod_cast (taylorSpecs_valid i).2.2.1) (by norm_num)

#print axioms taylorSpecs_valid
#print axioms original_taylor_system
#print axioms rowCoefficient_analytic
theorem entireSpecs_valid : ∀ i : Fin 11, 0<entireSpecs i ∧ entireSpecs i∣210 := by decide

theorem heckeSpecs_valid : ∀ i : Fin 66,
    (heckeSpecs i).1.Prime ∧ (heckeSpecs i).1∣210 := by decide

end QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanEntireV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive

/-- The eleven Ramanujan rows selected by the 210-grid determinant certificate
have actual entire extensions from the original hypotheses. -/
theorem original_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    (∀ i : Fin 11, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 35 k f (entireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 11, ∀ s : ℂ, B<s.re →
        ramanujanEntire 35 k f (entireSpecs i) s=gridSum k f 210 (entireSpecs i) 0 s := by
  have hh (i : Fin 11) := original_ramanujan_entire (by decide : 0<35) hk hf (entireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
    rw [hb i s (lt_of_le_of_lt hbi hs)]
    have hg := ramanujanAdditive_grid k f (by decide : 0<210)
      (entireSpecs_valid i).1 (entireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

#print axioms original_entire_rows
end QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanHeckeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticRetainedReconstruction

/-- The bad-prime additive Mellin identity follows from the actual original
Euler coefficient recurrence. No additive continuation is assumed. -/
theorem normalized_additive_bad_hecke {N m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f)
    {p : ℕ} (hp : p.Prime) (hpN : p∣N) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range p, original (2*m) f (r+(j:ℝ)/p) s)-
        ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*
          original (2*m) f ((p:ℝ)*r) s=0 := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  obtain ⟨B,hB⟩ := additive_convergence_halfplane
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
  refine ⟨B,?_⟩
  intro r s hs
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp.pos
  let a := fullCoefficients f (2*m)
  let C : ℂ := QuantitativeArithmeticRamifiedFullTrace.multiplier f m p
  have h1 := dilated_ray_hasMellin hpR r s (hB ((p:ℝ)*r) s hs).1
  simp only [Complex.ofReal_natCast] at h1
  have he : EqOn
      (fun y : ℝ => ∑ j∈Finset.range p, fourier a (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I))
      (fun y : ℝ => C*fourier a ((p:ℂ)*((r:ℂ)+(y:ℂ)*I))) (Ioi 0) := by
    intro y hy
    dsimp only
    have hh := QuantitativeArithmeticRamifiedFullTrace.original_complete_even
      hf.toEulerData hp hpN hm (z := (r:ℂ)+(y:ℂ)*I) (by simpa using hy)
    change completeTwist (fourier a) p ((r:ℂ)+(y:ℂ)*I)=_ at hh
    have hsum : (∑ j∈Finset.range p, fourier a (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I))=
        completeTwist (fourier a) p ((r:ℂ)+(y:ℂ)*I) := by
      unfold completeTwist
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      push_cast
      ring
    rw [hsum]
    exact hh
  have hsum : mellin
      (fun y : ℝ => ∑ j∈Finset.range p, fourier a (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I)) s=
      ∑ j∈Finset.range p, original (2*m) f (r+(j:ℝ)/p) s := by
    unfold mellin
    simp only [Finset.smul_sum]
    rw [integral_finsetSum (Finset.range p) (fun j _ => (hB (r+(j:ℝ)/p) s hs).1)]
    apply Finset.sum_congr rfl
    intro j _
    exact (hB (r+(j:ℝ)/p) s hs).2
  have heq : (∑ j∈Finset.range p, original (2*m) f (r+(j:ℝ)/p) s)=
      C*(p:ℂ)^(-s)*original (2*m) f ((p:ℝ)*r) s := by
    rw [←hsum,mellin_congr_positive he s]
    change mellin (fun y : ℝ => C • fourier a ((p:ℂ)*((r:ℂ)+(y:ℂ)*I))) s=_
    rw [mellin_const_smul,h1.2,(hB ((p:ℝ)*r) s hs).2]
    simp only [smul_eq_mul,mul_assoc,original]
  rw [heq]
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp.pos
  rw [show (m:ℂ)-s=(m:ℂ)+(-s) by ring,Complex.cpow_add _ _ hp0,Complex.cpow_natCast]
  dsimp [C,QuantitativeArithmeticRamifiedFullTrace.multiplier]
  ring

def heckeLeading (m : ℕ) (f : ℕ→ℂ) (p : ℕ) (j : ℤ) (s : ℂ) : ℂ :=
  (∑ a∈Finset.range p, grid (2*m) f 210 (j+(a:ℤ)*(210/p:ℕ)) s)-
    ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*grid (2*m) f 210 ((p:ℤ)*j) s+
    if p∣35 then 0 else
      ((p:ℂ)^((m:ℂ)-s))^2*grid (2*m) f 210 ((p:ℤ)^2*j) s

theorem original_hecke_grid {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    {p : ℕ} (hp : p.Prime) (hpQ : p∣210) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re → heckeLeading m f p j s=0 := by
  have hsum (j : ℤ) (s : ℂ) :
      (∑ a∈Finset.range p, original (2*m) f ((j:ℝ)/210+(a:ℝ)/p) s)=
      ∑ a∈Finset.range p, grid (2*m) f 210 (j+(a:ℤ)*(210/p:ℕ)) s := by
    apply Finset.sum_congr rfl
    intro a _
    unfold grid
    congr 1
    simpa only [Nat.cast_ofNat] using
      (grid_translation (by decide : 0<210) hp.pos hpQ (t := j) (j := a))
  have h1 (j : ℤ) : (p:ℝ)*((j:ℝ)/210)=(((p:ℤ)*j:ℤ):ℝ)/210 := by
    push_cast
    ring
  have h2 (j : ℤ) : (p:ℝ)^2*((j:ℝ)/210)=(((p:ℤ)^2*j:ℤ):ℝ)/210 := by
    push_cast
    ring
  by_cases hb : p∣35
  · obtain ⟨B,hB⟩ := normalized_additive_bad_hecke hm hf hp hb
    refine ⟨B,?_⟩
    intro j s hs
    have hh := hB ((j:ℝ)/210) s hs
    rw [hsum,h1] at hh
    simpa only [heckeLeading,ite_eq_left hb,add_zero,grid,Nat.cast_ofNat] using hh
  · obtain ⟨B,hB⟩ := normalized_additive_hecke hf hp hb
    refine ⟨B,?_⟩
    intro j s hs
    have hh := hB ((j:ℝ)/210) s hs
    rw [hsum,h1,h2] at hh
    simpa only [heckeLeading,ite_eq_right hb,grid,Nat.cast_ofNat] using hh

/-- All 66 actual selected Hecke rows, good and bad, in one half-plane. -/
theorem original_selected_hecke_rows {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ B : ℝ, ∀ i : Fin 66, ∀ s : ℂ, B<s.re →
      heckeLeading m f (heckeSpecs i).1 (heckeSpecs i).2 s=0 := by
  have hi (i : Fin 66) := original_hecke_grid hm hf
    (heckeSpecs_valid i).1 (heckeSpecs_valid i).2
  choose b hb using hi
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  refine ⟨B,?_⟩
  intro i s hs
  exact hb i (heckeSpecs i).2 s
    (lt_of_le_of_lt (Finset.le_sup' b (Finset.mem_univ i)) hs)

#print axioms normalized_additive_bad_hecke
#print axioms original_hecke_grid
#print axioms original_selected_hecke_rows
end QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanRatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct

/- Ramanujan grid identities and local phase parameters at level 35. -/

def phaseRoot (m : ℕ) (ε : ℂ) : ℂ := ε*I^(2*m)
def badFive (f : ℕ→ℂ) : ℂ := (Real.sqrt 5:ℂ)*f 5
def badSeven (f : ℕ→ℂ) : ℂ := (Real.sqrt 7:ℂ)*f 7
def localRoot (u v : ℂ) (q : ℕ) : ℂ :=
  (if 5∣q then -u else 1)*(if 7∣q then -v else 1)

theorem phaseRoot_sign (m : ℕ) {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    phaseRoot m ε=1 ∨ phaseRoot m ε= -1 := by
  unfold phaseRoot
  rw [pow_mul,I_sq]
  rcases neg_one_pow_eq_or ℂ m with hm|hm <;>
    rcases hε with rfl|rfl <;> simp [hm]

theorem root_five (f : ℕ→ℂ) : root 35 f 5= -badFive f := by
  have hp : (5:ℕ).primeFactors={5} := (by decide : Nat.Prime 5).primeFactors
  have hv : (5:ℕ).factorization 5=1 := (by decide : Nat.Prime 5).factorization_self
  norm_num [root,hp,hv,FinitenessNormalizedTwistLocal.sign,badFive]
  ring

theorem root_seven (f : ℕ→ℂ) : root 35 f 7= -badSeven f := by
  have hp : (7:ℕ).primeFactors={7} := (by decide : Nat.Prime 7).primeFactors
  have hv : (7:ℕ).factorization 7=1 := (by decide : Nat.Prime 7).factorization_self
  norm_num [root,hp,hv,FinitenessNormalizedTwistLocal.sign,badSeven]
  ring

theorem badFive_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 35 f) :
    badFive f=1 ∨ badFive f= -1 := by
  have h := root_unit hf 5
  rw [root_five] at h
  rcases h with h|h
  · right
    linear_combination -h
  · left
    linear_combination -h

theorem badSeven_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 35 f) :
    badSeven f=1 ∨ badSeven f= -1 := by
  have h := root_unit hf 7
  rw [root_seven] at h
  rcases h with h|h
  · right
    linear_combination -h
  · left
    linear_combination -h

theorem rowQ_values (i : Fin 89) :
    rowQ i=1 ∨ rowQ i=3 ∨ rowQ i=5 ∨ rowQ i=7 ∨ rowQ i=10 ∨
      rowQ i=15 ∨ rowQ i=21 ∨ rowQ i=30 ∨ rowQ i=35 := by
  revert i
  decide

/-- The three signs are exactly the Fricke slash sign and the two actual
ramified Euler signs; the good-prime eigenvalues do not occur here. -/
theorem selected_root_scalar (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 89) :
    root 35 f (rowQ i)*ε*I^(2*m)=
      phaseRoot m ε*localRoot (badFive f) (badSeven f) (rowQ i) := by
  have hp5 : (5:ℕ).primeFactors={5} := (by decide : Nat.Prime 5).primeFactors
  have hp7 : (7:ℕ).primeFactors={7} := (by decide : Nat.Prime 7).primeFactors
  have hp10 : (10:ℕ).primeFactors={2,5} := by
    rw [show (10:ℕ)=2*5 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp5]
  have hp15 : (15:ℕ).primeFactors={3,5} := by
    rw [show (15:ℕ)=3*5 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp5]
  have hp21 : (21:ℕ).primeFactors={3,7} := by
    rw [show (21:ℕ)=3*7 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp7]
  have hp30 : (30:ℕ).primeFactors={2,3,5} := by
    rw [show (30:ℕ)=2*15 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp15,Finset.insert_comm]
  have hp35 : (35:ℕ).primeFactors={5,7} := by
    rw [show (35:ℕ)=5*7 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num [hp5,hp7]
  have hv5 : (5:ℕ).factorization 5=1 := (by decide : Nat.Prime 5).factorization_self
  have hv7 : (7:ℕ).factorization 7=1 := (by decide : Nat.Prime 7).factorization_self
  have hv10 : (10:ℕ).factorization 5=1 := by
    rw [show (10:ℕ)=2*5 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣2),hv5]
  have hv15 : (15:ℕ).factorization 5=1 := by
    rw [show (15:ℕ)=3*5 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣3),hv5]
  have hv21 : (21:ℕ).factorization 7=1 := by
    rw [show (21:ℕ)=3*7 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬7∣3),hv7]
  have hv30 : (30:ℕ).factorization 5=1 := by
    rw [show (30:ℕ)=6*5 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣6),hv5]
  have hv35a : (35:ℕ).factorization 5=1 := by
    rw [show (35:ℕ)=5*7 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣7),hv5]
  have hv35b : (35:ℕ).factorization 7=1 := by
    rw [show (35:ℕ)=5*7 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬7∣5),hv7]
  rcases rowQ_values i with h|h|h|h|h|h|h|h|h <;> rw [h] <;>
    norm_num [root,hp5,hp7,hp10,hp15,hp21,hp30,hp35,
      hv5,hv7,hv10,hv15,hv21,hv30,hv35a,hv35b,FinitenessNormalizedTwistLocal.sign,
      phaseRoot,localRoot,badFive,badSeven] <;> ring

def rowRate (i : Fin 89) : ℚ := (rowL i:ℚ)*((rowT i:ℚ)/210)^2

/-- Exact signed valuations of L(t/210)^2. This is a rational identity,
not a logarithmic or numerical factorization. -/
def ratePower (p : ℕ) (i : Fin 89) : ℤ :=
  ((rowL i).factorization p:ℤ)+2*((rowT i).natAbs.factorization p:ℤ)-
    2*((210:ℕ).factorization p:ℤ)

/-- Literal prime exponents. Their required mathematical property is
verified directly by the rational identity `rate_certificate` below. -/
def ratePowers (i : Fin 89) : ℤ×ℤ×ℤ×ℤ :=
    ![(-2,0,-1,-1),(-2,0,-1,-1),(0,0,-1,-1),(0,0,-1,-1),
      (2,0,-1,-1),(2,0,-1,-1),(-2,0,1,-1),(-2,0,1,-1),
      (-2,0,-1,1),(-2,0,-1,1),(0,0,1,-1),(0,0,1,-1),
      (-2,-2,0,-1),(-2,-2,0,-1),(0,-2,0,-1),(0,-2,0,-1),
      (-2,0,0,-1),(-2,0,0,-1),(2,-2,0,-1),(2,-2,0,-1),
      (0,0,0,-1),(0,0,0,-1),(-2,2,0,-1),(-2,2,0,-1),
      (2,0,0,-1),(2,0,0,-1),(0,-2,0,1),(0,-2,0,1),
      (-2,-2,-1,0),(-2,-2,-1,0),(0,-2,-1,0),(0,-2,-1,0),
      (-2,0,-1,0),(-2,0,-1,0),(2,-2,-1,0),(-2,-2,1,0),
      (-2,-2,1,0),(-2,2,-1,0),(-2,2,-1,0),(0,-2,1,0),
      (0,-2,0,-1),(0,-2,0,-1),(-2,0,0,-1),(-2,0,0,-1),
      (0,0,0,-1),(0,0,0,-1),(2,0,0,-1),(2,0,0,-1),
      (-2,0,-1,0),(-2,0,-1,0),(0,0,0,-1),(0,0,0,-1),
      (-2,-2,0,0),
      (2,0,1,1),(0,0,1,1),(2,2,-1,1),(-2,2,1,1),
      (-2,-2,-1,-1),(0,-2,-1,-1),(-2,0,-1,-1),(2,-2,-1,-1),
      (-2,-2,1,-1),(0,0,-1,-1),(-2,-2,-1,1),(-2,2,-1,-1),
      (0,-2,1,-1),(2,0,-1,-1),(0,-2,-1,1),(-2,0,1,-1),
      (0,2,-1,-1),(2,-2,1,-1),(-2,0,-1,1),(2,-2,-1,1),
      (0,0,1,-1),(-2,-2,1,1),(2,2,-1,-1),(0,0,-1,1),
      (-2,2,1,-1),(2,0,1,-1),(-2,2,-1,1),(0,-2,1,1),
      (2,0,-1,1),(0,2,1,-1),(-2,0,1,1),(0,2,-1,1),
      (2,-2,1,1),(2,2,1,-1),(0,-2,-1,-1),(-2,-2,-1,-1)] i

/-- A literal evaluation table lets downstream row comparisons avoid
unfolding arithmetic factorizations inside complex-valued expressions. -/
theorem ratePowers_values : ∀ i : Fin 89, ratePowers i=
    ![(-2,0,-1,-1),(-2,0,-1,-1),(0,0,-1,-1),(0,0,-1,-1),
      (2,0,-1,-1),(2,0,-1,-1),(-2,0,1,-1),(-2,0,1,-1),
      (-2,0,-1,1),(-2,0,-1,1),(0,0,1,-1),(0,0,1,-1),
      (-2,-2,0,-1),(-2,-2,0,-1),(0,-2,0,-1),(0,-2,0,-1),
      (-2,0,0,-1),(-2,0,0,-1),(2,-2,0,-1),(2,-2,0,-1),
      (0,0,0,-1),(0,0,0,-1),(-2,2,0,-1),(-2,2,0,-1),
      (2,0,0,-1),(2,0,0,-1),(0,-2,0,1),(0,-2,0,1),
      (-2,-2,-1,0),(-2,-2,-1,0),(0,-2,-1,0),(0,-2,-1,0),
      (-2,0,-1,0),(-2,0,-1,0),(2,-2,-1,0),(-2,-2,1,0),
      (-2,-2,1,0),(-2,2,-1,0),(-2,2,-1,0),(0,-2,1,0),
      (0,-2,0,-1),(0,-2,0,-1),(-2,0,0,-1),(-2,0,0,-1),
      (0,0,0,-1),(0,0,0,-1),(2,0,0,-1),(2,0,0,-1),
      (-2,0,-1,0),(-2,0,-1,0),(0,0,0,-1),(0,0,0,-1),
      (-2,-2,0,0),
      (2,0,1,1),(0,0,1,1),(2,2,-1,1),(-2,2,1,1),
      (-2,-2,-1,-1),(0,-2,-1,-1),(-2,0,-1,-1),(2,-2,-1,-1),
      (-2,-2,1,-1),(0,0,-1,-1),(-2,-2,-1,1),(-2,2,-1,-1),
      (0,-2,1,-1),(2,0,-1,-1),(0,-2,-1,1),(-2,0,1,-1),
      (0,2,-1,-1),(2,-2,1,-1),(-2,0,-1,1),(2,-2,-1,1),
      (0,0,1,-1),(-2,-2,1,1),(2,2,-1,-1),(0,0,-1,1),
      (-2,2,1,-1),(2,0,1,-1),(-2,2,-1,1),(0,-2,1,1),
      (2,0,-1,1),(0,2,1,-1),(-2,0,1,1),(0,2,-1,1),
      (2,-2,1,1),(2,2,1,-1),(0,-2,-1,-1),(-2,-2,-1,-1)] i := by
  intro i
  rfl

theorem rate_certificate (i : Fin 89) :
    rowRate i=(2:ℚ)^(ratePowers i).1*(3:ℚ)^(ratePowers i).2.1*
      (5:ℚ)^(ratePowers i).2.2.1*(7:ℚ)^(ratePowers i).2.2.2 := by
  rw [ratePowers_values]
  fin_cases i <;> norm_num [rowRate,rowL,rowQ,rowT,taylorSpecs]

/-- Variables X,Y,Z,W stand for 2^(s-m),3^(s-m),5^(s-m),7^(s-m).
Thus the exponents here have the same sign as the rational rate valuations. -/
def rateMonomial (i : Fin 89) (X Y Z W : ℂ) : ℂ :=
  X^(ratePowers i).1*Y^(ratePowers i).2.1*
    Z^(ratePowers i).2.2.1*W^(ratePowers i).2.2.2

theorem positive_zpow_cpow {p : ℝ} (hp : 0<p) (a : ℤ) (s : ℂ) :
    ((p:ℂ)^a)^s=((p:ℂ)^s)^a := by
  have harg : (p:ℂ).arg=0 := arg_ofReal_of_nonneg hp.le
  exact (Complex.cpow_int_mul' (x := (p:ℂ)) (n := a)
    (by simp [harg,Real.pi_pos]) (by simp [harg,Real.pi_pos.le]) s).symm.trans
      (Complex.cpow_int_mul (p:ℂ) a s)

theorem rate_complex_power (i : Fin 89) (s : ℂ) :
    (rowRate i:ℂ)^s=
      rateMonomial i ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) := by
  have hr : (rowRate i:ℝ)=(2:ℝ)^(ratePowers i).1*
      (3:ℝ)^(ratePowers i).2.1*(5:ℝ)^(ratePowers i).2.2.1*
      (7:ℝ)^(ratePowers i).2.2.2 := by
    simpa only [Rat.cast_mul,Rat.cast_zpow,Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q:ℝ)) (rate_certificate i)
  have he : (rowRate i:ℂ)=(((2:ℝ)^(ratePowers i).1*
      (3:ℝ)^(ratePowers i).2.1*(5:ℝ)^(ratePowers i).2.2.1*
      (7:ℝ)^(ratePowers i).2.2.2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_ratCast] using congrArg (fun r : ℝ => (r:ℂ)) hr
  rw [he,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [positive_zpow_cpow (by norm_num : (0:ℝ)<2),
    positive_zpow_cpow (by norm_num : (0:ℝ)<3),
    positive_zpow_cpow (by norm_num : (0:ℝ)<5),
    positive_zpow_cpow (by norm_num : (0:ℝ)<7)]
  rfl

/-- Exact identification of all89 Taylor leading coefficients at every
complex s, using the same variables as the selectedRowsV3 certificates. -/
theorem rowCoefficient_complex (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 89) :
    rowCoefficient (2*m) f ε i 0 s=
      phaseRoot m ε*localRoot (badFive f) (badSeven f) (rowQ i)*
        rateMonomial i ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
          ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ))) := by
  unfold rowCoefficient taylorRowScalar
  simp only [pow_zero,mul_one,Ring.choose_zero_right]
  rw [selected_root_scalar]
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  rw [hex]
  have hr : (((rowL i:ℝ)*((rowT i:ℝ)/210)^2:ℝ):ℂ)=(rowRate i:ℂ) := by
    unfold rowRate
    push_cast
    rfl
  rw [hr,rate_complex_power]

theorem rowCoefficient_case0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (i : Fin 89) :
    rowCoefficient (2*m) f ε i 0 s=
      -rateMonomial i ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ))) := by
  rw [rowCoefficient_complex,hη,h5,h7]
  simp [localRoot]

#print axioms selected_root_scalar
#print axioms rate_certificate
#print axioms rowCoefficient_complex
#print axioms rowCoefficient_case0
end QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
end
end
