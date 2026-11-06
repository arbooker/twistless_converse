module

public import GridSpecialWindowsV1
public import GridSupportedDetectionV1
public import Mathlib.Algebra.Order.Ring.Cast

@[expose] public section

namespace GridParameters

open GridLabelDetection GridCenterChoice GridCarrier GridPrimeParts

theorem exists_grid_parameters {G : ℕ} (hG : 0<G) :
    ∃(r : Fin G → ℕ) (H R : ℕ),0<H ∧ 0<R ∧ ∀a,
      0<r a ∧ Nat.Coprime (r a) G ∧ r a∣H ∧ r a≤R ∧
      Nat.ModEq (labelModulus a) (r a*a.val) (labelModulus a/labelOrder a) := by
  classical
  have hh : ∀a:Fin G,∃r:ℕ,0<r ∧ Nat.Coprime r G ∧
      Nat.ModEq (labelModulus a) (r*a.val) (labelModulus a/labelOrder a) := by
    intro a
    exact positive_center_choice hG
  choose r hr using hh
  let H := ∏a:Fin G,r a
  let R := 1+∑a:Fin G,r a
  refine ⟨r,H,R,Finset.prod_pos (fun a _ => (hr a).1),by dsimp [R]; omega,?_⟩
  intro a
  have hsum : r a≤∑b:Fin G,r b := Finset.single_le_sum (fun b _ => Nat.zero_le (r b)) (Finset.mem_univ a)
  exact ⟨(hr a).1,(hr a).2.1,Finset.dvd_prod_of_mem r (Finset.mem_univ a),
    by dsimp [R]; omega,(hr a).2.2⟩

theorem quotient_estimates {r R v : ℕ} (hr : 0<r) (hrR : r≤R) (hv : 16*R≤v)
    (hrv : r∣v) : 0<v/r ∧ 2*(v/(8*R))<v/r ∧ 2*(v/(8*R))<v := by
  let J := v/(8*R)
  let w := v/r
  have hR : 0<R := hr.trans_le hrR
  have hv0 : 0<v := by omega
  have hwv : r*w=v := Nat.mul_div_cancel' hrv
  have hw : 0<w := Nat.pos_of_ne_zero (by intro he; rw [he,mul_zero] at hwv; omega)
  have hJ : J*(8*R)≤v := Nat.div_mul_le_self _ _
  have hsmall : 2*J<w := by
    by_contra! hn
    have hvJ : v≤r*(2*J) := by rw [←hwv]; exact Nat.mul_le_mul_left r hn
    have hrJ : r*(2*J)≤R*(2*J) := Nat.mul_le_mul_right (2*J) hrR
    nlinarith
  have hwle : w≤v := by rw [←hwv]; nlinarith
  exact ⟨hw,hsmall,hsmall.trans_le hwle⟩

theorem offset_bound {v R : ℕ} (hR : 0<R) (t : Offsets (v/(8*R))) :
    |(t.val:ℝ)|≤(v:ℝ)/(8*R) := by
  have ht : |t.val|≤(v/(8*R):ℕ) := abs_le.mpr (Finset.mem_Icc.mp t.property)
  have htR : |(t.val:ℝ)|≤((v/(8*R):ℕ):ℝ) := by
    apply abs_le.mpr
    have hh := abs_le.mp ht
    constructor
    · exact_mod_cast hh.1
    · simpa only [Int.cast_natCast] using (Int.cast_le (R:=ℝ)).mpr hh.2
  apply htR.trans
  apply (le_div_iff₀ (by positivity : (0:ℝ)<8*R)).mpr
  have hj : (v/(8*R))*(8*R)≤v := Nat.div_mul_le_self _ _
  exact_mod_cast hj

theorem row_factorization {G v r w : ℕ} (hG : 0<G) (a : Fin G) (hvw : v=r*w) :
    (primePart G (fun p => ¬p∣labelOrder a)*r)*(labelModulus a*w)=G*v := by
  have hmd := part_complement (Nat.ne_of_gt hG) (fun p => p∣labelOrder a)
  change labelModulus a*primePart G (fun p => ¬p∣labelOrder a)=G at hmd
  calc
    _=(labelModulus a*primePart G (fun p => ¬p∣labelOrder a))*(r*w) := by ring
    _=G*v := by rw [hmd,←hvw]

#print axioms exists_grid_parameters
#print axioms quotient_estimates

end GridParameters
