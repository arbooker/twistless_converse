module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Tactic

/-! Consolidated chapter: QuantitativeArithmeticFiniteAbelNegative. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticFiniteAbelNegativeV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticFiniteAbelNegative
open Finset

/-- Strict finite Abel inequality, stated for descending positive weights.
It permits exact certificates consisting only of negative prefix sums. -/
theorem weighted_negative (n : ℕ) (hn : 0<n) (c w : ℕ→ℝ)
    (hc : ∀ j, 0<j → j≤n → ∑ i ∈ range j, c i<0)
    (hw : 0<w (n-1))
    (hmono : ∀ i, i<n-1 → w (i+1)≤w i) :
    ∑ i ∈ range n, c i*w i<0 := by
  have hid := sum_range_by_parts' c w n
  simp only [smul_eq_mul] at hid
  rw [hid]
  have hfirst := mul_neg_of_neg_of_pos (hc n hn le_rfl) hw
  have hsum : 0≤∑ i ∈ range (n-1), (∑ j ∈ range (i+1), c j)*(w (i+1)-w i) := by
    apply sum_nonneg
    intro i hi
    have hi' := mem_range.mp hi
    exact mul_nonneg_of_nonpos_of_nonpos
      (le_of_lt (hc (i+1) (by omega) (by omega)))
      (sub_nonpos.mpr (hmono i hi'))
  linarith

/-- Two-dimensional finite Abel inequality. A rectangular table with all
nonempty upper-corner sums negative pairs negatively with positive
descending product weights. -/
theorem double_weighted_negative (n m : ℕ) (hn : 0<n) (hm : 0<m)
    (c : ℕ→ℕ→ℝ) (u w : ℕ→ℝ)
    (hc : ∀ j k, 0<j → j≤n → 0<k → k≤m →
      ∑ i ∈ range j, ∑ t ∈ range k, c i t<0)
    (hu : 0<u (n-1)) (hw : 0<w (m-1))
    (hmu : ∀ i, i<n-1 → u (i+1)≤u i)
    (hmw : ∀ i, i<m-1 → w (i+1)≤w i) :
    ∑ i ∈ range n, ∑ j ∈ range m, c i j*u i*w j<0 := by
  have hinner (k : ℕ) (hk : 0<k) (hkn : k≤n) :
      ∑ i ∈ range k, (∑ j ∈ range m, c i j*w j)<0 := by
    rw [sum_comm]
    simp_rw [← sum_mul]
    apply weighted_negative m hm (fun j => ∑ i ∈ range k, c i j) w ?_ hw hmw
    intro j hj hjm
    rw [sum_comm]
    exact hc k j hk hkn hj hjm
  have h := weighted_negative n hn (fun i => ∑ j ∈ range m, c i j*w j) u
    hinner hu hmu
  simpa only [sum_mul,mul_right_comm] using h

#print axioms weighted_negative
#print axioms double_weighted_negative
end QuantitativeArithmeticFiniteAbelNegative
end
end

/-! ## QuantitativeArithmeticFiniteAbelScanV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticFiniteAbelNegative

/-- Interpret the exact integer scan certificate as a statement about
every nonempty prefix sum. The certificate is checked by kernel reduction. -/
theorem scan_prefix_negative (xs : List ℤ)
    (h : ((xs.scanl (·+·) 0).tail).all (fun x => decide (x<0))=true)
    (k : ℕ) (hk : 0<k) (hlen : k≤xs.length) : (xs.take k).sum<0 := by
  have hi : k-1<((xs.scanl (·+·) 0).tail).length := by simp; omega
  have hm := List.getElem_mem hi
  have ht := (List.all_eq_true.mp h) _ hm
  have he : ((xs.scanl (·+·) 0).tail)[k-1]=(xs.take k).sum := by
    rw [List.getElem_tail]
    simp only [Nat.sub_add_cancel hk,List.getElem_scanl,← List.sum_eq_foldl]
  rw [he] at ht
  exact of_decide_eq_true ht

#print axioms scan_prefix_negative
end QuantitativeArithmeticFiniteAbelNegative
end
end

/-! ## QuantitativeArithmeticFiniteAbelComputeV1 -/
section
set_option autoImplicit false
@[expose] public section
namespace QuantitativeArithmeticFiniteAbelNegative

/-- A transparent scan for kernel checking of finite arithmetic data. -/
def exactScan {α β : Type} (f : β→α→β) (z : β) : List α→List β
  | [] => [z]
  | a::as => z::exactScan f (f z a) as

theorem exactScan_eq {α β : Type} (f : β→α→β) (z : β) (as : List α) :
    exactScan f z as=as.scanl f z := by
  induction as generalizing z with
  | nil => simp [exactScan]
  | cons a as ih => simp [exactScan,List.scanl_cons,ih]

theorem exactScan_prefix_negative (xs : List ℤ)
    (h : ((exactScan (·+·) 0 xs).tail).all (fun x => decide (x<0))=true)
    (k : ℕ) (hk : 0<k) (hlen : k≤xs.length) : (xs.take k).sum<0 := by
  rw [exactScan_eq] at h
  exact scan_prefix_negative xs h k hk hlen

#print axioms exactScan_eq
#print axioms exactScan_prefix_negative
end QuantitativeArithmeticFiniteAbelNegative
end
end

/-! ## QuantitativeArithmeticFiniteAbelTableV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticFiniteAbelNegative

theorem sum_zip_add (xs ys : List ℤ) (h : xs.length=ys.length) :
    (List.zipWith (·+·) xs ys).sum=xs.sum+ys.sum := by
  induction xs generalizing ys with
  | nil => have hy : ys=[] := List.length_eq_zero_iff.mp (by simpa using h.symm)
           simp [hy]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have hh : xs.length=ys.length := by simpa using h
      simp only [List.zipWith_cons_cons,List.sum_cons,ih ys hh]
      ring

theorem fold_zip_length (rows : List (List ℤ)) (d : ℕ)
    (hrows : ∀ r∈rows, r.length=d) (acc : List ℤ) (hacc : acc.length=d) :
    (rows.foldl (List.zipWith (·+·)) acc).length=d := by
  induction rows generalizing acc with
  | nil => exact hacc
  | cons r rows ih =>
    simp only [List.foldl_cons]
    apply ih (fun t ht => hrows t (by simp [ht]))
    simp [hacc,hrows r (by simp)]

theorem fold_zip_prefix_sum (rows : List (List ℤ)) (d l : ℕ)
    (hrows : ∀ r∈rows, r.length=d) (acc : List ℤ) (hacc : acc.length=d) :
    ((rows.foldl (List.zipWith (·+·)) acc).take l).sum=
      (acc.take l).sum+(rows.map (fun r => (r.take l).sum)).sum := by
  induction rows generalizing acc with
  | nil => simp
  | cons r rows ih =>
    have hr := hrows r (by simp)
    rw [List.foldl_cons,ih (fun t ht => hrows t (by simp [ht])) _ (by simp [hacc,hr])]
    rw [List.take_zipWith,sum_zip_add _ _ (by simp [hacc,hr])]
    simp only [List.map_cons,List.sum_cons]
    ring

/-- A kernel-checked table scan supplies every nonempty rectangular
prefix sum required by two-dimensional finite Abel summation. -/
theorem table_prefix_negative (rows : List (List ℤ)) (d : ℕ)
    (hrows : ∀ r∈rows, r.length=d)
    (h : ((exactScan (List.zipWith (·+·)) (List.replicate d 0) rows).tail).all
      (fun r => ((exactScan (·+·) 0 r).tail).all (fun x => decide (x<0)))=true)
    (k l : ℕ) (hk : 0<k) (hkr : k≤rows.length) (hl : 0<l) (hld : l≤d) :
    ((rows.take k).map (fun r => (r.take l).sum)).sum<0 := by
  rw [exactScan_eq] at h
  have hi : k-1<((rows.scanl (List.zipWith (·+·)) (List.replicate d 0)).tail).length := by simp; omega
  have hm := List.getElem_mem hi
  have ht := (List.all_eq_true.mp h) _ hm
  have he : ((rows.scanl (List.zipWith (·+·)) (List.replicate d 0)).tail)[k-1]=
      (rows.take k).foldl (List.zipWith (·+·)) (List.replicate d 0) := by
    rw [List.getElem_tail]
    simp only [Nat.sub_add_cancel hk,List.getElem_scanl]
  rw [he] at ht
  have hp : ∀ r∈rows.take k, r.length=d := fun r hr => hrows r (List.mem_of_mem_take hr)
  have hn := fold_zip_length (rows.take k) d hp (List.replicate d 0) (by simp)
  have hs := exactScan_prefix_negative _ ht l hl (by omega)
  rw [fold_zip_prefix_sum (rows.take k) d l hp _ (by simp)] at hs
  simpa using hs

#print axioms table_prefix_negative
end QuantitativeArithmeticFiniteAbelNegative
end
end

/-! ## QuantitativeArithmeticFiniteAbelListsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticFiniteAbelNegative
open Finset

theorem sum_take_eq_range (xs : List ℤ) (k : ℕ) (hk : k≤xs.length) :
    (xs.take k).sum=∑ i∈range k, xs[i]?.getD 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.sum_take_succ xs k (by omega),sum_range_succ,ih (by omega)]
    simp only [List.getElem?_eq_getElem (by omega : k<xs.length),Option.getD_some]

theorem list_weighted_negative (xs : List ℤ) (hn : 0<xs.length)
    (hc : ∀ k, 0<k → k≤xs.length → (xs.take k).sum<0)
    (w : ℕ→ℝ) (hw : 0<w (xs.length-1))
    (hmono : ∀ i, i<xs.length-1 → w (i+1)≤w i) :
    ∑ i∈range xs.length, ((xs[i]?.getD 0 : ℤ):ℝ)*w i<0 := by
  apply weighted_negative xs.length hn _ w ?_ hw hmono
  intro k hk hlen
  have h := hc k hk hlen
  rw [sum_take_eq_range xs k hlen] at h
  exact_mod_cast h

theorem rectangle_eq_ranges (rows : List (List ℤ)) (d k l : ℕ)
    (hrows : ∀ r∈rows, r.length=d) (hk : k≤rows.length) (hl : l≤d) :
    ((rows.take k).map (fun r => (r.take l).sum)).sum=
      ∑ i∈range k, ∑ j∈range l, ((rows[i]?.getD [])[j]?.getD 0) := by
  rw [List.map_take,sum_take_eq_range _ k (by simpa using hk)]
  apply sum_congr rfl
  intro i hi
  have hir : i<rows.length := lt_of_lt_of_le (mem_range.mp hi) hk
  simp only [List.getElem?_map,List.getElem?_eq_getElem hir,Option.map_some,Option.getD_some]
  exact sum_take_eq_range (rows[i]) l (by rw [hrows _ (List.getElem_mem hir)]; exact hl)

theorem table_weighted_negative (rows : List (List ℤ)) (d : ℕ)
    (hn : 0<rows.length) (hd : 0<d) (hrows : ∀ r∈rows, r.length=d)
    (hc : ∀ k l, 0<k → k≤rows.length → 0<l → l≤d →
      ((rows.take k).map (fun r => (r.take l).sum)).sum<0)
    (u w : ℕ→ℝ) (hu : 0<u (rows.length-1)) (hw : 0<w (d-1))
    (hmu : ∀ i, i<rows.length-1 → u (i+1)≤u i)
    (hmw : ∀ i, i<d-1 → w (i+1)≤w i) :
    ∑ i∈range rows.length, ∑ j∈range d,
      ((((rows[i]?.getD [])[j]?.getD 0):ℤ):ℝ)*u i*w j<0 := by
  apply double_weighted_negative rows.length d hn hd _ u w ?_ hu hw hmu hmw
  intro k l hk hkn hl hld
  have h := hc k l hk hkn hl hld
  rw [rectangle_eq_ranges rows d k l hrows hkn hld] at h
  exact_mod_cast h

#print axioms list_weighted_negative
#print axioms table_weighted_negative
end QuantitativeArithmeticFiniteAbelNegative
end
end

/-! ## QuantitativeArithmeticFiniteAbelEvaluationV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticFiniteAbelNegative
open Finset

theorem sum_map_range {α : Type} (xs : List α) (f : α→ℝ) (d : α) :
    (xs.map f).sum=∑ i∈range xs.length, f (xs[i]?.getD d) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,sum_range_succ',
      List.getElem?_cons_zero,Option.getD_some,List.getElem?_cons_succ,ih]
    ring

theorem sum_zip_range {α β : Type} (xs : List α) (ys : List β)
    (h : xs.length=ys.length) (f : α→β→ℝ) (a : α) (b : β) :
    ((xs.zip ys).map (fun t => f t.1 t.2)).sum=
      ∑ i∈range xs.length, f (xs[i]?.getD a) (ys[i]?.getD b) := by
  rw [sum_map_range _ _ (a,b)]
  simp only [List.length_zip,h,min_self]
  apply sum_congr rfl
  intro i hi
  have hy : i<ys.length := mem_range.mp hi
  have hx : i<xs.length := by omega
  simp only [List.zip,List.getElem?_zipWith,List.getElem?_eq_getElem hx,List.getElem?_eq_getElem hy,
    Option.getD_some]

theorem sum_filter_zero {α : Type} (xs : List α) (p : α→Bool) (f : α→ℝ)
    (hf : ∀ x∈xs, p x=false → f x=0) :
    ((xs.filter p).map f).sum=(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ht := ih (fun x hx => hf x (by simp [hx]))
    cases hp : p a with
    | false => simp [hp,ht,hf a (by simp) hp]
    | true => simp [hp,ht]

theorem sum_flatMap_map {α β : Type} (xs : List α) (g : α→List β) (f : β→ℝ) :
    ((xs.flatMap g).map f).sum=(xs.map (fun x => ((g x).map f).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

#print axioms sum_zip_range
#print axioms sum_filter_zero
#print axioms sum_flatMap_map
end QuantitativeArithmeticFiniteAbelNegative
end
end
