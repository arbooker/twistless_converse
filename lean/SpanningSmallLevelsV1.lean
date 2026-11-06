module

public import SpanningKernelDifferencesV1

@[expose] public section

namespace SpanningSmallLevels

open SpanningActualKernel SpanningWindows SpanningTraceAlgebra SpanningCyclicCoordinates
  SpanningLevelArithmetic

variable {K : Type} [AddCommGroup K]

theorem cyclic_four_zero {f : ℤ → K} (hf : Cyclic 4 f)
    (h0 : f 0=0) (h1 : f 1=0) (h2 : f 2=0) (h3 : f 3=0) : f=0 := by
  funext j
  change f j=0
  rw [←cyclic_emod hf j]
  change f (j%4)=0
  have hlo := Int.emod_nonneg j (by norm_num : (4:ℤ)≠0)
  have hhi := Int.emod_lt_of_pos j (by norm_num : (0:ℤ)<4)
  have he : j%4=0 ∨ j%4=1 ∨ j%4=2 ∨ j%4=3 := by omega
  rcases he with he|he|he|he
  · rw [he]; exact h0
  · rw [he]; exact h1
  · rw [he]; exact h2
  · rw [he]; exact h3

theorem radius_one_gt_two {N : ℕ} (hN : 0<N) (hN4 : N<4) : (2:ℝ)<radius N 4 1 := by
  have hs : (0:ℝ)<Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hn : (N:ℝ)<4 := by exact_mod_cast hN4
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N)
  have hlt : Real.sqrt (N:ℝ)<2 := by nlinarith [Real.sqrt_nonneg (N:ℝ)]
  simp only [radius,level,one_pow,Nat.lcm_one_right,Nat.cast_ofNat]
  apply (lt_div_iff₀ hs).mpr
  linarith

theorem kernel_zero_below_four {N : ℕ} (hN : 0<N) (hN4 : N<4)
    (f : ℤ → K) (hf : Kernel N 4 f) : f=0 := by
  have hcomp := (complete_iff_primitive hN (by omega : 0<4) f).mp hf
  have hz : ∀u:ℤ,-2≤u → u<2 → f u=0 := by
    intro u hlo hhi
    have hleg := legal_interval (radius_one_gt_two hN hN4) hlo hhi
    have hh := hcomp.2 1 (one_dvd 4) u hleg
    simpa [trace] using hh
  apply cyclic_four_zero hf.1 (hz 0 (by omega) (by omega)) (hz 1 (by omega) (by omega))
  · have he := hf.1 (-2)
    norm_num at he
    rw [he]
    exact hz (-2) (by omega) (by omega)
  · have he := hf.1 (-1)
    norm_num at he
    rw [he]
    exact hz (-1) (by omega) (by omega)

theorem kernel_zero_four (f : ℤ → K) (hf : Kernel 4 4 f) : f=0 := by
  have hcomp := (complete_iff_primitive (by omega : 0<4) (by omega : 0<4) f).mp hf
  have hroot : Real.sqrt (4:ℝ)=2 := by
    have hh := Real.sqrt_sq (by norm_num : (0:ℝ)≤2)
    norm_num at hh
    exact hh
  have hrad1 : radius 4 4 1=2 := by norm_num [radius,level,hroot]
  have hrad2 : radius 4 4 2=2 := by norm_num [radius,level,hroot]
  have hz : ∀u:ℤ,-1≤u → u≤0 → f u=0 := by
    intro u hlo hhi
    have hleg : Legal (radius 4 4 1) u := by
      rw [hrad1]
      constructor <;> exact_mod_cast (by omega)
    have hh := hcomp.2 1 (one_dvd 4) u hleg
    simpa [trace] using hh
  have htwo : ∀u:ℤ,-1≤u → u≤0 → f u+f (u+2)=0 := by
    intro u hlo hhi
    have hleg : Legal (radius 4 4 2) u := by
      rw [hrad2]
      constructor <;> exact_mod_cast (by omega)
    have hh := hcomp.2 2 (by decide) u hleg
    simpa [trace,Finset.sum_range_succ] using hh
  have h0 := hz 0 (by omega) (by omega)
  have hm1 := hz (-1) (by omega) (by omega)
  have h1 : f 1=0 := by simpa only [hm1,zero_add,show (-1:ℤ)+2=1 by omega] using htwo (-1) (by omega) (by omega)
  have h2 : f 2=0 := by simpa only [h0,zero_add] using htwo 0 (by omega) (by omega)
  have h3 : f 3=0 := by have he := hf.1 (-1); norm_num at he; exact he.trans hm1
  exact cyclic_four_zero hf.1 h0 h1 h2 h3

theorem kernel_zero_small {N : ℕ} (hN : 0<N) (hN4 : N≤4) :
    ∀f:ℤ → K,Kernel N 4 f → f=0 := by
  rcases lt_or_eq_of_le hN4 with hlt|rfl
  · exact kernel_zero_below_four hN hlt
  · exact kernel_zero_four

#print axioms kernel_zero_small

end SpanningSmallLevels
