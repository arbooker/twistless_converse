module
public import AsymptoticClassicalBadHeckeGroupV1
public import AsymptoticClassicalCosetBridgeV1
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane Matrix ConjAct AsymptoticCongruenceLabels
open scoped ModularForm MatrixGroups Pointwise

def upperRepresentative (N : ℕ) (a : ℤ) : level N :=
  ⟨SpecialLinearGroup.mapGL ℝ (upperSL (-a)), ⟨upperSL (-a), by
    change upperSL (-a) ∈ CongruenceSubgroup.Gamma0 N
    rw [gamma0_mem_dvd]
    simp [upperSL, AsymptoticFreshCRT.upper], rfl⟩⟩

def upperCoset (N p : ℕ) (hp : 0 < p) (a : Fin p) :
    level N ⧸ (upperDilationLevel N p hp).subgroupOf (level N) :=
  QuotientGroup.mk (upperRepresentative N a.val)

 theorem upperCoset_injective (N p : ℕ) (hp : 0 < p) :
    Function.Injective (upperCoset N p hp) := by
  intro a b hab
  have hh₀ : (upperRepresentative N a.val)⁻¹ * upperRepresentative N b.val ∈
      (upperDilationLevel N p hp).subgroupOf (level N) := QuotientGroup.eq.mp hab
  have hh : (upperRepresentative N a.val).val⁻¹ * (upperRepresentative N b.val).val ∈
      upperDilationLevel N p hp := hh₀
  have he : (upperRepresentative N a.val).val⁻¹ * (upperRepresentative N b.val).val =
      SpecialLinearGroup.mapGL ℝ (upperSL (a.val - b.val)) := by
    simp only [upperRepresentative, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    change Matrix.adjugate (!![1, -(a.val : ℤ); 0, 1]) *
      !![1, -(b.val : ℤ); 0, 1] = !![1, (a.val : ℤ) - b.val; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm]
  rw [he, upperDilationLevel_mem_iff N p hp _ (by
    rw [gamma0_mem_dvd]; simp [upperSL, AsymptoticFreshCRT.upper])] at hh
  change (p : ℤ) ∣ (a.val : ℤ) - b.val at hh
  have hz : (a.val : ZMod p) = b.val := by
    have hh' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hh
    exact sub_eq_zero.mp (by simpa only [Int.cast_sub, Int.cast_natCast] using hh')
  have hv := congrArg ZMod.val hz
  apply Fin.ext
  simpa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using hv

 theorem upperCoset_surjective (N p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    Function.Surjective (upperCoset N p hp.pos) := by
  let : Fact p.Prime := ⟨hp⟩
  refine Quotient.ind' fun g => ?_
  obtain ⟨A, hA, hAg⟩ := g.property
  have hc : (A 1 0 : ZMod p) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    exact dvd_trans (by exact_mod_cast hpN) ((gamma0_mem_dvd N A).mp hA)
  have hd : (A 1 1 : ZMod p) ≠ 0 := by
    have hdet := congrArg (fun x : ℤ => (x : ZMod p)) A.property
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one, hc,
      mul_zero, sub_zero] at hdet
    intro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  let x : ZMod p := -(A 0 1 : ZMod p) / (A 1 1 : ZMod p)
  let a : Fin p := ⟨x.val, ZMod.val_lt x⟩
  refine ⟨a, QuotientGroup.eq.mpr ?_⟩
  change (upperRepresentative N a.val).val⁻¹ * g.val ∈ upperDilationLevel N p hp.pos
  rw [← hAg]
  have he : (upperRepresentative N a.val).val⁻¹ * SpecialLinearGroup.mapGL ℝ A =
      SpecialLinearGroup.mapGL ℝ ((upperSL (-(a.val : ℤ)))⁻¹ * A) := by
    simp [upperRepresentative]
  rw [he, upperDilationLevel_mem_iff N p hp.pos _ (by
    apply mul_mem
    · apply inv_mem
      rw [gamma0_mem_dvd]; simp [upperSL, AsymptoticFreshCRT.upper]
    · exact hA)]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  change (((Matrix.adjugate !![1, -(a.val : ℤ); 0, 1] * A.val) 0 1 : ℤ) : ZMod p) = 0
  simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  change ((1 * A 0 1 + -(-(a.val : ℤ)) * A 1 1 : ℤ) : ZMod p) = 0
  simp only [Int.cast_add, Int.cast_mul, one_mul, neg_neg, Int.cast_natCast]
  change (A 0 1 : ZMod p) + (x.val : ZMod p) * (A 1 1 : ZMod p) = 0
  rw [ZMod.natCast_zmod_val]
  dsimp [x]
  rw [div_mul_cancel₀ _ hd, add_neg_cancel]
def upperCosetEquiv (N p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    Fin p ≃ level N ⧸ (upperDilationLevel N p hp.pos).subgroupOf (level N) :=
  Equiv.ofBijective (upperCoset N p hp.pos)
    ⟨upperCoset_injective N p hp.pos, upperCoset_surjective N p hp hpN⟩

#print axioms upperCoset_injective
#print axioms upperCoset_surjective
#print axioms upperCosetEquiv
end AsymptoticClassicalCusp
