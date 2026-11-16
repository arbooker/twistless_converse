module

public import QuantitativeMaassBandSupportV1
public import AsymptoticL2MultiplierV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory Filter

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)
  (c : α → ℂ) (hc : AEStronglyMeasurable c μ)
  (hb : ∀ n : ℤ,∃ C : ℝ,0≤C ∧ ∀ x∈region l n,‖c x‖≤C)

include hc hb in
/-- Local boundedness on each actual band suffices for multiplication on
the dense algebraic band space; the multiplier may be globally unbounded. -/
theorem finiteBand_memLp_mul (f : finiteBandSpace μ l hl) : MemLp (fun x => c x*f.val x) 2 μ := by
  refine Submodule.iSup_induction (space μ l hl)
    (motive:=fun g => MemLp (fun x => c x*g x) 2 μ) f.property ?_ ?_ ?_
  · intro n g hg
    obtain ⟨C,hC,hbound⟩ := hb n
    have hgb := (AsymptoticRegionL2.projection_eq_self_iff μ _ _ g).mp
      ((AsymptoticRegionL2.mem_space μ _ _ g).mp hg)
    have hmem := AsymptoticL2Multiplier.memLp_mul ((region l n).indicator c)
      (hc.indicator (region_measurable l hl n))
      (Eventually.of_forall (fun x => by
        classical
        by_cases hx : x∈region l n
        · rw [Set.indicator_of_mem hx]
          exact hbound x hx
        · rw [Set.indicator_of_notMem hx,norm_zero]
          exact hC)) g
    apply hmem.ae_eq
    filter_upwards [hgb] with x hx
    classical
    by_cases hxn : x∈region l n
    · rw [Set.indicator_of_mem hxn]
    · rw [Set.indicator_of_notMem hxn,hx hxn,zero_mul,mul_zero]
  · apply (MemLp.zero' : MemLp (fun _ : α => (0:ℂ)) 2 μ).ae_eq
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    simp only [hx,Pi.zero_apply,mul_zero]
  · intro g h hg hh
    apply (hg.add hh).ae_eq
    filter_upwards [Lp.coeFn_add g h] with x hx
    simp only [hx,Pi.add_apply,mul_add]

def finiteMultiplier : finiteBandSpace μ l hl →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (finiteBand_memLp_mul μ l hl c hc hb f).toLp (fun x => c x*f.val x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(finiteBand_memLp_mul μ l hl c hc hb (f+g)).coeFn_toLp,
      (finiteBand_memLp_mul μ l hl c hc hb f).coeFn_toLp,
      (finiteBand_memLp_mul μ l hl c hc hb g).coeFn_toLp,
      Lp.coeFn_add f.val g.val,
      Lp.coeFn_add ((finiteBand_memLp_mul μ l hl c hc hb f).toLp _)
        ((finiteBand_memLp_mul μ l hl c hc hb g).toLp _)] with x hfg hf hg ha hs
    calc
      _ = c x*((f+g).val x) := hfg
      _ = c x*f.val x+c x*g.val x := by
        change c x*((f.val+g.val) x)=_
        rw [ha,Pi.add_apply,mul_add]
      _ = _ := by rw [hs,Pi.add_apply,hf,hg]
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [(finiteBand_memLp_mul μ l hl c hc hb (z • f)).coeFn_toLp,
      (finiteBand_memLp_mul μ l hl c hc hb f).coeFn_toLp,Lp.coeFn_smul z f.val,
      Lp.coeFn_smul z ((finiteBand_memLp_mul μ l hl c hc hb f).toLp _)] with x hz hf ha hs
    calc
      _ = c x*((z • f).val x) := hz
      _ = z*(c x*f.val x) := by
        change c x*((z • f.val) x)=_
        rw [ha,Pi.smul_apply,smul_eq_mul]
        ring
      _ = _ := by rw [RingHom.id_apply,hs,Pi.smul_apply,smul_eq_mul,hf]

theorem finiteMultiplier_coeFn (f : finiteBandSpace μ l hl) :
    finiteMultiplier μ l hl c hc hb f=ᵐ[μ](fun x => c x*f.val x) :=
  (finiteBand_memLp_mul μ l hl c hc hb f).coeFn_toLp

theorem finiteMultiplier_preserves (f : finiteBandSpace μ l hl) :
    finiteMultiplier μ l hl c hc hb f∈finiteBandSpace μ l hl := by
  obtain ⟨S,hS⟩ := finiteBandSpace_support μ l hl f
  apply mem_finiteBandSpace_of_support μ l hl S
  intro n hn
  apply (AsymptoticRegionL2.projection_eq_zero_iff μ _ _ _).mpr
  have hf := (AsymptoticRegionL2.projection_eq_zero_iff μ _ _ f.val).mp (hS n hn)
  filter_upwards [finiteMultiplier_coeFn μ l hl c hc hb f,hf] with x hc hf hx
  rw [hc,hf hx,mul_zero]

def finiteMultiplierEnd : finiteBandSpace μ l hl →ₗ[ℂ] finiteBandSpace μ l hl :=
  (finiteMultiplier μ l hl c hc hb).codRestrict (finiteBandSpace μ l hl)
    (finiteMultiplier_preserves μ l hl c hc hb)

#print axioms finiteBand_memLp_mul
#print axioms finiteMultiplier_coeFn
#print axioms finiteMultiplier_preserves

end QuantitativeMaass.LogBands
