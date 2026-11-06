module

public import QuantitativeEulerDiamondRegionV1
public import QuantitativeEulerDensityGeneratorsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open Matrix CongruenceSubgroup AsymptoticCongruenceLabels UpperHalfPlane
open QuantitativeEulerDensityGenerators
open scoped MatrixGroups

/-- Each letter is paired with its literal suffix product. This ordering
is the one appropriate to right transport of the generator residual. -/
def generatorSuffixes : List SL(2,ℤ) → List (SL(2,ℤ) × SL(2,ℤ))
  | [] => []
  | a::l => (a,l.prod)::generatorSuffixes l

theorem generatorSuffixes_left_mem (l : List SL(2,ℤ)) (p : SL(2,ℤ) × SL(2,ℤ))
    (hp : p∈generatorSuffixes l) : p.1∈l := by
  induction l with
  | nil => simp [generatorSuffixes] at hp
  | cons a l ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih hp)

/-- Exact noncommutative telescoping, with no invariance assumption. -/
theorem generatorSuffixes_identity (l : List SL(2,ℤ)) :
    symbol (integralLabel l.prod)-1=
      ((generatorSuffixes l).map (fun p =>
        (symbol (integralLabel p.1)-1)*symbol (integralLabel p.2))).sum := by
  induction l with
  | nil => simp [generatorSuffixes]
  | cons a l ih =>
    simp only [generatorSuffixes,List.prod_cons,map_mul,List.map_cons,List.sum_cons,←ih]
    noncomm_ring

theorem gamma1_word (N : ℕ) [NeZero N] (γ : SL(2,ℤ)) (hγ : γ∈Gamma1 N) :
    ∃ l : List SL(2,ℤ), l.prod=γ ∧ ∀ a∈l,
      a∈generators N ∨ a⁻¹∈generators N := by
  rw [←generators_closure N] at hγ
  apply Subgroup.closure_induction_left (p := fun γ _ =>
    ∃ l : List SL(2,ℤ), l.prod=γ ∧ ∀ a∈l,
      a∈generators N ∨ a⁻¹∈generators N) ?_ ?_ ?_ hγ
  · exact ⟨[],rfl,by simp⟩
  · intro a ha b _ hb
    obtain ⟨l,rfl,hl⟩ := hb
    refine ⟨a::l,rfl,?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl ha
    · exact hl c hc
  · intro a ha b _ hb
    obtain ⟨l,rfl,hl⟩ := hb
    refine ⟨a⁻¹::l,rfl,?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inr (by simpa only [inv_inv,Finset.mem_coe] using ha)
    · exact hl c hc

/-- Every actual Gamma1 defect, even after an arbitrary fixed multiplier,
is an explicit finite sum of signed-generator defects with suffix
multipliers. The generators are the same ones used by density preparation. -/
theorem gamma1_generator_expansion (N : ℕ) [NeZero N] (γ : SL(2,ℤ))
    (hγ : γ∈Gamma1 N) :
    ∃ L : List (SL(2,ℤ) × SL(2,ℤ)),
      (∀ p∈L, p.1∈generators N ∨ p.1⁻¹∈generators N) ∧
      ∀ B : Ring, (symbol (integralLabel γ)-1)*B=
        (L.map (fun p => (symbol (integralLabel p.1)-1)*(symbol (integralLabel p.2)*B))).sum := by
  obtain ⟨l,hl,hletters⟩ := gamma1_word N γ hγ
  refine ⟨generatorSuffixes l,?_,?_⟩
  · intro p hp
    exact hletters p.1 (generatorSuffixes_left_mem l p hp)
  · intro B
    rw [←hl,generatorSuffixes_identity]
    generalize generatorSuffixes l = L
    induction L with
    | nil => simp
    | cons p L ih =>
      simp only [List.map_cons,List.sum_cons,add_mul,ih,mul_assoc]

/-- The finite algebraic expansion acts through the existing bounded
compact operators on every orbit vector. -/
theorem gamma1_compact_generator_expansion (N : ℕ) [NeZero N] (γ : SL(2,ℤ))
    (hγ : γ∈Gamma1 N) :
    ∃ L : List (SL(2,ℤ) × SL(2,ℤ)),
      (∀ p∈L, p.1∈generators N ∨ p.1⁻¹∈generators N) ∧
      ∀ (B : Ring) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ),
      compactAction hs hε t x ((symbol (integralLabel γ)-1)*B)=
        (L.map (fun p => compactAction hs hε t x
          ((symbol (integralLabel p.1)-1)*(symbol (integralLabel p.2)*B)))).sum := by
  obtain ⟨L,hL,h⟩ := gamma1_generator_expansion N γ hγ
  refine ⟨L,hL,?_⟩
  intro B s hs ε hε t x
  rw [h,map_list_sum]
  simp only [List.map_map,Function.comp_def]

#print axioms generatorSuffixes_identity
#print axioms gamma1_generator_expansion
#print axioms gamma1_compact_generator_expansion
end QuantitativeEulerDiamondDecode
