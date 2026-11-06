module

public import QuantitativeArithmeticSmallLevelCircTraceTranslateV1
public import AsymptoticClassicalMultiplicityMixedGroupsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalCosets
open scoped ModularForm

/-- Genuine full modular trace/restriction covariance across a subgroup diamond. -/
theorem trace_restrict_diamond
    {G H K J : Subgroup (GL (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] [K.HasDetOne] [J.HasDetOne]
    [G.IsFiniteRelIndex K] [H.IsFiniteRelIndex J]
    (k : ℤ) (hGH : G ≤ H) (hKJ : K ≤ J)
    (hmeet : H ⊓ K = G) (hindex : G.relIndex K = H.relIndex J)
    (f : ModularForm H k) :
    trace (G := G) (H := K) k (restrictModular k hGH f) =
      restrictModular k hKJ (trace (G := H) (H := J) k f) := by
  classical
  let := Fintype.ofFinite (K ⧸ G.subgroupOf K)
  let := Fintype.ofFinite (J ⧸ H.subgroupOf J)
  let e := diamondEquiv G H K J hGH hKJ hmeet hindex
  have he (a : K ⧸ G.subgroupOf K) :
      SlashInvariantForm.quotientFunc (restrictModular k hGH f) a =
        SlashInvariantForm.quotientFunc f (e a) := by
    induction a using Quotient.inductionOn with
    | h a =>
      rw [show e (QuotientGroup.mk a) =
        QuotientGroup.mk (⟨a.val, hKJ a.property⟩ : J) from diamondEquiv_mk ..]
      rw [SlashInvariantForm.quotientFunc_mk, SlashInvariantForm.quotientFunc_mk]
      rfl
  apply ModularForm.ext
  intro z
  change (∑ a : K ⧸ G.subgroupOf K,
    SlashInvariantForm.quotientFunc (restrictModular k hGH f) a) z =
    (∑ b : J ⧸ H.subgroupOf J, SlashInvariantForm.quotientFunc f b) z
  simp only [he]
  exact congrFun (e.sum_comp (SlashInvariantForm.quotientFunc f)) z

theorem arithmeticTrace_restrict_diamond
    {G H K J : Subgroup (GL (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] [K.HasDetOne] [J.HasDetOne]
    [G.IsArithmetic] [H.IsArithmetic] [K.IsArithmetic] [J.IsArithmetic]
    (k : ℤ) (hGH : G ≤ H) (hKJ : K ≤ J)
    (hmeet : H ⊓ K = G) (hindex : G.relIndex K = H.relIndex J)
    (f : ModularForm H k) :
    arithmeticTrace G K k (restrictModular k hGH f) =
      restrictModular k hKJ (arithmeticTrace H J k f) := by
  let : G.IsFiniteRelIndex K :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := K)).symm).1
  let : H.IsFiniteRelIndex J :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := J)).symm).1
  exact trace_restrict_diamond k hGH hKJ hmeet hindex f

/-- Ordinary level restriction commutes with lowering a distinct prime,
for actual modular forms including Eisenstein series. -/
theorem ordinary_cross_trace (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0<M) (hp : 0<p) (hq : q.Prime) (hc : p.Coprime q) (k : ℤ)
    (f : ModularForm (level (q*M)) k) :
    arithmeticTrace (level (p*(q*M))) (level (p*M)) k
      (restrictModular k (level_antitone (Nat.dvd_mul_left (q*M) p)) f) =
    restrictModular k (level_antitone (Nat.dvd_mul_left M p))
      (arithmeticTrace (level (q*M)) (level M) k f) := by
  let : NeZero (q*M) := ⟨(Nat.mul_pos hq.pos hM).ne'⟩
  let : NeZero (p*M) := ⟨(Nat.mul_pos hp hM).ne'⟩
  let : NeZero (p*(q*M)) := ⟨(Nat.mul_pos hp (Nat.mul_pos hq.pos hM)).ne'⟩
  exact arithmeticTrace_restrict_diamond k _ _ (coprime_level_inf M p q hc)
    (coprime_level_index M p q hM hp hq hc) f

#print axioms trace_restrict_diamond
#print axioms ordinary_cross_trace
end QuantitativeArithmeticSmallLevelCirc.ModularHecke
