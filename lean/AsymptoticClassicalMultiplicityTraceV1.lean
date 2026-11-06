module

public import AsymptoticClassicalMultiplicityCosetsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane AsymptoticClassicalCosets
open scoped ModularForm

/-- Classical trace commutes with restriction across an exact finite-index
 subgroup diamond. The equality follows by matching actual representatives. -/
theorem trace_restrict_diamond
    {G H K J : Subgroup (GL (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] [K.HasDetOne] [J.HasDetOne]
    [G.IsFiniteRelIndex K] [H.IsFiniteRelIndex J]
    (k : ℤ) (hGH : G ≤ H) (hKJ : K ≤ J)
    (hmeet : H ⊓ K = G) (hindex : G.relIndex K = H.relIndex J)
    (f : CuspForm H k) :
    trace (G := G) (H := K) k (restrict k hGH f) =
      restrict k hKJ (trace (G := H) (H := J) k f) := by
  classical
  let := Fintype.ofFinite (K ⧸ G.subgroupOf K)
  let := Fintype.ofFinite (J ⧸ H.subgroupOf J)
  let e := diamondEquiv G H K J hGH hKJ hmeet hindex
  have he (a : K ⧸ G.subgroupOf K) :
      SlashInvariantForm.quotientFunc (restrict k hGH f) a =
        SlashInvariantForm.quotientFunc f (e a) := by
    induction a using Quotient.inductionOn with
    | h a =>
      rw [show e (QuotientGroup.mk a) =
        QuotientGroup.mk (⟨a.val, hKJ a.property⟩ : J) from diamondEquiv_mk ..]
      rw [SlashInvariantForm.quotientFunc_mk, SlashInvariantForm.quotientFunc_mk]
      rfl
  apply CuspForm.ext
  intro z
  change (∑ a : K ⧸ G.subgroupOf K, SlashInvariantForm.quotientFunc (restrict k hGH f) a) z =
    (∑ b : J ⧸ H.subgroupOf J, SlashInvariantForm.quotientFunc f b) z
  simp only [he]
  exact congrFun (e.sum_comp (SlashInvariantForm.quotientFunc f)) z

/-- The arithmetic form of the diamond identity needs no separately supplied
 relative finiteness assumptions. -/
theorem arithmeticTrace_restrict_diamond
    {G H K J : Subgroup (GL (Fin 2) ℝ)}
    [G.HasDetOne] [H.HasDetOne] [K.HasDetOne] [J.HasDetOne]
    [G.IsArithmetic] [H.IsArithmetic] [K.IsArithmetic] [J.IsArithmetic]
    (k : ℤ) (hGH : G ≤ H) (hKJ : K ≤ J)
    (hmeet : H ⊓ K = G) (hindex : G.relIndex K = H.relIndex J)
    (f : CuspForm H k) :
    arithmeticTrace G K k (restrict k hGH f) =
      restrict k hKJ (arithmeticTrace H J k f) := by
  let : G.IsFiniteRelIndex K :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := K)).symm).1
  let : H.IsFiniteRelIndex J :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := J)).symm).1
  exact trace_restrict_diamond k hGH hKJ hmeet hindex f

#print axioms trace_restrict_diamond
#print axioms arithmeticTrace_restrict_diamond

end AsymptoticClassicalCusp
