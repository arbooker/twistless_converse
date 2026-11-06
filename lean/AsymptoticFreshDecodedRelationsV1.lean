module

public import AsymptoticOrbitDecodeV1
public import AsymptoticFreshResidueIdentificationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshDecodedRelations

open AsymptoticFreshCompactDefects AsymptoticFreshAveraging AsymptoticFreshResidues
open AsymptoticFreshMatrices AsymptoticOrbitDecode AsymptoticRegularBranchFamily
open AsymptoticCompactFamilyTranslation AsymptoticRationalBranches AsymptoticIntegralSubgroup
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch (cap)
open UpperHalfPlane
open scoped Classical

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

theorem defectLabel_integerIndex (a b c : ℤ) (ha : 0<a) (haq : a<(q:ℤ))
    (hb : 0<b) (hbq : b<(q:ℤ)) (h : (q:ℤ)*c=(N:ℤ)*a*b+1) :
    defectLabel N q hN hq (integerIndex q b hb hbq)=label N q hN (Fact.out : q.Prime).pos a b := by
  unfold defectLabel
  rw [(canonical_indices q N hq a b c ha haq hb hbq h).1,integerIndex_val]

variable (w : ℂ) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space)

theorem row_decode {s : Set ℍ} (hs : IsCompact s) (i : Fin (q-1))
    (g : AsymptoticRationalGroup.Group) :
    AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x f g=
      if g • x∈shifted (parameter q i) s then (cap ε t (g • x):ℂ)*
        (w*decode ε t x f (defectLabel N q hN hq i*g)-decode ε t x f g) else 0 := by
  classical
  change w*(compact (matrixBranch N q hN hq i) (shifted_compact (parameter q i) hs) hε t x f g)-
    compact identityBranch (shifted_compact (parameter q i) hs) hε t x f g=_
  rw [compact_decode,compact_decode,matrixBranch_label,identityBranch_label,one_mul]
  by_cases hg : g • x∈shifted (parameter q i) s
  · simp only [ite_eq_left hg]
    ring
  · simp only [ite_eq_right hg,mul_zero,sub_self]

/-- Vanishing of every compact observation is exactly the individual
relation on decoded group coordinates. Positive weights cancel only
pointwise; no unbounded inverse is treated as a bounded operator. -/
theorem all_compact_row_zero_iff (i : Fin (q-1)) :
    (∀ s : Set ℍ,∀ hs : IsCompact s,
      AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x f=0) ↔
    ∀ g : AsymptoticRationalGroup.Group,
      w*decode ε t x f (defectLabel N q hN hq i*g)=decode ε t x f g := by
  constructor
  · intro h g
    let y := (translationLabel (parameter q i))⁻¹ • (g • x)
    have hg : g • x∈shifted (parameter q i) {y} :=
      ⟨y,Set.mem_singleton y,smul_inv_smul _ _⟩
    have he := congrArg (fun v : Space => v g) (h {y} isCompact_singleton)
    rw [row_decode N q hN hq w hε t x f isCompact_singleton i g,ite_eq_left hg] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (cap_ne_zero hε t (g • x)))
  · intro h s hs
    apply lp.ext
    funext g
    rw [row_decode N q hN hq w hε t x f hs i g,h g,sub_self,mul_zero]
    simp

/-- The canonical matrix obtained by row and column reduction is
detected by the actual residue-indexed compact defect family. -/
theorem canonical_relation (a b c : ℤ) (ha : 0<a) (haq : a<(q:ℤ))
    (hb : 0<b) (hbq : b<(q:ℤ)) (h : (q:ℤ)*c=(N:ℤ)*a*b+1)
    (hrows : ∀ i : Fin (q-1),∀ s : Set ℍ,∀ hs : IsCompact s,
      AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x f=0)
    (hF : ∀ g : AsymptoticRationalGroup.Group,
      w*decode ε t x f (frickeLabel N hN*g)=decode ε t x f g) :
    ∀ g : AsymptoticRationalGroup.Group,
      decode ε t x f (canonicalLabel N q a b c h*g)=decode ε t x f g := by
  intro g
  have he := (all_compact_row_zero_iff N q hN hq w hε t x f
    (integerIndex q b hb hbq)).mp (hrows _) g
  rw [defectLabel_integerIndex N q hN hq a b c ha haq hb hbq h,
    label_eq_fricke_canonical N q hN (Fact.out : q.Prime).pos a b c h,mul_assoc,hF] at he
  exact he

#print axioms defectLabel_integerIndex
#print axioms row_decode
#print axioms all_compact_row_zero_iff
#print axioms canonical_relation

end AsymptoticFreshDecodedRelations
