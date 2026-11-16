module

public import QuantitativeNinaMaassOldDescentV1
public import AsymptoticClassicalMultiplicityOrdinaryV1
public import AsymptoticClassicalMultiplicityMixedGroupsV1
public import AsymptoticClassicalFrickeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory UpperHalfPlane Matrix
open QuantitativeMaass AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticCongruenceLabels AsymptoticClassicalCusp AsymptoticClassicalCosets
open AsymptoticFreshMatrices
open scoped BigOperators MatrixGroups

/-!
Finite-coset diamond identities for the actual weight-zero pullback trace.
The representative-compatible group bijection is reused from the classical
development; the trace identity is proved here for arbitrary functions in
a group action. No holomorphic cusp-form theorem is applied to a Maass vector.
-/

namespace QuantitativeNinaMaass

/-- A finite subgroup diamond gives an identity of literal pullback sums. -/
theorem finiteTrace_diamond {A X : Type*} [Group A] [MulAction A X]
    (G H K J : Subgroup A) (hGH : G ≤ H) (hKJ : K ≤ J)
    [Fintype (K ⧸ G.subgroupOf K)] [Fintype (J ⧸ H.subgroupOf J)]
    (hmeet : H ⊓ K = G) (hindex : G.relIndex K = H.relIndex J)
    (f : X → ℂ) (hi : ∀ h : H, ∀ x : X, f (h.val • x) = f x) (x : X) :
    CosetTrace.trace (G.subgroupOf K) f (fun g x => hi ⟨g.val.val, hGH g.property⟩ x) x =
      CosetTrace.trace (H.subgroupOf J) f (fun h x => hi ⟨h.val.val, h.property⟩ x) x := by
  classical
  let e := diamondEquiv G H K J hGH hKJ hmeet hindex
  have he (q : K ⧸ G.subgroupOf K) :
      CosetTrace.value (G.subgroupOf K) f (fun g x => hi ⟨g.val.val, hGH g.property⟩ x) q x =
        CosetTrace.value (H.subgroupOf J) f (fun h x => hi ⟨h.val.val, h.property⟩ x) (e q) x := by
    induction q using Quotient.inductionOn with
    | h q =>
      rw [show e (QuotientGroup.mk q) =
        QuotientGroup.mk (⟨q.val, hKJ q.property⟩ : J) from diamondEquiv_mk ..]
      rfl
  unfold CosetTrace.trace
  simp_rw [he]
  exact e.sum_comp (fun q =>
    CosetTrace.value (H.subgroupOf J) f (fun h x => hi ⟨h.val.val, h.property⟩ x) q x)

/-- Intersection of the actual projective congruence groups. The kernel
of the projective label is explicitly contained in each integral level. -/
theorem gamma_inf (A B : ℕ) : gamma A ⊓ gamma B = gamma (Nat.lcm A B) := by
  apply le_antisymm
  · rintro g ⟨⟨s, hs, rfl⟩, ht⟩
    have ht' : s ∈ CongruenceSubgroup.Gamma0 B := by
      have hh : s ∈ ((CongruenceSubgroup.Gamma0 B).map integralLabel).comap integralLabel := ht
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr (integralLabel_ker_le B)] at hh
      exact hh
    refine ⟨s, ?_, rfl⟩
    apply (gamma0_mem_dvd (Nat.lcm A B) s).mpr
    exact Int.natCast_dvd.mpr (Nat.lcm_dvd
      (Int.natCast_dvd.mp ((gamma0_mem_dvd A s).mp hs))
      (Int.natCast_dvd.mp ((gamma0_mem_dvd B s).mp ht')))
  · intro g hg
    exact ⟨gamma_le_of_dvd (Nat.dvd_lcm_left A B) hg,
      gamma_le_of_dvd (Nat.dvd_lcm_right A B) hg⟩

theorem coprime_gamma_inf (M p q : ℕ) (hc : p.Coprime q) :
    gamma (q * M) ⊓ gamma (p * M) = gamma (p * (q * M)) := by
  rw [gamma_inf, Nat.lcm_mul_right, hc.symm.lcm_eq_mul]
  congr 1
  ring

theorem coprime_gamma_index (M p q : ℕ) (hM : 0 < M) (hp : 0 < p)
    (hq : q.Prime) (hc : p.Coprime q) :
    (gamma (p * (q * M))).relIndex (gamma (p * M)) =
      (gamma (q * M)).relIndex (gamma M) := by
  simpa only [level_relIndex] using coprime_level_index M p q hM hp hq hc

/-- Ordinary level change commutes with the other prime's actual finite
trace, first on literal representatives. -/
theorem ordinary_cross_trace_representative (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hc : p.Coprime q)
    (f : AutomorphicL2.representatives (gamma (q * M)) (quotientMeasure (q * M))) :
    levelTraceRepresentative (show p * M ∣ p * (q * M) from ⟨q, by ring⟩)
      (levelCoverRepresentative (Nat.dvd_mul_left (q * M) p) f) =
    levelCoverRepresentative (Nat.dvd_mul_left M p)
      (levelTraceRepresentative (Nat.dvd_mul_left M q) f) := by
  let := Fintype.ofFinite (gamma (p * M) ⧸
    (gamma (p * (q * M))).subgroupOf (gamma (p * M)))
  let := Fintype.ofFinite (gamma M ⧸ (gamma (q * M)).subgroupOf (gamma M))
  apply Subtype.ext
  funext x
  exact finiteTrace_diamond (gamma (p * (q * M))) (gamma (q * M)) (gamma (p * M)) (gamma M)
    (gamma_le_of_dvd (Nat.dvd_mul_left (q * M) p)) (gamma_le_of_dvd (Nat.dvd_mul_left M p))
    (coprime_gamma_inf M p q hc) (coprime_gamma_index M p q hM hp hq hc)
    f.val f.property.2.1 x

/-- The same cross-prime identity on every completed physical quotient
vector, obtained by density with bounded operators. -/
theorem ordinary_cross_levelTrace (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hc : p.Coprime q)
    (v : AutomorphicSpace (q * M)) :
    levelTrace (show p * M ∣ p * (q * M) from ⟨q, by ring⟩)
      (levelCover (Nat.dvd_mul_left (q * M) p) v) =
    levelCover (Nat.dvd_mul_left M p) (levelTrace (Nat.dvd_mul_left M q) v) := by
  have he : (fun v : AutomorphicSpace (q * M) =>
      levelTrace (show p * M ∣ p * (q * M) from ⟨q, by ring⟩)
        (levelCover (Nat.dvd_mul_left (q * M) p) v)) =
      fun v => levelCover (Nat.dvd_mul_left M p) (levelTrace (Nat.dvd_mul_left M q) v) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma (q * M)) (quotientMeasure (q * M))).equalizer
      ((levelTrace (show p * M ∣ p * (q * M) from ⟨q, by ring⟩)).continuous.comp
        (levelCover (Nat.dvd_mul_left (q * M) p)).continuous)
      ((levelCover (Nat.dvd_mul_left M p)).continuous.comp
        (levelTrace (Nat.dvd_mul_left M q)).continuous)
    funext f
    simp only [Function.comp_apply, levelCover_apply, levelTraceRepresentative_embedding]
    rw [ordinary_cross_trace_representative M p q hM hp hq hc]
  exact congrFun he v

/-- Level covers compose as literal pullbacks, on every completed vector. -/
theorem levelCover_comp {L M N : ℕ} [NeZero M] [NeZero N]
    (hLM : L ∣ M) (hMN : M ∣ N) :
    (levelCover hMN).comp (levelCover hLM) = levelCover (hLM.trans hMN) := by
  apply DFunLike.coe_injective
  apply (AutomorphicL2.denseEmbedding_dense (gamma L) (quotientMeasure L)).equalizer
    ((levelCover hMN).continuous.comp (levelCover hLM).continuous) (levelCover _).continuous
  funext f
  simp only [Function.comp_apply, levelCover_apply]
  apply congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
  apply Subtype.ext
  simp only [levelCoverRepresentative_coe]

/-- Taking genuine adjoints gives exact transitivity of completed traces. -/
theorem levelTrace_comp {L M N : ℕ} [NeZero M] [NeZero N]
    (hLM : L ∣ M) (hMN : M ∣ N) :
    (levelTrace hLM).comp (levelTrace hMN) = levelTrace (hLM.trans hMN) := by
  have he := congrArg ContinuousLinearMap.adjoint (levelCover_comp hLM hMN)
  simpa only [ContinuousLinearMap.adjoint_comp, levelTrace] using he

/-- The weight-zero pullback trace for honest real matrix groups. This
definition uses no holomorphic structure or slash-weight normalization. -/
def matrixPullbackTrace (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] [H.IsArithmetic]
    (f : ℍ → ℂ) (hf : ∀ g : G, ∀ z : ℍ, f (g.val • z) = f z) : ℍ → ℂ := by
  let : G.IsFiniteRelIndex H :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := G)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := H)).symm).1
  let := Fintype.ofFinite (H ⧸ G.subgroupOf H)
  exact CosetTrace.trace (G.subgroupOf H) f (fun g z => hf ⟨g.val.val, g.property⟩ z)

theorem matrixPullbackTrace_target_congr (G H J : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [H.IsArithmetic] [J.IsArithmetic] (hHJ : H = J)
    (f : ℍ → ℂ) (hf : ∀ g : G, ∀ z : ℍ, f (g.val • z) = f z) :
    matrixPullbackTrace G H f hf = matrixPullbackTrace G J f hf := by
  subst J
  rfl

theorem matrixPullbackTrace_fun_congr (G H : Subgroup (GL (Fin 2) ℝ))
    [G.IsArithmetic] [H.IsArithmetic] (f g : ℍ → ℂ)
    (hf : ∀ a : G, ∀ z : ℍ, f (a.val • z) = f z)
    (hg : ∀ a : G, ∀ z : ℍ, g (a.val • z) = g z) (he : f = g) :
    matrixPullbackTrace G H f hf = matrixPullbackTrace G H g hg := by
  subst g
  rfl

theorem representative_matrix_invariant (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (g : level N) (z : ℍ) : f.val (g.val • z) = f.val z := by
  obtain ⟨A, hA, he⟩ := g.property
  rw [← he]
  simpa only [integralLabel_matrix_action] using
    f.property.2.1 ⟨integralLabel A, ⟨A, hA, rfl⟩⟩ z

/-- The matrix and completed-space traces use the same literal summands.
The relative-coset equivalences retain integral representatives. -/
theorem matrixPullbackTrace_level {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    matrixPullbackTrace (level N) (level M) f.val (representative_matrix_invariant N f) =
      (levelTraceRepresentative hMN f).val := by
  classical
  let : (level N).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let := Fintype.ofFinite (CongruenceSubgroup.Gamma0 M ⧸
    (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M))
  let := Fintype.ofFinite (level M ⧸ (level N).subgroupOf (level M))
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  funext z
  change (∑ q : level M ⧸ (level N).subgroupOf (level M),
      CosetTrace.value _ f.val _ q z) =
    ∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M), CosetTrace.value _ f.val _ q z
  rw [← (matrixEquiv N M).sum_comp, ← (projectiveEquiv N M).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h a =>
    change f.val ((SpecialLinearGroup.mapGL ℝ a.val)⁻¹ • z) =
      f.val ((integralLabel a.val)⁻¹ • z)
    rw [← map_inv, ← map_inv, integralLabel_matrix_action]

/-- The Fricke trace is precisely the pullback of the trace to the
conjugated old group, with no extra scalar at weight zero. -/
theorem matrixPullbackTrace_fricke {M N : ℕ} [NeZero M] [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) (z : ℍ) :
    matrixPullbackTrace (level N) (frickeOldLevel N M hN) f.val
        (representative_matrix_invariant N f) (frickeReal N hN • z) =
      (levelTraceRepresentative hMN (frickeRepresentative N hN f)).val z := by
  classical
  let : (level N).IsFiniteRelIndex (frickeOldLevel N M hN) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := frickeOldLevel N M hN)).symm).1
  let := Fintype.ofFinite (CongruenceSubgroup.Gamma0 M ⧸
    (CongruenceSubgroup.Gamma0 N).subgroupOf (CongruenceSubgroup.Gamma0 M))
  let := Fintype.ofFinite (frickeOldLevel N M hN ⧸
    (level N).subgroupOf (frickeOldLevel N M hN))
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  change (∑ q : frickeOldLevel N M hN ⧸ (level N).subgroupOf (frickeOldLevel N M hN),
      CosetTrace.value _ f.val _ q (frickeReal N hN • z)) =
    ∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M),
      CosetTrace.value _ (frickeRepresentative N hN f).val _ q z
  rw [← (frickeMatrixEquiv N M hN).sum_comp, ← (projectiveEquiv N M).sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h a =>
    rw [show frickeMatrixEquiv N M hN (QuotientGroup.mk a) =
      QuotientGroup.mk (frickeMatrixRepresentative N M hN a) from imageEquivOfEq_mk ..]
    change f.val ((frickeReal N hN * SpecialLinearGroup.mapGL ℝ a.val *
        (frickeReal N hN)⁻¹)⁻¹ • (frickeReal N hN • z)) =
      f.val (frickeLabel N hN • ((integralLabel a.val)⁻¹ • z))
    rw [← map_inv, integralLabel_matrix_action, map_inv, frickeLabel_action_real]
    simp only [_root_.mul_inv_rev, inv_inv, mul_smul, inv_smul_smul]

/-- Mixed ordinary/dilated trace compatibility for arbitrary invariant
functions. The arithmetic input is only the proved group diamond. -/
theorem mixed_matrixPullbackTrace (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hc : p.Coprime q)
    (f : ℍ → ℂ) (hf : ∀ g : level (q * M), ∀ z : ℍ, f (g.val • z) = f z) :
    matrixPullbackTrace (level (p * (q * M))) (dilationLevel (p * M) q hq.pos) f
        (fun g z => hf ⟨g.val, level_antitone (Nat.dvd_mul_left (q * M) p) g.property⟩ z) =
      matrixPullbackTrace (level (q * M)) (dilationLevel M q hq.pos) f hf := by
  classical
  let : (level (p * (q * M))).IsFiniteRelIndex (dilationLevel (p * M) q hq.pos) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * (q * M)))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := dilationLevel (p * M) q hq.pos)).symm).1
  let : (level (q * M)).IsFiniteRelIndex (dilationLevel M q hq.pos) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (q * M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := dilationLevel M q hq.pos)).symm).1
  let := Fintype.ofFinite (dilationLevel (p * M) q hq.pos ⧸
    (level (p * (q * M))).subgroupOf (dilationLevel (p * M) q hq.pos))
  let := Fintype.ofFinite (dilationLevel M q hq.pos ⧸
    (level (q * M)).subgroupOf (dilationLevel M q hq.pos))
  funext z
  exact finiteTrace_diamond (level (p * (q * M))) (level (q * M))
    (dilationLevel (p * M) q hq.pos) (dilationLevel M q hq.pos)
    (level_antitone (Nat.dvd_mul_left (q * M) p))
    (dilationLevel_mono hq.pos (Nat.dvd_mul_left M p))
    (mixed_level_inf M p q hq.pos) (mixed_level_index M p q hM hp hq hc) f hf z

/-- Continuity removes the almost-everywhere ambiguity in a vanishing
completed trace. The converse needs only the actual representative formula. -/
theorem continuous_trace_zero_iff {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    levelTrace hMN (AutomorphicL2.denseEmbedding _ _ f) = 0 ↔
      (levelTraceRepresentative hMN f).val = 0 := by
  constructor
  · intro h
    rw [levelTraceRepresentative_embedding] at h
    have he : levelTraceRepresentative hMN f = 0 :=
      continuous_representative_unique M _ _ (levelTraceRepresentative_continuous hMN f hf)
        continuous_const (by simpa only [map_zero] using h)
    exact congrArg Subtype.val he
  · intro h
    rw [levelTraceRepresentative_embedding]
    rw [show levelTraceRepresentative hMN f = 0 from Subtype.ext h, map_zero]

/-- The second physical newform equation is exactly the literal trace to
the Fricke-conjugated lower group. -/
theorem continuous_fricke_trace_zero_iff {M N : ℕ} [NeZero M] [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    levelTrace hMN (frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ f)) = 0 ↔
      matrixPullbackTrace (level N) (frickeOldLevel N M hN) f.val
        (representative_matrix_invariant N f) = 0 := by
  rw [frickeIsometry_apply,
    continuous_trace_zero_iff hMN _ (frickeRepresentative_continuous N hN f hf)]
  constructor
  · intro he
    funext z
    obtain ⟨w, rfl⟩ := (MulAction.bijective (frickeReal N hN)).surjective z
    rw [matrixPullbackTrace_fricke hN hMN f]
    exact congrFun he w
  · intro he
    funext z
    rw [← matrixPullbackTrace_fricke hN hMN f z]
    exact congrFun he (frickeReal N hN • z)

/-- Fricke interchanges the two genuine trace equations. -/
theorem newTraceKernel_fricke {M N : ℕ} [NeZero N] (hN : 0 < N) (hMN : M ∣ N)
    (v : AutomorphicSpace N) (hv : v ∈ newTraceKernel hN hMN) :
    frickeIsometry N hN v ∈ newTraceKernel hN hMN := by
  change levelTrace hMN v = 0 ∧ levelTrace hMN (frickeIsometry N hN v) = 0 at hv
  change levelTrace hMN (frickeIsometry N hN v) = 0 ∧
    levelTrace hMN (frickeIsometry N hN (frickeIsometry N hN v)) = 0
  exact ⟨hv.2, by rw [frickeIsometry_involutive N hN v]; exact hv.1⟩

/-- Ordinary level change preserves both newform trace equations at a
distinct prime. This is stated on actual continuous representatives and
their completed physical vectors, without a decomposition hypothesis. -/
theorem ordinary_cover_cross_new_continuous (M p q : ℕ)
    [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : q.Prime) (hc : p.Coprime q)
    (f : AutomorphicL2.representatives (gamma (q * M)) (quotientMeasure (q * M)))
    (hf : Continuous f.val)
    (hnew : AutomorphicL2.denseEmbedding _ _ f ∈
      newTraceKernel (Nat.mul_pos hq.pos hM) (Nat.dvd_mul_left M q)) :
    levelCover (Nat.dvd_mul_left (q * M) p) (AutomorphicL2.denseEmbedding _ _ f) ∈
      newTraceKernel (Nat.mul_pos hp (Nat.mul_pos hq.pos hM))
        (show p * M ∣ p * (q * M) from ⟨q, by ring⟩) := by
  change levelTrace _ (AutomorphicL2.denseEmbedding _ _ f) = 0 ∧
    levelTrace _ (frickeIsometry _ _ (AutomorphicL2.denseEmbedding _ _ f)) = 0 at hnew
  change levelTrace _ (levelCover _ (AutomorphicL2.denseEmbedding _ _ f)) = 0 ∧
    levelTrace _ (frickeIsometry _ _
      (levelCover _ (AutomorphicL2.denseEmbedding _ _ f))) = 0
  constructor
  · rw [ordinary_cross_levelTrace M p q hM hp hq hc, hnew.1, map_zero]
  · rw [levelCover_apply]
    apply (continuous_fricke_trace_zero_iff _ _
      (levelCoverRepresentative (Nat.dvd_mul_left (q * M) p) f)
      (levelCoverRepresentative_continuous _ f hf)).mpr
    have he := (continuous_fricke_trace_zero_iff (Nat.mul_pos hq.pos hM)
      (Nat.dvd_mul_left M q) f hf).mp hnew.2
    rw [matrixPullbackTrace_target_congr _ _ _
      (frickeOldLevel_eq_dilationLevel M q hM hq.pos)] at he
    have hg : frickeOldLevel (p * (q * M)) (p * M)
        (Nat.mul_pos hp (Nat.mul_pos hq.pos hM)) = dilationLevel (p * M) q hq.pos := by
      simpa only [Nat.mul_left_comm p q M] using
        frickeOldLevel_eq_dilationLevel (p * M) q (Nat.mul_pos hp hM) hq.pos
    rw [matrixPullbackTrace_target_congr _ _ _ hg]
    rw [matrixPullbackTrace_fun_congr _ _ _ f.val _
      (fun g z => representative_matrix_invariant (q * M) f
        ⟨g.val, level_antitone (Nat.dvd_mul_left (q * M) p) g.property⟩ z)
      (levelCoverRepresentative_coe (Nat.dvd_mul_left (q * M) p) f)]
    rw [mixed_matrixPullbackTrace M p q hM hp hq hc f.val
      (representative_matrix_invariant (q * M) f)]
    exact he

/-- The ordinary p-cover of a continuous q-Fricke-old vector is still
q-Fricke-old at the higher level. This uses inclusion of the actual
conjugated groups and the proved continuous descent criterion. -/
theorem cover_cross_fricke_old_continuous (M p q : ℕ)
    [NeZero M] [NeZero p] [NeZero q] (hM : 0 < M) (hp : 0 < p) (hq : 0 < q)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M))
    (hf : Continuous f.val) :
    levelCover (Nat.dvd_mul_left (q * M) p)
      (frickeIsometry (q * M) (Nat.mul_pos hq hM)
        (levelCover (Nat.dvd_mul_left M q) (AutomorphicL2.denseEmbedding _ _ f))) ∈
      ((frickeIsometry (p * (q * M)) (Nat.mul_pos hp (Nat.mul_pos hq hM))).toContinuousLinearMap.comp
        (levelCover (show p * M ∣ p * (q * M) from ⟨q, by ring⟩))).range := by
  let g := frickeRepresentative (q * M) (Nat.mul_pos hq hM)
    (levelCoverRepresentative (Nat.dvd_mul_left M q) f)
  have hg : Continuous g.val := frickeRepresentative_continuous _ _ _
    (levelCoverRepresentative_continuous _ f hf)
  have hgi : frickeOldLevel (q * M) M (Nat.mul_pos hq hM) ≤ pointwiseStabilizer g.val := by
    apply continuous_fricke_old_invariant (Nat.mul_pos hq hM) (Nat.dvd_mul_left M q) g hg
    refine ⟨AutomorphicL2.denseEmbedding _ _ f, ?_⟩
    change frickeIsometry (q * M) (Nat.mul_pos hq hM)
      (levelCover (Nat.dvd_mul_left M q) (AutomorphicL2.denseEmbedding _ _ f)) =
        AutomorphicL2.denseEmbedding _ _ g
    rw [levelCover_apply, frickeIsometry_apply]
  rw [frickeOldLevel_eq_dilationLevel M q hM hq] at hgi
  have hgroups : frickeOldLevel (p * (q * M)) (p * M)
      (Nat.mul_pos hp (Nat.mul_pos hq hM)) ≤ dilationLevel M q hq := by
    have he : frickeOldLevel (p * (q * M)) (p * M)
        (Nat.mul_pos hp (Nat.mul_pos hq hM)) = dilationLevel (p * M) q hq := by
      simpa only [Nat.mul_left_comm p q M] using
        frickeOldLevel_eq_dilationLevel (p * M) q (Nat.mul_pos hp hM) hq
    rw [he]
    exact dilationLevel_mono hq (Nat.dvd_mul_left M p)
  have hh := (continuous_fricke_cover_range_iff (Nat.mul_pos hp (Nat.mul_pos hq hM))
    (show p * M ∣ p * (q * M) from ⟨q, by ring⟩)
    (levelCoverRepresentative (Nat.dvd_mul_left (q * M) p) g)
    (levelCoverRepresentative_continuous _ g hg)).mpr
      (by simpa only [levelCoverRepresentative_coe] using hgroups.trans hgi)
  simpa only [levelCover_apply, frickeIsometry_apply, g] using hh

/-- The genuine adjoint of ordinary level change preserves the other
prime's paired trace kernel on every completed vector. The second equation
is tested against dense smooth Poincare vectors, then uses the actual old
group inclusion above. No regularity is assumed for the input vector. -/
theorem levelTrace_cross_new (M p q : ℕ) [NeZero M] [NeZero p] [NeZero q]
    (hM : 0 < M) (hp : 0 < p) (hq : 0 < q)
    (v : AutomorphicSpace (p * (q * M)))
    (hv : v ∈ newTraceKernel (Nat.mul_pos hp (Nat.mul_pos hq hM))
      (show p * M ∣ p * (q * M) from ⟨q, by ring⟩)) :
    levelTrace (Nat.dvd_mul_left (q * M) p) v ∈
      newTraceKernel (Nat.mul_pos hq hM) (Nat.dvd_mul_left M q) := by
  have ho : v ∈ (oldDirections (Nat.mul_pos hp (Nat.mul_pos hq hM))
      (show p * M ∣ p * (q * M) from ⟨q, by ring⟩))ᗮ := by
    rwa [← newTraceKernel_eq_orthogonal]
  change levelTrace _ v = 0 ∧ levelTrace _ (frickeIsometry _ _ v) = 0 at hv
  change levelTrace _ (levelTrace _ v) = 0 ∧
    levelTrace _ (frickeIsometry _ _ (levelTrace _ v)) = 0
  constructor
  · change ((levelTrace (Nat.dvd_mul_left M q)).comp
      (levelTrace (Nat.dvd_mul_left (q * M) p))) v = 0
    rw [levelTrace_comp]
    have he := DFunLike.congr_fun (levelTrace_comp (Nat.dvd_mul_left M p)
      (show p * M ∣ p * (q * M) from ⟨q, by ring⟩)) v
    rw [ContinuousLinearMap.comp_apply, hv.1, map_zero] at he
    exact he.symm
  · apply (poincareSeedVector_dense M).eq_of_inner_right (𝕜 := ℂ)
    intro u
    rw [inner_zero_right]
    rw [levelTrace, ContinuousLinearMap.adjoint_inner_right]
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (frickeIsometry_selfAdjoint (q * M) (Nat.mul_pos hq hM))
      (levelCover (Nat.dvd_mul_left M q) (poincareSeedVector M u))
      (levelTrace (Nat.dvd_mul_left (q * M) p) v)
    change inner ℂ (frickeIsometry (q * M) (Nat.mul_pos hq hM)
      (levelCover (Nat.dvd_mul_left M q) (poincareSeedVector M u)))
      (levelTrace (Nat.dvd_mul_left (q * M) p) v) =
        inner ℂ (levelCover (Nat.dvd_mul_left M q) (poincareSeedVector M u))
          (frickeIsometry (q * M) (Nat.mul_pos hq hM)
            (levelTrace (Nat.dvd_mul_left (q * M) p) v)) at hs
    rw [← hs, levelTrace, ContinuousLinearMap.adjoint_inner_right]
    let f : AutomorphicL2.representatives (gamma M) (quotientMeasure M) :=
      ⟨_, poincareSeed_representative M u⟩
    have hf : Continuous f.val := by
      let : ContinuousConstSMul (gamma M) ℍ :=
        ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
      exact poincareSum_continuous (G := gamma M) _ u.compact (upperFunction_continuous u.smooth)
    apply (Submodule.mem_orthogonal _ _).mp ho _
    apply Submodule.mem_sup_right
    exact cover_cross_fricke_old_continuous M p q hM hp hq f hf

#print axioms finiteTrace_diamond
#print axioms gamma_inf
#print axioms coprime_gamma_inf
#print axioms coprime_gamma_index
#print axioms ordinary_cross_trace_representative
#print axioms ordinary_cross_levelTrace
#print axioms levelCover_comp
#print axioms levelTrace_comp
#print axioms matrixPullbackTrace_target_congr
#print axioms matrixPullbackTrace_fun_congr
#print axioms representative_matrix_invariant
#print axioms matrixPullbackTrace_level
#print axioms matrixPullbackTrace_fricke
#print axioms mixed_matrixPullbackTrace
#print axioms continuous_trace_zero_iff
#print axioms continuous_fricke_trace_zero_iff
#print axioms newTraceKernel_fricke
#print axioms ordinary_cover_cross_new_continuous
#print axioms cover_cross_fricke_old_continuous
#print axioms levelTrace_cross_new

end QuantitativeNinaMaass
