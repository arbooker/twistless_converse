module

public import QuantitativeMaassRegularComplementTraceV1
public import QuantitativeMaassRegularSupportedErrorV1
public import QuantitativeMaassRegularFamilyOperationsV1

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped lp ENNReal
namespace AsymptoticRegularTrace
variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
    [TopologicalSpace α] [DiscreteTopology α]

/-- Semifinite regular weighted excess: only the positive filter trace and
the finite canonical projection trace occur, never the ambient unit trace. -/
theorem signedTrace_weighted_projection_excess (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (B F E : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
    (hmB : ∀ g h,Measurable (fun x => matrix (B x) g h))
    (hmF : ∀ g h,Measurable (fun x => matrix (F x) g h))
    (hmE : ∀ g h,Measurable (fun x => matrix (E x) g h))
    (hcB : Covariant B) (hcF : Covariant F) (hcE : Covariant E)
    (hp : ∀ x,0≤F x) (hp1 : ∀ x,F x≤1) (hE : ∀ x,IsStarProjection (E x))
    (hf : trace μ F<∞) (he : trace μ E<∞)
    {C δ : ℝ} (hC : 0≤C) (hδ : 0≤δ) (hb : ∀ x,‖B x‖≤C)
    (hfix : ∀ x,‖F x*E x-E x‖≤δ) :
    |signedTrace μ (fun x => B x*(F x-E x))|≤
      C*(signedTrace μ F-(trace μ E).toReal+4*δ*(trace μ E).toReal) := by
  let X := fun x => F x*E x-E x
  let D := fun x => (1 : ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))-E x
  let H := fun x => D x*F x*D x
  have hEn (x : α) : ‖E x‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hE x).nonneg).mpr (hE x).le_one
  have hFn (x : α) : ‖F x‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hp x)).mpr (hp1 x)
  have hEE (x : α) : E x*E x=E x := (hE x).isIdempotentElem.eq
  have hEs (x : α) : star (E x)=E x := (hE x).isSelfAdjoint.star_eq
  have hFs (x : α) : star (F x)=F x := (IsSelfAdjoint.of_nonneg (hp x)).star_eq
  have hDa (x : α) : (D x).adjoint=D x := by
    rw [←ContinuousLinearMap.star_eq_adjoint]
    simp only [D,star_sub,star_one,hEs]
  have hDn (x : α) : ‖D x‖≤2 := by
    have hh := norm_sub_le (1 : ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ)) (E x)
    have h1 : ‖(1 : ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))‖≤1 := ContinuousLinearMap.norm_id_le
    dsimp only [D]
    linarith [hEn x]
  have hmX := matrix_sub_measurable (fun x => F x*E x) E (matrix_comp_measurable _ _ hmF hmE) hmE
  have hcX := covariant_sub (fun x => F x*E x) E (covariant_comp _ _ hcF hcE) hcE
  have hmD := matrix_sub_measurable (fun _ : α => 1) E (fun _ _ => measurable_const) hmE
  have hcD := covariant_sub (fun _ : α => 1) E covariant_one hcE
  have hmH := matrix_comp_measurable (fun x => D x*F x) D (matrix_comp_measurable _ _ hmD hmF) hmD
  have hcH := covariant_comp (fun x => D x*F x) D (covariant_comp _ _ hcD hcF) hcD
  have hHpos (x : α) : 0≤H x := by
    have hh := star_left_conjugate_nonneg (hp x) (D x)
    have hs : star (D x)=D x := by rw [ContinuousLinearMap.star_eq_adjoint,hDa]
    simpa only [hs,H] using hh
  have hHn (x : α) : ‖H x‖≤4 := by
    calc
      _ ≤ (‖D x‖*‖F x‖)*‖D x‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (2*1)*2 := mul_le_mul
        (mul_le_mul (hDn x) (hFn x) (norm_nonneg _) (by norm_num)) (hDn x) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hHf : trace μ H<∞ := by
    have hh := positive_sandwich_trace_finite μ hmp F D hmF hmD hcF hcD hp hFn hDn hf
    simpa only [hDa,mul_def,comp_assoc,H] using hh
  have hXE (x : α) : X x*E x=X x := by
    dsimp only [X]
    rw [sub_mul,mul_assoc,hEE]
  have hXn (x : α) : ‖X x‖≤δ := hfix x
  have htx := signedTrace_right_supported_bound μ hmp E X hE hmE hmX hcE hcX he hXn hXE
  have hte : signedTrace μ E=(trace μ E).toReal := signedTrace_eq_toReal μ E (hmE 1 1)
    (fun x => nonneg_iff_isPositive.mp (hE x).nonneg)
  have htH := signedTrace_projection_complement μ hmp F E hmF hmE hcF hcE hp hE hFn hf he
  have hgt : signedTrace μ H≤signedTrace μ F-(trace μ E).toReal+δ*(trace μ E).toReal := by
    change signedTrace μ H=signedTrace μ F-signedTrace μ E-signedTrace μ X at htH
    rw [htH,hte]
    linarith [(abs_le.mp htx).1]
  have hbH := signedTrace_positive_weight_bound μ hmp H B hmH hmB hcH hcB hHpos hHn hb hHf
  rw [←signedTrace_eq_toReal μ H (hmH 1 1) (fun x => nonneg_iff_isPositive.mp (hHpos x))] at hbH
  have hiBH := positive_weight_diagonal_integrable μ hmp H B hmH hmB hcH hcB hHpos hHn hb hHf
  change Integrable (fun x => rootDiagonal (B x*H x)) μ at hiBH
  have rightBound (Z : α → ℓ²(G,ℂ)→L[ℂ]ℓ²(G,ℂ))
      (hmZ : ∀ g h,Measurable (fun x => matrix (Z x) g h)) (hcZ : Covariant Z)
      (hnZ : ∀ x,‖Z x‖≤δ) (hsZ : ∀ x,Z x*E x=Z x) :
      |signedTrace μ (fun x => B x*Z x)|≤C*δ*(trace μ E).toReal ∧
        Integrable (fun x => rootDiagonal (B x*Z x)) μ := by
    have hnorm (x : α) : ‖B x*Z x‖≤C*δ := (norm_mul_le _ _).trans
      (mul_le_mul (hb x) (hnZ x) (norm_nonneg _) hC)
    have hsup (x : α) : B x*Z x*E x=B x*Z x := by rw [mul_assoc,hsZ]
    have hmBZ := matrix_comp_measurable B Z hmB hmZ
    have hcBZ := covariant_comp B Z hcB hcZ
    exact ⟨signedTrace_right_supported_bound μ hmp E _ hE hmE hmBZ hcE hcBZ he hnorm hsup,
      right_supported_diagonal_integrable μ hmp E _ hE hmE hmBZ hcBZ he hnorm hsup⟩
  have hbX := rightBound X hmX hcX hXn hXE
  have hmXa : ∀ g h,Measurable (fun x => matrix (star (X x)) g h) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using matrix_adjoint_measurable X hmX
  have hcXa : Covariant (fun x => star (X x)) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using covariant_adjoint X hcX
  have hEXa (x : α) : E x*star (X x)=star (X x) := by
    have hh := congrArg star (hXE x)
    simpa only [star_mul,hEs] using hh
  have hbXa := left_supported_weight_trace_bound μ hmp E B (fun x => star (X x)) hE hmE hmB hmXa
    hcE hcB hcXa he hC hδ hb (fun x => by
      rw [ContinuousLinearMap.star_eq_adjoint,adjoint.norm_map]
      exact hXn x) hEXa
  have hEXn (x : α) : ‖E x*X x‖≤δ := (norm_mul_le _ _).trans
    ((mul_le_mul (hEn x) (hXn x) (norm_nonneg _) zero_le_one).trans_eq (one_mul δ))
  have hEXsup (x : α) : E x*X x*E x=E x*X x := by rw [mul_assoc,hXE]
  have hbEX := rightBound (fun x => E x*X x) (matrix_comp_measurable _ _ hmE hmX)
    (covariant_comp _ _ hcE hcX) hEXn hEXsup
  have hid (x : α) : F x-E x=H x+X x+star (X x)-E x*X x := by
    have hXa : star (X x)=E x*F x-E x := by
      change (F x*E x-E x).adjoint=_
      rw [map_sub]
      change ((F x).comp (E x)).adjoint-(E x).adjoint=_
      rw [adjoint_comp,(hE x).isSelfAdjoint.adjoint_eq,
        (IsSelfAdjoint.of_nonneg (hp x)).adjoint_eq]
      rfl
    rw [hXa]
    dsimp only [H,D,X]
    simp only [sub_mul,mul_sub,one_mul,mul_one,mul_assoc,hEE]
    abel
  have hsum : signedTrace μ (fun x => B x*(F x-E x))=
      signedTrace μ (fun x => B x*H x)+signedTrace μ (fun x => B x*X x)+
      signedTrace μ (fun x => B x*star (X x))-signedTrace μ (fun x => B x*(E x*X x)) := by
    simp_rw [hid,mul_sub,mul_add]
    rw [signedTrace_sub_of_integrable μ _ _
      (diagonal_integrable_add μ _ _ (diagonal_integrable_add μ _ _ hiBH hbX.2) hbXa.2) hbEX.2,
      signedTrace_add_of_integrable μ _ _ (diagonal_integrable_add μ _ _ hiBH hbX.2) hbXa.2,
      signedTrace_add_of_integrable μ _ _ hiBH hbX.2]
  rw [hsum]
  have hmain := (abs_sub
    (signedTrace μ (fun x => B x*H x)+signedTrace μ (fun x => B x*X x)+signedTrace μ (fun x => B x*star (X x)))
    (signedTrace μ (fun x => B x*(E x*X x)))).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  have hh := hmain.trans (add_le_add (add_le_add (add_le_add hbH hbX.1) hbXa.1) hbEX.1)
  have hg := mul_le_mul_of_nonneg_left hgt hC
  nlinarith

#print axioms signedTrace_weighted_projection_excess
end AsymptoticRegularTrace
