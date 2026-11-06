module

public import QuantitativeSpectralCornerAlgebraV1
public import QuantitativeEulerEndpointRetainedInitialPolynomialV1
public import QuantitativeEulerEndpointUpdateExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBernstein
open Polynomial
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem scalar_initializer_order {q : ℝ[X]} (hq : ScalarInitializer q)
    (a : A) (ha0 : 0≤a) (ha1 : a≤1) : 0≤aeval a q ∧ aeval a q≤1 := by
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  have hn : ‖a‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg a ha0).mpr ha1
  have hs (x : ℝ) (hx : x∈spectrum ℝ a) : x∈Set.Icc (0:ℝ) 1 :=
    ⟨spectrum_nonneg_of_nonneg ha0 hx,(le_abs_self x).trans
      ((quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ a hx)).trans hn)⟩
  rw [←cfc_polynomial q a ha]
  exact ⟨cfc_nonneg (fun x hx => (hq.2 ⟨x,hs x hx⟩).1),
    cfc_le_one q.eval a (fun x hx => (hq.2 ⟨x,hs x hx⟩).2)⟩

end QuantitativeEulerEndpointBernstein
namespace QuantitativeEulerEndpointPhysicalCorner
open Polynomial QuantitativeEulerEndpointBernstein QuantitativeEulerEndpointUpdateExpression

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (P : A) (hP : IsStarProjection P)

def Corner : Type _ := QuantitativeSpectralCornerAlgebra.cornerSubalgebra P hP.isIdempotentElem hP.isSelfAdjoint
instance cornerCStar : CStarAlgebra (Corner P hP) := inferInstanceAs
  (CStarAlgebra (QuantitativeSpectralCornerAlgebra.cornerSubalgebra P hP.isIdempotentElem hP.isSelfAdjoint))
instance cornerOrder : PartialOrder (Corner P hP) := CStarAlgebra.spectralOrder _
instance cornerStarOrdered : StarOrderedRing (Corner P hP) := CStarAlgebra.spectralOrderedRing _

def inclusion : Corner P hP →⋆ₙₐ[ℂ] A where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

def realInclusion : Corner P hP →ₗ[ℝ] A where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_le_iff (a b : Corner P hP) : a.val≤b.val ↔ a≤b :=
  NonUnitalStarAlgHom.map_le_map_iff (A:=Corner P hP) (B:=A) (inclusion P hP) (fun _ _ h => Subtype.ext h)

def lift (a : A) (hl : P*a=a) (hr : a*P=a) : Corner P hP :=
  ⟨a,(Subsemigroup.mem_corner_iff hP.isIdempotentElem).mpr ⟨hl,hr⟩⟩

theorem lift_order (a : A) (hl : P*a=a) (hr : a*P=a) (ha0 : 0≤a) (ha1 : a≤1) :
    0≤lift P hP a hl hr ∧ lift P hP a hl hr≤1 := by
  have h0 : 0≤lift P hP a hl hr := (coe_le_iff P hP 0 _).mp ha0
  have hn : ‖lift P hP a hl hr‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg a ha0).mpr ha1
  exact ⟨h0,(CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).mp hn⟩

omit [PartialOrder A] [StarOrderedRing A] in
theorem coe_support (a : Corner P hP) : P*a.val=a.val ∧ a.val*P=a.val :=
  (Subsemigroup.mem_corner_iff hP.isIdempotentElem).mp a.property

omit [PartialOrder A] [StarOrderedRing A] in
theorem coe_aeval (a : Corner P hP) (q : ℝ[X]) :
    (aeval a q : Corner P hP).val=aeval a.val q*P :=
  QuantitativeEulerEndpointCornerPolynomial.map_aeval_corner
    (realInclusion P hP) (fun _ _ => rfl) a q

omit [PartialOrder A] [StarOrderedRing A] in
theorem coe_update (a g : Corner P hP) (n : ℕ) :
    (QuantitativeEulerEndpointSoftUpdate.update a (a*g*a) n : Corner P hP).val=
      cornerUpdate P a.val g.val n :=
  QuantitativeEulerEndpointUpdateExpression.map_update (realInclusion P hP) (fun _ _ => rfl) a g n

include hP in
/-- Evaluate an initializer in the actual corner: its constant term is P. -/
theorem initial_order (a : A) (hl : P*a=a) (hr : a*P=a) (ha0 : 0≤a) (ha1 : a≤1)
    {q : ℝ[X]} (hq : ScalarInitializer q) :
    0≤aeval a q*P ∧ aeval a q*P≤P ∧
      P*(aeval a q*P)=aeval a q*P ∧ (aeval a q*P)*P=aeval a q*P := by
  let a' := lift P hP a hl hr
  have ha' := lift_order P hP a hl hr ha0 ha1
  have ho := scalar_initializer_order hq a' ha'.1 ha'.2
  have he : (aeval a' q : Corner P hP).val=aeval a q*P := coe_aeval P hP a' q
  have h0 : (0:A)≤(aeval a' q : Corner P hP).val := (coe_le_iff P hP 0 _).mpr ho.1
  have h1 : (aeval a' q : Corner P hP).val≤P := (coe_le_iff P hP _ 1).mpr ho.2
  have hs := coe_support P hP (aeval a' q)
  rw [he] at h0 h1 hs
  exact ⟨h0,h1,hs⟩

include hP in
/-- One physical update is order decreasing in the same band, for the same
scalar sharpening polynomial selected by the regular spectral measure. -/
theorem sharpened_order (a g : A) (hal : P*a=a) (har : a*P=a)
    (hgl : P*g=g) (hgr : g*P=g) (ha0 : 0≤a) (ha1 : a≤1) (hg0 : 0≤g) (hg1 : g≤1)
    (n : ℕ) {q : ℝ[X]} (hq : ScalarSharpening q) :
    let z := aeval (cornerUpdate P a g n) q*P
    0≤z ∧ z≤a ∧ P*z=z ∧ z*P=z := by
  let a' := lift P hP a hal har
  let g' := lift P hP g hgl hgr
  have ha' := lift_order P hP a hal har ha0 ha1
  have hg' := lift_order P hP g hgl hgr hg0 hg1
  have hc : 0≤a'*g'*a' ∧ a'*g'*a'≤1 := by
    simpa only [inv_one,one_smul] using QuantitativeEulerEndpointSoftUpdate.compressed_energy_order
      a' g' ha'.1 ha'.2 hg'.1 (by norm_num : (0:ℝ)<1) (by simpa only [one_smul] using hg'.2)
  let u := QuantitativeEulerEndpointSoftUpdate.update a' (a'*g'*a') n
  have hu := QuantitativeEulerEndpointSoftUpdate.update_order a' (a'*g'*a') ha'.1 ha'.2 hc.1 hc.2 n
  have hq' := scalar_sharpening_order hq u hu.1 (hu.2.trans ha'.2)
  have he : (aeval u q : Corner P hP).val=aeval (cornerUpdate P a g n) q*P := by
    rw [coe_aeval,coe_update]
    rfl
  have h0 : (0:A)≤(aeval u q : Corner P hP).val := (coe_le_iff P hP 0 _).mpr hq'.1
  have h1 : (aeval u q : Corner P hP).val≤a := (coe_le_iff P hP _ a').mpr (hq'.2.trans hu.2)
  have hs := coe_support P hP (aeval u q)
  rw [he] at h0 h1 hs
  exact ⟨h0,h1,hs⟩

#print axioms initial_order
#print axioms sharpened_order
end QuantitativeEulerEndpointPhysicalCorner
