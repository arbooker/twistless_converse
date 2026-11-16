module
public import QuantitativeArithmeticNewBandProjectionsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
@[expose] public noncomputable section
open QuantitativeMaass QuantitativeNinaMaass QuantitativeArithmeticNewBandProjections
open QuantitativeArithmeticRepeatedTwoBands
open scoped InnerProductSpace
namespace QuantitativeArithmeticNewBandProduct

section FiniteHilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

def listInf : List (Submodule ℂ E) → Submodule ℂ E
  | [] => ⊤
  | K::L => K ⊓ listInf L

omit [FiniteDimensional ℂ E] in
theorem mem_listInf (L : List (Submodule ℂ E)) (x : E) :
    x∈listInf L ↔ ∀ K∈L,x∈K := by
  induction L with
  | nil => simp [listInf]
  | cons K L ih => simp [listInf,ih]

theorem inf_projection (K J : Submodule ℂ E)
    (hc : Commute K.starProjection J.starProjection) :
    (K⊓J).starProjection=K.starProjection*J.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · constructor
    · exact K.starProjection_apply_mem _
    · have he := DFunLike.congr_fun hc.eq x
      change K.starProjection (J.starProjection x)=J.starProjection (K.starProjection x) at he
      change K.starProjection (J.starProjection x)∈J
      rw [he]
      exact J.starProjection_apply_mem _
  · intro w hw
    change inner ℂ (x-K.starProjection (J.starProjection x)) w=0
    rw [inner_sub_left,K.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hw.1,
      J.inner_starProjection_left_eq_right,Submodule.starProjection_eq_self_iff.mpr hw.2,
      sub_self]

/-- A finite product of commuting orthogonal projections is exactly the
projection onto their intersection, in any ordering. -/
theorem list_projection (L : List (Submodule ℂ E))
    (hc : ∀ K∈L,∀ J∈L,Commute K.starProjection J.starProjection) :
    (listInf L).starProjection=(L.map fun K => K.starProjection).prod := by
  induction L with
  | nil =>
    simp only [listInf,List.map_nil,List.prod_nil]
    apply ContinuousLinearMap.ext
    intro x
    exact Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_top)
  | cons K L ih =>
    have hh : (listInf L).starProjection=(L.map fun J => J.starProjection).prod :=
      ih (fun J hJ H hH => hc J (List.mem_cons_of_mem _ hJ) H (List.mem_cons_of_mem _ hH))
    have hk : Commute K.starProjection (listInf L).starProjection := by
      rw [hh]
      apply Commute.list_prod_right
      intro U hU
      obtain ⟨J,hJ,rfl⟩ := List.mem_map.mp hU
      exact hc K (List.mem_cons_self) J (List.mem_cons_of_mem _ hJ)
    rw [listInf,inf_projection _ _ hk,hh,List.map_cons,List.prod_cons]

/-- The same identity for an indexed finite family. -/
theorem family_projection {I : Type*} [Fintype I] (K : I → Submodule ℂ E)
    (hc : ∀ i j,Commute (K i).starProjection (K j).starProjection) :
    (⨅ i,K i).starProjection =
      ((Finset.univ : Finset I).toList.map fun i => (K i).starProjection).prod := by
  classical
  let L := (Finset.univ : Finset I).toList.map K
  have he : listInf L=⨅ i,K i := by
    ext x
    rw [mem_listInf,Submodule.mem_iInf]
    constructor
    · intro hx i
      exact hx _ (List.mem_map.mpr ⟨i,by simp,rfl⟩)
    · intro hx U hU
      obtain ⟨i,_,hu⟩ := List.mem_map.mp hU
      rw [←hu]
      exact hx i
  have hh : ∀ U∈L,∀ V∈L,Commute U.starProjection V.starProjection := by
    intro U hU V hV
    obtain ⟨i,_,hu⟩ := List.mem_map.mp hU
    obtain ⟨j,_,hv⟩ := List.mem_map.mp hV
    rw [←hu,←hv]
    exact hc i j
  have ht := list_projection L hh
  simpa only [he,L,List.map_map,Function.comp_def] using ht

end FiniteHilbert

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance




local instance (N : ℕ) (p : ↥N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

local instance (N : ℕ) [NeZero N] (p : ↥N.primeFactors) : NeZero (N/p.val) :=
  ⟨(prime_quotient_pos N p.val (NeZero.pos N)
    (Nat.prime_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩

variable (N : ℕ) [NeZero N] (hN : 0<N)
    (T : CuspEnergySpectrum N hN)
    (S : ∀ p : ↥N.primeFactors, CuspEnergySpectrum (N/p.val)
      (prime_quotient_pos N p.val hN (Nat.prime_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property))) (a b σ : ℝ)

def localNewBand (p : ↥N.primeFactors) : Submodule ℂ (T.parityBand a b σ) :=
  (S p).traceNewParityBand T (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors p.property)) a b σ

/-- The actual total trace-new subspace of the full cusp parity band. -/
def totalNewBand : Submodule ℂ (T.parityBand a b σ) :=
  (newSpace N hN).comap (inclusion T a b σ)

theorem local_commute (p q : ↥N.primeFactors) :
    Commute (localNewBand N hN T S a b σ p).starProjection
      (localNewBand N hN T S a b σ q).starProjection := by
  by_cases hpq : p=q
  · subst q
    exact Commute.refl _
  · exact prime_divisor_projections_commute N p.val q.val hN
      (Nat.prime_of_mem_primeFactors p.property) (Nat.prime_of_mem_primeFactors q.property)
      (Nat.dvd_of_mem_primeFactors p.property) (Nat.dvd_of_mem_primeFactors q.property)
      (fun he => hpq (Subtype.ext he)) (S p) (S q) T a b σ

theorem totalNewBand_eq_inf : totalNewBand N hN T a b σ =
    ⨅ p : ↥N.primeFactors,localNewBand N hN T S a b σ p := by
  ext x
  change (inclusion T a b σ x∈newSpace N hN) ↔ _
  simp only [newSpace,Submodule.mem_iInf]
  constructor
  · intro hx p
    apply ((S p).mem_traceNewParityBand T _ a b σ x).mpr
    exact hx ⟨p.val,Nat.prime_of_mem_primeFactors p.property,Nat.dvd_of_mem_primeFactors p.property⟩
  · intro hx p
    let i : ↥N.primeFactors := ⟨p.val,Nat.mem_primeFactors.mpr ⟨p.property.1,p.property.2,hN.ne'⟩⟩
    exact ((S i).mem_traceNewParityBand T _ a b σ x).mp (hx i)

/-- The finite product of the actual local projections is the exact
orthogonal projection onto the actual total-new cusp parity band. -/
theorem totalNewBand_projection :
    (totalNewBand N hN T a b σ).starProjection =
      ((Finset.univ : Finset ↥N.primeFactors).toList.map
        fun p => (localNewBand N hN T S a b σ p).starProjection).prod := by
  have hp := family_projection (localNewBand N hN T S a b σ) (local_commute N hN T S a b σ)
  have he := congrArg (fun K : Submodule ℂ (T.parityBand a b σ) => K.starProjection)
    (totalNewBand_eq_inf N hN T S a b σ)
  exact he.trans hp

#print axioms inf_projection
#print axioms list_projection
#print axioms family_projection
#print axioms local_commute
#print axioms totalNewBand_eq_inf
#print axioms totalNewBand_projection
end QuantitativeArithmeticNewBandProduct
