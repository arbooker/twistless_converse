module

public import QuantitativeArithmeticRetainedGeometricTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticEnvelope

variable {d r : ℕ} {f g : ℝ → ℝ}

/-- A fixed polynomial is bounded by an exponential with a linear exponent.
This avoids propagating an artificial polynomial degree into log-log scales. -/
theorem Poly.toLinearExp (hf : Poly d f) : Exp 1 f := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨C+d,by positivity,fun u hu => ?_⟩
  have hu0 : 0≤u := zero_le_one.trans hu
  have he : u≤Real.exp u := by linarith [Real.add_one_le_exp u]
  have hc : C≤Real.exp C := by linarith [Real.add_one_le_exp C]
  have hp : u^d≤Real.exp ((d:ℝ)*u) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hu0 he d
  apply (hf u hu).trans
  calc
    C*u^d ≤ Real.exp C*Real.exp ((d:ℝ)*u) := mul_le_mul hc hp (pow_nonneg hu0 _) (Real.exp_nonneg _)
    _ = Real.exp (C+(d:ℝ)*u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C+d)*u^1) := by
      apply Real.exp_le_exp.mpr
      simp only [pow_one]
      nlinarith

theorem Exp.compPoly (hf : Exp d f) (hg : Poly r g) (hg1 : ∀u,1≤u → 1≤g u) :
    Exp (r*d) (fun u => f (g u)) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C*D^d,by positivity,fun u hu => (hf _ (hg1 u hu)).trans ?_⟩
  apply Real.exp_le_exp.mpr
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (hg1 u hu)) (hg u hu) d) hC
  simpa only [mul_pow,←pow_mul,mul_assoc] using hp

/-- The full observation polynomial has an exponential degree; its expansion
therefore has a double-exponential bound at the same quadratic scale. -/
def DoubleExp (f : ℝ → ℝ) : Prop :=
  ∃C : ℝ,0≤C ∧ ∀u : ℝ,1≤u → f u≤Real.exp (Real.exp (C*u^2))

theorem DoubleExp.mono (hf : DoubleExp f) (hfg : ∀u,1≤u → g u≤f u) : DoubleExp g := by
  obtain ⟨C,hC,h⟩ := hf
  exact ⟨C,hC,fun u hu => (hfg u hu).trans (h u hu)⟩

theorem Exp.toDoubleExp (hf : Exp d f) : DoubleExp f := by
  obtain ⟨C,hC,hf⟩ := hf
  have hp : Poly d (fun u => C*u^d) := ⟨C,hC,fun _ _ => le_rfl⟩
  obtain ⟨D,hD,hd⟩ := hp.toLinearExp.weaken (by omega : 1≤2)
  exact ⟨D,hD,fun u hu => (hf u hu).trans (Real.exp_le_exp.mpr (hd u hu))⟩

theorem DoubleExp.const (c : ℝ) : DoubleExp (fun _ => c) := (Exp.const c 0).toDoubleExp

theorem DoubleExp.mul (hf : DoubleExp f) (hg : DoubleExp g) (hg0 : ∀u,1≤u → 0≤g u) :
    DoubleExp (fun u => f u*g u) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  have ha : Exp 2 (fun u => Real.exp (C*u^2)) := ⟨C,hC,fun _ _ => le_rfl⟩
  have hb : Exp 2 (fun u => Real.exp (D*u^2)) := ⟨D,hD,fun _ _ => le_rfl⟩
  obtain ⟨K,hK,hk⟩ := ha.add hb
  refine ⟨K,hK,fun u hu => ?_⟩
  apply (mul_le_mul (hf u hu) (hg u hu) (hg0 u hu) (Real.exp_nonneg _)).trans
  rw [←Real.exp_add]
  exact Real.exp_le_exp.mpr (hk u hu)

theorem DoubleExp.add (hf : DoubleExp f) (hg : DoubleExp g) : DoubleExp (fun u => f u+g u) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  have ha : Exp 2 (fun u => Real.exp (C*u^2)) := ⟨C,hC,fun _ _ => le_rfl⟩
  have hb : Exp 2 (fun u => Real.exp (D*u^2)) := ⟨D,hD,fun _ _ => le_rfl⟩
  obtain ⟨K,hK,hk⟩ := ((Exp.const 2 2).add ha).add hb
  refine ⟨K,hK,fun u hu => ?_⟩
  have a0 := Real.exp_nonneg (C*u^2)
  have b0 := Real.exp_nonneg (D*u^2)
  have h1 : f u≤Real.exp (Real.exp (C*u^2)+Real.exp (D*u^2)) :=
    (hf u hu).trans (Real.exp_le_exp.mpr (by linarith))
  have h2 : g u≤Real.exp (Real.exp (C*u^2)+Real.exp (D*u^2)) :=
    (hg u hu).trans (Real.exp_le_exp.mpr (by linarith))
  have htwo : (2:ℝ)≤Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  calc
    f u+g u ≤ 2*Real.exp (Real.exp (C*u^2)+Real.exp (D*u^2)) := by linarith
    _ ≤ Real.exp 2*Real.exp (Real.exp (C*u^2)+Real.exp (D*u^2)) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (2+Real.exp (C*u^2)+Real.exp (D*u^2)) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (hk u hu)

theorem Exp.natpowExp (hf : Exp d f) (hf0 : ∀u,1≤u → 0≤f u)
    (n : ℝ → ℕ) (hn : Exp 2 (fun u => (n u:ℝ))) : DoubleExp (fun u => f u^(n u)) := by
  obtain ⟨C,hC,hf⟩ := hf
  have hp : Poly d (fun u => C*u^d) := ⟨C,hC,fun _ _ => le_rfl⟩
  obtain ⟨D,hD,hd⟩ := hn.mul (hp.toLinearExp.weaken (by omega : 1≤2))
    (fun u hu => mul_nonneg hC (pow_nonneg (zero_le_one.trans hu) d))
  refine ⟨D,hD,fun u hu => ?_⟩
  apply (pow_le_pow_left₀ (hf0 u hu) (hf u hu) (n u)).trans
  rw [←Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (hd u hu)

/-- Polynomial accuracy exponents, including the sixth-degree mixed
reconstruction costs, preserve the quadratic double-exponential scale after
an observation polynomial of exponentially growing degree is applied. -/
theorem full_filter_growth {a b : ℕ} (B R : ℝ → ℝ) (n : ℝ → ℕ)
    (hB : Exp a B) (hR : Exp b R) (hB0 : ∀u,1≤u → 0≤B u)
    (hR0 : ∀u,1≤u → 0≤R u) (hn : Exp 2 (fun u => (n u:ℝ))) :
    DoubleExp (fun u => 4*(B u)^2*(2*max 1 (8*(R u)^2*(B u)^2))^(n u)) := by
  let j := max a b
  have hB' := hB.weaken (le_max_left a b)
  have hR' := hR.weaken (le_max_right a b)
  have hBs : Exp j (fun u => (B u)^2) := by simpa only [pow_two] using hB'.mul hB' hB0
  have hRs : Exp j (fun u => (R u)^2) := by simpa only [pow_two] using hR'.mul hR' hR0
  have hv := ((Exp.const 8 j).mul hRs (fun u _ => sq_nonneg _)).mul hBs (fun u _ => sq_nonneg _)
  have hm : Exp j (fun u => max 1 (8*(R u)^2*(B u)^2)) :=
    ((Exp.const 1 j).add hv).mono (fun u _ => max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left zero_le_one))
  have hb := (Exp.const 2 j).mul hm (fun _ _ => le_trans zero_le_one (le_max_left _ _))
  have hp := hb.natpowExp (fun _ _ => by positivity) n hn
  have hc := (Exp.const 4 j).mul hBs (fun _ _ => sq_nonneg _)
  exact hc.toDoubleExp.mul hp (fun _ _ => by positivity)

theorem filter_cost_growth {a b : ℕ} (B R : ℝ → ℝ) (n : ℝ → ℕ)
    (hB : Exp a B) (hR : Exp b R) (hB0 : ∀u,1≤u → 0≤B u)
    (hR0 : ∀u,1≤u → 0≤R u) (hn : Exp 2 (fun u => (n u:ℝ))) :
    DoubleExp (fun u => (B u)^2*(1+R u*(B u)^2)^(n u)) := by
  let j := max a b
  have hB' := hB.weaken (le_max_left a b)
  have hR' := hR.weaken (le_max_right a b)
  have hBs : Exp j (fun u => (B u)^2) := by simpa only [pow_two] using hB'.mul hB' hB0
  have hb := (Exp.const 1 j).add (hR'.mul hBs (fun _ _ => sq_nonneg _))
  have hp := hb.natpowExp (fun u hu => by have := hR0 u hu; positivity) n hn
  exact hBs.toDoubleExp.mul hp (fun u hu => pow_nonneg (by have := hR0 u hu; positivity) _)

#print axioms Poly.toLinearExp
#print axioms Exp.compPoly
#print axioms Exp.natpowExp
#print axioms full_filter_growth
#print axioms filter_cost_growth
end QuantitativeArithmeticEnvelope

namespace QuantitativeArithmeticRetainedGrowingEnvelope
open QuantitativeArithmeticEnvelope
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization QuantitativeArithmeticRetainedFiniteTransport
open QuantitativeArithmeticRetainedGeometricTrace QuantitativeArithmeticRetainedScheduleGrowth

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (P : Parameters A) (hS : ∀p∈S,p.Prime) (hN : 0<N)

theorem normalizer_growth : Exp 6 (fun u => normalizerMatrixHeight A P hS hN (accuracy u)) := by
  let C := Classical.choose (normalized_matrix_bound A P hS hN)
  have hc : 0≤C := zero_le_one.trans (Classical.choose_spec (normalized_matrix_bound A P hS hN)).1
  simpa only [normalizerMatrixHeight,tolerance,iterations,C] using normalizedMatrix_growth A P C hc

/-- The actual matrix height used in the mixed geometric trace theorem
retains the required quadratic double-exponential bound after reparametrizing
accuracy by any fixed polynomial. -/
theorem actual_matrix_growth {a b : ℕ} (u R : ℝ → ℝ) (d : ℝ → ℕ)
    (hu : Poly a u) (hu1 : ∀s,1≤s → 1≤u s)
    (hR : Exp b R) (hR0 : ∀s,1≤s → 0≤R s)
    (hd : Exp 2 (fun s => (d s:ℝ))) :
    DoubleExp (fun s =>
      4*(normalizerMatrixHeight A P hS hN (accuracy (u s)))^2*
        (2*max 1 (8*(R s)^2*(normalizerMatrixHeight A P hS hN (accuracy (u s)))^2))^(d s)) :=
  full_filter_growth _ R d ((normalizer_growth A P hS hN).compPoly hu hu1) hR
    (fun _ _ => normalizerMatrixHeight_nonneg A P hS hN _) hR0 hd

theorem normalizer_mass_growth (e : AsymptoticSectorSigns.Sector N) :
    Exp 2 (fun u => AsymptoticFiniteBranch.expressionBound
      (normalizedExpression A P hS hN (accuracy u) e)) :=
  (normalizedMass_growth A P).mono (fun u _ => normalized_mass A P hS hN (accuracy u) e)

theorem normalizer_length_growth (e : AsymptoticSectorSigns.Sector N) :
    Exp 6 (fun u => ((normalizedExpression A P hS hN (accuracy u) e).length:ℝ)) := by
  apply (normalizedLength_growth A P).mono
  intro u _
  have hh := normalized_length A P hS hN (accuracy u) e
  exact_mod_cast hh

/-- The corresponding coefficient mass and word-count costs satisfy the same
quadratic double-exponential bound. Row inputs are their literal square-sums,
as in quantified_complexity; no trace or spectral input occurs here. -/
theorem actual_complexity_growth {a b : ℕ} (e : AsymptoticSectorSigns.Sector N)
    (u M L : ℝ → ℝ) (d : ℝ → ℕ) (hu : Poly a u) (hu1 : ∀s,1≤s → 1≤u s)
    (hM : Exp b M) (hL : Exp b L) (hM0 : ∀s,1≤s → 0≤M s) (hL0 : ∀s,1≤s → 0≤L s)
    (hd : Exp 2 (fun s => (d s:ℝ))) :
    DoubleExp (fun s =>
      let V := normalizedExpression A P hS hN (accuracy (u s)) e
      AsymptoticFiniteBranch.expressionBound V^2*
        (1+M s*AsymptoticFiniteBranch.expressionBound V^2)^(d s)+
      (V.length:ℝ)^2*(1+L s*(V.length:ℝ)^2)^(d s)) := by
  have hm := (normalizer_mass_growth A P hS hN e).compPoly hu hu1
  have hl := (normalizer_length_growth A P hS hN e).compPoly hu hu1
  exact (filter_cost_growth _ M d hm hM
    (fun _ _ => AsymptoticFiniteBranch.expressionBound_nonneg _) hM0 hd).add
    (filter_cost_growth _ L d hl hL (fun _ _ => Nat.cast_nonneg _) hL0 hd)

#print axioms normalizer_mass_growth
#print axioms normalizer_length_growth
#print axioms actual_complexity_growth
#print axioms normalizer_growth
#print axioms actual_matrix_growth
end QuantitativeArithmeticRetainedGrowingEnvelope
