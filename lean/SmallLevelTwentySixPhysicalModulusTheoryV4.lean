module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SmallLevelFourPrimeRatesV1

/-! Consolidated chapter: SmallLevelTwentySixPhysicalModulus. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixPhysicalModulusV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPhysicalModulus

lemma cpow_norm_pow (p n : ℕ) (hp : 0<p) (h : ℂ) :
    ‖(p:ℂ)^h‖^n=((p:ℝ)^n)^h.re := by
  rw [Complex.norm_natCast_cpow_of_pos hp]
  rw [←Real.rpow_mul_natCast (Nat.cast_nonneg p),mul_comm,
    Real.rpow_natCast_mul (Nat.cast_nonneg p)]

/-- The physical squared moduli obey cubic/quartic bounds. This avoids any
numerical approximation to log9/log2 in the finite root exclusion. -/
theorem physical_bounds (h : ℂ) :
    (1≤‖(2:ℂ)^h‖^2 ∧ (‖(2:ℂ)^h‖^2)^3≤‖(9:ℂ)^h‖^2 ∧
      ‖(9:ℂ)^h‖^2≤(‖(2:ℂ)^h‖^2)^4) ∨
    (‖(2:ℂ)^h‖^2≤1 ∧ (‖(2:ℂ)^h‖^2)^4≤‖(9:ℂ)^h‖^2 ∧
      ‖(9:ℂ)^h‖^2≤(‖(2:ℂ)^h‖^2)^3) := by
  have hx := cpow_norm_pow 2 2 (by decide) h
  have hy := cpow_norm_pow 9 2 (by decide) h
  have h3 := cpow_norm_pow 2 6 (by decide) h
  have h4 := cpow_norm_pow 2 8 (by decide) h
  norm_num only [Nat.cast_ofNat,show (2:ℝ)^2=4 by norm_num] at hx
  norm_num only [Nat.cast_ofNat,show (9:ℝ)^2=81 by norm_num] at hy
  norm_num only [Nat.cast_ofNat,show (2:ℝ)^6=64 by norm_num] at h3
  norm_num only [Nat.cast_ofNat,show (2:ℝ)^8=256 by norm_num] at h4
  have h3' : (‖(2:ℂ)^h‖^2)^3=(64:ℝ)^h.re := by
    rw [←pow_mul]; exact h3
  have h4' : (‖(2:ℂ)^h‖^2)^4=(256:ℝ)^h.re := by
    rw [←pow_mul]; exact h4
  simp only [h3',h4']
  simp only [hx,hy]
  rcases le_total 0 h.re with hh|hh
  · exact Or.inl ⟨Real.one_le_rpow (by norm_num) hh,
      Real.rpow_le_rpow (x:=64) (y:=81) (by norm_num) (by norm_num) hh,
      Real.rpow_le_rpow (x:=81) (y:=256) (by norm_num) (by norm_num) hh⟩
  · exact Or.inr ⟨Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hh,
      Real.rpow_le_rpow_of_nonpos (x:=81) (y:=256) (by norm_num) (by norm_num) hh,
      Real.rpow_le_rpow_of_nonpos (x:=64) (y:=81) (by norm_num) (by norm_num) hh⟩

#print axioms physical_bounds
end SmallLevelTwentySixPhysicalModulus
end
end

/-! ## SmallLevelTwentySixCoarseIntervalsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixPhysicalModulus

/-- A finite interval certificate; root coverage is a separate obligation. -/
def IntervalExcluded (a b c d : ℝ) : Prop :=
  0≤a ∧ ((1<a ∧ (d<a^3 ∨ b^4<c)) ∨ (b<1 ∧ (d<a^4 ∨ b^3<c)))

theorem interval_excludes_physical (a b c d : ℝ) (hex : IntervalExcluded a b c d)
    (h : ℂ) (hx : a≤‖(2:ℂ)^h‖^2 ∧ ‖(2:ℂ)^h‖^2≤b)
    (hy : c≤‖(9:ℂ)^h‖^2 ∧ ‖(9:ℂ)^h‖^2≤d) : False := by
  have h0 : 0≤‖(2:ℂ)^h‖^2 := sq_nonneg _
  have h3l : a^3≤(‖(2:ℂ)^h‖^2)^3 := by gcongr; exact hex.1; exact hx.1
  have h4l : a^4≤(‖(2:ℂ)^h‖^2)^4 := by gcongr; exact hex.1; exact hx.1
  have h3u : (‖(2:ℂ)^h‖^2)^3≤b^3 := by gcongr; exact hx.2
  have h4u : (‖(2:ℂ)^h‖^2)^4≤b^4 := by gcongr; exact hx.2
  rcases physical_bounds h with ⟨hp,hlo,hhi⟩|⟨hp,hlo,hhi⟩ <;>
    rcases hex.2 with ⟨ha,hlt|hlt⟩|⟨hb,hlt|hlt⟩ <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem saved_interval_0 : IntervalExcluded (3631241001503/1000000000000:ℝ) (113476281297/31250000000:ℝ) (58794885191217/200000000000:ℝ) (146987212978043/500000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_1 : IntervalExcluded (25183988739/200000000000:ℝ) (7869996481/62500000000:ℝ) (377477496401/10000000000:ℝ) (37747749640101/1000000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_2 : IntervalExcluded (280849597109/1000000000000:ℝ) (28084959711/100000000000:ℝ) (4837227398653603/200000000000:ℝ) (1511633562079251/62500000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_3 : IntervalExcluded (794558216901/1000000000000:ℝ) (397279108451/500000000000:ℝ) (2267936710854461617/1000000000000:ℝ) (1133968355427230809/500000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_4 : IntervalExcluded (683982314809/500000000000:ℝ) (1367964629619/1000000000000:ℝ) (486574225111981/250000000000:ℝ) (77851876017917/40000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_5 : IntervalExcluded (6080115080697/500000000000:ℝ) (2432046032279/200000000000:ℝ) (340021501958913/200000000000:ℝ) (850053754897283/500000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_6 : IntervalExcluded (12219045031817/500000000000:ℝ) (4887618012727/200000000000:ℝ) (60275810674891/1000000000000:ℝ) (15068952668723/250000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_7 : IntervalExcluded (545135102217/62500000000:ℝ) (8722161635473/1000000000000:ℝ) (21593694527873/100000000000:ℝ) (215936945278731/1000000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_8 : IntervalExcluded (545135102217/62500000000:ℝ) (8722161635473/1000000000000:ℝ) (21593694527873/100000000000:ℝ) (215936945278731/1000000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_9 : IntervalExcluded (1643821430483/250000000000:ℝ) (6575285721933/1000000000000:ℝ) (32570539421761/250000000000:ℝ) (26056431537409/200000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_10 : IntervalExcluded (1643821430483/250000000000:ℝ) (6575285721933/1000000000000:ℝ) (32570539421761/250000000000:ℝ) (26056431537409/200000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_11 : IntervalExcluded (409019952261/62500000000:ℝ) (6544319236177/1000000000000:ℝ) (8233595151541/1000000000000:ℝ) (4116797575771/500000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_12 : IntervalExcluded (409019952261/62500000000:ℝ) (6544319236177/1000000000000:ℝ) (8233595151541/1000000000000:ℝ) (4116797575771/500000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_13 : IntervalExcluded (1986239208909/200000000000:ℝ) (4965598022273/500000000000:ℝ) (7958575633079/125000000000:ℝ) (63668605064633/1000000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_14 : IntervalExcluded (1986239208909/200000000000:ℝ) (4965598022273/500000000000:ℝ) (7958575633079/125000000000:ℝ) (63668605064633/1000000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_15 : IntervalExcluded (62815424389041/1000000000000:ℝ) (31407712194521/500000000000:ℝ) (205422902318471/1000000000000:ℝ) (25677862789809/125000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_16 : IntervalExcluded (62815424389041/1000000000000:ℝ) (31407712194521/500000000000:ℝ) (205422902318471/1000000000000:ℝ) (25677862789809/125000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_17 : IntervalExcluded (31912913259949/250000000000:ℝ) (127651653039797/1000000000000:ℝ) (111120190088207/500000000000:ℝ) (44448076035283/200000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_18 : IntervalExcluded (31912913259949/250000000000:ℝ) (127651653039797/1000000000000:ℝ) (111120190088207/500000000000:ℝ) (44448076035283/200000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_19 : IntervalExcluded (17693555558727/125000000000:ℝ) (141548444469817/1000000000000:ℝ) (291227042483463/500000000000:ℝ) (582454084966927/1000000000000:ℝ) := by
  norm_num [IntervalExcluded]

theorem saved_interval_20 : IntervalExcluded (17693555558727/125000000000:ℝ) (141548444469817/1000000000000:ℝ) (291227042483463/500000000000:ℝ) (582454084966927/1000000000000:ℝ) := by
  norm_num [IntervalExcluded]

#print axioms interval_excludes_physical
#print axioms saved_interval_20
end SmallLevelTwentySixPhysicalModulus
end
end

/-! ## SmallLevelTwentySixPhysicalSharpModulusV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentySixPhysicalModulus

/-- Integer comparisons of the bases give exact power comparisons of the
physical norms, with the direction reversed on the left half-plane. -/
theorem physical_power_comparison (p q a b : ℕ) (hp : 0<p) (hq : 0<q)
    (hpq : (p:ℝ)^a≤(q:ℝ)^b) (h : ℂ) :
    (0≤h.re → ‖(p:ℂ)^h‖^a≤‖(q:ℂ)^h‖^b) ∧
    (h.re≤0 → ‖(q:ℂ)^h‖^b≤‖(p:ℂ)^h‖^a) := by
  rw [cpow_norm_pow p a hp h,cpow_norm_pow q b hq h]
  constructor
  · intro hh
    exact Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg p) a) hpq hh
  · intro hh
    exact Real.rpow_le_rpow_of_nonpos
      (pow_pos (by exact_mod_cast hp) a) hpq hh

/-- Exact rational-exponent enclosure 19/6 < log(9)/log(2) < 127/40,
expressed entirely as integer-power norm inequalities. No numerical
approximation to a logarithm is used. -/
theorem physical_sharp_bounds (h : ℂ) :
    (0≤h.re ∧ ‖(2:ℂ)^h‖^19≤‖(9:ℂ)^h‖^6 ∧
      ‖(9:ℂ)^h‖^40≤‖(2:ℂ)^h‖^127) ∨
    (h.re≤0 ∧ ‖(9:ℂ)^h‖^6≤‖(2:ℂ)^h‖^19 ∧
      ‖(2:ℂ)^h‖^127≤‖(9:ℂ)^h‖^40) := by
  have hlo:=physical_power_comparison 2 9 19 6 (by decide) (by decide)
    (by norm_num) h
  have hhi:=physical_power_comparison 9 2 40 127 (by decide) (by decide)
    (by norm_num) h
  rcases le_total 0 h.re with hh|hh
  · exact Or.inl ⟨hh,hlo.1 hh,hhi.1 hh⟩
  · exact Or.inr ⟨hh,hlo.2 hh,hhi.2 hh⟩

#print axioms physical_power_comparison
#print axioms physical_sharp_bounds
end SmallLevelTwentySixPhysicalModulus
end
end

/-! ## SmallLevelTwentySixSharpIntervalsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixPhysicalModulus

theorem physical_sharp_squared_bounds (h : ℂ) :
    (1≤‖(2:ℂ)^h‖^2 ∧ (‖(2:ℂ)^h‖^2)^19≤(‖(9:ℂ)^h‖^2)^6 ∧
      (‖(9:ℂ)^h‖^2)^40≤(‖(2:ℂ)^h‖^2)^127) ∨
    (‖(2:ℂ)^h‖^2≤1 ∧ (‖(9:ℂ)^h‖^2)^6≤(‖(2:ℂ)^h‖^2)^19 ∧
      (‖(2:ℂ)^h‖^2)^127≤(‖(9:ℂ)^h‖^2)^40) := by
  have hlo:=physical_power_comparison 2 9 38 12 (by decide) (by decide)
    (by norm_num) h
  have hhi:=physical_power_comparison 9 2 80 254 (by decide) (by decide)
    (by norm_num) h
  have hx : ‖(2:ℂ)^h‖^2=(4:ℝ)^h.re := by
    simpa only [Nat.cast_ofNat,show (2:ℝ)^2=4 by norm_num] using cpow_norm_pow 2 2 (by decide) h
  rcases le_total 0 h.re with hh|hh
  · refine Or.inl ⟨?_,?_,?_⟩
    · rw [hx]; exact Real.one_le_rpow (by norm_num) hh
    · simpa only [←pow_mul,Nat.cast_ofNat] using hlo.1 hh
    · simpa only [←pow_mul,Nat.cast_ofNat] using hhi.1 hh
  · refine Or.inr ⟨?_,?_,?_⟩
    · rw [hx]; exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hh
    · simpa only [←pow_mul,Nat.cast_ofNat] using hlo.2 hh
    · simpa only [←pow_mul,Nat.cast_ofNat] using hhi.2 hh

def SharpIntervalExcluded (a b c d : ℝ) : Prop :=
  0≤a ∧ 0≤c ∧ ((1<a ∧ (d^6<a^19 ∨ b^127<c^40)) ∨
    (b<1 ∧ (d^40<a^127 ∨ b^19<c^6)))

theorem sharp_interval_excludes_physical (a b c d : ℝ)
    (hex : SharpIntervalExcluded a b c d) (h : ℂ)
    (hx : a≤‖(2:ℂ)^h‖^2 ∧ ‖(2:ℂ)^h‖^2≤b)
    (hy : c≤‖(9:ℂ)^h‖^2 ∧ ‖(9:ℂ)^h‖^2≤d) : False := by
  have h19l : a^19≤(‖(2:ℂ)^h‖^2)^19 := by gcongr; exact hex.1; exact hx.1
  have h127l : a^127≤(‖(2:ℂ)^h‖^2)^127 := by gcongr; exact hex.1; exact hx.1
  have h19u : (‖(2:ℂ)^h‖^2)^19≤b^19 := by gcongr; exact hx.2
  have h127u : (‖(2:ℂ)^h‖^2)^127≤b^127 := by gcongr; exact hx.2
  have h6l : c^6≤(‖(9:ℂ)^h‖^2)^6 := by gcongr; exact hex.2.1; exact hy.1
  have h40l : c^40≤(‖(9:ℂ)^h‖^2)^40 := by gcongr; exact hex.2.1; exact hy.1
  have h6u : (‖(9:ℂ)^h‖^2)^6≤d^6 := by gcongr; exact hy.2
  have h40u : (‖(9:ℂ)^h‖^2)^40≤d^40 := by gcongr; exact hy.2
  rcases physical_sharp_squared_bounds h with ⟨hp,hlo,hhi⟩|⟨hp,hlo,hhi⟩ <;>
    rcases hex.2.2 with ⟨ha,hlt|hlt⟩|⟨hb,hlt|hlt⟩ <;> linarith [hx.1,hx.2]

#print axioms physical_sharp_squared_bounds
#print axioms sharp_interval_excludes_physical
end SmallLevelTwentySixPhysicalModulus
end
end
