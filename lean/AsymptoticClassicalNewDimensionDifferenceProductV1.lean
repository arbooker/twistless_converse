module

public import AsymptoticClassicalNewDimensionTwoArithmeticV1
public import AsymptoticClassicalNewDimensionPrimesV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace AsymptoticClassicalDimension

/-- Every simple-prime second difference contributes the local factor (p-1)/(p+1). -/
theorem simpleDifference_product (b : ℕ) (C : ℕ → ℝ)
    (hscale : ∀ M p, 0 < M → b ∣ M → p.Prime → ¬ p ∣ M →
      C (p * M) = ((p : ℝ) + 1) * C M)
    (ps : List ℕ) (N : ℕ) (hN : 0 < N) (hb : b ∣ N)
    (hps : SimplePrimesAt ps N) (hbp : ∀ p ∈ ps, p.Coprime b) :
    simpleDifference ps C N = C N * (ps.map (fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) + 1))).prod := by
  induction ps generalizing N with
  | nil => simp [simpleDifference]
  | cons p ps ih =>
    have hp := hps.2 p List.mem_cons_self
    have hM : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hN hp.2.1) hp.1.pos
    have hbM := base_dvd_div hb hp.2.1 (hbp p List.mem_cons_self)
    have htail : ∀ q ∈ ps, q.Coprime b := fun q hq => hbp q (List.mem_cons_of_mem p hq)
    have hs := hscale (N / p) p hM hbM hp.1 (hp.1.coprime_iff_not_dvd.mp hp.2.2)
    rw [Nat.mul_div_cancel' hp.2.1] at hs
    rw [simpleDifference, ih N hN hb hps.tail htail,
      ih (N / p) hM hbM (hps.tail_div hN) htail, List.map_cons, List.prod_cons, hs]
    have hd : (p : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem fullDifference_product (ps : List ℕ) (N : ℕ) (hN : 0 < N)
    (hps : SimplePrimesAt ps N) :
    simpleDifference ps fullLeading N =
      fullLeading N * (ps.map (fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) + 1))).prod :=
  simpleDifference_product 1 fullLeading
    (fun M p hM _ hp hpM => fullLeading_mul_prime M p hM hp hpM)
    ps N hN (one_dvd N) hps (fun _ _ => Nat.coprime_one_right _)

theorem twoDifference_product (ps : List ℕ) (N : ℕ) (hN : 0 < N) (h4 : 4 ∣ N)
    (hps : SimplePrimesAt ps N) (hp4 : ∀ p ∈ ps, p.Coprime 4) :
    simpleDifference ps twoLeading N =
      twoLeading N * (ps.map (fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) + 1))).prod :=
  simpleDifference_product 4 twoLeading
    (fun M p hM h4 hp hpM => twoLeading_mul_prime M p hM h4 hp hpM)
    ps N hN h4 hps hp4

#print axioms simpleDifference_product
#print axioms fullDifference_product
#print axioms twoDifference_product
end AsymptoticClassicalDimension
