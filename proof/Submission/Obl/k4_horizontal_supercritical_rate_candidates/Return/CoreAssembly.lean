import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.NumFacts5

/-!
# The single sample under the chosen parameters

`core_of_big`: at one sample, with the fixed exponent relations and the pure large-`N`
inequalities, all numerical hypotheses of `core_sample` hold, hence its conclusion.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem neg_logb_le {N x s : ℝ} (hN : 1 < N) (hx : N ^ (-s) ≤ x) : -Real.logb N x ≤ s := by
  have hN0 : 0 < N := by linarith
  have h := Real.logb_le_logb_of_le hN (Real.rpow_pos_of_pos hN0 _) hx
  rw [Real.logb_rpow hN0 hN.ne'] at h
  linarith

/-- The fixed exponent relations. -/
structure ExpOK (d κ S s₀ s₁ vc M ε Rout η η₁ ηS εS Rcap : ℝ) : Prop where
  d0 : 0 ≤ d
  d1 : d < 1
  κ2 : 1 < 2 * κ
  κ1 : κ ≤ 1
  S0 : 0 < S
  S1 : S ≤ 1
  s₀0 : 0 < s₀
  s₀₁ : s₀ < s₁
  s₁lt : s₁ < 3 * s₀ / 2
  vc0 : 0 < vc
  vcle : vc ≤ (2 * κ - 1) * (s₁ - s₀) / (4 * κ)
  hM : M = 101 * s₀
  Rout : 2 * κ * s₁ + 10 ≤ Rout
  ε0 : 0 < ε
  η0 : 0 ≤ η
  ηη₁ : η = η₁ / 100
  η₁0 : 0 < η₁
  η₁S : η₁ ≤ ηS / 100
  η₁s₀ : η₁ ≤ s₀ / 1000
  η₁1 : η₁ ≤ 1
  η₁m : η₁ * (1 / (1 - d)) ≤ (2 * κ - 1) * (s₁ - s₀) / 2 / 40
  ηS0 : 0 < ηS
  εS0 : 0 ≤ εS
  εSε : 2 * εS ≤ ε
  εS1 : εS ≤ 1
  Rinv : Rcap⁻¹ ≤ s₀
  Rbig : M + 4 * s₀ + s₁ + 10 ≤ Rcap
  RS : 10 / ηS ≤ Rcap

/-- The pure large-`N` inequalities. -/
structure BigN (N d κ S s₀ s₁ vc M Rout η η₁ ηS εS Rcap C₀ : ℝ) : Prop where
  b1 : 54 * C₀ * N ^ (5 * η + 4 * κ * s₀ - M + s₁) ≤ 1
  b2 : 198 * C₀ * N ^ (4 * η + 4 * κ * s₀ - M + s₁) ≤ 1
  b3 : 5 * N ^ (η - s₁) ≤ 1
  b4 : 4 * N ^ (2 * η - 2 * κ * (s₁ - vc) + 2 * κ * s₀) ≤ 1
  b5 : 3 * N ^ (3 * η - κ * (300 * s₀) + κ * (s₁ - vc) + (M + 4 * s₀)) ≤ 1
  b6 : 68 * N ^ (7 * η - κ * (300 * s₀) + 2 * κ * s₀ + (s₁ - s₀)) ≤ 1
  b7 : 6426 * N ^ (5 * η - η₁) ≤ 1
  b8 : 2 * N ^ (η - ηS) ≤ 1
  b9 : 24 * N ^ (5 * η - (M + 4 * s₀) + 2 * κ * s₀ + (s₁ - s₀)) ≤ 1
  b10 : 2 * N ^ (-s₀) ≤ 1
  b11 : 1584 * N ^ (4 * η + S / Rcap - ηS) ≤ 1
  b12 : 112 * (10 ^ 9 : ℝ) ^ (1 / (1 - d)) * N ^ ((15 * η + 3 * η₁) * (1 / (1 - d)) +
    2 * η - s₀ + 2 * κ * s₀ - 2 * κ * (s₁ - vc) + s₁) ≤ 1
  b13 : 8 * N ^ (2 * η - 2 * κ * (s₁ - vc)) ≤ 1
  b14 : 24 * N ^ (6 * η - s₀ + 2 * κ * s₀ - 2 * κ * (s₁ - vc) + s₁) ≤ 1
  b15 : 22 * N ^ (6 * η - (s₁ - vc)) ≤ 1
  b16 : 11258676 * N ^ (11 * η + 2 * η₁ - ηS) ≤ 1
  b17 : 21 * N ^ (η - Rout) ≤ 1
  b18 : 72 * N ^ (5 * η + 2 * κ * s₀ - s₀ - Rout) ≤ 1
  b19 : 675 * C₀ * N ^ (4 * η + 5 * εS + 2 * κ * (s₁ - vc) - s₀ - Rout) ≤ 1

/-- A constant times a negative power of a large base is at most one. -/
theorem big_of_neg {C e : ℝ} (hC : 0 ≤ C) (he : e < 0) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → C * N ^ e ≤ 1 := by
  obtain ⟨N₀, h1, h2⟩ := const_mul_rpow_le_one hC (show 0 < -e by linarith)
  exact ⟨N₀, h1, fun N hN => by simpa using h2 N hN⟩

/-- The pure large-`N` inequalities hold eventually. -/
theorem exists_bigN {d κ S s₀ s₁ vc M ε Rout η η₁ ηS εS Rcap C₀ : ℝ}
    (hE : ExpOK d κ S s₀ s₁ vc M ε Rout η η₁ ηS εS Rcap) (hC₀ : 0 < C₀) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → BigN N d κ S s₀ s₁ vc M Rout η η₁ ηS εS Rcap C₀ := by
  obtain ⟨d0, d1, κ2, κ1, S0, S1, s₀0, s₀₁, s₁lt, vc0, vcle, hM, hRout, ε0, η0, ηη₁, η₁0, η₁S,
    η₁s₀, η₁1, η₁m, ηS0, εS0, εSε, εS1, Rinv, Rbig, RS⟩ := hE
  have hκ0 : 0 < κ := by linarith
  have hp1 : 1 ≤ 1 / (1 - d) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hp0 : 0 < 1 / (1 - d) := by linarith
  set p := 1 / (1 - d) with hp
  set mg := (2 * κ - 1) * (s₁ - s₀) / 2 with hmg
  have hs10 : 0 < s₁ - s₀ := by linarith
  have hk : 0 < 2 * κ - 1 := by linarith
  have hmg0 : 0 < mg := by rw [hmg]; positivity
  have hvcs : vc ≤ (s₁ - s₀) / 4 := by
    have h4κ : 0 < 4 * κ := by linarith
    have h := (le_div_iff₀ h4κ).mp vcle
    have h2 : (2 * κ - 1) * (s₁ - s₀) ≤ κ * (s₁ - s₀) := by nlinarith only [κ1, hs10]
    by_contra hc
    push Not at hc
    have h3 : 0 < κ * (4 * vc - (s₁ - s₀)) := mul_pos hκ0 (by linarith only [hc])
    nlinarith only [h, h2, h3]
  have hgap : mg ≤ 2 * κ * (s₁ - vc) - 2 * κ * s₀ - (s₁ - s₀) := by
    have h4κ : 0 < 4 * κ := by linarith
    have h := (le_div_iff₀ h4κ).mp vcle
    rw [hmg]; nlinarith only [h]
  have hmgs : mg ≤ (s₁ - s₀) / 2 := by
    rw [hmg]; nlinarith only [κ1, hs10]
  have hη₁p : η₁ * p ≤ mg / 40 := η₁m
  have hη₁mg : η₁ ≤ mg / 40 := le_trans (le_mul_of_one_le_right η₁0.le hp1) hη₁p
  have hηs₀ : η ≤ s₀ / 100000 := by rw [ηη₁]; linarith only [η₁s₀]
  have hηS : η ≤ ηS / 10000 := by rw [ηη₁]; linarith only [η₁S]
  have hηd : η ≤ (s₁ - s₀) / 8000 := by rw [ηη₁]; linarith only [hη₁mg, hmgs]
  have hκs₀ : κ * s₀ ≤ s₀ := by nlinarith only [κ1, s₀0]
  have hκs₁ : κ * s₀ ≤ κ * s₁ := by nlinarith only [hκ0, s₀₁]
  have hκvc : 0 ≤ κ * vc := by nlinarith only [hκ0, vc0]
  have hκX : ∀ X : ℝ, 0 ≤ X → X / 2 ≤ κ * X := fun X hX => by nlinarith only [κ2, hX]
  have hRS : S / Rcap ≤ ηS / 10 := by
    have hR0 : 0 < Rcap := lt_of_lt_of_le (by positivity) RS
    rw [div_le_iff₀ hR0]
    have h1 : 10 / ηS * ηS = 10 := by field_simp
    have h2 : 10 ≤ Rcap * ηS := by nlinarith only [RS, h1, ηS0]
    nlinarith only [h2, S1, S0, ηS0]
  -- the nineteen exponents are negative
  have e1 : 5 * η + 4 * κ * s₀ - M + s₁ < 0 := by
    rw [hM]; linarith only [hκs₀, hηs₀, s₁lt, s₀0]
  have e2 : 4 * η + 4 * κ * s₀ - M + s₁ < 0 := by
    rw [hM]; linarith only [hκs₀, hηs₀, s₁lt, s₀0]
  have e3 : η - s₁ < 0 := by linarith only [hηs₀, s₀₁, s₀0]
  have e4 : 2 * η - 2 * κ * (s₁ - vc) + 2 * κ * s₀ < 0 := by
    have h := hκX (s₁ - vc - s₀) (by linarith only [hvcs, hs10])
    nlinarith only [h, hηd, hvcs, hs10]
  have e5 : 3 * η - κ * (300 * s₀) + κ * (s₁ - vc) + (M + 4 * s₀) < 0 := by
    have h := hκX (300 * s₀ - (s₁ - vc)) (by linarith only [s₁lt, vc0, s₀0])
    rw [hM]; nlinarith only [h, hηs₀, s₁lt, vc0, s₀0]
  have e6 : 7 * η - κ * (300 * s₀) + 2 * κ * s₀ + (s₁ - s₀) < 0 := by
    have h := hκX (298 * s₀) (by linarith only [s₀0])
    nlinarith only [h, hηs₀, s₁lt, s₀0]
  have e7 : 5 * η - η₁ < 0 := by rw [ηη₁]; linarith only [η₁0]
  have e8 : η - ηS < 0 := by linarith only [hηS, ηS0]
  have e9 : 5 * η - (M + 4 * s₀) + 2 * κ * s₀ + (s₁ - s₀) < 0 := by
    rw [hM]; linarith only [hκs₀, hηs₀, s₁lt, s₀0]
  have e10 : -s₀ < 0 := by linarith only [s₀0]
  have e11 : 4 * η + S / Rcap - ηS < 0 := by linarith only [hηS, hRS, ηS0]
  have e12 : (15 * η + 3 * η₁) * p + 2 * η - s₀ + 2 * κ * s₀ - 2 * κ * (s₁ - vc) + s₁ < 0 := by
    have h2 : (15 * η + 3 * η₁) * p = 3.15 * (η₁ * p) := by rw [ηη₁]; ring
    have h3 : 2 * η ≤ 0.02 * (η₁ * p) := by
      rw [ηη₁]; have := le_mul_of_one_le_right η₁0.le hp1; linarith only [this]
    rw [h2]; linarith only [h3, hη₁p, hgap, hmg0]
  have e13 : 2 * η - 2 * κ * (s₁ - vc) < 0 := by
    have h := hκX (s₁ - vc) (by linarith only [hvcs, hs10, s₀0])
    linarith only [h, hηs₀, hvcs, hs10, s₀0]
  have e14 : 6 * η - s₀ + 2 * κ * s₀ - 2 * κ * (s₁ - vc) + s₁ < 0 := by
    rw [ηη₁]; linarith only [hη₁mg, hgap, hmg0]
  have e15 : 6 * η - (s₁ - vc) < 0 := by linarith only [hηs₀, hvcs, hs10, s₀0]
  have e16 : 11 * η + 2 * η₁ - ηS < 0 := by rw [ηη₁]; linarith only [η₁S, ηS0]
  have e17 : η - Rout < 0 := by
    have h2 := hκX s₁ (by linarith only [s₀₁, s₀0])
    linarith only [h2, hRout, hηs₀, s₀0, s₀₁]
  have e18 : 5 * η + 2 * κ * s₀ - s₀ - Rout < 0 := by
    linarith only [hκs₁, hRout, hηs₀, s₀0]
  have e19 : 4 * η + 5 * εS + 2 * κ * (s₁ - vc) - s₀ - Rout < 0 := by
    have : κ * (s₁ - vc) = κ * s₁ - κ * vc := by ring
    rw [show 2 * κ * (s₁ - vc) = 2 * (κ * (s₁ - vc)) by ring, this]
    linarith only [hκvc, hRout, hηs₀, s₀0, εS1]
  obtain ⟨N1, h1a, h1b⟩ := big_of_neg (by positivity : (0:ℝ) ≤ 54 * C₀) e1
  obtain ⟨N2, h2a, h2b⟩ := big_of_neg (by positivity : (0:ℝ) ≤ 198 * C₀) e2
  obtain ⟨N3, h3a, h3b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 5) e3
  obtain ⟨N4, h4a, h4b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 4) e4
  obtain ⟨N5, h5a, h5b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 3) e5
  obtain ⟨N6, h6a, h6b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 68) e6
  obtain ⟨N7, h7a, h7b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 6426) e7
  obtain ⟨N8, h8a, h8b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 2) e8
  obtain ⟨N9, h9a, h9b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 24) e9
  obtain ⟨N10, h10a, h10b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 2) e10
  obtain ⟨N11, h11a, h11b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 1584) e11
  obtain ⟨N12, h12a, h12b⟩ := big_of_neg (by positivity : (0:ℝ) ≤ 112 * (10 ^ 9 : ℝ) ^ p) e12
  obtain ⟨N13, h13a, h13b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 8) e13
  obtain ⟨N14, h14a, h14b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 24) e14
  obtain ⟨N15, h15a, h15b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 22) e15
  obtain ⟨N16, h16a, h16b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 11258676) e16
  obtain ⟨N17, h17a, h17b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 21) e17
  obtain ⟨N18, h18a, h18b⟩ := big_of_neg (by norm_num : (0:ℝ) ≤ 72) e18
  obtain ⟨N19, h19a, h19b⟩ := big_of_neg (by positivity : (0:ℝ) ≤ 675 * C₀) e19
  set N₀ := max 2 (max N1 (max N2 (max N3 (max N4 (max N5 (max N6 (max N7 (max N8 (max N9
    (max N10 (max N11 (max N12 (max N13 (max N14 (max N15 (max N16 (max N17 (max N18
      N19)))))))))))))))))) with hN₀
  refine ⟨N₀, le_max_left _ _, fun N hN => ?_⟩
  have g : ∀ {a b : ℝ}, a ≤ b → b ≤ N → a ≤ N := fun h1 h2 => h1.trans h2
  simp only [hN₀, max_le_iff] at hN
  obtain ⟨-, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18,
    n19⟩ := hN
  exact ⟨h1b N n1, h2b N n2, h3b N n3, h4b N n4, h5b N n5, h6b N n6, h7b N n7, h8b N n8,
    h9b N n9, h10b N n10, h11b N n11, h12b N n12, h13b N n13, h14b N n14, h15b N n15,
    h16b N n16, h17b N n17, h18b N n18, h19b N n19⟩

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
