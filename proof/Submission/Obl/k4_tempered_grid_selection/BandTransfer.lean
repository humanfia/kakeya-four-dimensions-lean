import Submission.Obl.k4_tempered_grid_selection.DensityTransfer
import Submission.Obl.k4_tempered_grid_selection.Exponents

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set
open scoped ENNReal

lemma power_band_absorb_factors {n a δ τ : ℝ} (hn : 1 ≤ n)
    (hδ : δ ≤ τ / 4) (hτ : 0 ≤ τ) (hfactor : 2 ≤ n ^ (τ / 4)) :
    ENNReal.ofReal (n ^ (-a - τ)) ≤
      ENNReal.ofReal (n ^ (-(τ / 4))) *
        ((2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (n ^ (-a - δ))) ∧
    2 * ENNReal.ofReal (n ^ (-a + δ)) ≤ ENNReal.ofReal (n ^ (-a + τ)) := by
  have hn0 : 0 < n := by linarith
  have hlo : n ^ (-a - τ) ≤ n ^ (-(τ / 4)) * (1 / 2 * n ^ (-a - δ)) := by
    have hmul : 2 * n ^ (-a - τ) ≤ n ^ (-(τ / 4)) * n ^ (-a - δ) := by
      calc
        2 * n ^ (-a - τ) ≤ n ^ (τ / 4) * n ^ (-a - τ) :=
          mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hn0.le _)
        _ = n ^ (τ / 4 + (-a - τ)) := (Real.rpow_add hn0 _ _).symm
        _ ≤ n ^ (-(τ / 4) + (-a - δ)) :=
          Real.rpow_le_rpow_of_exponent_le hn (by linarith)
        _ = n ^ (-(τ / 4)) * n ^ (-a - δ) := Real.rpow_add hn0 _ _
    nlinarith
  have hhi : 2 * n ^ (-a + δ) ≤ n ^ (-a + τ) := by
    calc
      2 * n ^ (-a + δ) ≤ n ^ (τ / 4) * n ^ (-a + δ) :=
        mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hn0.le _)
      _ = n ^ (τ / 4 + (-a + δ)) := (Real.rpow_add hn0 _ _).symm
      _ ≤ n ^ (-a + τ) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  constructor
  · have h := ENNReal.ofReal_le_ofReal hlo
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hn0.le _),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
    simpa only [hhalf] using h
  · simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hhi

/-- The factor-two finite-label approximation and its power-small exceptional
set transfer to an arbitrary retained density version. -/
theorem approximation_band_transfer {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (ρ : Measure Y) [SigmaFinite ρ] (μ μ₀ : Measure Ω) (hμ : μ₀ ≤ μ)
    (hmass : μ univ ≤ 1) (obs : Ω → Y) (hobs : Measurable obs)
    (G G₀ : Y → ℝ≥0∞) (hG : Measurable G) (hG₀ : Measurable G₀)
    (hlaw : μ.map obs = ρ.withDensity G)
    (hlaw₀ : μ₀.map obs = ρ.withDensity G₀)
    (n C a δ τ : ℝ) (hn : 1 < n) (hτ : 0 < τ)
    (hδ : δ ≤ τ / 4) (hfactor : 2 ≤ n ^ (τ / 4))
    (v : Ω → ℝ) (hv : ∀ p, 0 ≤ v p ∧ v p ≤ n ^ C)
    (hfit : ∀ᵐ p ∂μ₀, |boundedExponent C n (v p) - a| ≤ δ)
    (err : ℝ≥0∞)
    (happrox : μ {p | G (obs p) < (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (v p) ∨
        2 * ENNReal.ofReal (v p) < G (obs p) ∨
        ENNReal.ofReal (v p) < ENNReal.ofReal (n ^ (-C))} ≤ err) :
    μ₀ {p | G₀ (obs p) < ENNReal.ofReal (n ^ (-a - τ)) ∨
      ENNReal.ofReal (n ^ (-a + τ)) < G₀ (obs p)} ≤
      err + ENNReal.ofReal (n ^ (-(τ / 4))) := by
  let B := {p | G (obs p) < (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (v p) ∨
    2 * ENNReal.ofReal (v p) < G (obs p) ∨
    ENNReal.ofReal (v p) < ENNReal.ofReal (n ^ (-C))}
  let lower : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (n ^ (-a - δ))
  let upper : ℝ≥0∞ := 2 * ENNReal.ofReal (n ^ (-a + δ))
  let ε := ENNReal.ofReal (n ^ (-(τ / 4)))
  have hband : ∀ᵐ p ∂μ₀, p ∉ B → lower ≤ G (obs p) ∧ G (obs p) ≤ upper := by
    filter_upwards [hfit] with p hp hpB
    have hgood := not_or.mp hpB
    have hgood' := not_or.mp hgood.2
    have hvlo : n ^ (-C) ≤ v p := by
      exact (ENNReal.ofReal_le_ofReal_iff (hv p).1).mp (le_of_not_gt hgood'.2)
    have hvpos : 0 < v p := (Real.rpow_pos_of_pos (by linarith : 0 < n) _).trans_le hvlo
    rw [boundedExponent_eq hn hvlo (hv p).2] at hp
    obtain ⟨hlo, hhi⟩ := power_band_of_exponent_fit hn hvpos hp
    exact ⟨(mul_le_mul_right (ENNReal.ofReal_le_ofReal hlo) (2 : ℝ≥0∞)⁻¹).trans
        (le_of_not_gt hgood.1),
      (le_of_not_gt hgood'.1).trans
        (mul_le_mul_right (ENNReal.ofReal_le_ofReal hhi) 2)⟩
  obtain ⟨htlo, hthi⟩ := power_band_absorb_factors hn.le hδ hτ.le hfactor
  calc
    _ ≤ μ₀ {p | G₀ (obs p) < ε * lower ∨ upper < G₀ (obs p)} := by
      apply measure_mono
      intro p hp
      exact hp.elim (fun h => Or.inl (h.trans_le htlo))
        (fun h => Or.inr (hthi.trans_lt h))
    _ ≤ μ B + ε * μ univ :=
      observed_density_band_bound ρ μ μ₀ hμ obs hobs G G₀ hG hG₀ hlaw hlaw₀
        B lower upper ε hband
    _ ≤ err + ε := add_le_add happrox (by simpa only [mul_one] using mul_le_mul_right hmass ε)

end Submission.Obl.k4_tempered_grid_selection
