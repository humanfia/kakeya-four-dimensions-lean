import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Model

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- A physical cap passes to a normalized source through the original full
positive reference factor. -/
theorem cap_of_scaled_map_domination
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (law : Measure Ω) (μ : Measure Y) (f : Ω → Y) (hf : Measurable f)
    {W C : ℝ} (hW : 0 < W) (hC : 0 ≤ C)
    (hdom : ENNReal.ofReal W • law.map f ≤ μ)
    (E : Set Y) (hE : MeasurableSet E) (weight : ℝ≥0∞)
    (hcap : μ E ≤ ENNReal.ofReal C * weight) :
    law (f ⁻¹' E) ≤ ENNReal.ofReal (C / W) * weight := by
  have hscale := hdom E
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf hE] at hscale
  calc
    _ = (ENNReal.ofReal W)⁻¹ * (ENNReal.ofReal W * law (f ⁻¹' E)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal W)⁻¹ * (ENNReal.ofReal C * weight) :=
      mul_le_mul' le_rfl (hscale.trans hcap)
    _ = ENNReal.ofReal (C / W) * weight := by
      rw [ENNReal.ofReal_div_of_pos hW, div_eq_mul_inv]
      ring

theorem ae_of_scaled_map_domination
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (law : Measure Ω) (μ : Measure Y) (f : Ω → Y) (hf : Measurable f)
    {W : ℝ} (hW : 0 < W) (hdom : ENNReal.ofReal W • law.map f ≤ μ)
    {P : Y → Prop} (hP : ∀ᵐ p ∂μ, P p) : ∀ᵐ p ∂law, P (f p) := by
  have hscale := ae_mono hdom hP
  have hmap := (Measure.ae_ennreal_smul_measure_iff
    (by positivity : ENNReal.ofReal W ≠ 0)).mp hscale
  exact ae_of_ae_map hf.aemeasurable hmap

theorem fine_cell_cap_of_scaled_map_domination
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (law : Measure Ω) (μ : Measure Y) (f : Ω → Y) (hf : Measurable f)
    (point : Y → Fin 3 → ℝ) (hp : Measurable point)
    (signal : Y → ℝ) (hs : Measurable signal)
    (condition : Y → Prop) (hc : MeasurableSet {p | condition p})
    {W C δ Δ : ℝ} (hW : 0 < W) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hdom : ENNReal.ofReal W • law.map f ≤ μ) (weight : ℝ≥0∞)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | (fun i => ⌊point p i / δ⌋) = q ∧
        ⌊signal p / Δ⌋ = j ∧ condition p} ≤ ENNReal.ofReal (C * δ ^ 3) * weight) :
    ∀ (q : Fin 3 → ℤ) (j : ℤ),
      law {p | (fun i => ⌊point (f p) i / δ⌋) = q ∧
        ⌊signal (f p) / Δ⌋ = j ∧ condition (f p)} ≤
          ENNReal.ofReal ((C / W) * δ ^ 3) * weight := by
  intro q j
  have hcode : Measurable (fun p i => ⌊point p i / δ⌋) := by
    apply Measurable.of_eval
    intro i
    exact Int.measurable_floor.comp (((measurable_pi_apply i).comp hp).div_const δ)
  have hE : MeasurableSet {p | (fun i => ⌊point p i / δ⌋) = q ∧
      ⌊signal p / Δ⌋ = j ∧ condition p} :=
    (hcode (measurableSet_singleton q)).inter
      (((Int.measurable_floor.comp (hs.div_const Δ)) (measurableSet_singleton j)).inter hc)
  have hh := cap_of_scaled_map_domination law μ f hf hW (by positivity)
    hdom _ hE weight (hcap q j)
  convert hh using 1
  congr 2
  ring

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Original fine caps with a whole interval of hidden and angular exponents.
The original palette remains a factor in every joint cell. -/
structure FineCaps (cfg : Data α) (k : ℕ) (M sMax vMin vMax : ℝ) : Prop where
  pure : ∀ s : ℝ, 0 ≤ s → s ≤ sMax → ∀ (q : Fin 3 → ℤ) (j : ℤ),
    cfg.μ k {p | cfg.z k (cfg.N k) M p = q ∧
      ⌊cfg.x k p.1 p.2 3 / cfg.N k ^ (-s)⌋ = j} ≤
      ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-M)) ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d)
  joint : ∀ s v : ℝ, 0 ≤ s → s ≤ sMax → vMin ≤ v → v ≤ vMax →
    ∀ (q : Fin 3 → ℤ) (j a : ℤ),
    cfg.μ k {p | cfg.z k (cfg.N k) M p = q ∧
      ⌊cfg.x k p.1 p.2 3 / cfg.N k ^ (-s)⌋ = j ∧
      ⌊cfg.b k p.1 3 / cfg.N k ^ (-v)⌋ = a} ≤
      ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-M)) ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d) *
        cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = a}
  palette : ∀ v : ℝ, vMin ≤ v → v ≤ vMax → ∀ a : ℤ,
    cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = a} ≤
      ENNReal.ofReal (cfg.K k * cfg.N k ^ (-cfg.S * v))

/-- Uniform original caps can be requested on every fixed compact exponent
range; the lower angular endpoint may depend on the requested final loss. -/
theorem Valid.eventually_fine_caps (h : Valid cfg)
    {M sMax vMin vMax : ℝ} (hM : 0 < M) (hsMax : 0 ≤ sMax)
    (hvMin : 0 < vMin) (hvMax : vMin ≤ vMax) :
    ∀ᶠ k in atTop, FineCaps cfg k M sMax vMin vMax := by
  let R := 2 + M + sMax + vMax + M⁻¹ + vMin⁻¹
  have hvMax0 : 0 < vMax := hvMin.trans_le hvMax
  have hR : 1 < R := by
    dsimp [R]
    linarith [inv_pos.mpr hM, inv_pos.mpr hvMin]
  have hR0 : 0 < R := by linarith
  have hMR : M ≤ R := by
    dsimp [R]
    linarith [inv_pos.mpr hM, inv_pos.mpr hvMin]
  have hsR : sMax ≤ R := by
    dsimp [R]
    linarith [inv_pos.mpr hM, inv_pos.mpr hvMin]
  have hvR : vMax ≤ R := by
    dsimp [R]
    linarith [inv_pos.mpr hM, inv_pos.mpr hvMin]
  have hRM : R⁻¹ ≤ M := by
    apply (inv_le_comm₀ hR0 hM).mpr
    dsimp [R]
    linarith [inv_pos.mpr hvMin]
  have hRv : R⁻¹ ≤ vMin := by
    apply (inv_le_comm₀ hR0 hvMin).mpr
    dsimp [R]
    linarith [inv_pos.mpr hM]
  filter_upwards [h.caps R hR] with k hk
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hscale (s : ℝ) : cfg.N k ^ (-3 * M - cfg.d * s) =
      (cfg.N k ^ (-M)) ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le,
      ← Real.rpow_add hN]
    congr 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro s hs hsmax q j
    have hc := (hk M s vMin hRM hMR hs (hsmax.trans hsR) hRv (hvMax.trans hvR)).2.1
      false q j
    simpa only [Bool.false_eq_true, ↓reduceIte, hscale, mul_assoc] using hc
  · intro s v hs hsmax hvmin hvmax q j a
    have hc := (hk M s v hRM hMR hs (hsmax.trans hsR) (hRv.trans hvmin)
      (hvmax.trans hvR)).2.2 false q j a
    simpa only [Bool.false_eq_true, ↓reduceIte, hscale, mul_assoc] using hc
  · intro v hvmin hvmax a
    exact (hk M 0 v hRM hMR le_rfl (by linarith) (hRv.trans hvmin)
      (hvmax.trans hvR)).1 a

end Data

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
