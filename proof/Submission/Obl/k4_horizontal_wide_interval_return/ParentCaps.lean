import Submission.Obl.k4_horizontal_wide_interval_return.Model
import Submission.Obl.k4_horizontal_wide_interval_return.NormalizeCaps

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set Filter
open Submission.Lib.K4MovingMeshBoxes

namespace Data

/-- The frozen parent caps supply all native cap inputs required by the
final scalar transfer, uniformly in the scalar signal depth and in every
velocity rate above an arbitrary fixed positive lower rate. -/
theorem eventually_native_scalar_caps {α : Type} [MeasurableSpace α]
    (cfg : Data α) (hc : cfg.Valid) {Bdepth s v U' rmin : ℝ}
    (hB : 0 < Bdepth) (hs : 0 < s) (hv : 0 ≤ v) (hU : 0 < U') (hrmin : 0 < rmin) :
    ∀ᶠ k in atTop, ∀ lam : Measure (α × ℝ), lam ≤ cfg.μ k →
      (∀ r : ℝ, 0 ≤ r → r ≤ v → ∀ c j, lam
        {p | baseMesh (cfg.N k ^ (-Bdepth))
            (![p.2, lineZ (cfg.b k p.1) p.2, lineY (cfg.b k p.1) p.2] : Fin 3 → ℝ) = c ∧
          ⌊lineX (cfg.b k p.1) p.2 / (cfg.N k ^ (-s) * cfg.N k ^ (-r))⌋ = j} ≤
        ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-Bdepth)) ^ 3 *
          (cfg.N k ^ (-s) * cfg.N k ^ (-r)) ^ cfg.d)) ∧
      (∀ r : ℝ, rmin ≤ r → r ≤ U' → ∀ ℓ : ℤ,
        cfg.π k {w | ⌊w / cfg.N k ^ (-r)⌋ = ℓ} ≤
          ENNReal.ofReal (cfg.K k * cfg.N k ^ (-cfg.S * r))) ∧
      (∀ r : ℝ, rmin ≤ r → r ≤ U' → ∀ c j ℓ, lam
        {p | baseMesh (cfg.N k ^ (-Bdepth))
            (![p.2, lineZ (cfg.b k p.1) p.2, lineY (cfg.b k p.1) p.2] : Fin 3 → ℝ) = c ∧
          ⌊lineX (cfg.b k p.1) p.2 / (cfg.N k ^ (-s) * cfg.N k ^ (-v))⌋ = j ∧
          ⌊cfg.b k p.1 3 / cfg.N k ^ (-r)⌋ = ℓ} ≤
        ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-Bdepth)) ^ 3 *
          (cfg.N k ^ (-s) * cfg.N k ^ (-v)) ^ cfg.d) *
          cfg.π k {w | ⌊w / cfg.N k ^ (-r)⌋ = ℓ}) := by
  let R : ℝ := 2 + Bdepth + s + v + U' + Bdepth⁻¹ + rmin⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hB, inv_pos.mpr hrmin]
  have hR1 : 1 ≤ R := hR.le
  have hBR : Bdepth ≤ R := by dsimp [R]; linarith [inv_pos.mpr hB, inv_pos.mpr hrmin]
  have hminR : rmin⁻¹ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hB]
  have hBInvR : Bdepth⁻¹ ≤ R := by dsimp [R]; linarith [inv_pos.mpr hrmin]
  have hRloB : R⁻¹ ≤ Bdepth := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hB) hBInvR
  have hRloMin : R⁻¹ ≤ rmin := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hrmin) hminR
  have hRlo1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hsR : s + v ≤ R := by dsimp [R]; linarith [inv_pos.mpr hB, inv_pos.mpr hrmin]
  have hUR : U' ≤ R := by dsimp [R]; linarith [inv_pos.mpr hB, inv_pos.mpr hrmin]
  filter_upwards [hc.caps R hR] with k hcaps
  intro lam hlam
  have hNpos : 0 < cfg.N k := by linarith [hc.resolution_lower k]
  constructor
  · intro r hr hrv c j
    have hraw := (hcaps Bdepth (s + r) 1 hRloB hBR (by linarith)
      (by linarith) hRlo1 hR1).2.1 false c j
    simp only [Bool.false_eq_true, ↓reduceIte] at hraw
    rw [native_rpow_cell_factor hNpos Bdepth cfg.d s r,
      show -(s + r) = -s + -r by ring, Real.rpow_add hNpos] at hraw
    change cfg.μ k {p | baseMesh (cfg.N k ^ (-Bdepth))
        (![p.2, lineZ (cfg.b k p.1) p.2, lineY (cfg.b k p.1) p.2] : Fin 3 → ℝ) = c ∧
      ⌊lineX (cfg.b k p.1) p.2 / (cfg.N k ^ (-s) * cfg.N k ^ (-r))⌋ = j} ≤ _ at hraw
    refine (hlam _).trans ?_
    simpa only [mul_assoc] using hraw
  · constructor
    · intro r hr hrU ℓ
      exact (hcaps Bdepth (s + v) r hRloB hBR (by linarith)
        hsR (hRloMin.trans hr) (hrU.trans hUR)).1 ℓ
    · intro r hr hrU c j ℓ
      have hraw := (hcaps Bdepth (s + v) r hRloB hBR (by linarith)
        hsR (hRloMin.trans hr) (hrU.trans hUR)).2.2 false c j ℓ
      simp only [Bool.false_eq_true, ↓reduceIte] at hraw
      rw [native_rpow_cell_factor hNpos Bdepth cfg.d s v,
        show -(s + v) = -s + -v by ring, Real.rpow_add hNpos] at hraw
      change cfg.μ k {p | baseMesh (cfg.N k ^ (-Bdepth))
          (![p.2, lineZ (cfg.b k p.1) p.2, lineY (cfg.b k p.1) p.2] : Fin 3 → ℝ) = c ∧
        ⌊lineX (cfg.b k p.1) p.2 / (cfg.N k ^ (-s) * cfg.N k ^ (-v))⌋ = j ∧
        ⌊cfg.b k p.1 3 / (cfg.N k ^ (-r))⌋ = ℓ} ≤ _ at hraw
      refine (hlam _).trans ?_
      simpa only [mul_assoc] using hraw

end Data

end Submission.Obl.k4_horizontal_wide_interval_return
