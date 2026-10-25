/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/OriginalCapUse.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeOriginalCaps

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- A fixed physical base resolution and hidden scale use the original joint
cap, with no restriction or change to its law. -/
theorem Prepared.eventually_original_hidden_caps (h : cfg.Prepared)
    {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    ∀ᶠ k in atTop, ∀ q n,
      cfg.μ k {p | baseMesh (cfg.N k ^ (-r)) (originalBase (cfg.b k p.1) p.2) = q ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / cfg.N k ^ (-s)⌋ = n} ≤
        ENNReal.ofReal ((cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d) *
          (cfg.N k ^ (-r)) ^ 3) := by
  let R := 2 + r + r⁻¹ + s
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by dsimp [R]; linarith
  have hRp : 0 < R := by linarith
  have hRr : R⁻¹ ≤ r := (inv_le_comm₀ hRp hr).mpr (by dsimp [R]; linarith)
  have hrR : r ≤ R := by dsimp [R]; linarith
  have hsR : s ≤ R := by dsimp [R]; linarith
  have hR1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith : 1 ≤ R)
  filter_upwards [h.caps R hR] with k hk
  intro q n
  have hc := (hk r s 1 hRr hrR hs hsR hR1 (by linarith)).2.1 false q n
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have heq : cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s) =
      (cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d) * (cfg.N k ^ (-r)) ^ 3 := by
    rw [← Real.rpow_mul hN.le, ← Real.rpow_natCast, ← Real.rpow_mul hN.le,
      mul_assoc, ← Real.rpow_add hN]
    congr 2
    push_cast
    ring
  rw [heq] at hc
  exact hc

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
