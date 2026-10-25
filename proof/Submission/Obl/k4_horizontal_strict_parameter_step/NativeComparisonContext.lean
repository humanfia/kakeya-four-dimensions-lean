/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at a5c0b1bcb6dacb66c2e29bec68dd8eae37c23e9d, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeComparisonData.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeUniqueSupport
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeWidthCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeFrameSupport

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

/-- Pointwise preparation of the actual old/native comparison. Every stored
hypothesis concerns original data, original caps or an explicit numerical loss. -/
structure NativeComparisonData {α : Type} [MeasurableSpace α]
    (cfg : NativeModel α) (k : ℕ) (s : ℝ) (σ : Measure (α × ℝ)) where
  ε : ℝ
  D : ℝ
  a : ℝ
  M : ℝ
  R : ℝ
  re : ℝ
  A : ℝ
  m : ℕ
  AH : Fin m → Set α
  group : Fin m → Fin 3 → ℤ
  hH : Fin m → Fin 6 → ℝ
  support : NativeComparisonSupport cfg k s σ AH
  layer : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH
  measurable_b : Measurable (cfg.b k)
  dominated : σ ≤ cfg.μ k
  finite_original : IsFiniteMeasure σ
  finite_palette : IsFiniteMeasure (cfg.π k)
  caps : OriginalWidthCapsAt (cfg.N k) (cfg.K k) cfg.d R (cfg.μ k) (cfg.π k) (cfg.b k)
  re_lower : R⁻¹ ≤ re
  re_upper : re ≤ R
  velocity_lower : R⁻¹ ≤ cfg.e₀
  velocity_upper : cfg.e₀ ≤ R
  width_lower : cfg.N k ^ (-R) ≤ A
  width_upper : A ≤ 1
  L : Fin (cfg.n k s) → Fin 4 → ℝ
  slopes : ∀ i (e : Fin 3), |L i e.succ| ≤ M
  true_fit : ∀ i l, l ∈ cfg.B k s i → ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
    |cfg.b k l 2 + t * cfg.b k l 5 -
      (L i 0 + L i 1 * t + L i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
        L i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * a
  N_pos : 0 < cfg.N k
  K_one : 1 ≤ cfg.K k
  M_nonneg : 0 ≤ M
  D_pos : 0 < D
  D_one : D ≤ 1
  mesh_one : cfg.N k ^ (-re) ≤ 1
  mesh_time : cfg.N k ^ (-re) ≤ cfg.timeLength k s
  mesh_room : 2 * cfg.N k ^ (-cfg.e₀) +
    (3 * (3 * cfg.K k) + 4) * cfg.N k ^ (-re) ≤ D
  source_fit : cfg.N k ^ ε * a ≤ A
  witness_fit : cfg.K k * a + 2 * M * cfg.N k ^ (-cfg.e₀) ≤ A
  round_cell : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
    2 * (4 * B) * cfg.N k ^ (-re) + (6 * (4 * B) / D) *
      (cfg.N k ^ (-cfg.e₀) + (3 * cfg.K k + 1) * cfg.N k ^ (-re)) ≤ A
  round_jitter : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
    2 * B * cfg.N k ^ (-re) + (8 * B / D) *
      (3 * cfg.N k ^ (-cfg.e₀) + (4 * (3 * cfg.K k) + 5) * cfg.N k ^ (-re)) ≤ A

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

abbrev Index := c.support.table.Index c.group (cfg.j k s)
abbrev Colour (_c : NativeComparisonData cfg k s σ) := (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s)

def frame : c.Colour → ComparisonFrame :=
  fun l => nativeComparisonFrame (cfg.N k ^ (-cfg.e₀)) (cfg.timeLength k s) c.D l.1 (l.2 : ℕ)

theorem velocity_width : cfg.N k ^ (-cfg.e₀) ≤ c.D := by
  have hχ : 0 < cfg.N k ^ (-cfg.e₀) := Real.rpow_pos_of_pos c.N_pos _
  have hδ : 0 < cfg.N k ^ (-c.re) := Real.rpow_pos_of_pos c.N_pos _
  have hK := c.K_one
  nlinarith [c.mesh_room]

theorem mesh_parameter : 3 * cfg.K k * cfg.N k ^ (-c.re) ≤ c.D := by
  have hχ : 0 < cfg.N k ^ (-cfg.e₀) := Real.rpow_pos_of_pos c.N_pos _
  have hδ : 0 < cfg.N k ^ (-c.re) := Real.rpow_pos_of_pos c.N_pos _
  have hK := c.K_one
  have hm := mul_nonneg (by linarith : 0 ≤ 6 * cfg.K k + 4) hδ.le
  nlinarith [c.mesh_room]

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
