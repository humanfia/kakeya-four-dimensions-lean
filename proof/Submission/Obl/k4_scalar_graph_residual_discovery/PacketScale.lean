/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PacketScale.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Model
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketGeometry

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter

namespace ScalarData

/-- The frozen depth-one packet horizon has its original two-sided
scale, with the SAME original subpower K. -/
theorem packets.original_block_scale {D : ScalarData}
    (hp : D.packets) (hN : ∀ k, 2 ≤ D.N k) (hK : ∀ k, 1 ≤ D.K k) :
    ∀ᶠ k in atTop, D.N k ^ (-D.κ) / D.K k ≤ ((2 : ℝ) ^ D.T k 1)⁻¹ ∧
      ((2 : ℝ) ^ D.T k 1)⁻¹ ≤ D.K k * D.N k ^ (-D.κ) := by
  filter_upwards [hp 2 (by norm_num)] with k hk
  have h := hk 1 (by norm_num) (by norm_num)
  have hh := Submission.Obl.k4_scalar_grid_cartesian_field.blockLength_comparison
    (by linarith [hN k] : 0 < D.N k) (by linarith [hK k] : 0 < D.K k) (D.T k 1)
    (by simpa only [mul_one] using h.1) (by simpa only [mul_one] using h.2.1)
  exact hh

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
