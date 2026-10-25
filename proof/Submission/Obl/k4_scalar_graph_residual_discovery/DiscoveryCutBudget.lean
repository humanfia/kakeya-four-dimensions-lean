/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file DiscoveryCutBudget.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryGeometryNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open scoped ENNReal

noncomputable def discoveryCutBudget (n : ℕ) (H η Ac : ℝ)
    (θ old current π : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal H * (32 * n * ENNReal.ofReal η) * θ +
    (ENNReal.ofReal H * (n * ENNReal.ofReal (6860 * H * η)) * θ +
      ((ENNReal.ofReal η * old +
        (n * (ENNReal.ofReal η * current) +
          n * (ENNReal.ofReal η * (ENNReal.ofReal (512 * H) * (old * π))))) +
        (n * ENNReal.ofReal ((5000 * 111 ^ 3) / Ac)) * θ))

/-- The exact original global deletion cost has a fixed polynomial
majorant. This includes every coefficient box and every posterior entry. -/
theorem discovery_cut_budget_le {H H₀ η Ac : ℝ} (hH : 1 ≤ H)
    (hH₀ : 0 ≤ H₀) (hH₀H : H₀ ≤ H) (hη : 0 ≤ η) (hAc : Ac⁻¹ = η)
    {n : ℕ} (hn : 1 ≤ n) {θ old current π : ℝ≥0∞}
    (hθ : θ ≤ 1) (hold : old ≤ ENNReal.ofReal H) (hcurrent : current ≤ ENNReal.ofReal H)
    (hπ : π ≤ 1) :
    discoveryCutBudget n H₀ η Ac θ old current π ≤
      ENNReal.ofReal (10000000000 * n * H ^ 2 * η) := by
  have hHreal : 0 ≤ H := by linarith
  have hlarge : discoveryCutBudget n H₀ η Ac θ old current π ≤
      discoveryCutBudget n H η Ac 1 (ENNReal.ofReal H) (ENNReal.ofReal H) 1 := by
    unfold discoveryCutBudget
    gcongr
  have hcost : discoveryCutBudget n H η Ac 1 (ENNReal.ofReal H) (ENNReal.ofReal H) 1 =
      ENNReal.ofReal (H * (32 * n * η) +
        (H * (n * (6860 * H * η)) +
          ((η * H + (n * η * H + n * η * (512 * H * H))) + n * ((5000 * 111 ^ 3) * η)))) := by
    simp (disch := positivity) only [discoveryCutBudget, div_eq_mul_inv, hAc,
      ENNReal.ofReal_add, ENNReal.ofReal_mul, ENNReal.ofReal_natCast]
    norm_num
    ring
  exact hlarge.trans (hcost.le.trans (ENNReal.ofReal_le_ofReal (discovery_cut_scalar_budget hH hη hn)))

end Submission.Obl.k4_scalar_graph_residual_discovery
