import Submission.Obl.k4_scalar_graph_residual_discovery.SplitStatements
-- Adapted from this tree's obligation o229 `k4_scalar_grid_polynomial_qualification` (branch x0839, commit 9de6db41),
-- file `Submission/Obl/k4_scalar_grid_polynomial_qualification/DiscoveryInterfaceBridge.lean`: our own tree's unaccepted helper code, with the module path and
-- namespace renamed from `k4_scalar_grid_polynomial_qualification` to `k4_scalar_graph_residual_discovery`.

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

/-- Unbundling the raw frozen arrays recovers the discovery interface of
the checked endpoint argument, with no new mathematical hypothesis. -/
theorem polynomialDiscovery_of_closed (h : DiscoveryInput) : PolynomialDiscoveryStatement := by
  intro hMK D hp hbase hcaps hpackets H₀ θ E₀ hprep
  obtain ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hS⟩ := hp
  have hraw := h hMK D.N D.K hN hNt hK D.d D.κ D.S hd hd1 hκ hκ1 hS
    D.W D.ω D.ν D.ρ D.π D.T D.n D.γ D.j D.A D.u D.v D.F
  change D.base → D.caps → D.packets →
    ∀ (H₀ : ℕ → ℝ)
      (θ : (k : ℕ) → Fin (D.W k) → MeasureTheory.Measure ScalarLine)
      (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence),
      D.prepData H₀ θ E₀ → D.polynomialDiscovery E₀ at hraw
  exact hraw hbase hcaps hpackets H₀ θ E₀ hprep

/-- Child provers may work with the existing bundled interface and then
return to the Mathlib-only frozen type. -/
theorem discoveryInput_of_polynomialDiscovery (h : PolynomialDiscoveryStatement) :
    DiscoveryInput := by
  intro hMK N K hN hNt hK d κ S hd hd1 hκ hκ1 hS W ω ν ρ π T n γ j A u v F
  let D : ScalarData :=
    { N := N, K := K, d := d, κ := κ, S := S, W := W, ω := ω, ν := ν, ρ := ρ, π := π,
      T := T, n := n, γ := γ, j := j, A := A, u := u, v := v, F := F }
  change D.base → D.caps → D.packets →
    ∀ (H₀ : ℕ → ℝ)
      (θ : (k : ℕ) → Fin (D.W k) → MeasureTheory.Measure ScalarLine)
      (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence),
      D.prepData H₀ θ E₀ → D.polynomialDiscovery E₀
  exact h hMK D ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hS⟩

theorem discoveryInput_iff : DiscoveryInput ↔ PolynomialDiscoveryStatement :=
  ⟨polynomialDiscovery_of_closed, discoveryInput_of_polynomialDiscovery⟩

end Submission.Obl.k4_scalar_graph_residual_discovery
