/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 31f9862f, file DiscoveryPowerBounds.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryBudget

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open scoped ENNReal

/-- The numerical conditions independent of the physical graph precision. -/
structure DiscoveryPowerBounds
    (N H Hg K₀ d S δ α Cmk τ : ℝ) (C₁ C J₁ J₂ : ℕ) where
  η : ℝ
  m₀ : ℝ
  Hbig : ℝ
  Kbase : ℝ
  Kgeom : ℝ
  Lfill : ℝ
  P : ℝ
  Knormal : ℝ
  eta_pos : 0 < η
  eta_le_one : η ≤ 1
  tau_pos : 0 < τ
  mass_pos : 0 < m₀
  one_le_Hbig : 1 ≤ Hbig
  prep_le : H ≤ Hbig
  graph_le : Hg ≤ Hbig
  original_le : K₀ ≤ Hbig
  source_budget : ENNReal.ofReal (2 * m₀) * discoveryFirstFactor Hg C₁ J₁ ≤ ENNReal.ofReal (δ / (2 * Hg))
  cut_budget : 10000000000 * (C * J₂ + 1) * Hbig ^ 2 * η ≤ m₀
  Kbase_pos : 0 < Kbase
  Kgeom_pos : 0 < Kgeom
  Lfill_pos : 0 < Lfill
  Kbase_density : 3 * H ≤ Kbase
  Kbase_prior : H / (η * η) ≤ Kbase
  filling_budget : 200 * Cmk * Kbase ^ 4 * (1 + H) ^ 2 ≤ Lfill * N ^ (-τ)
  filling_le : Lfill ≤ Kgeom
  angular_budget : 5 * (ENNReal.ofReal Hg / ENNReal.ofReal η) *
    ENNReal.ofReal (K₀ * N ^ (-S * τ)) ≤ 1 / 2
  hereditary_budget : 18 * ((5 + 2 * Hg) + 1) * (13824 * H ^ 7) ≤ Kgeom
  overlap_budget : 2 * (5 + 2 * Hg) + 2 ≤ Kgeom
  one_le_Knormal : 1 ≤ Knormal
  constant_budget : Knormal ≤ N ^ α
  original_budget : K₀ ≤ Knormal
  P_pos : 0 < P
  selection_budget : ((4 : ℝ≥0∞) ^ 3 * (discoveryListBudget N H Hg η J₁ : ℝ≥0∞)) ^ (C * J₂ + 1) ≤
    ENNReal.ofReal P
  mass_budget : H * P / (m₀ / 2) ≤ Knormal
  row_budget : Hg ≤ Knormal
  row_compare_budget : 12 * discoveryTimeConstant N H Hg J₁ ^ 2 ≤ Knormal
  residual_budget : 6 * (N ^ (1 / (J₂ : ℝ)) + Hg + 5) ≤ Knormal
  cap_budget : 9 * H ^ 2 * (H * N ^ (1 / (J₂ : ℝ))) ^ 4 / η ≤ Knormal
  support_budget : ((4 * (3 + 2 * Hg) + 3) * (10648 * Kgeom ^ 3)) *
    ((N ^ (1 / (J₂ : ℝ))) ^ 2) ^ d ≤ Knormal

/-- The original small physical scale and block margins. -/
structure DiscoveryScaleBounds (N H Hg L B h cζ T τ : ℝ) (m M C₁ C J₁ : ℕ) where
  a : ℝ
  coarse_mesh : ∃ j : ℕ, a = (j : ℝ) / (m : ℝ)
  coarse_lower : T⁻¹ ≤ a
  fine_upper : a + C + 1 / (m : ℝ) ≤ T
  tau_lower : T⁻¹ ≤ τ
  tau_upper : τ ≤ T
  coarse_floor : (C : ℝ) ≤ a
  row_precision : a ≤ C₁
  graph_precision : (C₁ : ℝ) ≤ L
  fine_precision : a + C + 1 / (m : ℝ) ≤ B
  point_precision : (1 + 3 * (H + 1)) * N ^ (-B) ≤ N ^ (-a) * N ^ (-(C : ℝ))
  variation :
    (Hg * N ^ (-L) + discoveryRowConstant N Hg J₁ *
      (N ^ (-a) + 2 * N ^ (-B) + N ^ (-(C₁ : ℝ))) * (1 + H)) *
        (N ^ (-a) + 2 * N ^ (-B)) + 2 * (1 + 2 * Hg) * N ^ (-B) ≤
          N ^ (-a) * N ^ (-(C : ℝ))
  residual_precision :
    4 * discoveryTimeConstant N H Hg J₁ ^ 2 * N ^ (-a) + Hg * N ^ (-L) / N ^ (-a) +
      2 * (H + 1) * N ^ (-B) / N ^ (-a) ≤ N ^ (-(C : ℝ))
  support_precision :
    2 * (discoveryRowConstant N Hg J₁ * (N ^ (-a) + 2 * N ^ (-B) + N ^ (-(C₁ : ℝ))) +
      4 * discoveryTimeConstant N H Hg J₁ ^ 2 * N ^ (-a)) +
        (1 + 2 * Hg) * N ^ (-B) / N ^ (-a) ≤ N ^ (-(C : ℝ))
  graph_margin : Hg * N ^ (-L) ≤ h ^ M * h ^ ((1 : ℝ) / 8)
  row_margin : 4 * discoveryTimeConstant N H Hg J₁ ^ 2 * N ^ (-a) ≤ h ^ M * h ^ ((1 : ℝ) / 8)
  floor_margin : N ^ (-(C : ℝ)) ≤ h ^ cζ

noncomputable def DiscoveryPowerBounds.toBudget
    {N H Hg K₀ d S L B h δ α cζ Cmk T τ : ℝ} {m M C₁ C J₁ J₂ : ℕ}
    (p : DiscoveryPowerBounds N H Hg K₀ d S δ α Cmk τ C₁ C J₁ J₂)
    (s : DiscoveryScaleBounds N H Hg L B h cζ T τ m M C₁ C J₁) :
    DiscoveryBudget N H Hg K₀ d S L B h δ α cζ Cmk T m M C₁ C J₁ J₂ := {
  a := s.a, τ := τ, η := p.η, m₀ := p.m₀, Hbig := p.Hbig, Kbase := p.Kbase
  Kgeom := p.Kgeom, Lfill := p.Lfill, P := p.P, Knormal := p.Knormal
  eta_pos := p.eta_pos, eta_le_one := p.eta_le_one, tau_pos := p.tau_pos, mass_pos := p.mass_pos
  one_le_Hbig := p.one_le_Hbig, prep_le := p.prep_le, graph_le := p.graph_le, original_le := p.original_le
  coarse_mesh := s.coarse_mesh, coarse_lower := s.coarse_lower, fine_upper := s.fine_upper
  tau_lower := s.tau_lower, tau_upper := s.tau_upper, coarse_floor := s.coarse_floor
  row_precision := s.row_precision, graph_precision := s.graph_precision, fine_precision := s.fine_precision
  source_budget := p.source_budget, cut_budget := p.cut_budget, point_precision := s.point_precision
  variation := s.variation, residual_precision := s.residual_precision, support_precision := s.support_precision
  Kbase_pos := p.Kbase_pos, Kgeom_pos := p.Kgeom_pos, Lfill_pos := p.Lfill_pos
  Kbase_density := p.Kbase_density, Kbase_prior := p.Kbase_prior, filling_budget := p.filling_budget
  filling_le := p.filling_le, angular_budget := p.angular_budget, hereditary_budget := p.hereditary_budget
  overlap_budget := p.overlap_budget, one_le_Knormal := p.one_le_Knormal, constant_budget := p.constant_budget
  original_budget := p.original_budget, P_pos := p.P_pos, selection_budget := p.selection_budget
  mass_budget := p.mass_budget, row_budget := p.row_budget, row_compare_budget := p.row_compare_budget
  residual_budget := p.residual_budget, cap_budget := p.cap_budget, support_budget := p.support_budget
  graph_margin := s.graph_margin, row_margin := s.row_margin, floor_margin := s.floor_margin
}

end Submission.Obl.k4_scalar_graph_residual_discovery
