/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file DiscoveryBudget.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryGeometryNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open scoped ENNReal

noncomputable section

def discoveryRowConstant (N Hg : ℝ) (J : ℕ) : ℝ :=
  6 * (N ^ (1 / (J : ℝ)) + (2 * Hg + 2) ^ 2)

def discoveryTimeConstant (N H Hg : ℝ) (J : ℕ) : ℝ :=
  Zoom.worldRowConstant (H + 1) (discoveryRowConstant N Hg J)

def discoveryListFormula (N H Hg η : ℝ) (J : ℕ) : ℝ :=
  (Hg / η + 2) * ((η⁻¹ * H ^ 3 * (H + 2) ^ 2 / η) *
    (2 * (7 + Hg + 2 * (12 * discoveryTimeConstant N H Hg J ^ 2)) + 2))

def discoveryListBudget (N H Hg η : ℝ) (J : ℕ) : ℕ :=
  ⌈discoveryListFormula N H Hg η J + 1⌉₊

def discoveryFirstFactor (Hg : ℝ) (C J : ℕ) : ℝ≥0∞ :=
  ((4 : ℝ≥0∞) ^ 3 * (2 ^ 3 * (⌈(2 * Hg + 2) ^ 2⌉₊ : ℝ≥0∞))) ^ (C * J + 1)

/-- The remaining sample conditions are exclusively numerical. No
measure, geometric support, incidence floor, row function, polynomial fit
or list is a field of this record. Its parameters are literal original
sample values; the world producer constructs all analytical data. -/
structure DiscoveryBudget
    (N H Hg K₀ d S L B h δ α cζ Cmk T : ℝ) (m M C₁ C J₁ J₂ : ℕ) where
  a : ℝ
  τ : ℝ
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
  coarse_mesh : ∃ j : ℕ, a = (j : ℝ) / (m : ℝ)
  coarse_lower : T⁻¹ ≤ a
  fine_upper : a + C + 1 / (m : ℝ) ≤ T
  tau_lower : T⁻¹ ≤ τ
  tau_upper : τ ≤ T
  coarse_floor : (C : ℝ) ≤ a
  row_precision : a ≤ C₁
  graph_precision : (C₁ : ℝ) ≤ L
  fine_precision : a + C + 1 / (m : ℝ) ≤ B
  source_budget : ENNReal.ofReal (2 * m₀) * discoveryFirstFactor Hg C₁ J₁ ≤
    ENNReal.ofReal (δ / (2 * Hg))
  cut_budget : 10000000000 * (C * J₂ + 1) * Hbig ^ 2 * η ≤ m₀
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
  selection_budget :
    ((4 : ℝ≥0∞) ^ 3 * (discoveryListBudget N H Hg η J₁ : ℝ≥0∞)) ^ (C * J₂ + 1) ≤
      ENNReal.ofReal P
  mass_budget : H * P / (m₀ / 2) ≤ Knormal
  row_budget : Hg ≤ Knormal
  row_compare_budget : 12 * discoveryTimeConstant N H Hg J₁ ^ 2 ≤ Knormal
  residual_budget : 6 * (N ^ (1 / (J₂ : ℝ)) + Hg + 5) ≤ Knormal
  cap_budget : 9 * H ^ 2 * (H * N ^ (1 / (J₂ : ℝ))) ^ 4 / η ≤ Knormal
  support_budget : ((4 * (3 + 2 * Hg) + 3) * (10648 * Kgeom ^ 3)) *
    ((N ^ (1 / (J₂ : ℝ))) ^ 2) ^ d ≤ Knormal
  graph_margin : Hg * N ^ (-L) ≤ h ^ M * h ^ ((1 : ℝ) / 8)
  row_margin : 4 * discoveryTimeConstant N H Hg J₁ ^ 2 * N ^ (-a) ≤
    h ^ M * h ^ ((1 : ℝ) / 8)
  floor_margin : N ^ (-(C : ℝ)) ≤ h ^ cζ

end

end Submission.Obl.k4_scalar_graph_residual_discovery
