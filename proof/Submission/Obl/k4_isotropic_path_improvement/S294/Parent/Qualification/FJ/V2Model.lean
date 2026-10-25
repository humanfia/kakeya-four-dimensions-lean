-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Model, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Model.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Model.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Model.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Data
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalizedRows

set_option autoImplicit false

/-!
# The normalized observation model in version 2 (paper `tex-05`, "Local normalization")

The `j = 2` counterpart of `original_quadratic_normalized_model_error` and
`exists_normalized_observation_row` of o078 (session x0662, branch `x0662` at `f2bac599`,
`ScalarNormalizedRows.lean`, `ScalarBlockModel.lean`).

In a time block of length `H` around the anchor `c`, with `u ∈ [-1, 1]`,
`(S(c + H u) - base)/H = (S(c) - base)/H + u R(c) - φ(u) · y(c) + O(H (K + 14 K²))`, where
`φ(u) = (g(c + H u) - F(c))/H` is the normalized row of a componentwise `K`-Lipschitz
approximant `g` of `F` (`|g - F| ≤ 2 K ζ` at labelled times, `ζ ≤ H²`):

* `v2_quadratic_model_identity` (exact) and `v2_quadratic_model_error`;
* `exists_v2_row_approximant`: the approximant `g` (x0662's `original_row_anchor_normalization`
  applied to each component).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open scoped NNReal
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-- The exact local expansion of the scalar in a block. -/
theorem v2_quadratic_model_identity (c₀ : Fin 7 → ℝ) (Fstar Fcur g : Fin 2 → ℝ)
    {c H u base : ℝ} (hH : H ≠ 0) :
    ((zx c₀ (c + H * u) - Fcur ⬝ᵥ zy c₀ (c + H * u)) - base) / H -
      (((zx c₀ c - Fstar ⬝ᵥ zy c₀ c) - base) / H +
        u * (c₀ 1 + 2 * c₀ 2 * c - Fstar ⬝ᵥ zv c₀) - (H⁻¹ • (g - Fstar)) ⬝ᵥ zy c₀ c) =
      H * u ^ 2 * c₀ 2 + (H⁻¹ • (g - Fcur)) ⬝ᵥ zy c₀ c -
        H * u * ((H⁻¹ • (Fcur - Fstar)) ⬝ᵥ zv c₀) := by
  have hy : zy c₀ (c + H * u) = zy c₀ c + (H * u) • zv c₀ := by
    rw [zy_add c₀ (c + H * u) c]; congr 2; ring
  rw [hy]
  simp only [zx, dot_two, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, zy_zero,
    zy_one, zv_zero, zv_one]
  field_simp
  ring

/-- **The local model error.** -/
theorem v2_quadratic_model_error (c₀ : Fin 7 → ℝ) (Fstar Fcur g : Fin 2 → ℝ)
    {c H u base K ζ : ℝ} (hH : 0 < H) (hK : 0 ≤ K) (hζ : 0 ≤ ζ) (hζH : ζ ≤ H ^ 2) (hH1 : H ≤ 1)
    (hu : |u| ≤ 1) (hc2 : |c₀ 2| ≤ K) (hv : ‖zv c₀‖ ≤ K) (hy : ‖zy c₀ c‖ ≤ 2 * K)
    (hφ : ‖H⁻¹ • (g - Fstar)‖ ≤ K) (hg : ‖g - Fcur‖ ≤ 2 * K * ζ) :
    |((zx c₀ (c + H * u) - Fcur ⬝ᵥ zy c₀ (c + H * u)) - base) / H -
      (((zx c₀ c - Fstar ⬝ᵥ zy c₀ c) - base) / H +
        u * (c₀ 1 + 2 * c₀ 2 * c - Fstar ⬝ᵥ zv c₀) - (H⁻¹ • (g - Fstar)) ⬝ᵥ zy c₀ c)| ≤
      H * (K + 14 * K ^ 2) := by
  rw [v2_quadratic_model_identity c₀ Fstar Fcur g hH.ne']
  have hHinv : 0 < H⁻¹ := inv_pos.mpr hH
  -- the three error terms
  have hu2 : u ^ 2 ≤ 1 := by
    have := sq_abs u; nlinarith [abs_nonneg u]
  have e1 : |H * u ^ 2 * c₀ 2| ≤ H * K := by
    rw [abs_mul, abs_mul, abs_of_pos hH, abs_of_nonneg (sq_nonneg u)]
    calc H * u ^ 2 * |c₀ 2| ≤ H * 1 * K := by gcongr
      _ = H * K := by ring
  have hgn : ‖H⁻¹ • (g - Fcur)‖ ≤ 2 * K * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hHinv]
    calc H⁻¹ * ‖g - Fcur‖ ≤ H⁻¹ * (2 * K * ζ) := by gcongr
      _ ≤ H⁻¹ * (2 * K * H ^ 2) := by gcongr
      _ = 2 * K * H := by field_simp
  have e2 : |(H⁻¹ • (g - Fcur)) ⬝ᵥ zy c₀ c| ≤ 8 * K ^ 2 * H := by
    have := abs_dot_le (H⁻¹ • (g - Fcur)) (zy c₀ c)
    have h2 : 2 * ‖H⁻¹ • (g - Fcur)‖ * ‖zy c₀ c‖ ≤ 2 * (2 * K * H) * (2 * K) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hgn (by norm_num)) hy (norm_nonneg _) (by positivity)
    nlinarith
  have hφt : ‖H⁻¹ • (Fcur - Fstar)‖ ≤ 3 * K := by
    have hsplit : H⁻¹ • (Fcur - Fstar) = H⁻¹ • (g - Fstar) - H⁻¹ • (g - Fcur) := by
      rw [← smul_sub]; congr 1; abel
    rw [hsplit]
    calc ‖H⁻¹ • (g - Fstar) - H⁻¹ • (g - Fcur)‖
        ≤ ‖H⁻¹ • (g - Fstar)‖ + ‖H⁻¹ • (g - Fcur)‖ := norm_sub_le _ _
      _ ≤ K + 2 * K * H := add_le_add hφ hgn
      _ ≤ 3 * K := by nlinarith
  have e3 : |H * u * ((H⁻¹ • (Fcur - Fstar)) ⬝ᵥ zv c₀)| ≤ 6 * K ^ 2 * H := by
    rw [abs_mul, abs_mul, abs_of_pos hH]
    have := abs_dot_le (H⁻¹ • (Fcur - Fstar)) (zv c₀)
    have h2 : 2 * ‖H⁻¹ • (Fcur - Fstar)‖ * ‖zv c₀‖ ≤ 2 * (3 * K) * K :=
      mul_le_mul (mul_le_mul_of_nonneg_left hφt (by norm_num)) hv (norm_nonneg _) (by positivity)
    calc H * |u| * |(H⁻¹ • (Fcur - Fstar)) ⬝ᵥ zv c₀| ≤ H * 1 * (6 * K ^ 2) := by
          gcongr; nlinarith
      _ = 6 * K ^ 2 * H := by ring
  calc |H * u ^ 2 * c₀ 2 + (H⁻¹ • (g - Fcur)) ⬝ᵥ zy c₀ c -
        H * u * ((H⁻¹ • (Fcur - Fstar)) ⬝ᵥ zv c₀)|
      ≤ |H * u ^ 2 * c₀ 2| + |(H⁻¹ • (g - Fcur)) ⬝ᵥ zy c₀ c| +
          |H * u * ((H⁻¹ • (Fcur - Fstar)) ⬝ᵥ zv c₀)| := by
        have := abs_sub (H * u ^ 2 * c₀ 2 + (H⁻¹ • (g - Fcur)) ⬝ᵥ zy c₀ c)
          (H * u * ((H⁻¹ • (Fcur - Fstar)) ⬝ᵥ zv c₀))
        have := abs_add_le (H * u ^ 2 * c₀ 2) ((H⁻¹ • (g - Fcur)) ⬝ᵥ zy c₀ c)
        linarith
    _ ≤ H * K + 8 * K ^ 2 * H + 6 * K ^ 2 * H := by linarith
    _ = H * (K + 14 * K ^ 2) := by ring

/-- **The componentwise row approximant.** -/
theorem exists_v2_row_approximant {U : Set ℝ} {F : ℝ → Fin 2 → ℝ} {K ζ c H : ℝ}
    (hK : 0 ≤ K) (hH : 0 < H) (hc : c ∈ U)
    (hF : ∀ t ∈ U, ∀ s ∈ U, ‖F t - F s‖ ≤ K * (|t - s| + ζ)) :
    ∃ g : ℝ → Fin 2 → ℝ, g c = F c ∧ (∀ t ∈ U, ‖g t - F t‖ ≤ 2 * K * ζ) ∧
      (∀ i, ∀ u v, |(g (c + H * u) i - F c i) / H - (g (c + H * v) i - F c i) / H| ≤
        K * |u - v|) ∧
      (∀ u, ‖H⁻¹ • (g (c + H * u) - F c)‖ ≤ K * |u|) ∧
      (∀ i, Continuous (fun t => g t i)) := by
  have hcomp : ∀ i : Fin 2, ∀ t ∈ U, ∀ s ∈ U, |F t i - F s i| ≤ K * (|t - s| + ζ) := by
    intro i t ht s hs
    have := abs_le_norm (F t - F s) i
    simpa using this.trans (hF t ht s hs)
  choose g hgL hgc hgnear hgnorm hgbound using
    fun i : Fin 2 => original_row_anchor_normalization (F := fun t => F t i) hK hH hc (hcomp i)
  let G : ℝ → Fin 2 → ℝ := fun t i => g i t
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; exact hgc i
  · intro t ht
    -- each component is within `2 K ζ`
    have hζ0 : ∀ i, |g i t - F t i| ≤ 2 * K * ζ := fun i => hgnear i t ht
    have h0 : 0 ≤ 2 * K * ζ := le_trans (abs_nonneg _) (hζ0 0)
    exact norm_le_of_abs_le h0 fun i => by simpa [G] using hζ0 i
  · intro i u v; exact hgnorm i u v
  · intro u
    have h0 : 0 ≤ K * |u| := by positivity
    refine norm_le_of_abs_le h0 fun i => ?_
    have := hgbound i u
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, G]
    rw [show H⁻¹ * (g i (c + H * u) - F c i) = (g i (c + H * u) - F c i) / H by
      rw [div_eq_inv_mul]]
    exact this
  · intro i; exact (hgL i).continuous

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
