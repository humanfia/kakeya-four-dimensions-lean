-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripUniformSecondScaleNet, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripUniformSecondScaleNet.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripUniformSecondScaleNet.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripUniformSecondScaleNet.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripUniformSecondScaleNet.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripSecondScalePowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPowerBudgetedNet

/-! One cutoff supplies all geometric, packing, overlap and output-slack
budgets before any later path envelope or family of predicted strips. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Filter

structure StripSecondScaleBounds (N E A u a v τ loss : ℝ) (p q : ℕ) : Prop where
  N_two : 2 ≤ N
  E_one : 1 ≤ E
  E_le_N : E ≤ N
  scales :
    let r₀ := A * N ^ (-u)
    let r₁ := N ^ (-u / 2)
    let r₂ := N ^ (-u / 4)
    let w := r₀ + (1 + 2 * E) * r₁
    0 < r₁ ∧ 0 < r₂ ∧ r₁ ≤ r₂ ∧ r₂ ≤ 1 ∧ 4 * r₀ ≤ r₁ ∧ 4 * w ≤ r₂ ∧
      32 * (1 + 2 * E) * r₀ / r₁ ≤ N ^ (-u / 4) ∧
      32 * (1 + 2 * E) * w / r₂ ≤ N ^ (-u / 8) ∧
      E * (32 * (1 + 2 * E) * w / r₂) ≤ N ^ (-u / 16)
  packing : 2 * E ^ (q + 2 * p) * N ^ (2 * a - v) ≤ 1
  overlap : 900 * E ^ (4 * p + q + 8) * N ^ (4 * a - v) ≤ 1
  slack : 100 * E ^ 8 ≤ N ^ τ
  determinantSlack : 6 * E ^ 2 ≤ N ^ loss
  inverseRadius : (N ^ (-u / 4))⁻¹ ≤ N ^ ⌈u / 4⌉₊

theorem strip_uniform_second_scale_bounds {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) {A u a v τ loss : ℝ}
    (hA : 0 ≤ A) (hu : 0 < u) (hpack : 2 * a < v) (hoverlap : 4 * a < v)
    (hτ : 0 < τ) (hloss : 0 < loss) (p q : ℕ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ σ ≤ u / 32 ∧ ∀ᶠ k in atTop,
      ∀ E : ℝ, 1 ≤ E → E ≤ N k ^ σ →
        StripSecondScaleBounds (N k) E A u a v τ loss p q := by
  obtain ⟨σs, hσs, hσs1, hσsu, hs⟩ := strip_second_scale_power_window hN hA hu
  obtain ⟨σe, hσe, hσe1, he⟩ := strip_two_scale_error_window hN hpack hoverlap
    (q + 2 * p) (4 * p + q)
  obtain ⟨σo, hσo, hσo1, ho⟩ := strip_uniform_power_envelope hN hτ hloss
  let σ := min σs (min σe σo)
  have hσ : 0 < σ := lt_min hσs (lt_min hσe hσo)
  have hσs' : σ ≤ σs := min_le_left _ _
  have hσe' : σ ≤ σe := (min_le_right _ _).trans (min_le_left _ _)
  have hσo' : σ ≤ σo := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨σ, hσ, hσs'.trans hσs1, hσs'.trans hσsu, ?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop (2 : ℝ)), hs, he, ho]
    with k hk hks hke hko
  intro E hE hEN
  have hk1 : 1 ≤ N k := by linarith
  have hkpos : 0 < N k := by linarith
  have hEs := hEN.trans (Real.rpow_le_rpow_of_exponent_le hk1 hσs')
  have hEe := hEN.trans (Real.rpow_le_rpow_of_exponent_le hk1 hσe')
  have hEo := hEN.trans (Real.rpow_le_rpow_of_exponent_le hk1 hσo')
  obtain ⟨hpacking, hoverlapping⟩ := hke E hE hEe
  obtain ⟨hEN', hslack, hdet⟩ := hko E hE hEo
  refine ⟨hk, hE, hEN', hks E hE hEs, hpacking, hoverlapping, hslack, hdet, ?_⟩
  calc
    _ = N k ^ (u / 4) := by
      rw [show -u / 4 = -(u / 4) by ring, Real.rpow_neg hkpos.le, inv_inv]
    _ ≤ N k ^ (⌈u / 4⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le hk1 (Nat.le_ceil _)
    _ = _ := Real.rpow_natCast _ _

theorem StripSecondScaleBounds.geometric_budgets {N E A u a v τ loss K : ℝ}
    {p q : ℕ} (h : StripSecondScaleBounds N E A u a v τ loss p q)
    (hA : 0 ≤ A) (hu : 0 ≤ u) (hK : 1 ≤ K) (hKE : K ≤ E) :
    let r₀ := A * N ^ (-u)
    let r₁ := N ^ (-u / 2)
    let r₂ := N ^ (-u / 4)
    let w := r₀ + (1 + 2 * K) * r₁
    4 * w ≤ r₂ ∧
      32 * (1 + 2 * K) * r₀ / r₁ ≤ N ^ (-u / 8) ∧
      32 * (1 + 2 * K) * w / r₂ ≤ N ^ (-u / 8) := by
  have hNpos : 0 < N := by linarith [h.N_two]
  have hN1 : 1 ≤ N := by linarith [h.N_two]
  have hE0 : 0 ≤ E := by linarith [h.E_one]
  obtain ⟨hr₁, hr₂, _, _, _, hwidth, hpacking, hoverlap, _⟩ := h.scales
  dsimp only
  have hW : A * N ^ (-u) + (1 + 2 * K) * N ^ (-u / 2) ≤
      A * N ^ (-u) + (1 + 2 * E) * N ^ (-u / 2) := by gcongr
  refine ⟨(mul_le_mul_of_nonneg_left hW (by norm_num)).trans hwidth, ?_, ?_⟩
  · calc
      _ ≤ 32 * (1 + 2 * E) * (A * N ^ (-u)) / N ^ (-u / 2) := by gcongr
      _ ≤ N ^ (-u / 4) := hpacking
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  · calc
      _ ≤ 32 * (1 + 2 * E) *
          (A * N ^ (-u) + (1 + 2 * E) * N ^ (-u / 2)) / N ^ (-u / 4) := by gcongr
      _ ≤ _ := hoverlap

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
