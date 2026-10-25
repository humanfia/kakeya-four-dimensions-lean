-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.PacketGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketContainment
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketNormalization
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)

/-- A confined packet of frozen grains has the normalized geometry required
by the convex-body estimate, with an explicit Jacobian. -/
theorem frozen_packet_normalization {n : ℕ} {θ ρ a c s : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρθ : ρ ≤ θ)
    (ha : 0 < a) (hac : a ≤ ρ * c) (hc : 0 < c) (hc1 : c ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ θ * s * c)
    (z : Fin n → V) (e : Fin n → V ≃ₗᵢ[ℝ] V) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hD0 : ‖dualLinear θ (boxAxis e₀ 0)‖ ≤ 25 * θ)
    (hD1 : ‖dualLinear θ (boxAxis e₀ 1)‖ ≤ 25 * θ)
    (haxis : ∀ i, ‖coarseLinear θ (boxAxis (e i) 2)‖ ≤ 43)
    (hangle : ∀ i, ‖unit (dualLinear θ (boxAxis (e i) 0)) -
      unit (dualLinear θ (boxAxis e₀ 0))‖ ≤ s)
    (hcenter : ∀ i, ‖coarseLinear θ (z i - z₀)‖ ≤ c / 100)
    (hshortcenter : ∀ i, |inner ℝ (unit (dualLinear θ (boxAxis e₀ 0)))
      (coarseLinear θ (z i - z₀))| ≤ s * c / 100)
    (hlong : ∀ i, 1 / 2 ≤ |inner ℝ (boxAxis e₀ 2) (boxAxis (e i) 2)|) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ Q, volume (f '' Q) = ENNReal.ofReal (1 / (800000000 * θ ^ 2 * s * c ^ 3)) * volume Q) ∧
      (∀ i, f '' P a (ρ * c) c (z i) (e i) ⊆ ball (0 : V) 1) ∧
      (∀ i, ball (f (z i)) (a / 20000) ⊆ f '' P a (ρ * c) c (z i) (e i)) ∧
      (∀ i, ∃ p ∈ f '' P a (ρ * c) c (z i) (e i),
        ∃ q ∈ f '' P a (ρ * c) c (z i) (e i), (1 / 16 : ℝ) ≤ dist p q) := by
  have hρ1 : ρ ≤ 1 := hρθ.trans hθ1
  have hρc : ρ * c ≤ c := by nlinarith
  have hρcθ : ρ * c ≤ θ * c := mul_le_mul_of_nonneg_right hρθ hc.le
  have hsrc (i : Fin n) := frozen_prism_coarse_bounds hθ hθ1 ha.le hac hρcθ hc
    (z i) (e i) (haxis i)
  have hbox (i : Fin n) : P a (ρ * c) c (z i) (e i) ⊆
      orthogonalBox ![(10000 * θ * s * c) / 4, (10000 * θ * c) / 4, 2 * c] z₀ (frozenBasis e₀) := by
    have hh := physical_packet_enclosure hθ hθ1 hc hs has (z i) z₀
      (unit (dualLinear θ (boxAxis (e i) 0))) (frozenBasis e₀)
      (P a (ρ * c) c (z i) (e i)) hD0 hD1 (hangle i) (hcenter i) (hshortcenter i)
      (fun p hp => frozen_prism_norm ha.le hac hρc (z i) (e i) hp)
      (fun p hp => (hsrc i p hp).1) (fun p hp => (hsrc i p hp).2)
    convert hh using 1 <;> congr 1 <;> ext j <;> fin_cases j <;> simp <;> ring
  have hsc : s * c ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hs1 hc.le]
  have hθsc : θ * s * c ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsc hθ.le
    nlinarith
  have hθc : θ * c ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hθ1 hc.le]
  obtain ⟨f, hvol, hbounded, hint, hdiam⟩ := anisotropic_packet_normalization
    (by positivity : 0 < 10000 * θ * s * c) (by positivity : 0 < 10000 * θ * c) hc
    (by norm_num : (0 : ℝ) < 10000) (by nlinarith : 10000 * θ * s * c ≤ 10000)
    (by nlinarith : 10000 * θ * c ≤ 10000) (by linarith : 8 * c ≤ 10000)
    (frozenBasis e₀) z₀ (fun i => P a (ρ * c) c (z i) (e i)) z (fun i => boxAxis (e i) 2)
    hbox (fun i => ball_subset_frozen_prism hac hρc (z i) (e i))
    (fun i => frozen_prism_ends ha.le (mul_pos hρ hc).le hc.le (z i) (e i)) hlong
  refine ⟨f, ?_, hbounded, ?_, hdiam⟩
  · intro Q
    rw [hvol]
    congr 2
    ring
  · intro i
    convert hint i using 1 <;> congr 1 <;> ring

lemma normalized_packet_weight {a ρ θ s c : ℝ} (hθ : θ ≠ 0) (hs : s ≠ 0) (hc : c ≠ 0) :
    (1 / (800000000 * θ ^ 2 * s * c ^ 3)) * (a * (ρ * c) * c) =
      a * ρ / (800000000 * θ ^ 2 * s * c) := by
  field_simp

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
