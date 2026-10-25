-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PackedEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PackedEstimate.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyMultiplicity

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (BodyGeometry BodyConvexCount BodyPacking BodyEstimate TubeEstimate bodyWeight
    body_estimate_of_tube_estimate body_slab_of_convex_count)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (body_slab_coefficient_ge_one)

noncomputable section

/-- An independent packing coefficient retains the positive concentration
power in the body estimate after convex counting supplies the slab bound. -/
theorem packed_body_weight {σ w m p n : ℝ}
    (hw : 0 < w) (hm : 0 < m) (hp : 0 < p) (hn : 0 < n) :
    bodyWeight σ w m (8 * m / (w * n)) p n =
      (8 : ℝ) ^ (-σ) * m ^ (-1 + σ / 2) * p ^ (-σ) * n * w ^ (1 + σ / 2) := by
  unfold bodyWeight
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

/-- The body estimate with a convex count and an independently supplied
quadratic packing bound. -/
theorem packed_convex_body_estimate {σ ω : ℝ} (hbody : BodyEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set V)
        (x : Fin n → V) (B w m p : ℝ),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m → 1 ≤ p →
      BodyGeometry U x δ B w → (∀ i, U i ⊆ ball (0 : V) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      (∀ i, O (δ ^ η) * μ (U i) ≤ μ (Y i)) →
      BodyConvexCount U w m → BodyPacking U w p →
      O (A * δ ^ ε * B ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) * n * w ^ (1 + σ / 2)) ≤
        μ (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hsmall, H⟩ := hbody ε hε
  refine ⟨A * (8 : ℝ) ^ (-σ), η, d₀, by positivity, hη, hd₀, hsmall, ?_⟩
  intro δ hδ hδd n U Y x B w m p hn hcount hδB hw hm hp hG hball hYm hYU hden hK hpack
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hslab := body_slab_of_convex_count hn hw hm0.le hball hK
  have hl := body_slab_coefficient_ge_one hn hball (by positivity) hslab
  have hbound := H δ hδ hδd n U Y x B w m (8 * m / (w * n)) p
    hn hcount hδB hw hm hl hp hG hYm hYU hden hK hslab hpack
  rw [packed_body_weight hw hm0 hp0 hn0] at hbound
  convert hbound using 1 <;> congr 1 <;> ring

/-- Saturation turns the nonlinear volume lower bound into a density gain. -/
theorem saturated_packed_body_scalar {σ A δ ε B ω m p n w C V₀ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hm : 0 < m)
    (hp : 0 < p) (hw : 0 < w) (hC : 0 < C)
    (hsat : m * V₀ ≤ C * n * w) :
    (A / C) * δ ^ ε * B ^ ω * m ^ (σ / 2) * p ^ (-σ) * w ^ (σ / 2) * V₀ ≤
      A * δ ^ ε * B ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) * n * w ^ (1 + σ / 2) := by
  have hmain : m / C * V₀ ≤ n * w := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    nlinarith only [hsat]
  have hmexp : m ^ (-1 + σ / 2) * m = m ^ (σ / 2) := by
    calc
      _ = m ^ (-1 + σ / 2) * m ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hm]; congr 1; ring
  have hwexp : w ^ (1 + σ / 2) = w * w ^ (σ / 2) := by
    rw [Real.rpow_add hw, Real.rpow_one]
  have hh := mul_le_mul_of_nonneg_left hmain
    (show 0 ≤ A * δ ^ ε * B ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) * w ^ (σ / 2) by positivity)
  calc
    _ = (A * δ ^ ε * B ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) * w ^ (σ / 2)) *
        (m / C * V₀) := by
      rw [show (A * δ ^ ε * B ^ ω * m ^ (-1 + σ / 2) * p ^ (-σ) * w ^ (σ / 2)) *
        (m / C * V₀) = (A / C) * δ ^ ε * B ^ ω *
          (m ^ (-1 + σ / 2) * m) * p ^ (-σ) * w ^ (σ / 2) * V₀ by ring]
      rw [hmexp]
    _ ≤ _ := hh
    _ = _ := by rw [hwexp]; ring

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
