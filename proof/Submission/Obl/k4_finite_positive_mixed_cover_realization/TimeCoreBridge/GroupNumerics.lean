-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/GroupNumerics.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from LOT tree g-oai-074, obligation o194, session x0672,
-- commit c10e54a1, Submission/Obl/k4_greedy_cover_graph_atlas/GroupNumerics.lean.
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Numerics
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Core
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.CleanCaps

/-!
# Numerical conditions of one group step

The numerical hypotheses of `group_step` (o173/x0581) and of the root-test threshold, in terms of
the comparison ratio `R = δ(N, r₀) / δ(N, r₀ + h L)`, the spread unit `M = δ(N, r₀)`, the fine
and old fit factors, and power bounds with a positive exponent gap.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Submission.Lib.K4XInterface

/-- The comparison ratio of a gain step. -/
noncomputable def cmpRatio (N r₀ hL : ℝ) : ℝ := δ N r₀ / δ N (r₀ + hL)

theorem cmpRatio_bounds {N : ℝ} (hN : 0 < N) (r₀ hL : ℝ) :
    N ^ hL / 2 ≤ cmpRatio N r₀ hL ∧ cmpRatio N r₀ hL ≤ 2 * N ^ hL :=
  gδ_ratio_bounds hN r₀ hL

theorem cmpRatio_pos (N r₀ hL : ℝ) : 0 < cmpRatio N r₀ hL :=
  div_pos (gδ_pos N r₀) (gδ_pos N (r₀ + hL))

/-- `M R⁻¹ = δ(r₀ + hL)` for the spread unit `M = δ(r₀)`. -/
theorem spread_div_cmpRatio (N r₀ hL : ℝ) :
    δ N r₀ / cmpRatio N r₀ hL = δ N (r₀ + hL) := by
  unfold cmpRatio
  have h1 := (gδ_pos N r₀).ne'
  have h2 := (gδ_pos N (r₀ + hL)).ne'
  field_simp

/-- The width condition `2 η_fine + δ_L ≤ M R^(-1+ε)` of `group_step`. -/
theorem group_width {N r₀ hL δL X ε : ℝ} (hδL0 : 0 ≤ δL) (hδL : δL ≤ δ N (r₀ + hL))
    (hX : 1 ≤ X) (hRX : 3 * X ≤ cmpRatio N r₀ hL ^ ε) :
    2 * (δ N (r₀ + hL) * X) + δL ≤ δ N r₀ * cmpRatio N r₀ hL ^ (-1 + ε) := by
  have hR := cmpRatio_pos N r₀ hL
  have hδ1 := gδ_pos N (r₀ + hL)
  have he : δ N r₀ * cmpRatio N r₀ hL ^ (-1 + ε) =
      δ N (r₀ + hL) * cmpRatio N r₀ hL ^ ε := by
    rw [Real.rpow_add hR, Real.rpow_neg_one, ← mul_assoc, ← div_eq_mul_inv,
      spread_div_cmpRatio]
  rw [he]
  nlinarith

/-- The Remez band condition of `group_step`. -/
theorem group_band {M R ε Krem Crem θ ηf ηo Y : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ Krem)
    (hC : 0 ≤ Crem) (hθ : 0 < θ) (hη : ηf + ηo ≤ M * Y)
    (hY : Krem * (Crem * θ ^ (-Crem) * Y) ≤ R ^ ε) :
    Krem * (Crem * θ ^ (-Crem) * (ηf + ηo)) ≤ M * R ^ ε := by
  have hθC : 0 ≤ θ ^ (-Crem) := Real.rpow_nonneg hθ.le _
  calc Krem * (Crem * θ ^ (-Crem) * (ηf + ηo)) ≤ Krem * (Crem * θ ^ (-Crem) * (M * Y)) := by
        gcongr
    _ = M * (Krem * (Crem * θ ^ (-Crem) * Y)) := by ring
    _ ≤ M * R ^ ε := mul_le_mul_of_nonneg_left hY hM

/-- The root-test target `340 (η_fine + η_bin) ≤ δ(r₀) N^(-θ h L)`, with
`η_bin = Jsum M R^(-ε) / lower`. -/
theorem group_root_target {N r₀ hL X ε Jsum lower θo : ℝ} (hlower : 0 < lower)
    (htarget : 340 * (X / cmpRatio N r₀ hL + Jsum * cmpRatio N r₀ hL ^ (-ε) / lower) ≤
      N ^ (-θo)) :
    340 * (δ N (r₀ + hL) * X + Jsum * (δ N r₀ * cmpRatio N r₀ hL ^ (-ε)) / lower) ≤
      δ N r₀ * N ^ (-θo) := by
  have hR := cmpRatio_pos N r₀ hL
  have hδ0 := gδ_pos N r₀
  have he : δ N (r₀ + hL) = δ N r₀ / cmpRatio N r₀ hL := (spread_div_cmpRatio N r₀ hL).symm
  rw [he]
  have hrw : 340 * (δ N r₀ / cmpRatio N r₀ hL * X +
      Jsum * (δ N r₀ * cmpRatio N r₀ hL ^ (-ε)) / lower) =
      δ N r₀ * (340 * (X / cmpRatio N r₀ hL + Jsum * cmpRatio N r₀ hL ^ (-ε) / lower)) := by
    field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_left htarget hδ0.le

/-- A lower bound for `R^ε` from `R ≥ N^(hL)/2`. -/
theorem cmpRatio_rpow_lower {N r₀ hL ε : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hhL : 0 ≤ hL) : N ^ (ε * hL) / 2 ≤ cmpRatio N r₀ hL ^ ε := by
  have hN0 : 0 < N := by linarith
  obtain ⟨hlo, -⟩ := cmpRatio_bounds hN0 r₀ hL
  have hpos : 0 < N ^ hL / 2 := by positivity
  have h1 : (N ^ hL / 2) ^ ε ≤ cmpRatio N r₀ hL ^ ε :=
    Real.rpow_le_rpow hpos.le hlo hε
  have h2 : (N ^ hL / 2) ^ ε = N ^ (ε * hL) / 2 ^ ε := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hN0.le, mul_comm]
  have h3 : (2 : ℝ) ^ ε ≤ 2 := by
    calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
      _ = 2 := Real.rpow_one 2
  have h4 : N ^ (ε * hL) / 2 ≤ N ^ (ε * hL) / 2 ^ ε :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h3
  linarith

/-- A constant times a power is below `R^ε` once the exponent gap absorbs the constant. -/
theorem le_cmpRatio_rpow {N r₀ hL ε K₀ a ξ : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hhL : 0 ≤ hL) (hK₀ : 1 ≤ K₀) (hξ : 0 < ξ) (hNK : (2 * K₀) ^ (1 / ξ) ≤ N)
    (hgap : a + ξ ≤ ε * hL) : K₀ * N ^ a ≤ cmpRatio N r₀ hL ^ ε := by
  have h1 := rpow_absorb hN (by linarith : (1 : ℝ) ≤ 2 * K₀) hξ hNK hgap
  have h2 := cmpRatio_rpow_lower (r₀ := r₀) hN hε hε1 hhL
  linarith

/-- The count condition `n ≤ R^(d₀+ε)`. -/
theorem group_count {N r₀ hL ε d₀ n c ξ : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (hd₀ : 0 ≤ d₀)
    (hdε : d₀ + ε ≤ 1) (hhL : 0 ≤ hL) (hξ : 0 < ξ) (hN2 : (2 : ℝ) ^ (1 / ξ) ≤ N)
    (hn : n ≤ N ^ c) (hgap : c + ξ ≤ (d₀ + ε) * hL) : n ≤ cmpRatio N r₀ hL ^ (d₀ + ε) := by
  have hN0 : 0 < N := by linarith
  have hde : 0 ≤ d₀ + ε := by linarith
  have h1 : (2 : ℝ) * N ^ c ≤ N ^ ((d₀ + ε) * hL) :=
    rpow_absorb hN (by norm_num) hξ hN2 hgap
  obtain ⟨hlo, -⟩ := cmpRatio_bounds hN0 r₀ hL
  have h2 : (N ^ hL / 2) ^ (d₀ + ε) ≤ cmpRatio N r₀ hL ^ (d₀ + ε) :=
    Real.rpow_le_rpow (by positivity) hlo hde
  have h3 : (N ^ hL / 2) ^ (d₀ + ε) = N ^ ((d₀ + ε) * hL) / 2 ^ (d₀ + ε) := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hN0.le, mul_comm hL]
  have h4 : (2 : ℝ) ^ (d₀ + ε) ≤ 2 := by
    calc (2 : ℝ) ^ (d₀ + ε) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hdε
      _ = 2 := Real.rpow_one 2
  have h5 : N ^ ((d₀ + ε) * hL) / 2 ≤ N ^ ((d₀ + ε) * hL) / 2 ^ (d₀ + ε) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h4
  linarith

/-- The time budget: a dyadic count below `2 X` with `X ≤ N^a` and a positive gap fits. -/
theorem time_budget {N X a b ξ : ℝ} {s₀ : ℕ} (hN : 1 ≤ N) (hξ : 0 < ξ)
    (hN2 : (2 : ℝ) ^ (1 / ξ) ≤ N) (hs₀ : (2 : ℝ) ^ s₀ ≤ 2 * X) (hX : X ≤ N ^ a)
    (hgap : a + ξ ≤ b) : (2 : ℝ) ^ s₀ ≤ N ^ b := by
  have h1 := rpow_absorb hN (by norm_num : (1 : ℝ) ≤ 2) hξ hN2 hgap
  linarith

/-- The list budget: `Clist · 4κ(2κ+3)² ≤ N^β` for `κ ≤ N^σ`, `σ ≤ β/4`. -/
theorem list_budget {N κ σ β : ℝ} (Clist : ℕ) (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκσ : κ ≤ N ^ σ)
    (hσ : 0 ≤ σ) (hσβ : σ ≤ β / 4)
    (hN' : (100 * (Clist : ℝ) + 1) ^ (1 / (β / 4)) ≤ N) (hβ : 0 < β) :
    (Clist : ℝ) * (4 * κ * (2 * κ + 3) ^ 2) ≤ N ^ β := by
  have hN0 : 0 < N := by linarith
  have hκ5 : 2 * κ + 3 ≤ 5 * κ := by linarith
  have hpoly : 4 * κ * (2 * κ + 3) ^ 2 ≤ 100 * κ ^ 3 := by
    have : (2 * κ + 3) ^ 2 ≤ (5 * κ) ^ 2 := pow_le_pow_left₀ (by linarith) hκ5 2
    nlinarith
  have hκ3 : κ ^ 3 ≤ N ^ (3 * σ) := by
    calc κ ^ 3 ≤ (N ^ σ) ^ (3 : ℕ) := pow_le_pow_left₀ (by linarith) hκσ 3
      _ = N ^ (3 * σ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have habs := rpow_absorb hN (by have := Nat.cast_nonneg (α := ℝ) Clist; linarith : (1 : ℝ) ≤ 100 * (Clist : ℝ) + 1)
    (by positivity : (0 : ℝ) < β / 4) hN' (show 3 * σ + β / 4 ≤ β by linarith)
  calc (Clist : ℝ) * (4 * κ * (2 * κ + 3) ^ 2) ≤ (Clist : ℝ) * (100 * κ ^ 3) :=
        mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg _)
    _ = 100 * (Clist : ℝ) * κ ^ 3 := by ring
    _ ≤ (100 * (Clist : ℝ) + 1) * N ^ (3 * σ) :=
        mul_le_mul (by linarith) hκ3 (by positivity) (by positivity)
    _ ≤ N ^ β := habs

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
