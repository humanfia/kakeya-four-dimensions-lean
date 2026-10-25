-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.TubePower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.WideStripSecondMoment
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicPower
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallPowers
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PowerBudget

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The two logarithmic losses and the fixed width/separation ratio cost
an arbitrarily small power of the original fine scale, uniformly over all
coarser tube widths and polynomially many cells. -/
theorem tube_second_moment_power_coefficient {A D ν : ℝ}
    (hA : 1 ≤ A) (hD : 0 < D) (hν : 0 < ν) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ r w : ℝ, 0 < δ → δ ≤ δ₀ →
      0 < r → δ ≤ w → w ≤ 1 / 2 → w ≤ A * r →
      ∀ N : ℕ, (N : ℝ) ≤ δ ^ (-D) →
        (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) ∧
        64000 * (64 * w / r + 2) * (36 * w / r + 2) *
          (1 + Real.log (1 / w)) * (2 * ((Nat.log 2 N + 1 : ℕ) : ℝ) + 1) ≤
            δ ^ (-ν) := by
  let C₀ : ℝ := 3 * 64000 * (64 * A + 2) * (36 * A + 2)
  obtain ⟨d₁, hd₁, hd₁1, hc⟩ :=
    WangZahlLot.Obl.wz_nonconcentrated_dot_products.exists_power_bound C₀
      (show 0 < ν / 3 by positivity)
  obtain ⟨d₂, hd₂, hl⟩ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.logarithm_power_bound
    (M := 1) (by norm_num) (show 0 < ν / 3 by positivity)
  obtain ⟨d₃, hd₃, hn⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.logarithmic_count_power
      hD (show 0 < ν / 3 by positivity)
  refine ⟨min d₁ (min d₂ d₃), lt_min hd₁ (lt_min hd₂ hd₃),
    (min_le_left _ _).trans hd₁1, ?_⟩
  intro δ r w hδ hsmall hr hδw hw2 hwr N hN
  have hδd₁ := hsmall.trans (min_le_left _ _)
  have hδd₂ := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := hδd₁.trans hd₁1
  have hw : 0 < w := hδ.trans_le hδw
  have hratio : w / r ≤ A := (div_le_iff₀ hr).mpr hwr
  have h64 : 64 * w / r + 2 ≤ 64 * A + 2 := by rw [mul_div_assoc]; linarith
  have h36 : 36 * w / r + 2 ≤ 36 * A + 2 := by rw [mul_div_assoc]; linarith
  let L := δ ^ (-(ν / 3))
  have hL : 1 ≤ L := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hlog : 1 + Real.log (1 / w) ≤ L := by
    calc
      _ ≤ 1 + Real.log (1 / δ) := by
        gcongr
      _ ≤ L := hl δ hδ hδ1 hδd₂
  have hK : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ L := by
    simpa only [Nat.cast_add, Nat.cast_one] using hn δ hδ hδd₃ N hN
  have hK' : 2 * ((Nat.log 2 N + 1 : ℕ) : ℝ) + 1 ≤ 3 * L := by linarith
  have hlog0 : 0 ≤ 1 + Real.log (1 / w) := by
    have hh : 1 ≤ 1 / w := (le_div_iff₀ hw).mpr (by linarith)
    linarith [Real.log_nonneg hh]
  refine ⟨?_, ?_⟩
  · exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N).le
  · calc
      _ ≤ 64000 * (64 * A + 2) * (36 * A + 2) * L * (3 * L) := by
        gcongr
      _ = C₀ * L * L := by dsimp [C₀]; ring
      _ ≤ L * L * L := by gcongr; exact hc δ hδ hδd₁
      _ = δ ^ (-ν) := by
        dsimp [L]
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1
        ring

/-- The separated wide-tube second moment with its logarithms absorbed.
The Frostman constant remains explicit. -/
theorem wide_strip_second_moment_power {A D ν : ℝ}
    (hA : 1 ≤ A) (hD : 0 < D) (hν : 0 < ν) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ r w C : ℝ, 0 < δ → δ ≤ δ₀ → 0 < r → r ≤ w → δ ≤ w →
        w ≤ 1 / 2 → w ≤ A * r → 0 ≤ C →
      ∀ (Y : Finset E2), Y.Nonempty → (Y.card : ℝ) ≤ δ ^ (-D) →
        (∀ y ∈ Y, ‖y‖ ≤ 4) →
        (∀ x ρ, r ≤ ρ →
          ((Y.filter (fun y => y ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Y.card) →
      ∀ (J : Finset (E2 × E2)), (∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1) →
        (J : Set (E2 × E2)).Pairwise (StripSep r) →
      ∀ d : E2 × E2 → ℕ,
        (∀ j ∈ J, d j ≤ (Y.filter (fun y => |inner ℝ (y - j.1) j.2| < w)).card) →
        (∑ j ∈ J, (d j : ℝ) ^ 2) ≤ C * δ ^ (-ν) * (Y.card : ℝ) ^ 2 := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hcoeff⟩ := tube_second_moment_power_coefficient hA hD hν
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ r w C hδ hsmall hr hrw hδw hw2 hwr hC Y hY hYbound hY4 hFr J hJ hsep d hd
  obtain ⟨hK, hbound⟩ := hcoeff δ r w hδ hsmall hr hδw hw2 hwr Y.card hYbound
  have hh := wide_strip_second_moment hr hrw hw2 hC Y hY hY4 hFr J hJ hsep
    (Nat.log 2 Y.card + 1) hK d hd
  calc
    _ ≤ 64000 * (64 * w / r + 2) * (36 * w / r + 2) *
        C * (1 + Real.log (1 / w)) * (2 * ((Nat.log 2 Y.card + 1 : ℕ) : ℝ) + 1) *
          (Y.card : ℝ) ^ 2 := hh
    _ = C * (64000 * (64 * w / r + 2) * (36 * w / r + 2) *
        (1 + Real.log (1 / w)) * (2 * ((Nat.log 2 Y.card + 1 : ℕ) : ℝ) + 1)) *
          (Y.card : ℝ) ^ 2 := by ring
    _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
