-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.UnitInitialization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitGrains
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketGain
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitBroad
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Budgets

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, UnitInitialization.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O A E bodyCount)
open WangZahlLot.Obl.wz_broad_grains_initialization
  (State packet_gain unit_scale_grains_of_broad measurable_angular_packets_power)
open WangZahlLot.Obl.wz_normalized_projection_coarse_fine (exists_power_absorption)

/-- Preserve the actual coarse radius one in the accepted broad/narrow
initialization construction. The public initialization theorem leaves that
radius existential, which is insufficient for the monotone-radius conclusion. -/
theorem initialization_at_one {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000) (hε : 0 < ε) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
        O (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i) ∨
          ∃ c, State ω ζ δ ε 1 c n x v Y false := by
  let β := ω * ζ / 100
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβω : β ≤ ω / 2 := by
    have hζ1 : ζ ≤ 1 / 1000 := by linarith
    dsimp [β]
    nlinarith
  have hβ1 : β ≤ 1 := by linarith
  let u := min (ε / 2) β
  have hu : 0 < u := lt_min (half_pos hε) hβ
  have huε : u ≤ ε / 2 := min_le_left _ _
  let b := u / (2 * β)
  have hb : 0 < b := by dsimp [b]; positivity
  let α := b * (ω - β) / 4
  have hα : 0 < α := by dsimp [α]; exact div_pos (mul_pos hb (by linarith)) (by norm_num)
  obtain ⟨κ, hκ, η₀, hη₀, HP⟩ := packet_gain hσ hσ2 hω hE α hα
  let η := min (min (ε / 8) (1 / 16)) (min (α / 8) (η₀ / 8))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η ≤ min (ε / 8) (1 / 16) := min_le_left _ _
  have hηα : η ≤ α / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hηη₀ : η ≤ η₀ / 8 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨dG, hdG, _, HG⟩ := unit_scale_grains_of_broad hε
  obtain ⟨dP, hdP, hdP100, HPackets⟩ := measurable_angular_packets_power hβ hβ1 hη
  obtain ⟨dB, hdB, HB⟩ := exists_power_absorption (C := 2) (p := u / 2) (r := 0)
    (by norm_num) (half_pos hu)
  obtain ⟨dC, hdC, HC⟩ := exists_power_absorption (C := 8) (p := b) (r := 0)
    (by norm_num) hb
  obtain ⟨dM, hdM, HM⟩ := exists_power_absorption
    (C := 2 * (2 * 6 ^ 3 * 22 ^ 3 : ℝ)) (p := η₀) (r := η₀ / 2)
    (by norm_num) (by linarith)
  let d₀ := min dP (min dG (min dB (min dC dM)))
  refine ⟨α, κ, η, d₀, hα, hκ, hη,
    (hηε.trans (min_le_left _ _)).trans (by linarith),
    by dsimp [d₀]; positivity, (min_le_left _ _).trans hdP100, ?_⟩
  intro δ hδ hδd n x v Y hA
  have hcuts : δ ≤ dP ∧ δ ≤ dG ∧ δ ≤ dB ∧ δ ≤ dC ∧ δ ≤ dM := by
    simpa only [d₀, le_min_iff] using hδd
  have hδ100 := hcuts.1.trans hdP100
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  obtain ⟨θ, Z, packets, anchor, hδθ, _, hpack, hmass⟩ :=
    HPackets δ hδ hcuts.1 n v Y hA.1
      (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.2.1)
  by_cases hθbig : δ ^ b ≤ θ
  · right
    apply HG δ hδ hcuts.2.1 ω ζ η η u hω1 hηε hηε huε n x v Y Z hA hpack.1 hmass
    intro p u' r _ hdr _
    have hbroad : 2 ≤ δ ^ (-(u / 2)) := by
      have hh : 2 * δ ^ (u / 2) ≤ 1 := by simpa using HB δ hδ hcuts.2.2.1
      rw [Real.rpow_neg hδ.le, ← one_div]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr hh
    exact hpack.unit_broad hδ hβ hθbig hbroad p u' r hdr
  · left
    have hθ : 0 < θ := hδ.trans_le hδθ
    have hθle : θ ≤ δ ^ b := (lt_of_not_ge hθbig).le
    have hθsmall : 8 * θ ≤ 1 := by
      have hh : 8 * δ ^ b ≤ 1 := by simpa using HC δ hδ hcuts.2.2.2.1
      nlinarith
    have hdensity : 2 * (2 * 6 ^ 3 * 22 ^ 3 : ℝ) * δ ^ η₀ ≤ δ ^ (η + η) :=
      (HM δ hδ hcuts.2.2.2.2).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    have hgain := HP δ θ β η η hδ hδ100 hδθ hθsmall hβ.le hη.le
      n x v Y Z packets anchor hA hpack hmass hdensity
    have hscale : δ ^ (-4 * α) ≤ θ ^ (β - ω) := by
      calc
        _ = (δ ^ b) ^ (β - ω) := by
          rw [← Real.rpow_mul hδ.le]
          congr 1
          dsimp [α]
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos hθ hθle (by linarith)
    have hcoefficient : δ ^ (ω - α) ≤ δ ^ (ω + α + 2 * η + η) * θ ^ (β - ω) := by
      calc
        _ ≤ δ ^ (ω + α + 2 * η + η - 4 * α) :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        _ = δ ^ (ω + α + 2 * η + η) * δ ^ (-4 * α) := by
          rw [← Real.rpow_add hδ]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hδ.le _)
    apply (ENNReal.ofReal_le_ofReal ?_).trans hgain
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoefficient hκ.le)
        (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity))
      (Real.rpow_nonneg (show 0 ≤ (n : ℝ) * δ by positivity) (-σ))
    simpa only [mul_assoc] using hh

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
