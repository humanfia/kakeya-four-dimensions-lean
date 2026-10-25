-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.Initialization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitGrains
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketGain
import Submission.WZ.Obl.wz_broad_grains_initialization.UnitBroad

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (A bodyCount)
open wz_ad_dichotomy_from_separated (exists_power_bound exists_monomial_bound)

/-- The broad/narrow packet dichotomy gives the complete initial-state
alternative. The narrow case uses the rescaled estimate; the broad case
uses the elementary scale-one grain construction. -/
theorem initialization {σ ω : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2)
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : wz_clustered_cover_volume_gain.Parent.Interfaces.E σ ω)
    {ζ ε : ℝ} (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000) (hε : 0 < ε) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
        ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i) ∨
          ∃ ρ c : ℝ, State ω ζ δ ε ρ c n x v Y false := by
  let β : ℝ := ω * ζ / 100
  have hβ : 0 < β := by dsimp [β]; positivity
  have hζsmall : ζ ≤ 1 / 1000 := by linarith
  have hβω : β ≤ ω / 2 := by dsimp [β]; nlinarith
  have hβ1 : β ≤ 1 := by linarith
  let e : ℝ := min (ε / 2) β
  have he : 0 < e := lt_min (by positivity) hβ
  have heε : e ≤ ε / 2 := min_le_left _ _
  let c₀ : ℝ := e / (2 * β)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  let α : ℝ := c₀ * (ω - β) / 4
  have hα : 0 < α := by
    dsimp [α]
    have : 0 < ω - β := by linarith
    positivity
  obtain ⟨κ, hκ, η₀, hη₀, hgain⟩ := packet_gain hσ hσ2 hω hE α hα
  let η : ℝ := min (ε / 8) (min (1 / 16) (min (α / 4) (η₀ / 4)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η ≤ ε / 8 := min_le_left _ _
  have hηsmall : η ≤ 1 / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hηα : η ≤ α / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηη₀ : η ≤ η₀ / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηbudget : η ≤ min (ε / 8) (1 / 16) := le_min hηε hηsmall
  obtain ⟨dg, hdg, _, hgrains⟩ := unit_scale_grains_of_broad hε
  obtain ⟨dp, hdp, _, hpackets⟩ := measurable_angular_packets_power hβ hβ1 hη
  obtain ⟨db, hdb, _, hbroad⟩ := exists_power_bound 2 (by linarith : 0 < e / 2)
  obtain ⟨dc, hdc, _, hcarrier⟩ := exists_power_bound 8 hc₀
  obtain ⟨dd, hdd, _, hdensity⟩ := exists_monomial_bound (2 * (2 * 6 ^ 3 * 22 ^ 3 : ℝ))
    (by linarith : η₀ / 2 < η₀)
  let d₀ : ℝ := min (1 / 100) (min dg (min dp (min db (min dc dd))))
  refine ⟨α, κ, η, d₀, hα, hκ, hη, by linarith, by dsimp [d₀]; positivity,
    min_le_left _ _, ?_⟩
  intro δ hδ hδd n x v Y hA
  have hd := hδd
  dsimp only [d₀] at hd
  simp only [le_min_iff] at hd
  obtain ⟨hδsmall, hδg, hδp, hδb, hδc, hδdensity⟩ := hd
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨θ, Z, P, a, hδθ, hθ1, hR, hmass⟩ := hpackets δ hδ hδp n v Y hA.1
    (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.2.1)
  by_cases hcase : δ ^ c₀ ≤ θ
  · right
    obtain ⟨c, hc⟩ := hgrains δ hδ hδg ω ζ η η e hω1 hηbudget hηbudget heε n x v Y Z hA
      hR.1 hmass (by
        intro p u r _ hr _
        exact hR.unit_broad hδ hβ hcase (hbroad δ hδ hδb) p u r hr)
    exact ⟨1, c, hc⟩
  · left
    have hθ : 0 < θ := hδ.trans_le hδθ
    have hθc : θ ≤ δ ^ c₀ := (lt_of_not_ge hcase).le
    have h8 : 8 * δ ^ c₀ ≤ 1 := by
      calc
        _ ≤ δ ^ (-c₀) * δ ^ c₀ :=
          mul_le_mul_of_nonneg_right (hcarrier δ hδ hδc) (Real.rpow_nonneg hδ.le _)
        _ = _ := by rw [← Real.rpow_add hδ]; simp
    have hθsmall : 8 * θ ≤ 1 := (mul_le_mul_of_nonneg_left hθc (by norm_num)).trans h8
    have hden : 2 * (2 * 6 ^ 3 * 22 ^ 3 : ℝ) * δ ^ η₀ ≤ δ ^ (η + η) := by
      exact (hdensity δ hδ hδdensity).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    have hg := hgain δ θ β η η hδ hδsmall hδθ hθsmall hβ.le hη.le n x v Y Z P a hA hR hmass hden
    have hscale : δ ^ (-4 * α) ≤ θ ^ (β - ω) := by
      calc
        _ = (δ ^ c₀) ^ (β - ω) := by
          rw [← Real.rpow_mul hδ.le]
          congr 1
          dsimp [α]
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos hθ hθc (by linarith)
    have hcoeff : δ ^ (ω - α) ≤ δ ^ (ω + α + 2 * η + η) * θ ^ (β - ω) := by
      calc
        _ ≤ δ ^ ((ω + α + 2 * η + η) + (-4 * α)) :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        _ = δ ^ (ω + α + 2 * η + η) * δ ^ (-4 * α) := Real.rpow_add hδ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hδ.le _)
    apply (ENNReal.ofReal_le_ofReal ?_).trans hg
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff hκ.le)
        (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity))
      (Real.rpow_nonneg (show 0 ≤ (n : ℝ) * δ by positivity) (-σ))
    simpa only [mul_assoc] using hh

end WangZahlLot.Obl.wz_broad_grains_initialization
