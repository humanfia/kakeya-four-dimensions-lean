-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedExactCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedPrismBudget
import Submission.WZ.Obl.wz_broad_grains_improvement.UnitPrismCover
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.ShortLength
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RealMass

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (G)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData G_iff_data)

/-- The exact-cover step for aligned families, at every angular scale separated
from the fine scale by a fixed power. The grain length is preserved exactly. -/
theorem aligned_exact_prism_cover_data {ω ζ τ ε : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hβ : 0 < ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1)
    (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {u : V} {t : ℝ},
      0 < d → d ≤ d₀ → 0 ≤ h → h ≤ η →
      A d h (d^(-h)) (d^(-h)) n x v Y →
      (∀ i, ‖v i-u‖ ≤ 1/10) →
      (∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1) →
      (∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = t) →
      ∀ ρ c : ℝ, d^(1-τ) ≤ ρ → ∀ D : PrismData n,
        D.Valid ω ζ d h ρ c x v Y 0 →
        ∃ ρ' : ℝ, ρ ≤ ρ' ∧ d^ε*ρ' ≤ d^h*ρ ∧
          ∃ D' : PrismData n, D'.Valid ω ζ d ε ρ' c x v Y 1 ∧ PrismSelection D D'  := by
  obtain ⟨dA, hdA, hdA1, hbudgets⟩ := aligned_prism_stage_budgets (ω*ζ/100) ε hε
  obtain ⟨dS, hdS, hdS1, hshort⟩ :=
    WangZahlLot.Obl.wz_move_two_capped_prism_overlap.short_length_at_separated_scale hτ hτ1 hβ hβ1
  obtain ⟨dC, hdC, hc⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (show 0 < τ*(ω*ζ/100)/8 by positivity) (show 0 < (1/40:ℝ) by norm_num)
  obtain ⟨dB, hdB, hb⟩ := WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.power_absorption
    100000000 (show 0 < ε/2 by positivity)
  refine ⟨min (ε/2) (τ*(ω*ζ/100)/12), min dA (min dS (min dC (min dB (1/100)))),
    by positivity, (min_le_left _ _).trans (by linarith), by positivity,
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))), ?_⟩
  intro d h n x v Y u t hd hdd hh hhη hA hcap hmid halign ρ c hρbase D hG
  have hds : d ≤ dA ∧ d ≤ dS ∧ d ≤ dC ∧ d ≤ dB ∧ d ≤ 1/100 := by
    simpa only [le_min_iff] using hdd
  have hd1 : d ≤ 1 := hds.2.2.2.2.trans (by norm_num)
  have hhε : h ≤ ε/2 := hhη.trans (min_le_left _ _)
  have hhs : h ≤ τ*(ω*ζ/100)/12 := hhη.trans (min_le_right _ _)
  have hρ : 0 < ρ := (Real.rpow_pos_of_pos hd _).trans_le hρbase
  by_cases hrsmall : ρ ≤ 1/100000000
  · obtain ⟨hretain, hdensity, hbroad⟩ := hbudgets d h hd hds.1 hhε
    obtain ⟨D', hD', hsel⟩ := aligned_prism_stage_one_data hd hd1 hh hβ.le hρ hrsmall
      hretain hdensity hbroad (fun i => (hA.2.1 i).1) hcap hmid halign
      (WangZahlLot.Obl.wz_move_two_dense_broad_prisms.admissible_finite_mass hA)
      (WangZahlLot.Obl.wz_move_two_dense_broad_prisms.admissible_real_mass_pos hd hA) D hG
    refine ⟨10000*ρ, by linarith, ?_, D', hD', hsel⟩
    nlinarith [mul_le_mul_of_nonneg_right hdensity hρ.le]
  · have hcsmall : c ≤ 1/40 := (hshort d h hd hds.2.1 hhs n x v Y hA ρ c D 0 hG hρbase).le.trans
      (hc d hd hds.2.2.1)
    have hcost : 100000000*d^ε ≤ d^h := by
      calc
        _ = (100000000*d^(ε/2))*d^(ε/2) := by
          rw [mul_assoc, ← Real.rpow_add hd]
          congr 2
          ring
        _ ≤ 1*d^(ε/2) := mul_le_mul_of_nonneg_right (hb d hd hds.2.2.2.1) (by positivity)
        _ ≤ d^h := by
          rw [one_mul]
          exact Real.rpow_le_rpow_of_exponent_ge hd hd1 hhε
    let D₀ := raw_prism_of_valid D hG
    have hcp : 0 < c := hd.trans_le (D₀.shape.1.trans (D₀.shape.2.1.trans D₀.shape.2.2.1))
    have hr1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hcp).mp (by simpa using D₀.shape.2.2.1)
    have hrlarge : 1/100000000 ≤ ρ := (lt_of_not_ge hrsmall).le
    have hmass : 3*d^ε ≤ d^h := by nlinarith [Real.rpow_pos_of_pos hd ε]
    have hdense : d^ε ≤ d^h*ρ := by
      have hp := mul_le_mul_of_nonneg_left hrlarge (Real.rpow_nonneg hd.le h)
      nlinarith
    obtain ⟨D', hD', hsel⟩ := D₀.stage_one_at_one_data hd hd1 hh hβ.le hβ1 hcsmall
      (fun i => (hA.2.1 i).2.1) (fun i => (hA.2.1 i).2.2.2) hmass hdense
    exact ⟨1, hr1, by simpa using hdense, D', hD', hsel⟩

/-- The all-scale exact cover with its data-selection witnesses omitted. -/
theorem aligned_exact_prism_cover {ω ζ τ ε : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hβ : 0 < ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1)
    (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {u : V} {t : ℝ},
      0 < d → d ≤ d₀ → 0 ≤ h → h ≤ η →
      A d h (d^(-h)) (d^(-h)) n x v Y →
      (∀ i, ‖v i-u‖ ≤ 1/10) →
      (∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1) →
      (∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = t) →
      ∀ ρ c : ℝ, d^(1-τ) ≤ ρ → G ω ζ d h ρ c n x v Y 0 →
        ∃ ρ' : ℝ, ρ ≤ ρ' ∧ G ω ζ d ε ρ' c n x v Y 1 := by
  obtain ⟨η, d₀, hη, hηε, hd₀, hd₀small, Hcover⟩ :=
    aligned_exact_prism_cover_data hτ hτ1 hβ hβ1 hε
  refine ⟨η, d₀, hη, hηε, hd₀, hd₀small, ?_⟩
  intro d h n x v Y u t hd hdd hh hhη hA hcap hmid halign ρ c hbase hG
  obtain ⟨D, hD⟩ := G_iff_data.mp hG
  obtain ⟨ρ', hρ', _, D', hD', _⟩ := Hcover hd hdd hh hhη hA hcap hmid halign ρ c hbase D hD
  exact ⟨ρ', hρ', G_iff_data.mpr ⟨D', hD'⟩⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
