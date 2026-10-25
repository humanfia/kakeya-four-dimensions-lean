-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedCappedCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedExactCover
import Submission.WZ.Obl.wz_broad_grains_improvement.PrismSelectionCaps

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- The aligned exact-cover step preserves normalized incidence caps as well
as prism density. It only selects entire prism labels and changes their width. -/
theorem aligned_exact_capped_prism_cover {ω ζ τ ε : ℝ}
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
        D.Valid ω ζ d h ρ c x v Y 0 → D.HasCaps d h ρ c →
        ∃ ρ' : ℝ, ρ ≤ ρ' ∧ ∃ D' : PrismData n,
          D'.Valid ω ζ d ε ρ' c x v Y 1 ∧ D'.HasCaps d ε ρ' c ∧ PrismSelection D D' := by
  obtain ⟨η, d₀, hη, hηε, hd₀, hd₀small, Hcover⟩ :=
    aligned_exact_prism_cover_data hτ hτ1 hβ hβ1 hε
  refine ⟨η, d₀, hη, hηε, hd₀, hd₀small, ?_⟩
  intro d h n x v Y u t hd hdd hh hhη hA hcap hmid halign ρ c hbase D HD Hcaps
  obtain ⟨ρ', hρ', hbudget, D', HD', hsel⟩ :=
    Hcover hd hdd hh hhη hA hcap hmid halign ρ c hbase D HD
  have ha : 0 ≤ D.a := hd.le.trans HD.1
  have hc : 0 ≤ c := ha.trans (HD.2.1.trans HD.2.2.1)
  have hρ : 0 ≤ ρ := (Real.rpow_pos_of_pos hd _).le.trans hbase
  exact ⟨ρ', hρ', D', HD', caps_of_prism_selection hd ha hc hρ (hρ.trans hρ') hbudget hsel Hcaps, hsel⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
