-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedPrismBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedPrismStage
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.DyadicDepth

namespace WangZahlLot.Obl.wz_broad_grains_improvement

/-- Every fixed cost of the aligned prism cover is absorbed by half the error
budget, uniformly over smaller input errors. -/
theorem aligned_prism_stage_budgets (β ε : ℝ) (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ d h : ℝ, 0 < d → d ≤ d₀ → h ≤ ε/2 →
        alignedGridCost*d^ε ≤ d^h ∧ 10000*d^ε ≤ d^h ∧
          d^(-h)*(10000:ℝ)^β ≤ d^(-ε) := by
  let C := max alignedGridCost (max 10000 ((10000:ℝ)^β))
  have hC : 0 < C := alignedGridCost_pos.trans_le (le_max_left _ _)
  obtain ⟨d₁, hd₁, hsmall⟩ := WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.power_absorption
    C (show 0 < ε/2 by positivity)
  refine ⟨min d₁ 1, by positivity, min_le_right _ _, ?_⟩
  intro d h hd hdd hh
  have hd1 : d ≤ 1 := hdd.trans (min_le_right _ _)
  have hc := hsmall d hd (hdd.trans (min_le_left _ _))
  have hp : C*d^ε ≤ d^h := by
    calc
      C*d^ε = (C*d^(ε/2))*d^(ε/2) := by
        rw [mul_assoc, ← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ 1*d^(ε/2) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ d^h := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_ge hd hd1 hh
  refine ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hp,
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)).trans hp,
    ?_⟩
  have hangle : (10000:ℝ)^β*d^ε ≤ d^h :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
      (by positivity)).trans hp
  have hdε : 0 < d^ε := Real.rpow_pos_of_pos hd _
  have hdh : 0 < d^h := Real.rpow_pos_of_pos hd _
  rw [Real.rpow_neg hd.le, Real.rpow_neg hd.le]
  rw [inv_mul_eq_div, inv_eq_one_div]
  apply (div_le_div_iff₀ hdh hdε).mpr
  simpa using hangle


/-- At sufficiently small fine scale, the aligned stage-zero-to-one step needs
no hypotheses beyond alignment and the old prism data. -/
theorem aligned_prism_stage_one_small (ω ζ ε : ℝ) (hβ : 0 ≤ ω*ζ/100) (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ {d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {u : V} {t : ℝ},
      0 < d → d ≤ d₀ → 0 ≤ h → h ≤ ε/2 → 0 < ρ → ρ ≤ 1/100000000 →
      (∀ i, ‖v i‖ = 1) → (∀ i, ‖v i-u‖ ≤ 1/10) →
      (∀ i, ‖WangZahlLot.Obl.wz_multiscale_finite_tower.axisMidpoint (x i) (v i)‖ ≤ 1) →
      (∀ i, inner ℝ (v i) (WangZahlLot.Obl.wz_multiscale_finite_tower.axisMidpoint (x i) (v i)) = t) →
      (∀ i, μ (Y i) ≠ ⊤) → 0 < ∑ i, MeasureTheory.volume.real (Y i) →
      WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ d h ρ c n x v Y 0 →
      WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ d ε (10000*ρ) c n x v Y 1 := by
  obtain ⟨d₀, hd₀, hd₀1, hb⟩ := aligned_prism_stage_budgets (ω*ζ/100) ε hε
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro d h ρ c n x v Y u t hd hdd hh hhε hρ hρsmall hunit hcap hmid halign hYfin hYpos hG
  obtain ⟨hretain, hdensity, hbroad⟩ := hb d h hd hdd hhε
  exact aligned_prism_stage_one hd (hdd.trans hd₀1) hh hβ hρ hρsmall
    hretain hdensity hbroad hunit hcap hmid halign hYfin hYpos hG

end WangZahlLot.Obl.wz_broad_grains_improvement
