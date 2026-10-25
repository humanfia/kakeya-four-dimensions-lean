-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.LocalPrismCapsPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.LocalPrismCaps
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicPower
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Budgets

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (PrismPiece)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (logarithmic_count_power)
open WangZahlLot.Obl.wz_normalized_projection_coarse_fine (exists_power_absorption)

/-- For polynomially many fine tubes, local capping consumes an arbitrarily
small error increment. No incidence-retention premise is required. -/
theorem capped_cut_of_good_prism_power {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ {n N J : ℕ} {ω ζ d h a c s : ℝ} {ρ : Fin J → ℝ}
        {x v : Fin n → V} {y w : Fin N → V},
      0 < d → d ≤ d₀ → h ≤ ε/2 → (n:ℝ) ≤ d^(-D) →
      ∀ Q : PrismPiece n N J, Q.Good ω ζ d h a c s ρ x v y w →
      ∃ C : Set V, MeasurableSet C ∧
        (cutPrismPiece Q C).Good ω ζ d ε a c s ρ x v y w ∧
        PrismPieceCap d ε a c ρ (cutPrismPiece Q C) := by
  obtain ⟨dL,hdL,HL⟩ := logarithmic_count_power hD (by positivity : 0<ε/4)
  obtain ⟨dC,hdC,HC⟩ := exists_power_absorption (C := 2) (p := ε/4) (r := 0)
    (by norm_num) (by positivity)
  refine ⟨min 1 (min dL dC),by positivity,min_le_left _ _,?_⟩
  intro n N J ω ζ d h a c s ρ x v y w hd hdd hh hn Q HQ
  have hd1 := hdd.trans (min_le_left _ _)
  have hlog := HL d hd (hdd.trans ((min_le_right _ _).trans (min_le_left _ _))) n hn
  have hconstant : 2*d^(ε/4) ≤ 1 := by
    simpa only [Real.rpow_zero] using HC d hd (hdd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  apply capped_cut_of_good_prism Q hd hd1 (by linarith) HQ
  calc
    _ ≤ 2*d^(-(ε/4))*d^ε := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hlog) (by norm_num)) (by positivity)
    _ = (2*d^(ε/4))*d^(ε/2) := by
      rw [mul_assoc,← Real.rpow_add hd,mul_assoc,← Real.rpow_add hd]
      congr 2
      ring
    _ ≤ d^(ε/2) := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hd.le (ε/2))
    _ ≤ d^h := Real.rpow_le_rpow_of_exponent_ge hd hd1 hh

end WangZahlLot.Obl.wz_broad_grains_improvement
