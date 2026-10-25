import Submission.Obl.k4_horizontal_strict_parameter_step.SelectedComparedLayer
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeFinePreparation
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMenuCount
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeProductComparison
import Submission.Obl.k4_horizontal_strict_parameter_step.ComparisonNumerics

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

attribute [local instance] sum_measurableSingletonClass

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- Actual matching, original witness pruning and native block selection
produce the comparison-prepared layer with its original full assignments. -/
theorem comparedLayer_of_matching {δ E M cutoff X ε₀ R₀ : ℝ}
    (fine : NativeFinePreparation cfg k s E c.D)
    (hbasic : cfg.Basic) (hN : 2 ≤ cfg.N k) (hK : 3 ≤ cfg.K k)
    (hd : 0 ≤ cfg.d) (hd1 : cfg.d ≤ 1) (hℓ : cfg.ℓ = cfg.κ)
    (hκ : 0 ≤ cfg.κ) (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s)
    (ha : c.a = cfg.N k ^ (-s)) (hslopes : c.M = 8 * cfg.K k ^ 4) (hεδ : c.ε ≤ δ)
    (ρ : Measure (α × ℝ)) (hσρ : σ ≤ ρ)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-c.ε)) ≤ σ univ)
    (p : MatchingScales cfg.d ε₀) (J : JetData)
    (hmb : MatchBound p.middle ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hX : 4 ≤ X) (hXR : R₀ ≤ X) (hXJ : 3 * J.C₂ ≤ X)
    (hXB : budgetMatchingConstant p J ≤ X) (hKX : 16 * cfg.K k ≤ X)
    (hbudget : (∑ i : c.Index, c.comparison.density (c.comparison.colour i)) ≤ X ^ 2)
    (hthreshold : M = 2 * c.comparison.error * X ^ p.size)
    (hAM : c.A ≤ M) (hM1 : 2 * M ≤ 1) (hcut : 0 < cutoff)
    (hreserve : ((100800 * cfg.K k * (M / c.a) ^ cfg.d) / cutoff) * cfg.N k ^ (-δ) +
      X ^ (-5 : ℝ) + cutoff * (∑ i : c.WitnessIndex, c.witnessWeight i) ≤ cfg.N k ^ (-c.ε))
    (hrow : 4 * (M / c.a) ≤ cfg.N k ^ δ)
    (hcount : 6 * (811008 * cfg.K k ^ 12) ≤ cfg.N k ^ δ) :
    Nonempty (ComparedLayer cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ρ δ c.D c.a
      (cfg.N k ^ (-E))) := by
  have hap : 0 < c.a := by rw [ha]; exact Real.rpow_pos_of_pos c.N_pos _
  have hAp : 0 < c.A := (Real.rpow_pos_of_pos c.N_pos _).trans_le c.width_lower
  have hMp : 0 < M := hAp.trans_le hAM
  have hXp : 0 < X := by linarith
  have hσ0 : σ univ ≠ 0 := ne_of_gt
    ((ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos c.N_pos _)).trans_le hmass)
  have hμ0 : cfg.μ k univ ≠ 0 := by
    intro hz
    exact hσ0 (le_antisymm ((c.dominated univ).trans_eq hz) bot_le)
  have hbad : σ (c.badOriginal M) ≤ ENNReal.ofReal (X ^ (-5 : ℝ)) := by
    simpa only [hthreshold] using
      c.matching_bad_mass p J hmb hR₀ hX hXR hXJ hXB hKX hd hd1 le_rfl hbudget
  have hprod := c.native_product_comparison M
  have hmenu := native_original_menu_counting α cfg k s σ c hbasic fine.parent hμ0
    ha hd hd1 M cutoff hAM hM1 hcut hprod
  let F := (100800 * cfg.K k * (M / c.a) ^ cfg.d) / cutoff
  have hF : 0 < F := by
    have hpow := Real.rpow_pos_of_pos (div_pos hMp hap) cfg.d
    dsimp [F]
    have hKp : 0 < cfg.K k := by linarith
    positivity
  obtain ⟨choice, hchoice, τ, hτgood, hselected, hτcover⟩ :=
    c.select_native_blocks fine.parent hbasic hmenu hF.le
  have hτ : τ ≤ σ := hτgood.trans (c.goodLaw_le M cutoff)
  have hw : 0 ≤ ∑ i : c.WitnessIndex, c.witnessWeight i :=
    Finset.sum_nonneg (fun i _ => c.witnessWeight_nonneg hap.le i)
  let loss := X ^ (-5 : ℝ) + cutoff * ∑ i : c.WitnessIndex, c.witnessWeight i
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  have htotal : ENNReal.ofReal (cfg.N k ^ (-c.ε)) ≤
      ENNReal.ofReal F * τ univ + ENNReal.ofReal loss := by
    calc
      _ ≤ σ univ := hmass
      _ ≤ c.goodLaw M cutoff univ + σ (c.badOriginal M) +
          ENNReal.ofReal (cutoff * ∑ i : c.WitnessIndex, c.witnessWeight i) :=
        c.goodLaw_mass hap.le M hcut.le
      _ ≤ ENNReal.ofReal F * τ univ + ENNReal.ofReal (X ^ (-5 : ℝ)) +
          ENNReal.ofReal (cutoff * ∑ i : c.WitnessIndex, c.witnessWeight i) :=
        add_le_add (add_le_add hselected hbad) le_rfl
      _ = _ := by
        dsimp only [loss]
        rw [ENNReal.ofReal_add (Real.rpow_nonneg hXp.le _) (mul_nonneg hcut.le hw)]
        ac_rfl
  have hτmass : ENNReal.ofReal (cfg.N k ^ (-δ)) ≤ τ univ :=
    retained_mass_of_budget hF hloss (by simpa only [F, loss, add_assoc] using hreserve) htotal
  exact c.comparedLayer_of_selected fine.parent fine.grid fine.child fine.affine choice hchoice
    fine.event fine.measurable_event fine.event_prop fine.nested ρ τ hσρ hτ hτmass
    (ae_mono (hτ.trans c.dominated) fine.conull) hτcover
    (hbasic k).2.1 hN hK hd hℓ hκ hκ1 hs ha hslopes hεδ (hbasic k).2.2.2.1
    fine.large fine.parameter_small fine.caps fine.contact_budget fine.spatial_budget
    hMp.le hprod hrow hcount

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
