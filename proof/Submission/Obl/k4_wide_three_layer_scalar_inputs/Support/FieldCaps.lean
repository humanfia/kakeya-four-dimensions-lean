import Submission.Obl.k4_wide_three_layer_scalar_inputs.Field.CellBudget
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Caps
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Good
import Submission.Obl.k4_critical_conditional_row_preparation.PaletteCaps

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H R : ℝ}

/-- Every original true assignment has positive prior mass. -/
theorem true_assignment_ne_zero (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k)
    (hK : 0 < cfg.K k) (i : Fin (cfg.n k s)) : cfg.ν k (cfg.A k s i) ≠ 0 := by
  have hfloor : 0 < ENNReal.ofReal ((cfg.N k ^ (-s)) ^ cfg.d *
      (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 * cfg.N k ^ (-cfg.κ * s) / cfg.K k) := by
    apply ENNReal.ofReal_pos.mpr
    exact div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos
      (Real.rpow_pos_of_pos hN _) _) (by positivity)) (Real.rpow_pos_of_pos hN _)) hK
  exact (hfloor.trans_le (hB.nu_lo i)).ne'

namespace ComparedBlock

/-- The field base-cell ceiling, with the FULL original reference `q ν(A_i)`.
No mass of a surviving label or of an intersection replaces that reference. -/
theorem field_base_cell_cap (CB : ComparedBlock cfg k s u v χ H)
    (hcap : CapsAt cfg k R) (hB : BlocksAt cfg k s R)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hb : Measurable (cfg.b k))
    (hπ : IsProbabilityMeasure (cfg.π k)) (hρμ : cfg.ρ k ≤ cfg.μ k)
    (lam : Measure (α × ℝ)) (hlam : lam ≤ CB.lam)
    {δ r s' η Lb : ℝ} (hδ : 0 < δ) (hδg : δ ≤ CB.frame.g)
    (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hs1 : 0 ≤ s') (hs2 : s' ≤ R)
    (hR1 : R⁻¹ ≤ 1) (hR : 1 ≤ R) (hLb : ∀ e, |CB.L e| ≤ Lb)
    (ha' : 2 * cfg.K k * cfg.N k ^ (-s) ≤ cfg.N k ^ (-s'))
    (hmesh : (cfg.K k + cfg.K k ^ 2 + 1) * cfg.N k ^ (-r) ≤ CB.frame.q * δ / 2)
    (hlip : 3 * Lb * cfg.N k ^ (-r) ≤ cfg.N k ^ (-s'))
    (hbudget : 2250 * (cfg.K k) ^ 3 * (cfg.N k ^ (-s')) ^ cfg.d ≤
      cfg.N k ^ η * (cfg.N k ^ (-s)) ^ cfg.d) (Q : Fin 2 → ℤ) :
    lam {p | ⌊CB.frame.zt p.2 / δ⌋ = Q 0 ∧ ⌊CB.frame.zZ (cfg.b k p.1) p.2 / δ⌋ = Q 1} ≤
      ENNReal.ofReal (cfg.N k ^ η * δ ^ 2) *
        (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)) := by
  have hq : 0 < CB.frame.q := by dsimp [frame, blockFrame]; positivity
  have hg : 0 < CB.frame.g := Real.rpow_pos_of_pos hN _
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hac : lam ≪ CB.lam := Measure.absolutelyContinuous_of_le hlam
  have hgood := hac.ae_le CB.ae_good
  have hlamμ := hlam.trans (CB.lam_le.trans hρμ)
  calc _ ≤ lam {p | p.1 ∈ cfg.B k s CB.i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s CB.i) ∧
        ⌊CB.frame.zt p.2 / δ⌋ = Q 0 ∧ ⌊CB.frame.zZ (cfg.b k p.1) p.2 / δ⌋ = Q 1} := by
        apply measure_mono_ae
        filter_upwards [hgood] with p hp hcell
        exact ⟨hp.B, hp.I, hcell⟩
    _ ≤ cfg.μ k {p | p.1 ∈ cfg.B k s CB.i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s CB.i) ∧
        ⌊CB.frame.zt p.2 / δ⌋ = Q 0 ∧ ⌊CB.frame.zZ (cfg.b k p.1) p.2 / δ⌋ = Q 1} := hlamμ _
    _ ≤ ENNReal.ofReal (6000 * cfg.K k * (CB.frame.q * δ / 2) * (CB.frame.q * δ / 2) *
        (cfg.K k * CB.frame.q * CB.frame.g + cfg.K k * (CB.frame.q * δ / 2)) *
        (cfg.N k ^ (-s')) ^ cfg.d) :=
        block_cell_cap hcap hB hN hK hb hπ CB.i CB.L CB.hL hLb hδ hr1 hr2 hs1 hs2 hR1 hR
          ha' hmesh hlip Q
    _ ≤ _ := Field.cell_cap_full_reference hKp hq.le hg.le hδ.le hδg
      (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg (Real.rpow_nonneg hN.le _) _)
      (Real.rpow_nonneg (Real.rpow_nonneg hN.le _) _) hbudget (hB.nu_lo CB.i)

end ComparedBlock

/-- The palette part of the frozen caps supplies precisely the field's
interval bound; only the positive exponent range is required. -/
theorem field_frostman_from_caps (hcap : CapsAt cfg k R)
    [IsProbabilityMeasure (cfg.π k)] (hN : 1 < cfg.N k) (hK : 0 ≤ cfg.K k)
    (hS : 0 < cfg.S) {m v₀ η : ℝ} (hv₀ : 0 < v₀) (hv₀m : v₀ ≤ m)
    (hv₀η : v₀ * cfg.S ≤ η) (hKη : 4 * cfg.K k ≤ cfg.N k ^ η)
    (hRv₀ : R⁻¹ ≤ v₀) (hmR : m ≤ R) (hR1 : R⁻¹ ≤ 1) (hR : 1 ≤ R) :
    ∀ x r : ℝ, cfg.N k ^ (-m) ≤ r → r ≤ 1 →
      cfg.π k (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (cfg.N k ^ η * r ^ cfg.S) := by
  apply interval_cap_from_power_grid_caps (cfg.π k) (cfg.N k) (cfg.K k) cfg.S m v₀ η
    hN hK hS hv₀ hv₀m hv₀η hKη
  intro w hw1 hw2 j
  exact (hcap 1 0 w hR1 hR le_rfl (zero_le_one.trans hR)
    (hRv₀.trans hw1) (hw2.trans hmR)).1 j

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
