import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeDens

set_option linter.unusedVariables false

/-!
# The palette sums of the coefficient agreement

The palette weight of the target classes near one source cell, the sources of a compared block
and their total cap.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H R : ℝ}

theorem isProbabilityMeasure_paletteBins (π : Measure ℝ) [IsProbabilityMeasure π] (δ : ℝ) :
    IsProbabilityMeasure (paletteBins π δ) := by
  unfold paletteBins; infer_instance

namespace ComparedBlock

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable (CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams)

open scoped Classical in
/-- **Palette weight near a source cell.** -/
theorem near_sum_le (hπ : IsProbabilityMeasure (cfg.π k)) (hχ : 0 < χ) (hH : 0 ≤ H) {ρN : ℝ}
    (hρN : 0 ≤ ρN) (δv : ℝ) (sr : CB.Γ × ℤ) (c : ℤ) :
    ∑ γ' ∈ Finset.univ.filter (fun γ' => CB.Near P ρN sr c γ'),
      paletteBins (cfg.π k) δv (Vt δv χ (CB.chartOf γ').1) ≤
      ENNReal.ofReal (2 * H * (2 * ρN / χ + 1)) := by
  have := isProbabilityMeasure_paletteBins (cfg.π k) δv
  convert sum_window_charts_le CB.chartOf CB.G hH CB.G_card
    (fun ch => |((ch.2 : ℝ) + 1 / 2) * χ -
      (CB.x1ref P sr.1 c - CB.refT P c * ((ch.1 : ℝ) + 1 / 2) * χ)| ≤ ρN) hχ hρN
    (fun n => CB.x1ref P sr.1 c - CB.refT P c * ((n : ℝ) + 1 / 2) * χ) (fun n m h => h)
    (paletteBins (cfg.π k) δv) δv using 3
  simp only [Near]

/-- Charts meeting the block. -/
def blockCh (ch : ℤ × ℤ) : Prop :=
  |((ch.2 : ℝ) + 1 / 2) * χ - (CB.frame.c 0 + CB.frame.t₀ * CB.frame.c 1 -
    CB.frame.t₀ * ((ch.1 : ℝ) + 1 / 2) * χ)| ≤ cfg.K k * CB.frame.q + 2 * χ

open scoped Classical in
/-- The coefficient classes of the block. -/
def ΓF : Finset CB.Γ := Finset.univ.filter (fun γ => CB.blockCh (CB.chartOf γ) ∧ γ ∈ CB.G (CB.chartOf γ))

open scoped Classical in
/-- The sources of the block. -/
def SrcF : Finset (CB.Γ × ℤ) :=
  (CB.ΓF.sigma (fun γ => CB.F1 (CB.chartOf γ) γ)).map
    ⟨fun x => (x.1, x.2), fun x y h => by
      obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl⟩

/-- Good incidences have their source among the sources of the block. -/
theorem good_src_mem (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hL : HorizontalForm (cfg.F k s CB.i) CB.L) (hχ : 0 < χ) {p : α × ℝ} (hp : CB.Good p) :
    CB.src p ∈ CB.SrcF := by
  classical
  have hch := hp.chart
  simp only [chart] at hch
  set n := (CB.chartOf (CB.cls p)).1
  set m := (CB.chartOf (CB.cls p)).2
  have hn : ⌊cfg.b k p.1 3 / χ⌋ = n := by simp only [n, cls]; rw [← hch]
  have hm : ⌊cfg.b k p.1 0 / χ⌋ = m := by simp only [m, cls]; rw [← hch]
  have e1 := abs_sub_center_of_floor hχ hn
  have e2 := abs_sub_center_of_floor hχ hm
  -- the line at the block start
  have hA : p.1 ∈ cfg.A k s CB.i := (hB.sets CB.i).2.2 hp.B
  have ht₀ : CB.frame.t₀ ∈ Data.I (cfg.T k s) (cfg.j k s CB.i) := by
    simp only [frame, blockFrame, Data.I, mem_Icc]
    exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  obtain ⟨hx, -, -⟩ := hB.geom CB.i p.1 hA _ ht₀
  simp only [x_one] at hx
  have ht01 : 0 ≤ CB.frame.t₀ ∧ CB.frame.t₀ ≤ 1 := I_subset_unit ht₀
  have hblk : CB.blockCh (n, m) := by
    simp only [blockCh]
    have e : ((m : ℝ) + 1 / 2) * χ - (CB.frame.c 0 + CB.frame.t₀ * CB.frame.c 1 -
        CB.frame.t₀ * ((n : ℝ) + 1 / 2) * χ) =
        (cfg.b k p.1 0 + CB.frame.t₀ * cfg.b k p.1 3 - cfg.c k s CB.i 0 - CB.frame.t₀ * cfg.c k s CB.i 1) -
        (cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)) - CB.frame.t₀ * (cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)) := by
      simp only [frame, blockFrame]; ring
    rw [e]
    have ht0' : |CB.frame.t₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht01.1], ht01.2⟩
    calc _ ≤ |cfg.b k p.1 0 + CB.frame.t₀ * cfg.b k p.1 3 - cfg.c k s CB.i 0 - CB.frame.t₀ * cfg.c k s CB.i 1| +
          |cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)| + |CB.frame.t₀| * |cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)| := by
          have := abs_sub (cfg.b k p.1 0 + CB.frame.t₀ * cfg.b k p.1 3 - cfg.c k s CB.i 0 -
            CB.frame.t₀ * cfg.c k s CB.i 1 - (cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)))
            (CB.frame.t₀ * (cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)))
          have := abs_sub (cfg.b k p.1 0 + CB.frame.t₀ * cfg.b k p.1 3 - cfg.c k s CB.i 0 -
            CB.frame.t₀ * cfg.c k s CB.i 1) (cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2))
          rw [abs_mul] at *
          linarith
      _ ≤ cfg.K k * CB.frame.q + χ / 2 + 1 * (χ / 2) := by gcongr; exact hx
      _ ≤ cfg.K k * CB.frame.q + 2 * χ := by linarith
  have hch' : CB.chart p = CB.chartOf (CB.cls p) := hp.chart
  simp only [SrcF, Finset.mem_map, Finset.mem_sigma, ΓF, Finset.mem_filter, Finset.mem_univ,
    true_and]
  refine ⟨⟨CB.cls p, ⌊CB.D1 (CB.lab p.1) / cfg.N k ^ (-u)⌋⟩, ⟨⟨hblk, ?_⟩, ?_⟩, rfl⟩
  · have := hp.coarse; rw [hch'] at this; exact this
  · have := hp.off1; rw [hch'] at this; exact this

open scoped Classical in
/-- **The total cap of the sources.** -/
theorem src_cap_sum_le (hπ : IsProbabilityMeasure (cfg.π k)) (hχ : 0 < χ) (hH : 0 ≤ H)
    (hK : 0 ≤ cfg.K k) (hq : 0 < CB.frame.q) (r s' v' : ℝ) :
    ∑ sr ∈ CB.SrcF, CB.capcell P r s' v' sr ≤
      ENNReal.ofReal (6000 * cfg.K k * (CB.frame.q * P.δt / 2) * χ *
        (CB.frame.q * CB.frame.g * P.δU / 2 + cfg.K k * χ) * (cfg.N k ^ (-s')) ^ cfg.d) *
      (ENNReal.ofReal (H * cfg.N k ^ (cfg.d * u)) *
        ENNReal.ofReal (2 * H * (2 * (cfg.K k * CB.frame.q + 2 * χ) / χ + 1))) := by
  have := isProbabilityMeasure_paletteBins (cfg.π k) (cfg.N k ^ (-v'))
  set cc := ENNReal.ofReal (6000 * cfg.K k * (CB.frame.q * P.δt / 2) * χ *
        (CB.frame.q * CB.frame.g * P.δU / 2 + cfg.K k * χ) * (cfg.N k ^ (-s')) ^ cfg.d)
  have h1 : ∑ sr ∈ CB.SrcF, CB.capcell P r s' v' sr ≤
      ∑ γ ∈ CB.ΓF, ∑ d ∈ CB.F1 (CB.chartOf γ) γ, CB.capcell P r s' v' (γ, d) := by
    rw [SrcF, Finset.sum_map, Finset.sum_sigma]
    rfl
  have h2 : ∀ γ, ∑ d ∈ CB.F1 (CB.chartOf γ) γ, CB.capcell P r s' v' (γ, d) ≤
      ENNReal.ofReal (H * cfg.N k ^ (cfg.d * u)) *
        (cc * paletteBins (cfg.π k) (cfg.N k ^ (-v')) (Vt (cfg.N k ^ (-v')) χ (CB.chartOf γ).1)) := by
    intro γ
    simp only [capcell, Finset.sum_const, nsmul_eq_mul]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (CB.F1_card _ _)
  have h3 := sum_window_charts_le CB.chartOf CB.G hH CB.G_card
    (fun ch => |((ch.2 : ℝ) + 1 / 2) * χ - (CB.frame.c 0 + CB.frame.t₀ * CB.frame.c 1 -
      CB.frame.t₀ * ((ch.1 : ℝ) + 1 / 2) * χ)| ≤ cfg.K k * CB.frame.q + 2 * χ) hχ
    (by positivity : 0 ≤ cfg.K k * CB.frame.q + 2 * χ)
    (fun n => CB.frame.c 0 + CB.frame.t₀ * CB.frame.c 1 - CB.frame.t₀ * ((n : ℝ) + 1 / 2) * χ)
    (fun n m h => h) (paletteBins (cfg.π k) (cfg.N k ^ (-v'))) (cfg.N k ^ (-v'))
  calc _ ≤ _ := h1
    _ ≤ ∑ γ ∈ CB.ΓF, ENNReal.ofReal (H * cfg.N k ^ (cfg.d * u)) *
          (cc * paletteBins (cfg.π k) (cfg.N k ^ (-v')) (Vt (cfg.N k ^ (-v')) χ (CB.chartOf γ).1)) :=
        Finset.sum_le_sum fun γ _ => h2 γ
    _ = cc * (ENNReal.ofReal (H * cfg.N k ^ (cfg.d * u)) * ∑ γ ∈ CB.ΓF,
          paletteBins (cfg.π k) (cfg.N k ^ (-v')) (Vt (cfg.N k ^ (-v')) χ (CB.chartOf γ).1)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro γ _; ring
    _ ≤ _ := by
        gcongr
        exact h3

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
