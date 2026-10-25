/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeTable.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeFloors
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.PredictorCells
import Submission.Obl.k4_scalar_initial_true_horizon.Basic

/-! Genuine true affine entries have bounded nonconstant coefficients at every
subcritical horizontal rate. The time-ratio and original-witness arguments adapt
this LOT tree, o245/x0852, NativeAssignments.lean, a80fc09b; the slope estimate
itself is imported from accepted o226. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_critical_intercept_concentration

noncomputable section

namespace Data

open Submission.Obl.k4_critical_intercept_concentration.Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem Prepared.native_hidden_time_ratios (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (hs : 0 ≤ s) :
    cfg.N k ^ (-s) / cfg.timeLength k s ≤ cfg.K k ∧
      cfg.N k ^ (-s) / cfg.timeLength k s ^ 2 ≤ cfg.K k ^ 2 := by
  have hN : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hNp : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  let g := cfg.N k ^ (-cfg.κ * s)
  have hg : 0 < g := Real.rpow_pos_of_pos hNp _
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by
    nlinarith [h.rate_pos])
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hcmp : g ≤ cfg.K k * cfg.timeLength k s :=
    (time_length_comparison hNp hK a.time_lower a.time_upper).2
  have ha : cfg.N k ^ (-s) ≤ g ^ 2 := by
    rw [show g ^ 2 = cfg.N k ^ (-cfg.κ * s + -cfg.κ * s) by
      rw [pow_two, Real.rpow_add hNp]]
    exact Real.rpow_le_rpow_of_exponent_le hN (by nlinarith [h.subcritical_rate])
  constructor
  · apply (div_le_iff₀ hq).mpr
    exact ha.trans ((by nlinarith [sq_nonneg g] : g ^ 2 ≤ g).trans hcmp)
  · apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
    exact ha.trans (by nlinarith [sq_nonneg (cfg.K k * cfg.timeLength k s - g)])

theorem Prepared.native_base_position_bound (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (l : α) (hl : l ∈ cfg.A k s i)
    {t : ℝ} (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
    |(cfg.x k l t) 1| ≤ 3 * cfg.K k := by
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  have htime := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) ht
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg htime.1]; exact htime.2
  have hq : cfg.timeLength k s ≤ 1 := by
    unfold timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hm : |t * cfg.c k s i 1| ≤ cfg.K k := by
    rw [abs_mul]
    exact (mul_le_mul ht1 (a.coefficient_bound i 1) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _ = |((cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1) +
        cfg.c k s i 0 + t * cfg.c k s i 1| := by congr 1; ring
    _ ≤ |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| +
        |cfg.c k s i 0| + |t * cfg.c k s i 1| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ cfg.K k * cfg.timeLength k s + cfg.K k + cfg.K k :=
      add_le_add (add_le_add (a.geometry i l hl t ht).1 (a.coefficient_bound i 0)) hm
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hq hK]

/-- Choose each entry using its original witness. No retained chart intersection
is used as its nonemptiness or coefficient certificate. -/
theorem Prepared.native_affine_table (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (hs : 0 ≤ s)
    (hμ : ∀ i, ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    ∃ L : Fin (cfg.n k s) → Fin 4 → ℝ,
      (∀ i, ∀ e : Fin 3, |L i e.succ| ≤ 36 * cfg.K k ^ 4) ∧
      ∀ i, cfg.F k s i = X (3 : Fin 4) -
        (C (L i 0) + C (L i 1) * X (0 : Fin 4) + C (L i 2) * X (1 : Fin 4) +
          C (L i 3) * X (2 : Fin 4)) ∧
        ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
          |cfg.b k l 2 + t * cfg.b k l 5 - (L i 0 + L i 1 * t +
            L i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
            L i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * cfg.N k ^ (-s) := by
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hq1 : cfg.timeLength k s ≤ 1 := by
    unfold timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hratios := h.native_hidden_time_ratios a hs
  have hex : ∀ i : Fin (cfg.n k s), ∃ L : Fin 4 → ℝ,
      (∀ e : Fin 3, |L e.succ| ≤ 36 * cfg.K k ^ 4) ∧
      cfg.F k s i = X (3 : Fin 4) -
        (C (L 0) + C (L 1) * X (0 : Fin 4) + C (L 2) * X (1 : Fin 4) + C (L 3) * X (2 : Fin 4)) ∧
      ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |cfg.b k l 2 + t * cfg.b k l 5 - (L 0 + L 1 * t +
          L 2 * (cfg.b k l 0 + t * cfg.b k l 3) + L 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤
            cfg.K k * cfg.N k ^ (-s) := by
    intro i
    have hpositive : 0 < cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) :=
      (ENNReal.ofReal_pos.mpr (by positivity)).trans_le (h.native_witness_lower a hμ i)
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hpositive.ne'
    obtain ⟨L, hF, hvertical, hrow⟩ := a.affine_entry i
    have htime := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
      (cfg.T k s) (cfg.j k s i) hp.2
    have hbase := h.native_base_position_bound a i p.1 (a.fitted_subset i hp.1) hp.2
    have hcoef := Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.horizontal_affine_coeff_bounds L
      (by linarith : 1 ≤ 3 * cfg.K k) (by positivity : 0 ≤ cfg.N k ^ (-s)) hq hq1 hbase htime
      (hvertical.trans (by gcongr; linarith : cfg.K k * (1 + cfg.N k ^ (-s) / cfg.timeLength k s ^ 2) ≤
        (3 * cfg.K k) * (1 + cfg.N k ^ (-s) / cfg.timeLength k s ^ 2)))
      ((hrow p.1 hp.1 p.2 hp.2).trans (by gcongr; linarith))
    have hbound : 2 * (3 * cfg.K k) ^ 2 * (1 + cfg.N k ^ (-s) / cfg.timeLength k s ^ 2) ≤
        36 * cfg.K k ^ 4 := by
      have hsq : 1 ≤ cfg.K k ^ 2 := one_le_pow₀ hK
      have hh := mul_le_mul_of_nonneg_left (add_le_add_left hratios.2 1)
        (show 0 ≤ 2 * (3 * cfg.K k) ^ 2 by positivity)
      nlinarith [sq_nonneg (cfg.K k ^ 2 - 1)]
    refine ⟨L, ?_, hF, ?_⟩
    · intro e
      fin_cases e
      · exact hcoef.1.trans hbound
      · exact hcoef.2.1.trans hbound
      · exact hcoef.2.2.trans hbound
    · intro l hl t ht
      have hf := (a.fitted i l hl t ht).1
      rw [hF] at hf
      simpa [x] using hf
  choose L hL hF hfit using hex
  exact ⟨L, hL, fun i => ⟨hF i, hfit i⟩⟩

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
