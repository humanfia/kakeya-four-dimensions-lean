/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeAssignments.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.Interface
import Submission.Obl.k4_critical_derivative_evaluation_lists.AffineEntries

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter

noncomputable section

/-- Reuse the accepted field-named native data without imposing its critical-rate
validity predicate. The interior problem has the same native assignments. -/
abbrev NativeModel (α : Type) [MeasurableSpace α] :=
  Submission.Obl.k4_critical_derivative_evaluation_lists.Data α

namespace NativeModel

open Submission.Obl.k4_critical_derivative_evaluation_lists

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Extraction of the full original assignments uses only the frozen atlas.
In particular, the accepted assignment structure makes sense below the critical rate. -/
theorem assignment_levels_on_range (ha : cfg.Atlas) (R : ℝ) (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → cfg.AssignmentLevel k s := by
  filter_upwards [ha R hR] with k hk
  intro s hRs hsU
  obtain ⟨htl, htu, hm, hd, he, hcov, hpal⟩ := hk s hRs hsU
  have hq : (2 : ℝ) ^ (-(cfg.T k s : ℤ)) = cfg.timeLength k s := by
    simp [Data.timeLength]
  refine {
    time_lower := htl
    time_upper := htu
    measurable := fun i => (hm i).1
    fitted_measurable := fun i => (hm i).2.1
    fitted_subset := fun i => (hm i).2.2
    disjoint := hd
    covers := hcov
    prior_lower := fun i => ?_
    prior_upper := fun i => ?_
    witness_lower := fun i => ?_
    coefficient_bound := fun i => (he i).2.2.2.1
    geometry := fun i => ?_
    fitted := fun i => (he i).2.2.2.2.2.2.1
    plane_center := fun i => ?_
    affine_entry := fun i => ?_
    native_hidden := fun i => ((he i).2.2.2.2.2.2.2.2 rfl).1
    horizontal_equation := fun i => ((he i).2.2.2.2.2.2.2.2 rfl).2.1 }
  · simpa only [hq] using (he i).1
  · simpa only [hq] using (he i).2.1
  · simpa only [hq] using (he i).2.2.2.2.2.1
  · simpa only [hq] using ((he i).2.2.2.2.2.2.2.2 rfl).2.2.1
  · simpa only [hq] using ((he i).2.2.2.2.2.2.2.2 rfl).2.2.2
  · simpa only [hq] using (he i).2.2.1

/-- The pointwise version is a specialization of the uniform compact-range
atlas extraction, which also permits sample-dependent finite depth grids. -/
theorem assignment_levels (ha : cfg.Atlas) {s : ℝ} (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, cfg.AssignmentLevel k s := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by dsimp [R]; have := inv_pos.mpr hs; linarith
  have hRs : R⁻¹ ≤ s := (inv_le_comm₀ (by linarith : 0 < R) hs).mpr (by dsimp [R]; linarith)
  filter_upwards [cfg.assignment_levels_on_range ha R hR] with k hk
  exact hk s hRs hsU

/-- The full original assignment prior has the same cubic time-volume floor
throughout the horizontal regime; the identity `2κ=1` is not needed. -/
theorem prior_bounds {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hν : IsProbabilityMeasure (cfg.ν k)) (hN : 0 < cfg.N k) (hK : 0 < cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ) (i : Fin (cfg.n k s)) :
    cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 ≤
        (cfg.ν k).real (cfg.A k s i) ∧
      (cfg.ν k).real (cfg.A k s i) ≤
        cfg.K k ^ 2 * cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d := by
  letI := hν
  have hlo := ENNReal.toReal_mono (measure_ne_top (cfg.ν k) _) (a.prior_lower i)
  have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top (a.prior_upper i)
  rw [ENNReal.toReal_ofReal (by positivity)] at hlo hhi
  change _ ≤ (cfg.ν k).real (cfg.A k s i) at hlo
  change (cfg.ν k).real (cfg.A k s i) ≤ _ at hhi
  rw [hℓ] at hlo hhi
  exact assignment_bounds_from_time_comparison hN hK a.time_lower a.time_upper hlo hhi

/-- The true affine slope estimates only need `2κ≤1`: the hidden width is
at most the square of the horizontal power scale. -/
theorem hidden_time_ratios {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hN : 1 ≤ cfg.N k) (hK : 0 < cfg.K k) (hκ : 0 ≤ cfg.κ)
    (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s) :
    cfg.N k ^ (-s) / cfg.timeLength k s ≤ cfg.K k ∧
      cfg.N k ^ (-s) / cfg.timeLength k s ^ 2 ≤ cfg.K k ^ 2 := by
  have hNp : 0 < cfg.N k := zero_lt_one.trans_le hN
  let g := cfg.N k ^ (-cfg.κ * s)
  have hg : 0 < g := Real.rpow_pos_of_pos hNp _
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hcmp : g ≤ cfg.K k * cfg.timeLength k s :=
    (time_length_comparison hNp hK a.time_lower a.time_upper).2
  have ha : cfg.N k ^ (-s) ≤ g ^ 2 := by
    rw [show g ^ 2 = cfg.N k ^ (-cfg.κ * s + -cfg.κ * s) by
      rw [pow_two, Real.rpow_add hNp]]
    exact Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  constructor
  · apply (div_le_iff₀ hq).mpr
    exact ha.trans ((by nlinarith [sq_nonneg g] : g ^ 2 ≤ g).trans hcmp)
  · apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
    exact ha.trans (by nlinarith [sq_nonneg (cfg.K k * cfg.timeLength k s - g)])

/-- Every true entry has a nonempty earlier full-domain witness, without
requiring anything about a later restricted incidence law. -/
theorem witness_nonempty {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hN : 0 < cfg.N k) (hK : 0 < cfg.K k) (i : Fin (cfg.n k s)) :
    (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)).Nonempty := by
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hprior : 0 < cfg.ν k (cfg.A k s i) :=
    (ENNReal.ofReal_pos.mpr (by positivity)).trans_le (a.prior_lower i)
  apply nonempty_of_measure_ne_zero
  apply ne_of_gt
  apply lt_of_lt_of_le _ (a.witness_lower i)
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (div_pos hq hK)).ne' hprior.ne'

/-- Actual true assignments give bounded horizontal positions throughout their block. -/
theorem base_position_bound {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hK : 0 ≤ cfg.K k) (i : Fin (cfg.n k s)) (l : α) (hl : l ∈ cfg.A k s i)
    {t : ℝ} (ht : t ∈ Data.I (cfg.T k s) (cfg.j k s i)) :
    |(cfg.x k l t) 1| ≤ 3 * cfg.K k := by
  have htime := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) ht
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg htime.1]; exact htime.2
  have hq : cfg.timeLength k s ≤ 1 := by
    unfold Data.timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hm : |t * cfg.c k s i 1| ≤ cfg.K k := by
    rw [abs_mul]
    exact (mul_le_mul ht1 (a.coefficient_bound i 1) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  calc
    _ = |((cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1) +
      cfg.c k s i 0 + t * cfg.c k s i 1| := by congr 1; ring
    _ ≤ |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| +
      |cfg.c k s i 0| + |t * cfg.c k s i 1| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ cfg.K k * cfg.timeLength k s + cfg.K k + cfg.K k :=
      add_le_add (add_le_add (a.geometry i l hl t ht).1 (a.coefficient_bound i 0)) hm
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hq hK]

/-- Choose the genuine true affine table with bounded slopes, using the unchanged
earlier witness of each entry. This does not select one fitted point from the current law. -/
theorem affine_table {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hN : 1 ≤ cfg.N k) (hK : 1 ≤ cfg.K k) (hκ : 0 ≤ cfg.κ)
    (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s) :
    ∃ L : Fin (cfg.n k s) → Fin 4 → ℝ,
      (∀ i, ∀ e : Fin 3, |L i e.succ| ≤ 8 * cfg.K k ^ 4) ∧
      ∀ i l, l ∈ cfg.B k s i → ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
        |cfg.b k l 2 + t * cfg.b k l 5 - (L i 0 + L i 1 * t +
          L i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
          L i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * cfg.N k ^ (-s) := by
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hNp : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hratios := cfg.hidden_time_ratios a hN hKp hκ hκ1 hs
  have hex : ∀ i : Fin (cfg.n k s), ∃ L : Fin 4 → ℝ,
      (∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4) ∧
      ∀ l ∈ cfg.B k s i, ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
        |cfg.b k l 2 + t * cfg.b k l 5 - (L 0 + L 1 * t +
          L 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
          L 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * cfg.N k ^ (-s) := by
    intro i
    obtain ⟨p, hp⟩ := cfg.witness_nonempty a hNp hKp i
    obtain ⟨L, hF, hvertical, hrow⟩ := a.affine_entry i
    have htime := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
      (cfg.T k s) (cfg.j k s i) hp.2
    refine ⟨L, affine_entry_slopes_le L (cfg.K k) (cfg.N k ^ (-s)) (cfg.timeLength k s)
      p.2 ((cfg.x k p.1 p.2) 1) hK hratios.1 hratios.2
      (by rw [abs_of_nonneg htime.1]; exact htime.2)
      (cfg.base_position_bound a (by linarith) i p.1 (a.fitted_subset i hp.1) hp.2)
      hvertical (hrow p.1 hp.1 p.2 hp.2), ?_⟩
    intro l hl t ht
    have hf := (a.fitted i l hl t ht).1
    rw [hF] at hf
    simpa [Data.x] using hf
  choose L hL hfit using hex
  exact ⟨L, hL, hfit⟩

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
