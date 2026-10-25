/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/OriginalMass.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/OriginalMass.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.PreparedModel
import Submission.Obl.k4_critical_switching_state_preparation.CriticalScales

namespace Submission.Obl.k4_critical_switching_state_preparation

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

def timeLength (cfg : Data α) (k : ℕ) (s : ℝ) : ℝ := ((2 : ℝ) ^ cfg.T k s)⁻¹

/-- The native incidence and every dense residual are finite in original units. -/
theorem Valid.incidence_mass_le (h : cfg.Valid) (k : ℕ) :
    cfg.μ k univ ≤ ENNReal.ofReal (cfg.K k) := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hs : MeasurableSet (univ ×ˢ Icc (0 : ℝ) 1 : Set (α × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hdom := (h.basic k).2.2.2.1 (univ ×ˢ Icc (0 : ℝ) 1)
  have hz := (h.basic k).2.2.2.2.2.1
  have heq : cfg.μ k univ = cfg.μ k (univ ×ˢ Icc (0 : ℝ) 1) := by
    have hh := measure_add_measure_compl (μ := cfg.μ k) hs
    rw [hz, add_zero] at hh
    exact hh.symm
  rw [heq]
  simpa [Measure.smul_apply, Measure.prod_prod, Real.volume_Icc] using hdom

theorem Valid.incidence_finite (h : cfg.Valid) (k : ℕ) : IsFiniteMeasure (cfg.μ k) :=
  ⟨(h.incidence_mass_le k).trans_lt ENNReal.ofReal_lt_top⟩

theorem Valid.residual_finite (h : cfg.Valid) (k : ℕ) : IsFiniteMeasure (cfg.ρ k) := by
  let := h.incidence_finite k
  exact isFiniteMeasure_of_le (cfg.μ k) (h.basic k).2.2.2.2.1

/-- Only the full trajectory assignments and their original priors are stored. -/
structure AssignmentLevel (cfg : Data α) (k : ℕ) (s : ℝ) : Prop where
  time_lower : cfg.N k ^ (cfg.κ * s) / cfg.K k ≤ (2 : ℝ) ^ cfg.T k s
  time_upper : (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s)
  measurable : ∀ i, MeasurableSet (cfg.A k s i)
  disjoint : ∀ i i', i ≠ i' → cfg.j k s i = cfg.j k s i' →
    Disjoint (cfg.A k s i) (cfg.A k s i')
  prior_lower : ∀ i, ENNReal.ofReal
    ((cfg.N k ^ (-s)) ^ cfg.d * cfg.timeLength k s ^ 2 * cfg.N k ^ (-cfg.ℓ * s) /
      cfg.K k) ≤ cfg.ν k (cfg.A k s i)
  prior_upper : ∀ i, cfg.ν k (cfg.A k s i) ≤ ENNReal.ofReal
    (cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d * cfg.timeLength k s ^ 2 *
      cfg.N k ^ (-cfg.ℓ * s))
  covers : ∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ cfg.B k s i ∧
    p.2 ∈ I (cfg.T k s) (cfg.j k s i)
  fitted_subset : ∀ i, cfg.B k s i ⊆ cfg.A k s i
  coefficient_bound : ∀ i e, |cfg.c k s i e| ≤ cfg.K k
  geometry : ∀ i l, l ∈ cfg.A k s i → ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
    |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤ cfg.K k * cfg.timeLength k s ∧
    |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤
      cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s) ∧
    |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤
      cfg.K k * cfg.N k ^ (-cfg.ℓ * s)
  fitted : ∀ i l, l ∈ cfg.B k s i → cfg.fit k (cfg.K k) (cfg.N k ^ (-s))
    (cfg.F k s i) l (I (cfg.T k s) (cfg.j k s i))
  plane_center : ∀ i,
    |cfg.c k s i 3 + cfg.c k s i 0 +
        (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s * cfg.c k s i 1| +
      |cfg.c k s i 4 - (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s| ≤
        cfg.K k * cfg.timeLength k s
  affine_entry : ∀ i, ∃ L : Fin 4 → ℝ,
    cfg.F k s i = MvPolynomial.X (3 : Fin 4) -
      (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) +
        MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
        MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧
    |L 3| ≤ cfg.K k * (1 + cfg.N k ^ (-s) / cfg.timeLength k s ^ 2) ∧
    ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤
        cfg.K k * (1 + cfg.N k ^ (-s) / cfg.timeLength k s)
  native_hidden : ∀ _i : Fin (cfg.n k s), cfg.P k = MvPolynomial.X (3 : Fin 4)
  horizontal_equation : ∀ _i : Fin (cfg.n k s),
    ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)

/-- At each fixed positive depth, the frozen atlas supplies its exact
original assignment floors at every sufficiently late sample. -/
theorem Valid.eventually_assignment_level (h : cfg.Valid) {s : ℝ}
    (hs : 0 < s) (hsU : s ≤ cfg.U) : ∀ᶠ k in atTop, cfg.AssignmentLevel k s := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by
    have hh : 0 < s⁻¹ := inv_pos.mpr hs
    dsimp [R]
    linarith
  have hRs : R⁻¹ ≤ s := by
    have hRpos : 0 < R := by linarith
    have hle : s⁻¹ ≤ R := by dsimp [R]; linarith
    exact (inv_le_comm₀ hRpos hs).mpr hle
  filter_upwards [h.atlas R hR] with k hk
  have hk := hk s hRs hsU
  refine ⟨hk.1, hk.2.1, (fun i => (hk.2.2.1 i).1), hk.2.2.2.1,
    ?_, ?_, hk.2.2.2.2.2.1, (fun i => (hk.2.2.1 i).2.2),
    (fun i => (hk.2.2.2.2.1 i).2.2.2.1), ?_,
    (fun i => (hk.2.2.2.2.1 i).2.2.2.2.2.2.1), ?_, ?_,
    (fun i => ((hk.2.2.2.2.1 i).2.2.2.2.2.2.2.2 rfl).1),
    (fun i => ((hk.2.2.2.2.1 i).2.2.2.2.2.2.2.2 rfl).2.1)⟩
  · intro i
    simpa only [timeLength, zpow_neg, zpow_natCast] using (hk.2.2.2.2.1 i).1
  · intro i
    simpa only [timeLength, zpow_neg, zpow_natCast] using (hk.2.2.2.2.1 i).2.1
  · intro i l hl t ht
    simpa only [timeLength, zpow_neg, zpow_natCast] using
      (hk.2.2.2.2.1 i).2.2.2.2.2.1 l hl t ht
  · intro i
    simpa only [timeLength, zpow_neg, zpow_natCast] using
      ((hk.2.2.2.2.1 i).2.2.2.2.2.2.2.2 rfl).2.2.1
  · intro i
    simpa only [timeLength, zpow_neg, zpow_natCast] using
      ((hk.2.2.2.2.1 i).2.2.2.2.2.2.2.2 rfl).2.2.2

/-- At the critical horizontal rate the original floors have three powers
of the ACTUAL dyadic length, with only a squared slack loss. -/
theorem AssignmentLevel.critical_prior_bounds (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 ≤
        (cfg.ν k).real (cfg.A k s i) ∧
      (cfg.ν k).real (cfg.A k s i) ≤
        cfg.K k ^ 2 * cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hlow := ENNReal.toReal_mono (measure_ne_top (cfg.ν k) _) (a.prior_lower i)
  have hupp := ENNReal.toReal_mono ENNReal.ofReal_ne_top (a.prior_upper i)
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤
    (cfg.N k ^ (-s)) ^ cfg.d * cfg.timeLength k s ^ 2 * cfg.N k ^ (-cfg.ℓ * s) / cfg.K k),
    ← measureReal_def] at hlow
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤
    cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d * cfg.timeLength k s ^ 2 *
      cfg.N k ^ (-cfg.ℓ * s)), ← measureReal_def] at hupp
  rw [h.horizontal_rate] at hlow hupp
  exact assignment_bounds_from_time_comparison hN hK a.time_lower a.time_upper hlow hupp


/-- Once a true horizontal label is present, its native polynomial is the
hidden coordinate. The original native bounds then control both hidden
trajectory coefficients on the original incidence law. -/
theorem AssignmentLevel.native_hidden_bounds (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 2| ≤ cfg.K k ∧ |cfg.b k p.1 5| ≤ 2 * cfg.K k ∧
      ∀ t ∈ Icc (0 : ℝ) 1, |cfg.b k p.1 2 + t * cfg.b k p.1 5| ≤ cfg.K k := by
  have heq := a.native_hidden i
  filter_upwards [(h.basic k).2.2.2.2.2.2.2.2.2] with p hp
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |cfg.b k p.1 2 + t * cfg.b k p.1 5| ≤ cfg.K k := by
    have ht' := (hp.1 t ht).1
    rw [heq] at ht'
    simpa [x] using ht'
  have hzero := hbound 0 (by norm_num)
  have hone := hbound 1 (by norm_num)
  simp only [zero_mul, add_zero] at hzero
  simp only [one_mul] at hone
  refine ⟨hzero, ?_, hbound⟩
  calc
    |cfg.b k p.1 5| = |(cfg.b k p.1 2 + cfg.b k p.1 5) - cfg.b k p.1 2| := by congr 1; ring
    _ ≤ |cfg.b k p.1 2 + cfg.b k p.1 5| + |cfg.b k p.1 2| := abs_sub _ _
    _ ≤ 2 * cfg.K k := by linarith

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
