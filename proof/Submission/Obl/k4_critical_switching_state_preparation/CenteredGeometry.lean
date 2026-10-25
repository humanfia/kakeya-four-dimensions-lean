import Submission.Obl.k4_critical_switching_state_preparation.SwitchingModel
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The centered curve is precisely the contact normalization of its original curve. -/
theorem centeredLine_eq_normalized (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (l : α) (t : ℝ) :
    cfg.centeredLine k s i l t = normalizedHorizontalLine (cfg.timeLength k s)
      (cfg.blockOrigin k s i 0) (cfg.blockOrigin k s i 1)
      (cfg.blockOrigin k s i 2) (cfg.c k s i 1) (cfg.b k l) t := rfl

theorem centeredLine_time (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (l : α) (t : ℝ) : cfg.centeredLine k s i l t 0 = t := by
  rw [centeredLine_eq_normalized]
  exact normalizedHorizontalLine_time _ _ _ _ _ (cfg.timeLength_pos k s).ne' _ _

theorem measurable_centeredLine (h : cfg.Valid) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) : Measurable (Function.uncurry (cfg.centeredLine k s i)) := by
  have hb : Measurable (cfg.b k) := (h.basic k).1
  unfold Function.uncurry centeredLine framedPoint parentFrame horizontalFrame nativeHorizontalLine
  fun_prop

theorem measurable_centeredVelocity (h : cfg.Valid) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) : Measurable (cfg.centeredVelocity k s i) := by
  have hb : Measurable (cfg.b k) := (h.basic k).1
  unfold centeredVelocity
  fun_prop

theorem measurable_midpointBin (h : cfg.Valid) (k : ℕ) (s v : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) :
    Measurable (cfg.midpointBin k s v i L) := by
  have hb : Measurable (cfg.b k) := (h.basic k).1
  unfold midpointBin midpointValue affineResidualIntercept affineResidualSlope
  fun_prop

/-- Every time of a trajectory in the full original parent has bounded normalized coordinates. -/
theorem AssignmentLevel.centeredLine_bounds (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (parent : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s))
    {l : α} (hl : l ∈ cfg.A k s i) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ e, |cfg.centeredLine k s i l t e| ≤ 8 * cfg.K k ^ 4 := by
  apply (parent.framedPoint_bounds h i hl ?_).2.2
  rw [cfg.block_interval]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (cfg.timeLength_pos k s).le ht.1)
  · nlinarith [ht.2, cfg.timeLength_pos k s]

/-- The velocity is bounded in the same original subpower units as the parent. -/
theorem AssignmentLevel.centeredVelocity_bound (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (parent : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) {l : α}
    (hb : |cfg.b k l 3| ≤ 2 * cfg.K k) :
    |cfg.centeredVelocity k s i l| ≤ 8 * cfg.K k ^ 4 := by
  have hK := h.subpower.1 k
  have hpow : cfg.K k ≤ cfg.K k ^ 4 := by
    simpa using pow_le_pow_right₀ hK (show 1 ≤ 4 by norm_num)
  exact (abs_sub _ _).trans (by linarith [parent.coefficient_bound i 1])

/-- The first horizontal traversal identity is exact. -/
theorem centeredLine_horizontal_first (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (l : α) (t u : ℝ) :
    cfg.centeredLine k s i l u 1 = cfg.centeredLine k s i l t 1 +
      cfg.centeredVelocity k s i l * (u - t) := by
  have hH : cfg.timeLength k s ≠ 0 := (cfg.timeLength_pos k s).ne'
  simp only [centeredLine_eq_normalized, normalizedHorizontalLine, horizontalFrame,
    nativeHorizontalLine, Matrix.cons_val_zero, Matrix.cons_val_one, centeredVelocity]
  field_simp [hH]
  ring

/-- The second horizontal traversal has just the original horizontal defect divided by time length. -/
theorem centeredLine_horizontal_error (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (l : α) {E : ℝ} (hE : 0 ≤ E) (hb : |cfg.b k l 4 + cfg.b k l 0| ≤ E)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    |cfg.centeredLine k s i l u 2 - cfg.centeredLine k s i l t 2 -
      (-cfg.centeredLine k s i l t 1 + t * cfg.centeredVelocity k s i l) * (u - t)| ≤
      E / cfg.timeLength k s := by
  have hh := normalizedHorizontalLine_traverse_error (cfg.timeLength k s)
    (cfg.blockOrigin k s i 0) (cfg.blockOrigin k s i 1)
    (cfg.blockOrigin k s i 2) (cfg.c k s i 1) E (cfg.timeLength_pos k s) hE
    (cfg.b k l) hb t u ht hu (1 : Fin 2)
  simpa only [← centeredLine_eq_normalized, Fin.reduceFinMk,
    Fin.succ_one_eq_two, horizontalTraverse, Matrix.cons_val_one,
    Matrix.cons_val_zero, centeredVelocity, sub_sub] using hh

/-- Any requested positive power absorbs all fixed coordinate and velocity bounds. -/
theorem Valid.eventually_centered_bound (h : cfg.Valid) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, 8 * cfg.K k ^ 4 ≤ cfg.N k ^ δ := by
  have hh := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k)
    h.scale_limit h.subpower.1 h.subpower.2 4 hδ (A := 8) (by norm_num)
  filter_upwards [hh] with k hk
  simpa using hk.le

/-- The frozen defect margin pays for the fine switching precision, uniformly over parents. -/
theorem Valid.eventually_centered_error (h : cfg.Valid) {s : ℝ}
    (hs : 0 < s) (he : 1000 * s < cfg.e₀) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, cfg.N k ^ (-cfg.e₀) / cfg.timeLength k s ≤
      cfg.N k ^ (-20 * (10 * s)) := by
  filter_upwards [h.eventually_assignment_level hs hsU, h.subpower.2 s hs]
    with k parent hK
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hκs : cfg.κ * s ≤ s := mul_le_of_le_one_left hs.le h.rate_le_one
  have htime : (2 : ℝ) ^ cfg.T k s ≤ cfg.N k ^ (2 * s) := by
    calc
      _ ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) := parent.time_upper
      _ ≤ cfg.N k ^ s * cfg.N k ^ s := by
        exact mul_le_mul hK (Real.rpow_le_rpow_of_exponent_le hN1 hκs)
          (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
      _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring
  calc
    _ = cfg.N k ^ (-cfg.e₀) * (2 : ℝ) ^ cfg.T k s := by simp [timeLength, div_eq_mul_inv]
    _ ≤ cfg.N k ^ (-cfg.e₀) * cfg.N k ^ (2 * s) := by gcongr
    _ = cfg.N k ^ (-cfg.e₀ + 2 * s) := (Real.rpow_add hN _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
