import Submission.Obl.k4_unbounded_width_exclusion.Width

noncomputable section

namespace Submission.Obl.k4_unbounded_width_exclusion

/-- A single maximizer can simultaneously have a prescribed narrow atlas,
a two-sided horizon estimate, and the relative-profile estimate. Absolute
profile offsets remain unrestricted. -/
theorem exists_prepared_near {ds kr S η : ℝ} (hes : es ds kr S η)
    (hnb : ¬ BoundedWidth ds kr S η)
    {a w t : ℝ} (ha : 0 < a) (hw : 0 ≤ w) (ht : 0 < t) :
    ∃ p : Problem, Near ds kr S η t p ∧ p.Narrow (kr + a) w ∧
      |p.horizon - kr| ≤ t ∧ |p.d - ds| ≤ t ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 → |p.f r - p.f 0 - ds * r| ≤ t := by
  obtain ⟨aH, haH, hH⟩ := hes.2.2.2.2.2.1 t ht
  obtain ⟨aP, haP, hP⟩ := hes.2.2.2.2.2.2 t ht
  let t' := min t (min aH aP)
  have ht' : 0 < t' := lt_min ht (lt_min haH haP)
  obtain ⟨p, hp, hn⟩ := exists_narrow_near hes hnb ha hw ht'
  have hpt : Near ds kr S η t p := hp.mono (min_le_left _ _)
  have hpH : Near ds kr S η aH p :=
    hp.mono ((min_le_right _ _).trans (min_le_left _ _))
  have hpP : Near ds kr S η aP p :=
    hp.mono ((min_le_right _ _).trans (min_le_right _ _))
  have hupper : p.horizon ≤ kr + t := by
    have h := hH p.N p.K p.L p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G hp.2.1 hpH.2.2.1
    simpa only [Problem.horizon, hp.1, mul_one] using h
  have hprofile : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      |p.f r - p.f 0 - ds * r| ≤ t := by
    intro r hr hr1
    have h := hP p.N p.K p.L p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      hp.2.1 hpP.2.2.1 (by simpa only [Problem.horizon, hp.1, mul_one] using hpP.2.2.2)
      r hr (by simpa only [hp.1] using hr1)
    simpa only [hp.1, mul_one] using h
  have hdimension : |p.d - ds| ≤ t := by
    have hprof := hprofile 1 (by norm_num) le_rfl
    have hcap := hp.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hc : p.f 1 - p.f 0 ≤ p.d := by
      have := hcap 0 le_rfl (by simpa only [hp.1] using (zero_le_one : (0 : ℝ) ≤ 1))
      simpa only [hp.1, sub_zero, mul_one] using this
    rw [abs_le] at hprof ⊢
    constructor <;> linarith [hpt.2.2.1]
  refine ⟨p, hpt, hn, ?_, hdimension, hprofile⟩
  rw [abs_le]
  constructor <;> linarith [hpt.2.2.2]

/-- The natural outer scales for unbounded optimized narrowness. -/
def outerError (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)

theorem outerError_pos (i : ℕ) : 0 < outerError i := by
  unfold outerError
  positivity

theorem outerError_tendsto : Filter.Tendsto outerError Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem exists_prepared_sequence {ds kr S η : ℝ} (hes : es ds kr S η)
    (hnb : ¬ BoundedWidth ds kr S η) :
    ∃ p : ℕ → Problem, ∀ i,
      Near ds kr S η (outerError i) (p i) ∧
      (p i).Narrow (kr + outerError i) (i : ℝ) ∧
      |(p i).horizon - kr| ≤ outerError i ∧
      |(p i).d - ds| ≤ outerError i ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        |(p i).f r - (p i).f 0 - ds * r| ≤ outerError i := by
  exact Classical.axiomOfChoice fun i =>
    exists_prepared_near hes hnb (outerError_pos i) (Nat.cast_nonneg i) (outerError_pos i)

end Submission.Obl.k4_unbounded_width_exclusion
