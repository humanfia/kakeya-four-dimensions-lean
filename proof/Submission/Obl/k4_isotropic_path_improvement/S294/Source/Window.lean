-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.Window, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Scale choices and the front window of the relative source (session x1088).

All choices of the relative source that precede the original data: the qualification degree
`M`, the gain, the strip width exponent `ub`, the narrow width `u0`, the depth tolerance `δ₀`,
the grid and the front window (`C` levels below an ancestor level `i ∈ indices`, all ending at
or before the middle level `target` with `s target = 1/2`).  The window fraction `C/m` is
`≈ c₀ = 16 ((Ep + 1) precision + 2) gain / κ₁`, so a descendant `b` of the ancestor `a` (level `i`)
can be taken at a relative depth large against `precision * gain` and `Ep * precision * gain`
inside the window. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SourceGrid

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The qualification degree: `κ₁ M ≥ 8`. -/
def qualDegree (κ₁ : ℝ) : ℕ := ⌈8 / κ₁⌉₊ + 1

theorem one_le_qualDegree (κ₁ : ℝ) : 1 ≤ qualDegree κ₁ := by
  unfold qualDegree; omega

theorem eight_le_mul_qualDegree {κ₁ : ℝ} (hκ : 0 < κ₁) : 8 ≤ κ₁ * qualDegree κ₁ := by
  unfold qualDegree
  have h := Nat.le_ceil (8 / κ₁)
  have : 8 / κ₁ * κ₁ = 8 := div_mul_cancel₀ 8 hκ.ne'
  push_cast
  nlinarith

/-- The tunable pre-data factors of the relative source, chosen by the producers as functions of
`(κ₁, d₁, Ep, precision, loss)`: a DEPTH factor `≥ 1` (window and palette depth, e.g. the
qualification depth `cZeta`, x1096 10:50Z) and a BUDGET factor in `(0, 1]` (the strip exponent `ub`,
e.g. the qualification budget `α`, x1096 10:51Z). -/
structure Tuning where
  depth : ℝ → ℝ → ℕ → ℝ → ℝ → ℝ
  budget : ℝ → ℝ → ℕ → ℝ → ℝ → ℝ
  one_le_depth : ∀ κ₁ d₁ Ep precision loss, 1 ≤ depth κ₁ d₁ Ep precision loss
  budget_pos : ∀ κ₁ d₁ Ep precision loss, 0 < budget κ₁ d₁ Ep precision loss
  budget_le_one : ∀ κ₁ d₁ Ep precision loss, budget κ₁ d₁ Ep precision loss ≤ 1
  /-- A fixed slack dividing the path tolerance and the prepared tolerances (e.g. x1095's
  `FixedSourcePowers.slack`, paying core/jet powers). -/
  slack : ℝ
  one_le_slack : 1 ≤ slack

/-- The gain cap, after `Ep`, `precision` and `loss`. -/
def gainCap (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss : ℝ) : ℝ :=
  loss * (1 - d₁) ^ 2 * κ₁ ^ 2 * tune.budget κ₁ d₁ Ep precision loss /
    (2 ^ 48 * ((Ep : ℝ) + 1) * (((Ep : ℝ) + 1) * precision + 3) ^ 2 *
      tune.depth κ₁ d₁ Ep precision loss ^ 2)

/-- The gain. -/
def gainOf (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss e0 : ℝ) : ℝ :=
  min e0 (gainCap tune κ₁ d₁ Ep precision loss)

/-- The strip-width exponent of the front (`r = N^(-ub L)`). It is a tiny multiple of the
per-sample budget `loss gain/(Ep+1)` (the MK4 graph pays `N^(18 ub L)`, x1095 10:36Z), times `κ₁`
(a middle level between ancestor and child, x1082 11:19Z) and the budget factor. -/
def ubOf (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss gain : ℝ) : ℝ :=
  κ₁ * tune.budget κ₁ d₁ Ep precision loss * loss * gain / (4096 * ((Ep : ℝ) + 1))

/-- The prepared path tolerance and pure-ceiling exponent, chosen after the front's prediction
budget: `min (δ₀ L) (budget / 1024)` (x1095 10:37Z: the record supplier needs
`12 (τ + ε) < budget`). -/
def tauOf (tune : Tuning) (δ₀ L budget : ℝ) : ℝ := min (δ₀ * L) (budget / (1024 * tune.slack))

/-- The window fraction `c₀ = C/m` (up to `1/m`): the depth from the ancestor level to the end
histories, `1024 ((Ep+1) precision + 3) gain depth / ((1 - d₁) κ₁)`, deep enough for the
ancestor's MK4 census (`mesh ~ θ^(24/(1-d₁))`, x1082 10:42Z) and the qualification depth. -/
def windowOf (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss gain : ℝ) : ℝ :=
  1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * tune.depth κ₁ d₁ Ep precision loss /
    ((1 - d₁) * κ₁)

/-- The grid fineness: `1/m ≤ gridFineOf/8`, so consecutive levels cost little against the
per-sample budget (x1082 12:47Z: consecutive census depths). -/
def gridFineOf (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss gain : ℝ) : ℝ :=
  tune.budget κ₁ d₁ Ep precision loss * loss * gain / (512 * ((Ep : ℝ) + 1))

theorem gridFineOf_pos (tune : Tuning) {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss gain : ℝ}
    (hloss : 0 < loss) (hg : 0 < gain) : 0 < gridFineOf tune κ₁ d₁ Ep precision loss gain := by
  unfold gridFineOf
  have := tune.budget_pos κ₁ d₁ Ep precision loss
  positivity

theorem gridFineOf_le_gain (tune : Tuning) {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss gain : ℝ}
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hg : 0 < gain) :
    gridFineOf tune κ₁ d₁ Ep precision loss gain ≤ gain := by
  unfold gridFineOf
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hE : (1 : ℝ) ≤ 512 * ((Ep : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) Ep; linarith
  rw [div_le_iff₀ (by linarith)]
  have h1 : tune.budget κ₁ d₁ Ep precision loss * loss ≤ 1 := by nlinarith
  have h2 : tune.budget κ₁ d₁ Ep precision loss * loss * gain ≤ gain := by nlinarith
  nlinarith

/-- The depth tolerance cap. -/
def tolOf (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) (precision loss gain : ℝ) : ℝ :=
  tune.budget κ₁ d₁ Ep precision loss * loss * gain / (10000 * ((Ep : ℝ) + 1) * tune.slack)

/-- The tolerance cap is below the budget- and slack-free one. -/
theorem tolOf_le (tune : Tuning) (κ₁ d₁ : ℝ) (Ep : ℕ) {precision loss gain : ℝ}
    (hloss : 0 < loss) (hg : 0 < gain) :
    tolOf tune κ₁ d₁ Ep precision loss gain ≤ loss * gain / (10000 * ((Ep : ℝ) + 1)) := by
  unfold tolOf
  have hE : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  have hS := tune.one_le_slack
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : tune.budget κ₁ d₁ Ep precision loss * loss * gain ≤ loss * gain := by
    have : 0 < loss * gain := by positivity
    nlinarith
  have h2 : 10000 * ((Ep : ℝ) + 1) ≤ 10000 * ((Ep : ℝ) + 1) * tune.slack := by nlinarith
  have h3 : 0 ≤ loss * gain := by positivity
  calc tune.budget κ₁ d₁ Ep precision loss * loss * gain * (10000 * ((Ep : ℝ) + 1))
      ≤ loss * gain * (10000 * ((Ep : ℝ) + 1)) := by gcongr
    _ ≤ loss * gain * (10000 * ((Ep : ℝ) + 1) * tune.slack) := by gcongr

section Facts

variable {tune : Tuning} {κ₁ d₁ : ℝ} {Ep : ℕ} {precision loss e0 : ℝ}

theorem gainCap_pos (hκ : 0 < κ₁) (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) (hloss : 0 < loss) :
    0 < gainCap tune κ₁ d₁ Ep precision loss := by
  unfold gainCap
  have : 0 < 1 - d₁ := by linarith
  have : 0 < (1 - d₁) ^ 2 := by positivity
  have : 0 < tune.depth κ₁ d₁ Ep precision loss :=
    lt_of_lt_of_le zero_lt_one (tune.one_le_depth κ₁ d₁ Ep precision loss)
  have := tune.budget_pos κ₁ d₁ Ep precision loss
  have : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have : 0 ≤ ((Ep : ℝ) + 1) * precision := by positivity
  positivity

theorem gainOf_pos (hκ : 0 < κ₁) (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) (hloss : 0 < loss)
    (he0 : 0 < e0) : 0 < gainOf tune κ₁ d₁ Ep precision loss e0 :=
  lt_min he0 (gainCap_pos hκ hd₁ hprec hloss)

theorem gainOf_le_e0 : gainOf tune κ₁ d₁ Ep precision loss e0 ≤ e0 := min_le_left _ _

theorem gainOf_le_cap : gainOf tune κ₁ d₁ Ep precision loss e0 ≤ gainCap tune κ₁ d₁ Ep precision loss :=
  min_le_right _ _

/-- The gain cap is tiny: `gainCap ≤ κ₁² / 2^24 / 9`. -/
theorem gainCap_le (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1)
    (hprec : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1) :
    gainCap tune κ₁ d₁ Ep precision loss ≤ κ₁ ^ 2 / (2 ^ 48 * 9) := by
  unfold gainCap
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hEp : 0 ≤ ((Ep : ℝ) + 1) * precision := by positivity
  have hD := tune.one_le_depth κ₁ d₁ Ep precision loss
  have hD2 : (1 : ℝ) ≤ tune.depth κ₁ d₁ Ep precision loss ^ 2 := one_le_pow₀ hD
  have hD0 : 0 < tune.depth κ₁ d₁ Ep precision loss := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h9 : (9 : ℝ) ≤ (((Ep : ℝ) + 1) * precision + 3) ^ 2 := by nlinarith
  have h1 : (1 : ℝ) ≤ (Ep : ℝ) + 1 := by linarith
  have hκ2 : 0 < κ₁ ^ 2 := by positivity
  have hd2 : (1 - d₁) ^ 2 ≤ 1 := by nlinarith
  have hl : loss * (1 - d₁) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - d₁)]
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hl' : loss * (1 - d₁) ^ 2 * tune.budget κ₁ d₁ Ep precision loss ≤ 1 := by
    have : 0 ≤ loss * (1 - d₁) ^ 2 := by positivity
    nlinarith
  calc loss * (1 - d₁) ^ 2 * κ₁ ^ 2 * tune.budget κ₁ d₁ Ep precision loss * (2 ^ 48 * 9)
      = loss * (1 - d₁) ^ 2 * tune.budget κ₁ d₁ Ep precision loss * κ₁ ^ 2 * (2 ^ 48 * 9) := by
        ring
    _ ≤ 1 * κ₁ ^ 2 * (2 ^ 48 * 9) := by gcongr
    _ = κ₁ ^ 2 * (2 ^ 48 * 1 * 9 * 1) := by ring
    _ ≤ κ₁ ^ 2 * (2 ^ 48 * ((Ep : ℝ) + 1) * (((Ep : ℝ) + 1) * precision + 3) ^ 2 *
          tune.depth κ₁ d₁ Ep precision loss ^ 2) := by gcongr

end Facts

/-- A smaller positive tolerance keeps a grid a grid. -/
theorem grid_shrink_delta {κ₁ ρ gain δ₀ δ₁ u0 : ℝ} {m : ℕ} {s : ℕ → ℝ}
    (hgrid : Parent.grid κ₁ ρ m s gain δ₀ u0) (hδ₁ : 0 < δ₁) (hδ₁₀ : δ₁ ≤ δ₀) :
    Parent.grid κ₁ ρ m s gain δ₁ u0 := by
  obtain ⟨h1, hg, hg1, -, hδρ, heven, hm2, hs, hm, hδg, hδu, hδρ', hu, hu1⟩ := hgrid
  unfold Parent.grid
  exact ⟨h1, hg, hg1, hδ₁, hδ₁₀.trans hδρ, heven, hm2, hs, hm, hδ₁₀.trans hδg, hδ₁₀.trans hδu,
    hδ₁₀.trans hδρ', hu, hu1⟩

/-- **The grid and the window of the relative source.** For `0 < gain ≤ κ₁/2^20` (so the
window fraction is at most `1/16`) there are a grid, a positive `δ₀ ≤ tolerance` with
`4 δ₀ m ≤ κ₁` (so that depths and clocks increase from level to level), a middle level
`target` with `s target = 1/2`, a window length `C` with `c₀ m ≤ C ≤ c₀ m + 1` and a set of
ancestor levels `indices = {i | i + C ≤ target}` of size at least `m/4`. -/
theorem exists_relative_grid {κ₁ ρ gain u0 c₀ fine tolerance : ℝ}
    (hκ : 0 < κ₁) (hρ : 0 < ρ) (hg : 0 < gain) (hg1 : gain ≤ 1 / 8)
    (hu : 0 < u0) (hu1 : u0 ≤ 4 * gain) (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1 / 16)
    (hfine : 0 < fine) (hfinec : fine ≤ c₀) (htol : 0 < tolerance) :
    ∃ (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (C target : ℕ) (indices : Finset ℕ),
      Parent.grid κ₁ ρ m s gain δ₀ u0 ∧ δ₀ ≤ tolerance ∧ 4 * δ₀ * (m : ℝ) ≤ κ₁ ∧ 8 ≤ m ∧
      8 ≤ fine * m ∧
      target < m ∧ s target = 1 / 2 ∧ 2 * (target + 1) = m ∧
      1 ≤ C ∧ c₀ * m ≤ C ∧ (C : ℝ) ≤ c₀ * m + 1 ∧ C + 1 ≤ target ∧
      indices = Finset.range (target + 1 - C) ∧ (m : ℝ) / 4 ≤ (indices.card : ℝ) ∧
      (∀ i ∈ indices, i < m ∧ i + C < m ∧ i + C ≤ target) := by
  obtain ⟨m, s, δ₀, hgrid, hfirst, hδ, hdvd, j, hj, hsj⟩ :=
    Parent.SourceGrid.exists_grid_with_shallow_ancestor hκ hρ hg hg1 hu hu1
      (show 0 < fine / 8 by positivity) htol 2 le_rfl
  have hm0 : 0 < m := hgrid.1.1
  have hs : ∀ i, s i = ((i : ℝ) + 1) / m := hgrid.2.2.2.2.2.2.2.1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  -- `1/m ≤ fine/8 ≤ c₀/8`
  have hfm : 8 ≤ fine * m := by
    have h := hfirst
    rw [hs 0] at h
    simp only [Nat.cast_zero, zero_add] at h
    have := (div_le_iff₀ hmR).mp h
    nlinarith
  have hm8 : 8 / c₀ ≤ (m : ℝ) := by
    rw [div_le_iff₀ hc₀]
    have : fine * m ≤ c₀ * m := mul_le_mul_of_nonneg_right hfinec hmR.le
    linarith
  have hm8' : (8 : ℝ) ≤ m := by
    have : (8 : ℝ) ≤ 8 / c₀ := by
      rw [le_div_iff₀ hc₀]; nlinarith
    linarith
  have hm8n : 8 ≤ m := by exact_mod_cast hm8'
  -- the middle level
  have hj2 : 2 * (j + 1) = m := by
    have h := hsj
    rw [hs j] at h
    have : ((j : ℝ) + 1) * 2 = m := by
      field_simp at h; push_cast at h; linarith
    have : ((2 * (j + 1) : ℕ) : ℝ) = (m : ℝ) := by push_cast; linarith
    exact_mod_cast this
  -- the window
  set C := ⌈c₀ * m⌉₊ with hCdef
  have hCge : c₀ * m ≤ C := Nat.le_ceil _
  have hCle : (C : ℝ) ≤ c₀ * m + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hC1 : 1 ≤ C := by
    have : (1 : ℝ) ≤ c₀ * m := by
      have := mul_le_mul_of_nonneg_left hm8 hc₀.le
      rw [mul_div_cancel₀ _ hc₀.ne'] at this
      linarith
    exact_mod_cast this.trans hCge
  have hCm : (C : ℝ) ≤ (m : ℝ) / 16 + 1 := by
    have := mul_le_mul_of_nonneg_right hc₀1 hmR.le
    linarith
  have hjR : ((j : ℝ) + 1) * 2 = m := by exact_mod_cast (show (j + 1) * 2 = m by omega)
  have hCj : C + 1 ≤ j := by
    have : (C : ℝ) + 1 ≤ j := by nlinarith
    exact_mod_cast this
  -- the tolerance below `κ₁/(4m)`
  have hδ₀ : 0 < δ₀ := hgrid.2.2.2.1
  have hδ₁ : 0 < min δ₀ (κ₁ / (4 * m)) := lt_min hδ₀ (by positivity)
  have hδ₁m : 4 * min δ₀ (κ₁ / (4 * m)) * (m : ℝ) ≤ κ₁ := by
    have h := min_le_right δ₀ (κ₁ / (4 * m))
    have e : κ₁ / (4 * m) * (4 * m) = κ₁ := by field_simp
    nlinarith
  refine ⟨m, s, min δ₀ (κ₁ / (4 * m)), C, j, Finset.range (j + 1 - C),
    grid_shrink_delta hgrid hδ₁ (min_le_left _ _), (min_le_left _ _).trans hδ, hδ₁m, hm8n, hfm,
    hj, hsj, hj2, hC1, hCge, hCle, hCj, rfl, ?_, ?_⟩
  · rw [Finset.card_range]
    have hsub : ((j + 1 - C : ℕ) : ℝ) = (j : ℝ) + 1 - C := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hsub]
    nlinarith
  · intro i hi
    rw [Finset.mem_range] at hi
    refine ⟨by omega, by omega, by omega⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
