-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepHyp.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/PrepHyp.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepDefs

/-!
# Hypotheses of one preparation sample, and the frames

`PrepData.Hyp` records what a known old sample of one scale class provides: the frozen
chart conditions with knowledge by the old lists, disjoint trajectory sets, the class
scales, and the frame parameters.  From them: the fitting matrices satisfy the
hypotheses of x0661's `FramePackage`, old charts are confined in their frames on the
whole coarse block, and the frames have the frozen frame bounds.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MeasureTheory Set MvPolynomial Submission.Lib.K4VelocityStrips

namespace PrepData

variable (D : PrepData)

/-- The hypotheses on one preparation sample. -/
structure Hyp (N : ℝ) (M₀ D₀ : ℕ) (L : ℝ) (E : Fin D.W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) :
    Prop where
  chart : ∀ b, chart N M₀ D₀ D.κ₀ (D.T + D.s) ((D.j b : ℕ) : ℝ) L (D.B (D.γ b)) (E (D.γ b))
    (D.c b) (D.u b) (D.Q b) (D.R b) (D.A b) (D.F b)
    (∀ p ∈ D.F b, b ∈ D.lst (D.γ b) (obs (D.B (D.γ b)) (δ N L) p))
  disj : ∀ b b', b ≠ b' → D.γ b = D.γ b' → D.j b = D.j b' → Disjoint (D.A b) (D.A b')
  r₁lo : ∀ b, D.R₁ ≤ r₁ (D.Q b)
  r₁hi : ∀ b, r₁ (D.Q b) < 2 * D.R₁
  r₂lo : ∀ b, D.R₂ ≤ r₂ (D.Q b)
  r₂hi : ∀ b, r₂ (D.Q b) < 2 * D.R₂
  R₁pos : 0 < D.R₁
  R₂pos : 0 < D.R₂
  R21 : D.R₂ ≤ D.R₁
  gpos : 0 < D.g
  g8 : D.g ≤ 1 / 8
  κ₀one : 1 ≤ D.κ₀
  hKb : 2 * (78 * (4 * D.κ₀)) + 1 ≤ (D.Kb : ℝ)
  Bpos : ∀ γ, 0 < D.B γ
  Good_sub : ∀ γ, D.Good γ ⊆ E γ
  Good_meas : ∀ γ, MeasurableSet (D.Good γ)
  N2 : 2 ≤ N

variable {D} {N : ℝ} {M₀ D₀ : ℕ} {L : ℝ} {E : Fin D.W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}

theorem Hyp.det (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) : (D.Q b).det ≠ 0 := (h.chart b).1

theorem Hyp.entrySum (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) :
    (∑ i : Fin 2, ∑ j : Fin 2, |D.Q b i j|) ≤ D.κ₀ / 2 ^ (D.T + D.s) := (h.chart b).2.2.2.1

/-- The selected incidences of an old chart. -/
theorem Hyp.sel (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) {p : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hp : p ∈ D.F b) : p ∈ E (D.γ b) ∧ p.1 ∈ D.A b ∧
      p.2 ∈ Icc (((D.j b : ℕ) : ℝ) / (2 : ℝ) ^ (D.T + D.s))
        ((((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)) ∧
      D.B (D.γ b) / D.κ₀ ≤ |eval (x p.1 p.2) (pderiv 3 (D.R b))| := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsel, -⟩ := h.chart b
  exact hsel p hp

/-- The whole old block of a trajectory of an old chart. -/
theorem Hyp.whole (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) {l : ℕ × (Fin 6 → ℝ)}
    (hl : l ∈ D.A b) : (l.1 : ℝ) ≤ N ^ M₀ ∧ (∀ e, |l.2 e| ≤ N ^ M₀) ∧
      ∀ t ∈ Icc (((D.j b : ℕ) : ℝ) / (2 : ℝ) ^ (D.T + D.s))
        ((((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)),
      ‖Matrix.toEuclideanLin (D.Q b)⁻¹ (y l t - D.c b - t • D.u b)‖ ≤ D.κ₀ ∧
      |eval (x l t) (D.R b)| ≤ D.κ₀ * δ N L ∧
      |eval (x l t) (pderiv 3 (D.R b))| ≤ D.κ₀ * D.B (D.γ b) ∧
      |eval (x l t) (pderiv 3 (pderiv 3 (D.R b)))| ≤ D.κ₀ * D.B (D.γ b) ^ 2 / δ N L := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hwhole, -, -⟩ := h.chart b
  exact hwhole l hl

theorem Hyp.knows (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) {p : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hp : p ∈ D.F b) : b ∈ D.lst (D.γ b) (obs (D.B (D.γ b)) (δ N L) p) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk⟩ := h.chart b
  exact hk p hp

theorem Hyp.Fmeas (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) : MeasurableSet (D.F b) :=
  (h.chart b).2.2.2.2.2.2.2.1

theorem Hyp.Rdeg (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) : (D.R b).totalDegree ≤ 2 :=
  (h.chart b).2.2.2.2.1

theorem Hyp.Rcoeff (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) :
    ∀ e, |(D.R b).coeff e| ≤ N ^ M₀ := (h.chart b).2.2.2.2.2.1

theorem Hyp.cu (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) : ‖D.c b‖ + ‖D.u b‖ ≤ N ^ M₀ :=
  (h.chart b).2.1

theorem Hyp.Qframe (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) :
    (∑ e : Fin 2, ∑ e' : Fin 2, (|D.Q b e e'| + |(D.Q b)⁻¹ e e'|)) ≤ N ^ M₀ :=
  (h.chart b).2.2.1

theorem Hyp.fmtF (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) (i : ℕ) :
    fmt 7 (N ^ M₀) D₀ {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ D.F b} :=
  ((h.chart b).2.2.2.2.2.2.2.2.1 i).2

/-- The fitting matrices satisfy the class hypotheses of the frame package. -/
theorem Hyp.fit (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) :
    (D.Qf b).det ≠ 0 ∧ D.R₁ ≤ r₁ (D.Qf b) ∧ r₁ (D.Qf b) ≤ 2 * D.R₁ ∧
      r₂ (D.Qf b) ≤ 2 * fitR₂ (D.iso = true) D.R₁ D.R₂ ∧
      fitR₂ (D.iso = true) D.R₁ D.R₂ ≤ D.R₁ ∧
      (∑ i : Fin 2, ∑ j : Fin 2, |D.Qf b i j|) ≤ (4 * D.κ₀) / 2 ^ (D.T + D.s) := by
  have hc := fitMat_class (D.iso = true) (h.det b) h.R₁pos (h.r₁lo b) (h.r₁hi b) (h.r₂lo b)
    (h.r₂hi b) h.R21 (h.entrySum b)
  unfold fitR₂
  exact hc

/-- Old confinement in the fitting matrix. -/
theorem Hyp.oldConfined (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) {l : ℕ × (Fin 6 → ℝ)}
    (hl : l ∈ D.A b) : OldConfined (D.j b) (D.c b) (D.u b) (D.Qf b) (4 * D.κ₀) l := by
  intro t ht
  have hκ0 : 0 ≤ D.κ₀ := le_trans zero_le_one h.κ₀one
  exact fitMat_confined (D.iso = true) (h.det b) h.R₁pos (h.r₁hi b) hκ0
    ((h.whole b hl).2.2 t ht).1

theorem Hyp.S₁pos (h : D.Hyp N M₀ D₀ L E) : 0 < D.S₁ := by
  unfold S₁; have := h.R₁pos; positivity

theorem Hyp.S₂pos (h : D.Hyp N M₀ D₀ L E) : 0 < D.S₂ := by
  unfold S₂
  have : 0 < max (fitR₂ (D.iso = true) D.R₁ D.R₂) (D.g * D.R₁) :=
    lt_max_of_lt_left (fitR₂_pos _ h.R₁pos h.R₂pos)
  positivity

theorem Hyp.S₂_le_S₁ (h : D.Hyp N M₀ D₀ L E) : D.S₂ ≤ D.S₁ := by
  unfold S₂ S₁
  have h1 := fitR₂_le (D.iso = true) h.R21
  have h2 : D.g * D.R₁ ≤ D.R₁ := by
    have := h.R₁pos; have := h.g8; nlinarith
  have : max (fitR₂ (D.iso = true) D.R₁ D.R₂) (D.g * D.R₁) ≤ D.R₁ := max_le h1 h2
  gcongr

/-- The long class scale is at most `κ₀ / 2^(T+s)`. -/
theorem Hyp.R₁_le (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) :
    D.R₁ ≤ D.κ₀ / 2 ^ (D.T + D.s) :=
  (h.r₁lo b).trans ((r₁_le_entrySum _).trans (h.entrySum b))

/-- **Whole-coarse-block confinement** of a trajectory of an old chart in its frame. -/
theorem Hyp.frame_conf (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) {l : ℕ × (Fin 6 → ℝ)}
    (hl : l ∈ D.A b) {t : ℝ}
    (ht : t ∈ Icc (((coarseIdx (D.j b) : ℕ) : ℝ) / 2 ^ D.T)
      ((((coarseIdx (D.j b) : ℕ) : ℝ) + 1) / 2 ^ D.T)) :
    ‖Matrix.toEuclideanLin (keyQ D.g D.S₁ D.S₂ D.Afr (D.src b))⁻¹
      (y l t - keyC D.g D.S₁ D.S₂ (D.src b) - t • keyU D.g D.S₁ D.S₂ (D.src b))‖ ≤ 2 := by
  obtain ⟨hQ, -, h1, h2, -, -⟩ := h.fit b
  have hκ0 : 0 ≤ 4 * D.κ₀ := by have := h.κ₀one; linarith
  exact frame_confinement_key (γ₀ := D.γ) (j₀ := D.j) (c₀ := D.c) (u₀ := D.u) (Q₀ := D.Qf)
    h.gpos h.g8 h.R₁pos (fitR₂_pos _ h.R₁pos h.R₂pos) hκ0 b hQ h1 h2 (h.oldConfined b hl) ht

/-- **Frame bounds.** -/
theorem Hyp.frame_bounds (h : D.Hyp N M₀ D₀ L E) (i : Fin D.J) :
    (D.fQ i).det ≠ 0 ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, |D.fQ i e e'|) ≤ (632 * (4 * D.κ₀) ^ 2) / 2 ^ D.T ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, (|D.fQ i e e'| + |(D.fQ i)⁻¹ e e'|)) ≤
      4 * ((632 * (4 * D.κ₀) ^ 2) / 2 ^ D.T) + 4 / (D.Afr * D.S₂) ∧
    |(D.fQ i).det| = (D.Afr * D.S₁) * (D.Afr * D.S₂) ∧
    ∃ b, D.src b = D.key i := by
  obtain ⟨b, hb⟩ := exists_src_of_mem _ _ _ _ _ _ _ _ (D.key_mem i)
  obtain ⟨hQ, hR₁b, -, -, hR, hsum⟩ := h.fit b
  have hκ : 1 ≤ 4 * D.κ₀ := by have := h.κ₀one; linarith
  have hg1 : D.g ≤ 1 := by have := h.g8; linarith
  obtain ⟨hdet, habs, hent, hinv⟩ := frameQ_key_bounds (γ₀ := D.γ) (j₀ := D.j) (c₀ := D.c)
    (u₀ := D.u) (Q₀ := D.Qf) h.gpos hg1 h.g8 h.R₁pos (fitR₂_pos _ h.R₁pos h.R₂pos) hR hκ b hQ
    hR₁b hsum
  have hfQ : D.fQ i = keyQ D.g D.S₁ D.S₂ D.Afr (D.src b) := by
    rw [fQ, ← hb]; rfl
  rw [hfQ]
  exact ⟨hdet, hent, hinv, habs, b, hb⟩

/-- The frame center and velocity. -/
theorem Hyp.frame_cu (h : D.Hyp N M₀ D₀ L E) (i : Fin D.J) :
    ‖D.fc i‖ + ‖D.fu i‖ ≤ 4 * N ^ M₀ + 8 * D.κ₀ := by
  obtain ⟨b, hb⟩ := exists_src_of_mem _ _ _ _ _ _ _ _ (D.key_mem i)
  obtain ⟨hQ, -, -, -, -, -⟩ := h.fit b
  have hT : (0 : ℝ) < 1 / 2 ^ D.T := by positivity
  have hcf := frame_center_velocity_le (tm := tmid D.T (coarseIdx (D.j b))) h.gpos h.g8 h.S₁pos
    h.S₂pos hT (c := D.c b) (u := D.u b) hQ
  have hfc : D.fc i = frameC D.g D.S₁ D.S₂ (1 / 2 ^ D.T) (tmid D.T (coarseIdx (D.j b)))
      (chartCode D.g D.S₁ D.S₂ (1 / 2 ^ D.T) (tmid D.T (coarseIdx (D.j b))) (D.c b) (D.u b)
        (D.Qf b)) := by
    rw [fc, ← hb]; rfl
  have hfu : D.fu i = frameU D.g D.S₁ D.S₂ (1 / 2 ^ D.T)
      (chartCode D.g D.S₁ D.S₂ (1 / 2 ^ D.T) (tmid D.T (coarseIdx (D.j b))) (D.c b) (D.u b)
        (D.Qf b)) := by
    rw [fu, ← hb]; rfl
  rw [hfc, hfu]
  refine hcf.trans ?_
  -- the midpoint lies in `[0, 1]`
  have htm0 : 0 ≤ tmid D.T (coarseIdx (D.j b)) := by unfold tmid; positivity
  have htm1 : tmid D.T (coarseIdx (D.j b)) ≤ 1 := by
    unfold tmid
    have hlt := (coarseIdx (D.j b)).isLt
    have hpos : (0 : ℝ) < 2 ^ D.T := by positivity
    rw [div_le_one hpos]
    have : ((coarseIdx (D.j b) : ℕ) : ℝ) + 1 ≤ 2 ^ D.T := by exact_mod_cast hlt
    linarith
  have hS₁ : D.S₁ ≤ D.κ₀ / 2 ^ D.T := by
    have h1 := h.R₁_le b
    unfold S₁
    calc 2 ^ D.s * D.R₁ ≤ 2 ^ D.s * (D.κ₀ / 2 ^ (D.T + D.s)) := by gcongr
      _ = D.κ₀ / 2 ^ D.T := by rw [pow_add]; field_simp
  have hS₂ := h.S₂_le_S₁
  have hκ := h.κ₀one
  have hcu := h.cu b
  have hNM : 0 ≤ N ^ M₀ := by have := h.N2; positivity
  have hpT : (1 : ℝ) ≤ 2 ^ D.T := one_le_pow₀ (by norm_num)
  have hdiv : (D.S₁ + D.S₂) / (1 / 2 ^ D.T) ≤ 2 * D.κ₀ := by
    rw [div_div_eq_mul_div, div_one]
    have : D.S₁ * 2 ^ D.T ≤ D.κ₀ := by
      have := mul_le_mul_of_nonneg_right hS₁ (by positivity : (0 : ℝ) ≤ 2 ^ D.T)
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    have : D.S₂ * 2 ^ D.T ≤ D.S₁ * 2 ^ D.T := by gcongr
    nlinarith
  have hS12 : D.S₁ + D.S₂ ≤ 2 * D.κ₀ := by
    have : D.κ₀ / 2 ^ D.T ≤ D.κ₀ := div_le_self (by linarith) hpT
    linarith
  have hu := norm_nonneg (D.u b)
  have hc := norm_nonneg (D.c b)
  rw [abs_of_nonneg htm0]
  nlinarith

end PrepData

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
