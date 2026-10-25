-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.HalfEndgameLemmas.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.HalfConfig
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PlaneCover
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Packing

/-!
# Lemmas for the parallel-projection endgame at `s = 1/2`

* `norm_le_frame`, `pin_dist_le_of_cots`: a pin far from `ℓ₀` is determined, in a
  Lipschitz way, by its two cotangents from the base pins on `ℓ₀`.
* `separated_card_le_ball`: an `r`-separated plane set in a ball of radius `R ≥ r` has at
  most `225 (R / r) ^ 2` points.
* `cot_value_count`: Katz–Tao bushes give Frostman counts of their cotangents.
* `cover_of_centers`: a covering by balls around the points of a finite set.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

theorem norm_le_frame {n : Plane} (hn : ‖n‖ = 1) (v : Plane) :
    ‖v‖ ≤ |inner ℝ v (perp n)| + |inner ℝ v n| := by
  have h := inner_frame hn v v
  rw [real_inner_self_eq_norm_sq] at h
  have h2 : ‖v‖ ^ 2 ≤ (|inner ℝ v (perp n)| + |inner ℝ v n|) ^ 2 := by
    rw [h]
    nlinarith [abs_nonneg (inner ℝ v (perp n)), abs_nonneg (inner ℝ v n),
      sq_abs (inner ℝ v (perp n)), sq_abs (inner ℝ v n)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h2

theorem abs_alongCoord_le {n p₀ q : Plane} (hn : ‖n‖ = 1) (hq : ‖q - p₀‖ ≤ 8) :
    |alongCoord n p₀ q| ≤ 8 := by
  unfold alongCoord
  calc |inner ℝ (q - p₀) (perp n)| ≤ ‖q - p₀‖ * ‖perp n‖ := abs_real_inner_le_norm _ _
    _ = ‖q - p₀‖ := by rw [perp_norm, hn, mul_one]
    _ ≤ 8 := hq

theorem abs_acrossCoord_le {n p₀ q : Plane} (hn : ‖n‖ = 1) (hq : ‖q - p₀‖ ≤ 8) :
    |acrossCoord n p₀ q| ≤ 8 := by
  unfold acrossCoord
  calc |inner ℝ (q - p₀) n| ≤ ‖q - p₀‖ * ‖n‖ := abs_real_inner_le_norm _ _
    _ = ‖q - p₀‖ := by rw [hn, mul_one]
    _ ≤ 8 := hq

/-- A pin far from `ℓ₀` is a Lipschitz function of its two cotangents. -/
theorem pin_dist_le_of_cots {n p₀ q q' : Plane} {h₁ h₂ c : ℝ} (hn : ‖n‖ = 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (hgap : c ≤ |h₂ - h₁|) (hh₁ : |h₁| ≤ 8)
    (hq : c ≤ acrossCoord n p₀ q) (hq' : c ≤ acrossCoord n p₀ q')
    (hqb : ‖q - p₀‖ ≤ 8) (hqb' : ‖q' - p₀‖ ≤ 8) :
    dist q q' ≤ 1100 / c ^ 2 *
      (|(alongCoord n p₀ q - h₁) / acrossCoord n p₀ q -
          (alongCoord n p₀ q' - h₁) / acrossCoord n p₀ q'| +
        |(alongCoord n p₀ q - h₂) / acrossCoord n p₀ q -
          (alongCoord n p₀ q' - h₂) / acrossCoord n p₀ q'|) := by
  set X := alongCoord n p₀ q
  set Y := acrossCoord n p₀ q
  set X' := alongCoord n p₀ q'
  set Y' := acrossCoord n p₀ q'
  have hY : 0 < Y := hc.trans_le hq
  have hY' : 0 < Y' := hc.trans_le hq'
  have hY8 : Y ≤ 8 := (le_abs_self Y).trans (abs_acrossCoord_le hn hqb)
  have hY8' : Y' ≤ 8 := (le_abs_self Y').trans (abs_acrossCoord_le hn hqb')
  have hX8' : |X'| ≤ 8 := abs_alongCoord_le hn hqb'
  set Δα := (X - h₁) / Y - (X' - h₁) / Y'
  set Δβ := (X - h₂) / Y - (X' - h₂) / Y'
  have hgap' : 0 < |h₂ - h₁| := hc.trans_le hgap
  have hgne : h₂ - h₁ ≠ 0 := abs_pos.mp hgap'
  -- the across coordinates
  have hinv : (h₂ - h₁) * (1 / Y - 1 / Y') = Δα - Δβ := by
    simp only [Δα, Δβ]
    field_simp
    ring
  have hYY : |Y - Y'| ≤ 64 / c * (|Δα| + |Δβ|) := by
    have h1 : |1 / Y - 1 / Y'| ≤ (|Δα| + |Δβ|) / c := by
      rw [le_div_iff₀ hc]
      have h2 : |(h₂ - h₁) * (1 / Y - 1 / Y')| ≤ |Δα| + |Δβ| := by
        rw [hinv]
        exact abs_sub _ _
      rw [abs_mul] at h2
      calc |1 / Y - 1 / Y'| * c ≤ |1 / Y - 1 / Y'| * |h₂ - h₁| :=
            mul_le_mul_of_nonneg_left hgap (abs_nonneg _)
        _ = |h₂ - h₁| * |1 / Y - 1 / Y'| := mul_comm _ _
        _ ≤ |Δα| + |Δβ| := h2
    have h3 : Y - Y' = -(Y * Y') * (1 / Y - 1 / Y') := by
      field_simp
      ring
    rw [h3, abs_mul, abs_neg, abs_of_pos (mul_pos hY hY')]
    calc Y * Y' * |1 / Y - 1 / Y'| ≤ 64 * ((|Δα| + |Δβ|) / c) := by
          apply mul_le_mul _ h1 (abs_nonneg _) (by norm_num)
          nlinarith
      _ = 64 / c * (|Δα| + |Δβ|) := by ring
  -- the along coordinates
  have hα' : |(X' - h₁) / Y'| ≤ 16 / c := by
    rw [abs_div, abs_of_pos hY', div_le_div_iff₀ hY' hc]
    have : |X' - h₁| ≤ 16 := (abs_sub _ _).trans (by linarith)
    nlinarith [abs_nonneg (X' - h₁)]
  have hXX : |X - X'| ≤ 8 * |Δα| + 16 / c * (64 / c * (|Δα| + |Δβ|)) := by
    have e : X - X' = Δα * Y + (X' - h₁) / Y' * (Y - Y') := by
      simp only [Δα]
      field_simp
      ring
    rw [e]
    calc |Δα * Y + (X' - h₁) / Y' * (Y - Y')| ≤ |Δα * Y| + |(X' - h₁) / Y' * (Y - Y')| :=
          abs_add_le _ _
      _ = |Δα| * Y + |(X' - h₁) / Y'| * |Y - Y'| := by
          rw [abs_mul, abs_mul, abs_of_pos hY]
      _ ≤ 8 * |Δα| + 16 / c * (64 / c * (|Δα| + |Δβ|)) := by
          have h1 : |Δα| * Y ≤ 8 * |Δα| := by nlinarith [abs_nonneg Δα]
          have h2 : |(X' - h₁) / Y'| * |Y - Y'| ≤ 16 / c * (64 / c * (|Δα| + |Δβ|)) :=
            mul_le_mul hα' hYY (abs_nonneg _) (by positivity)
          linarith
  -- the distance
  have hd : dist q q' ≤ |X - X'| + |Y - Y'| := by
    rw [dist_eq_norm]
    have h := norm_le_frame hn (q - q')
    have e1 : inner ℝ (q - q') (perp n) = X - X' := (alongCoord_sub n p₀ q q').symm
    have e2 : inner ℝ (q - q') n = Y - Y' := (acrossCoord_sub n p₀ q q').symm
    rwa [e1, e2] at h
  have hsum : 0 ≤ |Δα| + |Δβ| := by positivity
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  calc dist q q' ≤ |X - X'| + |Y - Y'| := hd
    _ ≤ 8 * |Δα| + 16 / c * (64 / c * (|Δα| + |Δβ|)) + 64 / c * (|Δα| + |Δβ|) := by linarith
    _ ≤ (8 + 1024 / c ^ 2 + 64 / c) * (|Δα| + |Δβ|) := by
        have : 8 * |Δα| ≤ 8 * (|Δα| + |Δβ|) := by nlinarith [abs_nonneg Δβ]
        have e : 16 / c * (64 / c * (|Δα| + |Δβ|)) = 1024 / c ^ 2 * (|Δα| + |Δβ|) := by
          field_simp
          ring
        nlinarith
    _ ≤ 1100 / c ^ 2 * (|Δα| + |Δβ|) := by
        apply mul_le_mul_of_nonneg_right _ hsum
        have h1 : 8 ≤ 8 / c ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        have h2 : 64 / c ≤ 64 / c ^ 2 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith
        have e : 1100 / c ^ 2 = 8 / c ^ 2 + 1024 / c ^ 2 + 64 / c ^ 2 + 4 / c ^ 2 := by ring
        have h4 : 0 ≤ 4 / c ^ 2 := by positivity
        linarith

/-- An `r`-separated plane set inside a ball of radius `R ≥ r` has at most `225 (R / r)²`
points. -/
theorem separated_card_le_ball {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (S : Finset Plane)
    (c : Plane) (hball : ∀ x ∈ S, dist x c ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ dist x y) :
    (S.card : ℝ) ≤ 225 * (R / r) ^ 2 := by
  obtain ⟨m, hm, hcov⟩ := plane_closedBall_radius_cover hr hrR
  obtain ⟨d, hd⟩ := hcov c
  have hS : Covers r (↑S : Set Plane) d := by
    intro x hx
    exact hd (Metric.mem_closedBall.mpr (hball x hx))
  have h := separated_card_le_twentyfive_mul_cover hr S hsep hS
  have h' : (S.card : ℝ) ≤ 25 * (m : ℝ) := by exact_mod_cast h
  nlinarith

/-- Katz–Tao bushes give Frostman counts of their cotangents. -/
theorem cot_value_count {n : Plane} {r K c' x R : ℝ} {E : Finset Plane} (hn : ‖n‖ = 1)
    (hr : 0 < r) (hc' : 0 < c') (hK : 0 ≤ K) (hE : HalfBush r K E) (hR : r * c' ≤ 2 * R) :
    ((E.filter (fun e => c' ≤ |inner ℝ e (perp n)| ∧ |cotNormal n e - x| ≤ R)).card : ℝ) ≤
      2 * K * (2 * R / (c' * r)) ^ (1 / 2 : ℝ) := by
  classical
  obtain ⟨hunit, _, hKT⟩ := hE
  set F := E.filter (fun e => c' ≤ |inner ℝ e (perp n)| ∧ |cotNormal n e - x| ≤ R)
  set Fp := F.filter (fun e => 0 ≤ inner ℝ e (perp n))
  set Fm := F.filter (fun e => ¬ 0 ≤ inner ℝ e (perp n))
  have hsplit : (F.card : ℝ) = (Fp.card : ℝ) + (Fm.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not _).symm
  have hRpos : 0 ≤ 2 * R / (c' * r) := by
    apply div_nonneg _ (by positivity)
    nlinarith [mul_pos hr hc']
  have hrad : r ≤ 2 * R / c' := by
    rw [le_div_iff₀ hc']
    linarith
  have hbound : ∀ e' ∈ E, ∀ G : Finset Plane, G ⊆ E → (∀ e ∈ G, dist e e' ≤ 2 * R / c') →
      (G.card : ℝ) ≤ K * (2 * R / (c' * r)) ^ (1 / 2 : ℝ) := by
    intro e' he' G hGE hG
    have h := hKT e' (hunit e' he') (2 * R / c') hrad
    have hsub : G ⊆ E.filter (fun e => dist e e' ≤ 2 * R / c') := by
      intro e he
      exact Finset.mem_filter.mpr ⟨hGE he, hG e he⟩
    have hc : ((G.card : ℝ)) ≤ ((E.filter (fun e => dist e e' ≤ 2 * R / c')).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have e : 2 * R / c' / r = 2 * R / (c' * r) := by field_simp
    rw [e] at h
    linarith
  have hFp : (Fp.card : ℝ) ≤ K * (2 * R / (c' * r)) ^ (1 / 2 : ℝ) := by
    rcases Fp.eq_empty_or_nonempty with h0 | ⟨e', he'⟩
    · rw [h0, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hK (Real.rpow_nonneg hRpos _)
    · have he'F := (Finset.mem_filter.mp he').1
      have he'E := (Finset.mem_filter.mp he'F).1
      apply hbound e' he'E Fp (fun e he => (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1)
      intro e he
      have heF := Finset.mem_filter.mp he
      have heE := Finset.mem_filter.mp heF.1
      have hw : c' ≤ inner ℝ e (perp n) := by
        have := heE.2.1
        rwa [abs_of_nonneg heF.2] at this
      have hw' : c' ≤ inner ℝ e' (perp n) := by
        have := (Finset.mem_filter.mp he'F).2.1
        rwa [abs_of_nonneg (Finset.mem_filter.mp he').2] at this
      have hexp := cotNormal_expanding hn (hunit e heE.1) (hunit e' he'E) hc' hw hw'
      have hcot : |cotNormal n e - cotNormal n e'| ≤ 2 * R := by
        have h1 := heE.2.2
        have h2 := (Finset.mem_filter.mp he'F).2.2
        have := abs_sub_le (cotNormal n e) x (cotNormal n e')
        rw [abs_sub_comm x] at this
        linarith
      rw [dist_eq_norm, le_div_iff₀ hc']
      linarith
  have hFm : (Fm.card : ℝ) ≤ K * (2 * R / (c' * r)) ^ (1 / 2 : ℝ) := by
    rcases Fm.eq_empty_or_nonempty with h0 | ⟨e', he'⟩
    · rw [h0, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hK (Real.rpow_nonneg hRpos _)
    · have he'F := (Finset.mem_filter.mp he').1
      have he'E := (Finset.mem_filter.mp he'F).1
      apply hbound e' he'E Fm (fun e he => (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1)
      intro e he
      have heF := Finset.mem_filter.mp he
      have heE := Finset.mem_filter.mp heF.1
      have hneg : inner ℝ e (perp n) < 0 := lt_of_not_ge heF.2
      have hneg' : inner ℝ e' (perp n) < 0 := lt_of_not_ge (Finset.mem_filter.mp he').2
      have hw : c' ≤ inner ℝ (-e) (perp n) := by
        have := heE.2.1
        rw [abs_of_neg hneg] at this
        rwa [inner_neg_left]
      have hw' : c' ≤ inner ℝ (-e') (perp n) := by
        have := (Finset.mem_filter.mp he'F).2.1
        rw [abs_of_neg hneg'] at this
        rwa [inner_neg_left]
      have hexp := cotNormal_expanding hn (by rw [norm_neg]; exact hunit e heE.1)
        (by rw [norm_neg]; exact hunit e' he'E) hc' hw hw'
      rw [cotNormal_neg, cotNormal_neg] at hexp
      have hcot : |cotNormal n e - cotNormal n e'| ≤ 2 * R := by
        have h1 := heE.2.2
        have h2 := (Finset.mem_filter.mp he'F).2.2
        have := abs_sub_le (cotNormal n e) x (cotNormal n e')
        rw [abs_sub_comm x] at this
        linarith
      have e2 : ‖-e - -e'‖ = dist e e' := by
        rw [dist_eq_norm, ← norm_neg]
        congr 1
        abel
      rw [e2] at hexp
      rw [le_div_iff₀ hc']
      linarith
  linarith

/-- A covering by closed balls around the points of a finite set of centers. -/
theorem cover_of_centers {δ : ℝ} (C : Finset ℝ) (S : Set ℝ)
    (h : ∀ x ∈ S, ∃ c ∈ C, dist x c ≤ δ) :
    ∃ (m : ℕ) (cc : Fin m → ℝ), Covers δ S cc ∧ (m : ℝ) = (C.card : ℝ) := by
  classical
  let e := C.equivFin
  refine ⟨C.card, fun i => (e.symm i : ℝ), ?_, rfl⟩
  intro x hx
  obtain ⟨c, hc, hxc⟩ := h x hx
  refine Set.mem_iUnion.mpr ⟨e ⟨c, hc⟩, ?_⟩
  simp only [Equiv.symm_apply_apply, Metric.mem_closedBall]
  exact hxc

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
