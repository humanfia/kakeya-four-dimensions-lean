-- Adapted from this LOT tree, o232, session x0891, commit c506359f (SourceSelectionMain.lean).
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionProof

/-!
# The selection component from x0812's per-sample selection

`sourceSelectionSpec_of_sample : SelectionSample → SourceSelectionSpec`: the outer schedule.
With x0923's `sourceTrackingSpec` this gives `StageModels` (`stageModels_of_sample`).

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 4000000 in
/-- **The selection component from the per-sample selection.** -/
theorem sourceSelectionSpec_of_sample (hS : SelectionSample) : SourceSelectionSpec := by
  intro d₁ κ₁ ℓ S η ρ hd₁ hd₁' hκ₁ hκ₁' hℓ hS₀ hS' hη hρ hρ' n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  obtain ⟨T, N₀, hnT, hT1, hN₀2, hup⟩ := exists_rawUpgrade (n : ℝ) hn1
  have hT0 : 0 < T := by linarith
  have hGc : (0 : ℝ) < (groupsC : ℝ) + 2 := by positivity
  set u₀ : ℝ := min (min (κ₁ * ρ / (T * (((n : ℝ) + 2) ^ 2 * ((groupsC : ℝ) + 2)) * 10 ^ 15))
    (η / ((n : ℝ) + 2))) (min (ℓ / (8 * ((n : ℝ) + 2))) 1) with hu₀def
  have hu₀ : 0 < u₀ := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by positivity) one_pos)
  refine ⟨u₀, hu₀, fun u hu hu' => ?_⟩
  have hu1 : u * T * (((n : ℝ) + 2) ^ 2 * ((groupsC : ℝ) + 2)) * 10 ^ 15 ≤ κ₁ * ρ := by
    have h := hu'.trans ((min_le_left _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hu2 : u * ((n : ℝ) + 2) ≤ η := by
    have h := hu'.trans ((min_le_left _ _).trans (min_le_right _ _))
    rwa [le_div_iff₀ (by positivity)] at h
  have hu3 : u * ((n : ℝ) + 2) ≤ ℓ / 8 := by
    have h := hu'.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hule1 : u ≤ 1 := hu'.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨u / (10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2)), by positivity,
    fun gain hg hg' m s δ₀ hgrid hδ₀ hδ₀' => ?_⟩
  have hg1 : gain * (10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2)) ≤ u := by
    rwa [le_div_iff₀ (by positivity)] at hg'
  have hgu : gain ≤ u := by
    have : (1 : ℝ) ≤ 10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2) := by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have : (1 : ℝ) ≤ (groupsC : ℝ) + 2 := by linarith
      nlinarith
    nlinarith
  have hδ : δ₀ ≤ 1 / 2 := by nlinarith
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  refine ⟨1, fun ε hε => ?_⟩
  obtain ⟨hNge, hNt, hL, -, -, -, -, -⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G
      hprob
  have hN1 : ∀ k, (1 : ℝ) ≤ N k := fun k => le_trans (by norm_num) (hNge k)
  -- the budget, the axis width and the tolerances
  set b₀ : ℝ := selectionBudget n ρ u L with hb₀def
  have hb₀ : 0 < b₀ := by
    simp only [hb₀def, selectionBudget, stagePower]
    positivity
  have hβ : 0 < min (stagePower n ρ / 1000) (ℓ / 1000) :=
    lt_min (by unfold stagePower; positivity) (by positivity)
  set a : ℝ := u * L * min (stagePower n ρ / 1000) (ℓ / 1000) / 2 with hadef
  have ha : 0 < a := by positivity
  have haη : a ≤ η * L := by
    have h1 : min (stagePower n ρ / 1000) (ℓ / 1000) ≤ 1 := by
      refine (min_le_left _ _).trans ?_
      unfold stagePower
      rw [div_le_one (by norm_num)]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : u ≤ η := by nlinarith
    have : a ≤ u * L / 2 := by
      rw [hadef]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ u * L)
      linarith
    nlinarith
  set τt : ℝ := min (b₀ / 2) (S * a / 8) with hτtdef
  have hτt : 0 < τt := lt_min (by positivity) (by positivity)
  set ma : ℝ := min b₀ (u * L / (2 * n)) with hmadef
  have hma : 0 < ma := lt_min hb₀ (by positivity)
  obtain ⟨Qd, hLQd, hQd, hQdc⟩ := exists_roundup_grid hL.le hb₀
  have huLn : 0 < u * L / n := by positivity
  have hmalt : ma < u * L / n := by
    refine (min_le_right _ _).trans_lt ?_
    have hn0 : (0 : ℝ) < n := by linarith
    exact div_lt_div_of_pos_left (mul_pos hu hL) hn0 (by linarith)
  have hab : u * L / n ≤ u * L * n := by
    have hn0 : (0 : ℝ) < n := by linarith
    rw [div_le_iff₀ hn0]
    have huL : 0 < u * L := mul_pos hu hL
    have : u * L ≤ u * L * n := le_mul_of_one_le_right huL.le hn1
    have : u * L * n ≤ u * L * n * n := le_mul_of_one_le_right (by positivity) hn1
    linarith
  obtain ⟨Qa₀, hQa₀, hQa₀c⟩ := exists_positive_angular_depth_menu huLn hab hma hmalt
  set Qa : Finset ℝ := insert a Qa₀ with hQadef
  have hQa : ∀ r ∈ Qa, 0 < r ∧ r ≤ η * L := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨ha, haη⟩
    · refine ⟨(hQa₀ r hr).1, (hQa₀ r hr).2.trans ?_⟩
      have h1 : u * n ≤ u * ((n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hu.le
      have h2 : u * n ≤ η := h1.trans hu2
      have h3 : u * n * L ≤ η * L := mul_le_mul_of_nonneg_right h2 hL.le
      calc u * L * n = u * n * L := by ring
        _ ≤ η * L := h3
  have hQac : ∀ t, u * L / n ≤ t → t ≤ u * L * n → ∃ r ∈ Qa, t - ma ≤ r ∧ r ≤ t := by
    intro t h1 h2
    obtain ⟨r, hr, hr1, hr2⟩ := hQa₀c t ⟨h1, h2⟩
    exact ⟨r, Finset.mem_insert_of_mem hr, hr1, hr2⟩
  have hax : a ∈ Qa := Finset.mem_insert_self _ _
  set aτ : ℝ := min (ε / 4000000) (min (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 4) (1 / 2))
    with haτdef
  have haτ : 0 < aτ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  -- the tails and the largeness facts
  let q : Fin Qd.card → ℝ := fun i => (Qd.equivFin.symm i : ℝ)
  let w : Fin Qa.card → ℝ := fun j => (Qa.equivFin.symm j : ℝ)
  have hq : ∀ i, q i ∈ Icc 0 L := fun i =>
    ⟨(hQd _ (Qd.equivFin.symm i).2).1, (hQd _ (Qd.equivFin.symm i).2).2⟩
  have hw : ∀ j, 0 < w j ∧ w j ≤ η * L := fun j => hQa _ (Qa.equivFin.symm j).2
  let aL : Fin 6 → ℝ := ![u * L, b₀ / 2, 3 / 4, aτ / 2, a, S * a / 2]
  let CL : Fin 6 → ℝ := ![N₀, selectionConst m n T κ₁ ρ u L, 2, 10 ^ 6 * ((m : ℝ) + 1) ^ 2, 4,
    1560 * m]
  have haL : ∀ l, 0 < aL l := by
    intro l
    fin_cases l
    · exact (show (0 : ℝ) < u * L from mul_pos hu hL)
    · exact (show (0 : ℝ) < b₀ / 2 from half_pos hb₀)
    · exact (show (0 : ℝ) < 3 / 4 by norm_num)
    · exact (show (0 : ℝ) < aτ / 2 from half_pos haτ)
    · exact (show (0 : ℝ) < a from ha)
    · exact (show (0 : ℝ) < S * a / 2 from half_pos (mul_pos hS₀ ha))
  obtain ⟨cd, ca, hcd, hca, hlate⟩ :=
    exists_lateFacts hprob q hq hτt w hw hτt 0 (by positivity : (0 : ℝ) < b₀ / 16) aL CL haL
  set c : ℝ := min cd ca with hcdef
  have hc : 0 < c := lt_min hcd hca
  have hE1 : ∀ᶠ k in atTop, 12 * (((Qd.card + Qa.card + 1 : ℕ) : ℝ)) ≤ N k ^ (7 * c / 8) :=
    eventually_rpow_ge hNt (by positivity)
  have hE3 : ∀ᶠ k in atTop, 48 * (m : ℝ) ≤ N k ^ (3 * c / 4) :=
    eventually_rpow_ge hNt (by positivity)
  obtain ⟨kp, hkp⟩ := eventually_atTop.mp (hlate.and (hE1.and hE3))
  refine ⟨min (min (c / 8) (S * a / 24)) (min (b₀ / 80) (min (aτ / 24) (1 / 4))),
    lt_min (lt_min (by positivity) (by positivity))
      (lt_min (by positivity) (lt_min (by positivity) (by norm_num))),
    kp, fun σ hσ hσ' k hk p hp H hH hmass => ?_⟩
  obtain ⟨hLF, hb1, hb3⟩ := hkp k hk
  have hσc : σ ≤ c / 8 := hσ'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hσa : σ ≤ S * a / 24 := hσ'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hσb : σ ≤ b₀ / 80 := hσ'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hστ : σ ≤ aτ / 24 :=
    hσ'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσq : σ ≤ 1 / 4 :=
    hσ'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hκ := hp.one_le_slack
  have hκ0 : 0 ≤ p.κ := by linarith
  have hκσ := hp.slack_le
  have hNk := hN1 k
  have hmono : ∀ x : ℝ, c ≤ x → ENNReal.ofReal (N k ^ (-x)) ≤ ENNReal.ofReal (N k ^ (-c)) :=
    fun x hx => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hNk (by linarith))
  have hupT : ∀ r ∈ Qd, k4_fixed_menu_density_pruning.upperTail (N k) (W k) (ω k) (ν k) (E k)
      (B k) f (g k) τt r ≤ ENNReal.ofReal (N k ^ (-c)) := by
    intro r hr
    have h := hLF.pure (Qd.equivFin ⟨r, hr⟩)
    have hqr : q (Qd.equivFin ⟨r, hr⟩) = r := by simp [q]
    rw [hqr] at h
    exact h.trans (hmono cd (min_le_left _ _))
  have hlowT : lowerTail (N k) L (W k) (ω k) (ν k) (E k) (B k) f (g k) τt ≤
      ENNReal.ofReal (N k ^ (-c)) := hLF.lower.trans (hmono cd (min_le_left _ _))
  have hangT : ∀ r ∈ Qa, angularTail (N k) L S (W k) (ω k) (ν k) (E k) (B k) f (G k) τt r ≤
      ENNReal.ofReal (N k ^ (-c)) := by
    intro r hr
    have h := hLF.angular (Qa.equivFin ⟨r, hr⟩)
    have hwr : w (Qa.equivFin ⟨r, hr⟩) = r := by simp [w]
    rw [hwr] at h
    exact h.trans (hmono ca (min_le_right _ _))
  have hb0 : N₀ ≤ N k ^ (u * L) := hLF.big 0
  have hbc : selectionConst m n T κ₁ ρ u L ≤ N k ^ (b₀ / 2) := hLF.big 1
  have hb2 : (2 : ℝ) ≤ N k ^ (3 / 4 : ℝ) := hLF.big 2
  have hbm : 10 ^ 6 * ((m : ℝ) + 1) ^ 2 ≤ N k ^ (aτ / 2) := hLF.big 3
  have hb4 : (4 : ℝ) ≤ N k ^ a := hLF.big 4
  have hb5 : 1560 * (m : ℝ) ≤ N k ^ (S * a / 2) := hLF.big 5
  have hK1 : 1 ≤ K k := hprob.2.2.1.1 k
  have hconst0 : 0 ≤ selectionConst m n T κ₁ ρ u L := by
    unfold selectionConst
    positivity
  have hτtb : τt ≤ b₀ := (min_le_left _ _).trans (half_le_self hb₀.le)
  have hτta : 2 * τt ≤ S * a / 4 := by
    have := min_le_right (b₀ / 2) (S * a / 8)
    linarith
  have hK0 : 0 ≤ K k := le_trans zero_le_one hK1
  have hA0 : (0 : ℝ) ≤ 10 ^ 6 * ((m : ℝ) + 1) ^ 2 := by positivity
  have hax2 : u * L * min (stagePower n ρ / 1000) (ℓ / 1000) =
      2 * (u * L * min (stagePower n ρ / 1000) (ℓ / 1000) / 2) := by ring
  exact selection_at_sample hS hd₁ hd₁' hκ₁ hκ₁' hℓ hS₀ hS' hη hρ hρ' hn hu hg hgrid hδ₀ hδ₀' hδ
    hprob hprof hε hσ hp hnT hup hu1 hu2 hu3 hg1 hLQd hQd hb₀ hQdc hQa hma hQac hτt.le
    hτtb le_rfl (min_le_left _ _) hax hb0
    (SelectionNumbers.const_budget hNk hκ0 hκσ hσb hK0 hLF.K_le hconst0 hbc)
    (SelectionNumbers.two_kappa hNk hκσ hσq hb2)
    (SelectionNumbers.floor_room hNk hκ0 hκσ hστ hA0 hbm)
    (SelectionNumbers.floor_inv_le hNk (min_le_left _ _))
    (SelectionNumbers.floor_inv_le hNk ((min_le_right _ _).trans (min_le_left _ _)))
    (SelectionNumbers.floor_inv_le hNk ((min_le_right _ _).trans (min_le_right _ _)))
    hupT hlowT hangT
    (SelectionNumbers.budget hNk hκ hκσ hσc hσa hτta
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hb1 hb5 hb3)
    (SelectionNumbers.axis_full hNk hax2 hκ hb4) H hH hmass

end

end Submission.Obl.k4_finite_affine_parent_sources
