-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.TubeLineFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.CoarseTubes
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.Thinning

/-!
# Tube-line Frostman from counts in coarser tubes

In the chart of a coarse-class tube `t` (axis `perp t.2`, centre `(0, (lineChart (perp t.2) t).2)`,
scale `λ = 16 Δ`, as in `caseA_coarse_false`) a box of side `2 ρ` of tube-line coordinates is a
sub-tube of width `16 Δ ρ`. If `g` maps lines to a `StripSep σ`-separated family with the
`9σ/σ` geometry and `16 Δ ρ ≤ σ ≤ Δ`, the lines of the box have at most `1022²` images
(`box_images_card_le`): their charts lie in a sup-ball of radius `51 σ` and are `σ/10`-separated.
Hence the number of lines of the box is at most `1022²` times the largest fibre of `g`
(`box_card_le_fibres`), which turns tube counts at the scales of a palette into the tube-line
Frostman hypothesis of `caseA_coarse_false` (`tube_line_frostman_of_fibres`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

/-- `cotNormal` is `8`-Lipschitz on transverse unit normals. -/
theorem cotNormal_lipschitz {v e e' : Plane} (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (hw : 1 / 2 ≤ |inner ℝ e (perp v)|) (hw' : 1 / 2 ≤ |inner ℝ e' (perp v)|) :
    |cotNormal v e - cotNormal v e'| ≤ 8 * ‖e - e'‖ := by
  have hpv : ‖perp v‖ = 1 := by rw [perp_norm, hv]
  have hev : |inner ℝ e v| ≤ 1 := by
    have := abs_real_inner_le_norm e v; rw [he, hv] at this; linarith
  have hepv : |inner ℝ e (perp v)| ≤ 1 := by
    have := abs_real_inner_le_norm e (perp v); rw [he, hpv] at this; linarith
  have hdv : |inner ℝ (e' - e) v| ≤ ‖e - e'‖ := by
    have := abs_real_inner_le_norm (e' - e) v; rw [hv, mul_one, norm_sub_rev] at this; exact this
  have hdpv : |inner ℝ (e' - e) (perp v)| ≤ ‖e - e'‖ := by
    have := abs_real_inner_le_norm (e' - e) (perp v)
    rw [hpv, mul_one, norm_sub_rev] at this; exact this
  have hne : inner ℝ e (perp v) ≠ 0 := by intro h; rw [h, abs_zero] at hw; linarith
  have hne' : inner ℝ e' (perp v) ≠ 0 := by intro h; rw [h, abs_zero] at hw'; linarith
  have hnum : cotNormal v e - cotNormal v e' =
      (inner ℝ (e' - e) v * inner ℝ e (perp v) - inner ℝ e v * inner ℝ (e' - e) (perp v)) /
        (inner ℝ e (perp v) * inner ℝ e' (perp v)) := by
    simp only [cotNormal, inner_sub_left]
    field_simp
    ring
  rw [hnum, abs_div, abs_mul (inner ℝ e (perp v))]
  have hden : 1 / 4 ≤ |inner ℝ e (perp v)| * |inner ℝ e' (perp v)| := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  have hN : |inner ℝ (e' - e) v * inner ℝ e (perp v) - inner ℝ e v * inner ℝ (e' - e) (perp v)| ≤
      2 * ‖e - e'‖ := by
    calc _ ≤ |inner ℝ (e' - e) v * inner ℝ e (perp v)| +
          |inner ℝ e v * inner ℝ (e' - e) (perp v)| := abs_sub _ _
      _ = |inner ℝ (e' - e) v| * |inner ℝ e (perp v)| +
          |inner ℝ e v| * |inner ℝ (e' - e) (perp v)| := by rw [abs_mul, abs_mul]
      _ ≤ ‖e - e'‖ * 1 + 1 * ‖e - e'‖ := by
          gcongr
      _ = 2 * ‖e - e'‖ := by ring
  have hpos : 0 ≤ ‖e - e'‖ := norm_nonneg _
  nlinarith


/-- Closeness up to sign composes. -/
theorem near_pm_trans {a b c : Plane} {x y : ℝ} (hab : dist a b < x ∨ dist a (-b) < x)
    (hbc : dist b c < y ∨ dist b (-c) < y) : dist a c < x + y ∨ dist a (-c) < x + y := by
  have e1 : dist (-b) (-c) = dist b c := dist_neg_neg b c
  have e2 : dist (-b) c = dist b (-c) := by
    rw [dist_eq_norm, dist_eq_norm, show -b - c = -(b - -c) by abel, norm_neg]
  rcases hab with h1 | h1 <;> rcases hbc with h2 | h2
  · exact Or.inl (lt_of_le_of_lt (dist_triangle a b c) (by linarith))
  · exact Or.inr (lt_of_le_of_lt (dist_triangle a b (-c)) (by linarith))
  · exact Or.inr (lt_of_le_of_lt (dist_triangle a (-b) (-c)) (by rw [e1]; linarith))
  · exact Or.inl (lt_of_le_of_lt (dist_triangle a (-b) c) (by rw [e2]; linarith))

/-- A unit normal within `θ ≤ 1/2` of `± t.2` is transverse to the axis `perp t.2`. -/
theorem transverse_of_near {t2 e : Plane} {θ : ℝ} (hθ : θ ≤ 1 / 2) (ht2 : ‖t2‖ = 1)
    (he : ‖e‖ = 1) (hd : dist e t2 < θ ∨ dist e (-t2) < θ) :
    1 / 2 ≤ |inner ℝ e (perp (perp t2))| := by
  rw [perp_perp, inner_neg_right, abs_neg]
  obtain ⟨σ, hσ, hdσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖e - σ • t2‖ < θ := by
    rcases hd with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_smul, ← dist_eq_norm]; exact h⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_smul, ← dist_eq_norm]; exact h⟩
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hθ0 : 0 ≤ θ := le_trans (norm_nonneg _) hdσ.le
  have hsq : ‖e - σ • t2‖ ^ 2 = 2 - 2 * (σ * inner ℝ e t2) := by
    rw [@norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hσabs, he, ht2]
    ring
  have hlt : ‖e - σ • t2‖ ^ 2 < θ ^ 2 := pow_lt_pow_left₀ hdσ (norm_nonneg _) (by norm_num)
  have hθ2 : θ ^ 2 ≤ 1 / 4 := by nlinarith
  have h1 : 1 / 2 ≤ σ * inner ℝ e t2 := by linarith
  calc 1 / 2 ≤ σ * inner ℝ e t2 := h1
    _ ≤ |σ * inner ℝ e t2| := le_abs_self _
    _ = |inner ℝ e t2| := by rw [abs_mul, hσabs, one_mul]

/-- **A box of tube-line coordinates meets few coarse lines.** -/
theorem box_images_card_le {t : Plane × Plane} {Δ σ ρ : ℝ} (hΔ : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4)
    (hσ : 0 < σ) (hσΔ : σ ≤ Δ) (hρ : 16 * Δ * ρ ≤ σ) (ht2 : ‖t.2‖ = 1)
    (J : Finset (Plane × Plane))
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ (dist j.2 t.2 < Δ ∨ dist j.2 (-t.2) < Δ))
    (g : Plane × Plane → Plane × Plane)
    (hg : ∀ j ∈ J, ‖(g j).2‖ = 1 ∧ ‖(g j).1‖ ≤ 4 ∧ |inner ℝ (j.1 - (g j).1) (g j).2| < 9 * σ ∧
      (dist j.2 (g j).2 < σ ∨ dist j.2 (-(g j).2) < σ))
    (hgsep : ∀ j ∈ J, ∀ j' ∈ J, g j ≠ g j' → StripSep σ (g j) (g j'))
    (c a : ℝ) :
    (((J.filter (fun j =>
        |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (16 * Δ) j).1 - c| ≤ ρ ∧
        |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (16 * Δ) j).2 - a| ≤ ρ)).image g).card :
          ℝ) ≤ 1022 ^ 2 := by
  classical
  set v := perp t.2 with hv
  have hvn : ‖v‖ = 1 := by rw [hv, perp_norm, ht2]
  set aT := (lineChart v t).2 with haT
  set lam := 16 * Δ with hlam
  have hlam0 : 0 < lam := by positivity
  set Jb := J.filter (fun j =>
    |(tubeLine v 0 aT lam j).1 - c| ≤ ρ ∧ |(tubeLine v 0 aT lam j).2 - a| ≤ ρ) with hJb
  set Img := Jb.image g with hImg
  set z₀ : ℝ × ℝ := (lam * c, aT + lam * a) with hz₀
  -- transversality of the lines and of their images
  have htj : ∀ j ∈ J, 1 / 2 ≤ |inner ℝ j.2 (perp v)| := by
    intro j hj
    obtain ⟨hj2, _, hjd⟩ := hJ j hj
    exact transverse_of_near (θ := Δ) (by linarith) ht2 hj2 hjd
  have htg : ∀ j ∈ J, 1 / 2 ≤ |inner ℝ (g j).2 (perp v)| := by
    intro j hj
    obtain ⟨hj2, _, hjd⟩ := hJ j hj
    obtain ⟨hg2, _, _, hgd⟩ := hg j hj
    have hgj : dist (g j).2 j.2 < σ ∨ dist (g j).2 (-j.2) < σ := by
      rcases hgd with h | h
      · exact Or.inl (by rw [dist_comm]; exact h)
      · refine Or.inr ?_
        rw [dist_eq_norm, show (g j).2 - -j.2 = j.2 - -(g j).2 by abel, ← dist_eq_norm]
        exact h
    have := near_pm_trans hgj hjd
    exact transverse_of_near (θ := σ + Δ) (by linarith) ht2 hg2 this
  -- the charts of the images lie in a sup-ball about `z₀`
  have hball : ∀ j ∈ Jb, dist (lineChart v (g j)) z₀ ≤ 51 * σ := by
    intro j hj
    obtain ⟨hjJ, hbox1, hbox2⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj2, hj1, _⟩ := hJ j hjJ
    obtain ⟨hg2, hg1, hginc, hgd⟩ := hg j hjJ
    have hslope_j : |(lineChart v j).1 - lam * c| ≤ σ := by
      have h := hbox1
      simp only [tubeLine, sub_zero] at h
      rw [show (lineChart v j).1 / lam - c = ((lineChart v j).1 - lam * c) / lam by
        field_simp, abs_div, abs_of_pos hlam0, div_le_iff₀ hlam0] at h
      nlinarith
    have hint_j : |(lineChart v j).2 - (aT + lam * a)| ≤ σ := by
      have h := hbox2
      simp only [tubeLine] at h
      rw [show ((lineChart v j).2 - aT) / lam - a = ((lineChart v j).2 - (aT + lam * a)) / lam by
        field_simp; ring, abs_div, abs_of_pos hlam0, div_le_iff₀ hlam0] at h
      nlinarith
    -- slopes of a line and of its image
    have hslope : |(lineChart v (g j)).1 - (lineChart v j).1| ≤ 8 * σ := by
      simp only [lineChart]
      rcases hgd with h | h
      · have := cotNormal_lipschitz hvn hg2 (htg j hjJ) (htj j hjJ)
        rw [← dist_eq_norm, dist_comm] at this
        linarith
      · have hneg : cotNormal v (g j).2 = cotNormal v (-(g j).2) := (cotNormal_neg _ _).symm
        rw [hneg]
        have hn2 : ‖-(g j).2‖ = 1 := by rw [norm_neg, hg2]
        have hw2 : 1 / 2 ≤ |inner ℝ (-(g j).2) (perp v)| := by
          rw [inner_neg_left, abs_neg]; exact htg j hjJ
        have := cotNormal_lipschitz hvn hn2 hw2 (htj j hjJ)
        rw [← dist_eq_norm, dist_comm] at this
        linarith
    -- intercepts of a line and of its image
    have hint : |(lineChart v (g j)).2 - (lineChart v j).2| ≤ 50 * σ := by
      have hne : inner ℝ (g j).2 (perp v) ≠ 0 := by
        intro h; have := htg j hjJ; rw [h, abs_zero] at this; linarith
      have hci := chart_incidence (p := (g j).1) (q := j.1) (e := (g j).2) (r := 9 * σ) hvn
        (by norm_num : (0 : ℝ) < 1 / 2) (htg j hjJ) hginc.le
      have hpin := lineChart_height_pin v j.1 j.2
      have hX : |(pointChart v j.1).1| ≤ 4 := by
        calc |(pointChart v j.1).1| = |inner ℝ j.1 v| := rfl
          _ ≤ ‖j.1‖ * ‖v‖ := abs_real_inner_le_norm _ _
          _ ≤ 4 := by rw [hvn, mul_one]; exact hj1
      simp only [height] at hci hpin
      have hgeq : lineChart v ((g j).1, (g j).2) = lineChart v (g j) := rfl
      have hjeq : lineChart v (j.1, j.2) = lineChart v j := rfl
      rw [hgeq] at hci
      rw [hjeq] at hpin
      set X := (pointChart v j.1).1
      have e : (lineChart v (g j)).2 - (lineChart v j).2 =
          -((pointChart v j.1).2 - ((lineChart v (g j)).1 * X + (lineChart v (g j)).2)) -
            ((lineChart v (g j)).1 - (lineChart v j).1) * X := by
        rw [← hpin]; ring
      rw [e]
      have h18 : 9 * σ / (1 / 2) = 18 * σ := by ring
      rw [h18] at hci
      calc _ ≤ |-((pointChart v j.1).2 - ((lineChart v (g j)).1 * X + (lineChart v (g j)).2))| +
            |((lineChart v (g j)).1 - (lineChart v j).1) * X| := abs_sub _ _
        _ ≤ 18 * σ + 8 * σ * 4 := by
            rw [abs_neg, abs_mul]
            have := mul_le_mul hslope hX (abs_nonneg _) (by linarith)
            linarith
        _ = 50 * σ := by ring
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
    constructor
    · calc |(lineChart v (g j)).1 - z₀.1|
          ≤ |(lineChart v (g j)).1 - (lineChart v j).1| + |(lineChart v j).1 - lam * c| := by
            rw [hz₀]; exact abs_sub_le _ _ _
        _ ≤ 51 * σ := by linarith
    · calc |(lineChart v (g j)).2 - z₀.2|
          ≤ |(lineChart v (g j)).2 - (lineChart v j).2| +
            |(lineChart v j).2 - (aT + lam * a)| := by
            rw [hz₀]; exact abs_sub_le _ _ _
        _ ≤ 51 * σ := by linarith
  -- the charts of distinct images are separated
  set L := Img.image (lineChart v) with hL
  have hsepL : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → σ / 10 ≤ dist l l' := by
    intro l hl l' hl' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hl'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hx'
    have hjJ := (Finset.mem_filter.mp hj).1
    have hj'J := (Finset.mem_filter.mp hj').1
    have hgne : g j ≠ g j' := by intro h; rw [h] at hne; exact hne rfl
    exact lineChart_separated hvn (hg j hjJ).1 (hg j' hj'J).1 (hg j' hj'J).2.1 (htg j hjJ)
      (htg j' hj'J) (hgsep j hjJ j' hj'J hgne)
  have hinj : Set.InjOn (lineChart v) ↑Img := by
    intro x hx x' hx' heq
    by_contra hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hx'
    have hjJ := (Finset.mem_filter.mp hj).1
    have hj'J := (Finset.mem_filter.mp hj').1
    have := lineChart_separated hvn (hg j hjJ).1 (hg j' hj'J).1 (hg j' hj'J).2.1 (htg j hjJ)
      (htg j' hj'J) (hgsep j hjJ j' hj'J hne)
    rw [heq, dist_self] at this
    linarith
  have hcardL : L.card = Img.card := Finset.card_image_of_injOn hinj
  have hfilt : L.filter (fun l => dist l z₀ ≤ 51 * σ) = L := by
    apply Finset.filter_true_of_mem
    intro l hl
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hball j hj
  have hpack := card_sup_ball_le (σ := σ / 10) (ρ := 51 * σ) (by positivity) (by positivity) L
    hsepL z₀
  rw [hfilt, hcardL] at hpack
  have e : (2 * (51 * σ) / (σ / 10) + 2) = 1022 := by field_simp; ring
  rw [e] at hpack
  exact hpack

/-- **Lines of a box: at most `1022²` fibres of the coarse map.** -/
theorem box_card_le_fibres {t : Plane × Plane} {Δ σ ρ : ℝ} (hΔ : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4)
    (hσ : 0 < σ) (hσΔ : σ ≤ Δ) (hρ : 16 * Δ * ρ ≤ σ) (ht2 : ‖t.2‖ = 1)
    (J : Finset (Plane × Plane))
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ (dist j.2 t.2 < Δ ∨ dist j.2 (-t.2) < Δ))
    (g : Plane × Plane → Plane × Plane)
    (hg : ∀ j ∈ J, ‖(g j).2‖ = 1 ∧ ‖(g j).1‖ ≤ 4 ∧ |inner ℝ (j.1 - (g j).1) (g j).2| < 9 * σ ∧
      (dist j.2 (g j).2 < σ ∨ dist j.2 (-(g j).2) < σ))
    (hgsep : ∀ j ∈ J, ∀ j' ∈ J, g j ≠ g j' → StripSep σ (g j) (g j'))
    {N : ℕ} (hN : ∀ T' : Plane × Plane, (J.filter (fun j => g j = T')).card ≤ N) (c a : ℝ) :
    ((J.filter (fun j =>
        |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (16 * Δ) j).1 - c| ≤ ρ ∧
        |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (16 * Δ) j).2 - a| ≤ ρ)).card : ℝ) ≤
      1022 ^ 2 * N := by
  classical
  set Jb := J.filter (fun j =>
    |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (16 * Δ) j).1 - c| ≤ ρ ∧
    |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (16 * Δ) j).2 - a| ≤ ρ) with hJb
  have hfib : ∀ b ∈ Jb.image g, (Jb.filter (fun j => g j = b)).card ≤ N := by
    intro b _
    refine le_trans (Finset.card_le_card ?_) (hN b)
    intro j hj
    obtain ⟨hjb, hgj⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjb).1, hgj⟩
  have h1 := Finset.card_le_mul_card_image Jb N hfib
  have h2 := box_images_card_le hΔ hΔ4 hσ hσΔ hρ ht2 J hJ g hg hgsep c a
  have h1' : (Jb.card : ℝ) ≤ N * (Jb.image g).card := by exact_mod_cast h1
  calc (Jb.card : ℝ) ≤ N * (Jb.image g).card := h1'
    _ ≤ N * 1022 ^ 2 := mul_le_mul_of_nonneg_left (by convert h2 using 2) (Nat.cast_nonneg _)
    _ = 1022 ^ 2 * N := by ring

/-- **Tube-line Frostman from coarse fibre counts**, in the form of `caseA_coarse_false`: for
every `ρ ∈ [δ, 1/16]` some scale `σ ∈ [16 Δ ρ, Δ]` has a separated coarse map whose fibres in
`J` number at most `N` with `1022² N ≤ K₀ ρ^(1+b) #J`; larger `ρ` are trivial. -/
theorem tube_line_frostman_of_fibres {t : Plane × Plane} {Δ δ K₀ b : ℝ} (hΔ : 0 < Δ)
    (hΔ4 : Δ ≤ 1 / 4) (ht2 : ‖t.2‖ = 1) (J : Finset (Plane × Plane))
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ (dist j.2 t.2 < Δ ∨ dist j.2 (-t.2) < Δ))
    (hscale : ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 / 16 → ∃ (σ : ℝ) (g : Plane × Plane → Plane × Plane) (N : ℕ),
      0 < σ ∧ 16 * Δ * ρ ≤ σ ∧ σ ≤ Δ ∧
      (∀ j ∈ J, ‖(g j).2‖ = 1 ∧ ‖(g j).1‖ ≤ 4 ∧ |inner ℝ (j.1 - (g j).1) (g j).2| < 9 * σ ∧
        (dist j.2 (g j).2 < σ ∨ dist j.2 (-(g j).2) < σ)) ∧
      (∀ j ∈ J, ∀ j' ∈ J, g j ≠ g j' → StripSep σ (g j) (g j')) ∧
      (∀ T' : Plane × Plane, (J.filter (fun j => g j = T')).card ≤ N) ∧
      1022 ^ 2 * (N : ℝ) ≤ K₀ * ρ ^ (1 + b) * J.card)
    (hbig : ∀ ρ : ℝ, 1 / 16 < ρ → 1 ≤ K₀ * ρ ^ (1 + b)) :
    ∀ c a ρ : ℝ, δ ≤ ρ →
      ((J.filter (fun j =>
        |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (16 * Δ) j).1 - c| ≤ ρ ∧
        |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (16 * Δ) j).2 - a| ≤ ρ)).card : ℝ) ≤
      K₀ * ρ ^ (1 + b) * J.card := by
  intro c a ρ hρ
  by_cases hsmall : ρ ≤ 1 / 16
  · obtain ⟨σ, g, N, hσ, hρσ, hσΔ, hg, hgsep, hN, hNle⟩ := hscale ρ hρ hsmall
    exact (box_card_le_fibres hΔ hΔ4 hσ hσΔ hρσ ht2 J hJ g hg hgsep hN c a).trans hNle
  · push Not at hsmall
    have h1 := hbig ρ hsmall
    calc ((J.filter _).card : ℝ) ≤ J.card := by exact_mod_cast Finset.card_filter_le _ _
      _ = 1 * J.card := by ring
      _ ≤ K₀ * ρ ^ (1 + b) * J.card := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/TubeLineFrostman.lean
