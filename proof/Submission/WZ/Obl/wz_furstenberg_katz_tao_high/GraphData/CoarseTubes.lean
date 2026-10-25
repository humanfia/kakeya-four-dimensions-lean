-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.CoarseTubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.CaseA

/-!
# Coarse classes as tubes

Take as tubes the classes at a coarser scale `Δ`: a fine class `j` belongs to the tube of a
coarse representative `c` when `j` and `c` fail `Δ`-separation (o213's `near_of_not_stripSep`
gives `|⟪j.1 - c.1, c.2⟫| < 9 Δ` and `j.2` within `Δ` of `± c.2`). With axis `v = perp c.2`,
centre `(0, (lineChart v c).2)` and width `Δs = 4 Δ`, the geometric per-tube hypotheses of
`caseA_false` hold automatically (`coarse_class_tube_geom`): transversality, chart slopes at most
`Δs`, and centred heights at most `7/2` on `|y| ≤ 4`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

/-- **Geometry of a coarse-class tube.** -/
theorem coarse_class_tube_geom {c j : Plane × Plane} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hc2 : ‖c.2‖ = 1) (hc1 : ‖c.1‖ ≤ 4) (hj2 : ‖j.2‖ = 1) (hj1 : ‖j.1‖ ≤ 4)
    (hnear : |inner ℝ (j.1 - c.1) c.2| < 9 * Δ)
    (hdir : dist j.2 c.2 < Δ ∨ dist j.2 (-c.2) < Δ) :
    1 / 2 ≤ |inner ℝ j.2 (perp (perp c.2))| ∧ |(lineChart (perp c.2) j).1| ≤ 4 * Δ ∧
    ∀ y : ℝ, |y| ≤ 4 →
      |lineHeight (tubeLine (perp c.2) 0 (lineChart (perp c.2) c).2 (4 * (4 * Δ)) j) y| ≤
        7 / 2 := by
  set v := perp c.2 with hv
  have hvn : ‖v‖ = 1 := by rw [hv, perp_norm, hc2]
  have hpv : perp v = -c.2 := perp_perp c.2
  obtain ⟨σ, hσ, hjσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖j.2 - σ • c.2‖ < Δ := by
    rcases hdir with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_smul, ← dist_eq_norm]; exact h⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_smul, ← dist_eq_norm]; exact h⟩
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hcv : inner ℝ c.2 v = 0 := perp_inner c.2
  have hjv : |inner ℝ j.2 v| < Δ := by
    have e : inner ℝ j.2 v = inner ℝ (j.2 - σ • c.2) v := by
      rw [inner_sub_left, inner_smul_left, hcv]; simp
    rw [e]
    calc |inner ℝ (j.2 - σ • c.2) v| ≤ ‖j.2 - σ • c.2‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ < Δ := by rw [hvn, mul_one]; exact hjσ
  -- the transverse component of `j.2`
  have hjc : 1 / 2 ≤ |inner ℝ j.2 c.2| := by
    have hn2 : ‖j.2 - σ • c.2‖ ^ 2 < Δ ^ 2 := pow_lt_pow_left₀ hjσ (norm_nonneg _) (by norm_num)
    have hsq : ‖j.2 - σ • c.2‖ ^ 2 = 2 - 2 * (σ * inner ℝ j.2 c.2) := by
      rw [@norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hσabs, hj2, hc2]
      ring
    have hΔsq : Δ ^ 2 ≤ 1 := by nlinarith
    have h1 : 1 / 2 ≤ σ * inner ℝ j.2 c.2 := by linarith
    calc 1 / 2 ≤ σ * inner ℝ j.2 c.2 := h1
      _ ≤ |σ * inner ℝ j.2 c.2| := le_abs_self _
      _ = |inner ℝ j.2 c.2| := by rw [abs_mul, hσabs, one_mul]
  have hperp : 1 / 2 ≤ |inner ℝ j.2 (perp v)| := by
    rw [hpv, inner_neg_right, abs_neg]; exact hjc
  have hslope : |(lineChart v j).1| ≤ 2 * Δ := by
    simp only [lineChart, cotNormal]
    rw [abs_div, abs_neg, div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (inner ℝ j.2 v)]
  refine ⟨hperp, by linarith, ?_⟩
  intro y hy
  have hlam4 : (4 * (4 * Δ) : ℝ) ≠ 0 := by positivity
  rw [lineHeight_tubeLine v hlam4 j y]
  -- the centre is the height of the coarse line, which is horizontal in this frame
  have hcot : cotNormal v c.2 = 0 := by
    simp only [cotNormal, hcv, neg_zero, zero_div]
  have hcint : (lineChart v c).2 = (pointChart v c.1).2 := by
    simp only [lineChart, hcot, zero_mul, sub_zero]
  rw [hcint]
  -- the line `j` passes near `c.1`
  have hne : inner ℝ j.2 (perp v) ≠ 0 := by
    intro h; rw [h, abs_zero] at hperp; linarith
  have hchart := inner_eq_chart_error hvn j.1 c.1 j.2 hne
  have hinner : |inner ℝ (c.1 - j.1) j.2| ≤ 17 * Δ := by
    have hdec : inner ℝ (c.1 - j.1) j.2 =
        -(σ * inner ℝ (j.1 - c.1) c.2) + inner ℝ (c.1 - j.1) (j.2 - σ • c.2) := by
      rw [inner_sub_right, inner_smul_right]
      have : inner ℝ (c.1 - j.1) c.2 = -inner ℝ (j.1 - c.1) c.2 := by
        rw [← inner_neg_left, neg_sub]
      rw [this]; ring
    rw [hdec]
    have h8 : ‖c.1 - j.1‖ ≤ 8 := by
      calc ‖c.1 - j.1‖ ≤ ‖c.1‖ + ‖j.1‖ := norm_sub_le _ _
        _ ≤ 8 := by linarith
    have hA : |-(σ * inner ℝ (j.1 - c.1) c.2)| ≤ 9 * Δ := by
      rw [abs_neg, abs_mul, hσabs, one_mul]; exact hnear.le
    have hB : |inner ℝ (c.1 - j.1) (j.2 - σ • c.2)| ≤ 8 * Δ := by
      calc |inner ℝ (c.1 - j.1) (j.2 - σ • c.2)| ≤ ‖c.1 - j.1‖ * ‖j.2 - σ • c.2‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ 8 * Δ := mul_le_mul h8 hjσ.le (norm_nonneg _) (by norm_num)
    calc |-(σ * inner ℝ (j.1 - c.1) c.2) + inner ℝ (c.1 - j.1) (j.2 - σ • c.2)|
        ≤ |-(σ * inner ℝ (j.1 - c.1) c.2)| + |inner ℝ (c.1 - j.1) (j.2 - σ • c.2)| :=
          abs_add_le _ _
      _ ≤ 17 * Δ := by linarith
  have hgap : |(pointChart v c.1).2 - height (lineChart v j) (pointChart v c.1).1| ≤ 34 * Δ := by
    have h := hinner
    rw [hchart, abs_mul] at h
    have hpos : 0 ≤ |(pointChart v c.1).2 - height (lineChart v (j.1, j.2)) (pointChart v c.1).1| :=
      abs_nonneg _
    have : |(pointChart v c.1).2 - height (lineChart v (j.1, j.2)) (pointChart v c.1).1| ≤ 34 * Δ := by
      nlinarith
    simpa using this
  have hX : |(pointChart v c.1).1| ≤ 4 := by
    calc |(pointChart v c.1).1| = |inner ℝ c.1 v| := rfl
      _ ≤ ‖c.1‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ 4 := by rw [hvn, mul_one]; exact hc1
  have hdiff : |height (lineChart v j) y - height (lineChart v j) (pointChart v c.1).1| ≤ 16 * Δ := by
    simp only [height]
    have e : (lineChart v j).1 * y + (lineChart v j).2 -
        ((lineChart v j).1 * (pointChart v c.1).1 + (lineChart v j).2) =
        (lineChart v j).1 * (y - (pointChart v c.1).1) := by ring
    rw [e, abs_mul]
    have hy8 : |y - (pointChart v c.1).1| ≤ 8 := by
      calc |y - (pointChart v c.1).1| ≤ |y| + |(pointChart v c.1).1| := abs_sub _ _
        _ ≤ 8 := by linarith
    calc |(lineChart v j).1| * |y - (pointChart v c.1).1| ≤ (2 * Δ) * 8 :=
          mul_le_mul hslope hy8 (abs_nonneg _) (by linarith)
      _ = 16 * Δ := by ring
  have htot : |height (lineChart v j) y - ((pointChart v c.1).2 + 0 * y)| ≤ 50 * Δ := by
    have e : height (lineChart v j) y - ((pointChart v c.1).2 + 0 * y) =
        (height (lineChart v j) y - height (lineChart v j) (pointChart v c.1).1) -
        ((pointChart v c.1).2 - height (lineChart v j) (pointChart v c.1).1) := by ring
    rw [e]
    calc _ ≤ |height (lineChart v j) y - height (lineChart v j) (pointChart v c.1).1| +
          |(pointChart v c.1).2 - height (lineChart v j) (pointChart v c.1).1| := abs_sub _ _
      _ ≤ 50 * Δ := by linarith
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * (4 * Δ)), div_le_iff₀ (by positivity)]
  linarith

/-- **Case A with the coarse classes at scale `Δ` as tubes.** -/
theorem caseA_coarse_false {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (r Δ w K₀ A I E X : ℝ) (D J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
      (P U : Finset E2) (Bd : ℝ → ℝ) (JΔ : Finset (E2 × E2)) (clsΔ : E2 × E2 → E2 × E2)
      (M : E2 × E2 → ℝ) (Ut : E2 × E2 → Finset E2),
    0 < r → r ≤ 1 / 4 → 0 < Δ → Δ ≤ 1 → 0 < w → 9 ≤ K₀ → 0 ≤ A → 16 * Δ * w ≤ 18 * r →
    tubeTol (9 * r) (4 * Δ) w ≤ δ₀ →
    K₀ ≤ (tubeTol (9 * r) (4 * Δ) w) ^ (-η) → A ≤ (tubeTol (9 * r) (4 * Δ) w) ^ (-η) →
    0 < I → 0 < E → 0 < X → (tubeTol (9 * r) (4 * Δ) w) ^ η ≤ I ^ 2 / (E * X) →
    (∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q)) →
    J₀ ⊆ D → (∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1) →
    (∀ j ∈ J₀, ∀ j' ∈ J₀, j ≠ j' → StripSep r j j') →
    (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ ρ ρ', r ≤ ρ → ρ ≤ ρ' → Bd ρ ≤ Bd ρ') →
    (∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ Bd ρ) →
    U ⊆ P →
    (∀ j ∈ J₀, clsΔ j ∈ JΔ ∧
      (j = clsΔ j ∨ ¬ StripSep Δ j (clsΔ j) ∨ ¬ StripSep Δ (clsΔ j) j)) →
    (∀ c ∈ JΔ, ‖c.1‖ ≤ 4 ∧ ‖c.2‖ = 1) →
    I ≤ ∑ t ∈ JΔ, ∑ j ∈ J₀.filter (fun j => clsΔ j = t), ((pinsOf D cls j ∩ Ut t).card : ℝ) →
    ∑ p ∈ U, ∑ p' ∈ U.filter (fun p' => dist p p' ≤ 6 * w + 36 * r),
      2 * Bd (91 * r / max (dist p p') (40 * r)) ≤ E →
    ∑ t ∈ JΔ, (((Ut t).image (tubeCol (perp t.2) w)).card : ℝ) *
      ((J₀.filter (fun j => clsΔ j = t)).card : ℝ) ≤ X →
    (∀ t ∈ JΔ, Ut t ⊆ U ∧ 0 < M t ∧
      8 * ((J₀.filter (fun j => clsΔ j = t)).card : ℝ) / M t ≤
        (tubeTol (9 * r) (4 * Δ) w) ^ (-(1 - e)) ∧
      64 * ((J₀.filter (fun j => clsΔ j = t)).card : ℝ) ≤ K₀ * M t ^ 2 ∧
      (∀ x ∈ Ut t, M t ≤ (((J₀.filter (fun j => clsΔ j = t)).filter
        (fun j => x ∈ pinsOf D cls j)).card : ℝ)) ∧
      (∀ j ∈ J₀.filter (fun j => clsΔ j = t), ∀ z ρ : ℝ, tubeTol (9 * r) (4 * Δ) w ≤ ρ →
        ((((Ut t).image (tubeCol (perp t.2) w)).filter (fun y =>
          (∃ x ∈ Ut t, x ∈ pinsOf D cls j ∧ tubeCol (perp t.2) w x = y) ∧
            |y - z| ≤ ρ)).card : ℝ) ≤
        A * ρ ^ β * ((((Ut t).image (tubeCol (perp t.2) w)).filter (fun y =>
          ∃ x ∈ Ut t, x ∈ pinsOf D cls j ∧ tubeCol (perp t.2) w x = y)).card : ℝ)) ∧
      (∀ c a ρ : ℝ, tubeTol (9 * r) (4 * Δ) w ≤ ρ →
        (((J₀.filter (fun j => clsΔ j = t)).filter (fun j =>
          |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (4 * (4 * Δ)) j).1 - c| ≤ ρ ∧
          |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (4 * (4 * Δ)) j).2 - a| ≤ ρ)).card :
            ℝ) ≤
        K₀ * ρ ^ (1 + b) * ((J₀.filter (fun j => clsΔ j = t)).card : ℝ))) →
    False := by
  obtain ⟨η, δ₀, hη, hδ₀, hδ₀2, hmain⟩ := caseA_false (τ := E2 × E2) he hb hβ
  refine ⟨η, δ₀, hη, hδ₀, hδ₀2, ?_⟩
  intro r Δ w K₀ A I E X D J₀ cls P U Bd JΔ clsΔ M Ut hr hr4 hΔ hΔ1 hw hK₀ hA0 hwι hδ hK₀δ hAδ
    hI hE hX hdδ hcls hJ₀ hnorm hsep hP4 hBd hcap hU hclsΔ hJΔ hIsum hEsum hXsum htube
  refine hmain r (4 * Δ) w K₀ A I E X D J₀ cls P U Bd JΔ clsΔ (fun t => perp t.2) (fun _ => 0)
    (fun t => (lineChart (perp t.2) t).2) M Ut hr hr4 (by positivity) hw hK₀ hA0 (by linarith) hδ
    hK₀δ hAδ hI hE hX hdδ hcls hJ₀ hnorm hsep hP4 hBd hcap hU hIsum hEsum hXsum ?_
  intro t ht
  obtain ⟨hUt, hM, hF, hquad, hdeg, htwo, hline⟩ := htube t ht
  have ht2 : ‖t.2‖ = 1 := (hJΔ t ht).2
  have ht1 : ‖t.1‖ ≤ 4 := (hJΔ t ht).1
  have hvt : ‖perp t.2‖ = 1 := by rw [perp_norm, ht2]
  have hgeom : ∀ j ∈ J₀.filter (fun j => clsΔ j = t),
      1 / 2 ≤ |inner ℝ j.2 (perp (perp t.2))| ∧ |(lineChart (perp t.2) j).1| ≤ 4 * Δ ∧
      ∀ y : ℝ, |y| ≤ 4 →
        |lineHeight (tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (4 * (4 * Δ)) j) y| ≤
          7 / 2 := by
    intro j hj
    obtain ⟨hjJ, hjt⟩ := Finset.mem_filter.mp hj
    have hjD := hnorm j (hJ₀ hjJ)
    have hc := (hclsΔ j hjJ).2
    rw [hjt] at hc
    have hn := near_of_not_stripSep (q := j) (j := t) hjD.1 ht1 hc hΔ
    exact coarse_class_tube_geom hΔ hΔ1 ht2 ht1 hjD.2 hjD.1 hn.1 hn.2
  refine ⟨hvt, hUt, hM, hF, hquad, fun j hj => ⟨(hgeom j hj).1, (hgeom j hj).2.1⟩, hdeg, ?_,
    htwo, hline⟩
  intro j hj y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (hgeom j hj).2.2 _ (abs_tubeCol_le hvt hw (hP4 x (hU (hUt hx))))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/CoarseTubes.lean
