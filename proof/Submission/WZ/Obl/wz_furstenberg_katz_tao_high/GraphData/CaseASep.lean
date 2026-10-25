-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.CaseASep.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.CoarseTubes

/-!
# Case A with decoupled scales

`caseA_false_sep` is `caseA_false` with the separation scale `rs` of the classes decoupled from
the scale `r` of the label/class geometry (pins within `9 r` of their class, energy weights at
`r`), provided `9 r ≤ K₀ rs`. `hcls_of_geo` turns the `9ρ/ρ` geometry of a class map (the
`cls_geo`/`tube_geo` form of x0675's `HighConfig`) into the `StripSep` form at scale `17 ρ`.
`caseA_coarse_geo` takes the coarse tubes in that geometric form (`tube_geo` of `HighConfig`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open scoped BigOperators

/-- **Case A at a coarse configuration**, with the class separation scale `rs` decoupled from the
label/class geometry scale `r` (`9 r ≤ K₀ rs`). -/
theorem caseA_false_sep {τ : Type*} [DecidableEq τ] {e b β : ℝ} (he : 0 < e) (hb : 0 < b)
    (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (r rs Δs w K₀ A I E X : ℝ) (D J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
      (P U : Finset E2) (Bd : ℝ → ℝ) (T : Finset τ) (tube : E2 × E2 → τ) (v : τ → Plane)
      (cT aT M : τ → ℝ) (Ut : τ → Finset E2),
    0 < r → r ≤ 1 / 4 → 0 < rs → 9 * r ≤ K₀ * rs → 0 < Δs → 0 < w → 1 ≤ K₀ → 0 ≤ A →
    4 * Δs * w ≤ 2 * (9 * r) →
    tubeTol (9 * r) Δs w ≤ δ₀ →
    K₀ ≤ (tubeTol (9 * r) Δs w) ^ (-η) → A ≤ (tubeTol (9 * r) Δs w) ^ (-η) →
    0 < I → 0 < E → 0 < X → (tubeTol (9 * r) Δs w) ^ η ≤ I ^ 2 / (E * X) →
    (∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q)) →
    J₀ ⊆ D → (∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1) →
    (∀ j ∈ J₀, ∀ j' ∈ J₀, j ≠ j' → StripSep rs j j') →
    (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ ρ ρ', r ≤ ρ → ρ ≤ ρ' → Bd ρ ≤ Bd ρ') →
    (∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ Bd ρ) →
    U ⊆ P →
    I ≤ ∑ t ∈ T, ∑ j ∈ J₀.filter (fun j => tube j = t), ((pinsOf D cls j ∩ Ut t).card : ℝ) →
    ∑ p ∈ U, ∑ p' ∈ U.filter (fun p' => dist p p' ≤ 6 * w + 36 * r),
      2 * Bd (91 * r / max (dist p p') (40 * r)) ≤ E →
    ∑ t ∈ T, (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
      ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤ X →
    (∀ t ∈ T, ‖v t‖ = 1 ∧ Ut t ⊆ U ∧ 0 < M t ∧
      8 * ((J₀.filter (fun j => tube j = t)).card : ℝ) / M t ≤
        (tubeTol (9 * r) Δs w) ^ (-(1 - e)) ∧
      64 * ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤ K₀ * M t ^ 2 ∧
      (∀ j ∈ J₀.filter (fun j => tube j = t),
        1 / 2 ≤ |inner ℝ j.2 (perp (v t))| ∧ |(lineChart (v t) j).1| ≤ Δs) ∧
      (∀ x ∈ Ut t, M t ≤ (((J₀.filter (fun j => tube j = t)).filter
        (fun j => x ∈ pinsOf D cls j)).card : ℝ)) ∧
      (∀ j ∈ J₀.filter (fun j => tube j = t), ∀ y ∈ (Ut t).image (tubeCol (v t) w),
        |lineHeight (tubeLine (v t) (cT t) (aT t) (4 * Δs) j) y| ≤ 7 / 2) ∧
      (∀ j ∈ J₀.filter (fun j => tube j = t), ∀ z ρ : ℝ, tubeTol (9 * r) Δs w ≤ ρ →
        ((((Ut t).image (tubeCol (v t) w)).filter (fun y =>
          (∃ x ∈ Ut t, x ∈ pinsOf D cls j ∧ tubeCol (v t) w x = y) ∧ |y - z| ≤ ρ)).card : ℝ) ≤
        A * ρ ^ β * ((((Ut t).image (tubeCol (v t) w)).filter (fun y =>
          ∃ x ∈ Ut t, x ∈ pinsOf D cls j ∧ tubeCol (v t) w x = y)).card : ℝ)) ∧
      (∀ c a ρ : ℝ, tubeTol (9 * r) Δs w ≤ ρ →
        (((J₀.filter (fun j => tube j = t)).filter (fun j =>
          |(tubeLine (v t) (cT t) (aT t) (4 * Δs) j).1 - c| ≤ ρ ∧
          |(tubeLine (v t) (cT t) (aT t) (4 * Δs) j).2 - a| ≤ ρ)).card : ℝ) ≤
        K₀ * ρ ^ (1 + b) * ((J₀.filter (fun j => tube j = t)).card : ℝ))) →
    False := by
  obtain ⟨η, δ₀, hη, hδ₀, hδ₀2, hmain⟩ := tube_two_ends_false he hb hβ
  refine ⟨η, δ₀, hη, hδ₀, hδ₀2, ?_⟩
  intro r rs Δs w K₀ A I E X D J₀ cls P U Bd T tube v cT aT M Ut hr hr4 hrs hrK hΔs hw hK₀ hA0 hwι hδ
    hK₀δ hAδ hI hE hX hdδ hcls hJ₀ hnorm hsep hP4 hBd hcap hU hIsum hEsum hXsum htube
  obtain ⟨t, ht, hJne, hUne, hdens⟩ := exists_dense_column_tube hr hr4 hw hI hE hX hcls hJ₀
    hnorm hP4 Bd hBd hcap hU T tube v Ut (fun t ht => (htube t ht).1)
    (fun t ht j hj => ((htube t ht).2.2.2.2.2.1 j hj).1) (fun t ht => (htube t ht).2.1)
    hIsum hEsum hXsum
  obtain ⟨hvt, hUtU, hMt, hF, hquad, hJnorm, hdeg, hheight, htwo, hline⟩ := htube t ht
  have hδpos : 0 < tubeTol (9 * r) Δs w := tubeTol_pos (by positivity) hΔs hw
  have hδ1 : (tubeTol (9 * r) Δs w) ^ η ≤ 1 :=
    Real.rpow_le_one hδpos.le (by linarith) hη.le
  set d := min (I ^ 2 / (E * X)) 1 with hd
  have hdle : d ≤ I ^ 2 / (E * X) := min_le_left _ _
  have hJt := hJne
  apply hmain (v t) (cT t) (aT t) rs (9 * r) Δs w (M t) d K₀ A hvt hrs (by positivity) hΔs hw hMt
    hK₀ hA0 hwι hrK hδ hK₀δ hAδ (le_min hdδ hδ1) (min_le_right _ _)
    (J₀.filter (fun j => tube j = t)) (Ut t) (fun j x => x ∈ pinsOf D cls j) hJne hUne hF
  · intro j hj
    have hjD := hJ₀ (Finset.mem_filter.mp hj).1
    exact ⟨(hnorm j hjD).2, (hnorm j hjD).1, (hJnorm j hj).1, (hJnorm j hj).2⟩
  · intro j hj j' hj' hne
    exact hsep j (Finset.mem_filter.mp hj).1 j' (Finset.mem_filter.mp hj').1 hne
  · intro j _ x _ hx
    exact (pin_near hr hcls hJ₀ hnorm hx).le
  · intro x hx
    exact hP4 x (hU (hUtU hx))
  · intro x hx
    convert hdeg x hx
  · exact hheight
  · have hpos : 0 ≤ (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
        ((J₀.filter (fun j => tube j = t)).card : ℝ) := by positivity
    have h1 : d * (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
        ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤
        I ^ 2 / (E * X) * (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
        ((J₀.filter (fun j => tube j = t)).card : ℝ) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right hdle hpos
    convert h1.trans hdens
  · intro j hj z ρ hρ
    convert htwo j hj z ρ hρ
  · exact hline
  · exact hquad

/-- The `9ρ/ρ` geometry of a class map gives the `StripSep` form at scale `17 ρ`. -/
theorem hcls_of_geo {ρ : ℝ} {q j : E2 × E2} (hq4 : ‖q.1‖ ≤ 4) (hj4 : ‖j.1‖ ≤ 4)
    (hoff : |inner ℝ (q.1 - j.1) j.2| < 9 * ρ) (hdir : dist q.2 j.2 < ρ ∨ dist q.2 (-j.2) < ρ) :
    ¬ StripSep (17 * ρ) q j := by
  have hρ : 0 < ρ := by
    rcases hdir with h | h <;> linarith [dist_nonneg (x := q.2) (y := j.2),
      dist_nonneg (x := q.2) (y := -j.2)]
  have h8 : ‖q.1 - j.1‖ ≤ 8 := by
    calc ‖q.1 - j.1‖ ≤ ‖q.1‖ + ‖j.1‖ := norm_sub_le _ _
      _ ≤ 8 := by linarith
  rintro (⟨h1, h2⟩ | h3)
  · rcases hdir with h | h <;> linarith
  · obtain ⟨σ, hσ, hdσ⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖q.2 - σ • j.2‖ < ρ := by
      rcases hdir with h | h
      · exact ⟨1, Or.inl rfl, by rw [one_smul, ← dist_eq_norm]; exact h⟩
      · exact ⟨-1, Or.inr rfl, by rw [neg_one_smul, ← dist_eq_norm]; exact h⟩
    have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hdec : inner ℝ (q.1 - j.1) q.2 =
        σ * inner ℝ (q.1 - j.1) j.2 + inner ℝ (q.1 - j.1) (q.2 - σ • j.2) := by
      rw [inner_sub_right, inner_smul_right]; ring
    have hA : |σ * inner ℝ (q.1 - j.1) j.2| < 9 * ρ := by
      rw [abs_mul, hσabs, one_mul]; exact hoff
    have hB : |inner ℝ (q.1 - j.1) (q.2 - σ • j.2)| ≤ 8 * ρ := by
      calc |inner ℝ (q.1 - j.1) (q.2 - σ • j.2)| ≤ ‖q.1 - j.1‖ * ‖q.2 - σ • j.2‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ 8 * ρ := mul_le_mul h8 hdσ.le (norm_nonneg _) (by norm_num)
    have : |inner ℝ (q.1 - j.1) q.2| < 17 * ρ := by
      rw [hdec]
      calc _ ≤ |σ * inner ℝ (q.1 - j.1) j.2| + |inner ℝ (q.1 - j.1) (q.2 - σ • j.2)| :=
            abs_add_le _ _
        _ < 17 * ρ := by linarith
    linarith

/-- **Case A with coarse tubes in geometric form** (`tube_geo` of `HighConfig`) and decoupled
separation scale `rs`. -/
theorem caseA_coarse_geo {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (r rs Δ w K₀ A I E X : ℝ) (D J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
      (P U : Finset E2) (Bd : ℝ → ℝ) (JΔ : Finset (E2 × E2)) (clsΔ : E2 × E2 → E2 × E2)
      (M : E2 × E2 → ℝ) (Ut : E2 × E2 → Finset E2),
    0 < r → r ≤ 1 / 4 → 0 < rs → 9 * r ≤ K₀ * rs → 0 < Δ → Δ ≤ 1 → 0 < w → 1 ≤ K₀ → 0 ≤ A →
    16 * Δ * w ≤ 18 * r →
    tubeTol (9 * r) (4 * Δ) w ≤ δ₀ →
    K₀ ≤ (tubeTol (9 * r) (4 * Δ) w) ^ (-η) → A ≤ (tubeTol (9 * r) (4 * Δ) w) ^ (-η) →
    0 < I → 0 < E → 0 < X → (tubeTol (9 * r) (4 * Δ) w) ^ η ≤ I ^ 2 / (E * X) →
    (∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q)) →
    J₀ ⊆ D → (∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1) →
    (∀ j ∈ J₀, ∀ j' ∈ J₀, j ≠ j' → StripSep rs j j') →
    (∀ p ∈ P, ‖p‖ ≤ 4) → (∀ ρ ρ', r ≤ ρ → ρ ≤ ρ' → Bd ρ ≤ Bd ρ') →
    (∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ Bd ρ) →
    U ⊆ P →
    (∀ j ∈ J₀, clsΔ j ∈ JΔ ∧ |inner ℝ (j.1 - (clsΔ j).1) (clsΔ j).2| < 9 * Δ ∧
      (dist j.2 (clsΔ j).2 < Δ ∨ dist j.2 (-(clsΔ j).2) < Δ)) →
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
  obtain ⟨η, δ₀, hη, hδ₀, hδ₀2, hmain⟩ := caseA_false_sep (τ := E2 × E2) he hb hβ
  refine ⟨η, δ₀, hη, hδ₀, hδ₀2, ?_⟩
  intro r rs Δ w K₀ A I E X D J₀ cls P U Bd JΔ clsΔ M Ut hr hr4 hrs hrK hΔ hΔ1 hw hK₀ hA0 hwι hδ
    hK₀δ hAδ
    hI hE hX hdδ hcls hJ₀ hnorm hsep hP4 hBd hcap hU hclsΔ hJΔ hIsum hEsum hXsum htube
  refine hmain r rs (4 * Δ) w K₀ A I E X D J₀ cls P U Bd JΔ clsΔ (fun t => perp t.2) (fun _ => 0)
    (fun t => (lineChart (perp t.2) t).2) M Ut hr hr4 hrs hrK (by positivity) hw hK₀ hA0 (by linarith) hδ
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
    exact coarse_class_tube_geom hΔ hΔ1 ht2 ht1 hjD.2 hjD.1 hc.1 hc.2
  refine ⟨hvt, hUt, hM, hF, hquad, fun j hj => ⟨(hgeom j hj).1, (hgeom j hj).2.1⟩, hdeg, ?_,
    htwo, hline⟩
  intro j hj y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (hgeom j hj).2.2 _ (abs_tubeCol_le hvt hw (hP4 x (hU (hUt hx))))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/CaseASep.lean
