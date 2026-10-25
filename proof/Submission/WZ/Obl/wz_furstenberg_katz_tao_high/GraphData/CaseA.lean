-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.CaseA.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.TubeTwoEnds
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.CellEnergy

/-!
# Case A at a coarse configuration

A configuration at scale `r` (labels `D`, classes `J₀` with the class map `cls` of o213, points `P`
with bush cap bounds `Bd`, pins `U ⊆ P`) and a family of coarse tubes: a map `tube` from classes
to an index type, for each tube `t ∈ T` an axis `v t`, a centre `(cT t, aT t)`, pins `Ut t ⊆ U`.
The columns of the tube `t` are `tubeCol (v t) w` (rounded first chart coordinate).

* `dist_le_of_same_tubeCol`: two pins of a class in one column are `6 w + 36 r`-close.
* `sum_tubeEnergy_le`: the column energies of all tubes add up to at most the ball energy
  `∑_{p ∈ U} ∑_{p' ∈ U, dist p p' ≤ 6 w + 36 r} 2 Bd(91 r / max (dist p p') (40 r))`.
* `exists_dense_column_tube`: with `I ≤` incidences, `E ≥` ball energy and
  `X ≥ ∑_t #columns(t) #classes(t)`, some tube has (column, class) density at least `I² / (E X)`
  (Cauchy–Schwarz in each tube, then `exists_tube_energy_ratio`).
* `caseA_false`: with `tube_two_ends_false` inside that tube, the configuration cannot exist
  once `δ^η ≤ I² / (E X)` and the per-tube data (pin degree, `#J_t ≲ M²`, transversality,
  heights, two-ended classes, tube-line Frostman) hold, at tolerance `δ = tubeTol (9 r) Δs w`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open scoped BigOperators

/-- A pin of a class lies within `9 r` of its line. -/
theorem pin_near {r : ℝ} (hr : 0 < r) {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1) {j : E2 × E2} {x : E2}
    (hx : x ∈ pinsOf D cls j) : |inner ℝ (x - j.1) j.2| < 9 * r := by
  obtain ⟨e, hxe, hcj⟩ := mem_pinsOf.mp hx
  have hc := hcls _ hxe
  rw [hcj] at hc
  have hj4 : ‖j.1‖ ≤ 4 := (hnorm j (hJ₀ hc.1)).1
  exact (near_of_not_stripSep (q := (x, e)) (j := j) (hnorm _ hxe).1 hj4 hc.2 hr).1

/-- Two points near one transverse line and in one column are close. -/
theorem dist_le_of_same_tubeCol {v n p p' a : Plane} {w r : ℝ} (hv : ‖v‖ = 1) (hw : 0 < w)
    (hn : ‖n‖ = 1) (hnv : 1 / 2 ≤ |inner ℝ n (perp v)|)
    (hp : |inner ℝ (p - a) n| < 9 * r) (hp' : |inner ℝ (p' - a) n| < 9 * r)
    (hcol : tubeCol v w p = tubeCol v w p') : dist p p' ≤ 6 * w + 36 * r := by
  set u := p - p' with hu
  have h1 : |inner ℝ u v| ≤ 2 * w := by
    have c1 := tubeCol_close v hw p
    have c2 := tubeCol_close v hw p'
    rw [hcol] at c1
    simp only [pointChart] at c1 c2
    rw [hu, inner_sub_left]
    calc |inner ℝ p v - inner ℝ p' v|
        = |(tubeCol v w p' - inner ℝ p' v) - (tubeCol v w p' - inner ℝ p v)| := by ring_nf
      _ ≤ |tubeCol v w p' - inner ℝ p' v| + |tubeCol v w p' - inner ℝ p v| := abs_sub _ _
      _ ≤ w + w := add_le_add c2 c1
      _ = 2 * w := by ring
  have h2 : |inner ℝ u n| < 18 * r := by
    have e : inner ℝ u n = inner ℝ (p - a) n - inner ℝ (p' - a) n := by
      rw [hu, ← inner_sub_left]; congr 1; abel
    rw [e]
    calc |inner ℝ (p - a) n - inner ℝ (p' - a) n|
        ≤ |inner ℝ (p - a) n| + |inner ℝ (p' - a) n| := abs_sub _ _
      _ < 9 * r + 9 * r := add_lt_add hp hp'
      _ = 18 * r := by ring
  have hframe := inner_frame hv u n
  have hnv1 : |inner ℝ n v| ≤ 1 := by
    have := abs_real_inner_le_norm n v
    rw [hn, hv] at this; linarith
  have h3 : |inner ℝ u (perp v)| * |inner ℝ n (perp v)| ≤ 18 * r + 2 * w := by
    rw [← abs_mul]
    have e : inner ℝ u (perp v) * inner ℝ n (perp v) = inner ℝ u n - inner ℝ u v * inner ℝ n v := by
      linarith [hframe]
    rw [e]
    calc |inner ℝ u n - inner ℝ u v * inner ℝ n v|
        ≤ |inner ℝ u n| + |inner ℝ u v * inner ℝ n v| := abs_sub _ _
      _ ≤ 18 * r + 2 * w := by
          rw [abs_mul]
          have := mul_le_mul h1 hnv1 (abs_nonneg _) (by linarith)
          linarith
  have h4 : |inner ℝ u (perp v)| ≤ 36 * r + 4 * w := by
    have ha := abs_nonneg (inner ℝ u (perp v))
    nlinarith
  have hsq : ‖u‖ ^ 2 = inner ℝ u (perp v) ^ 2 + inner ℝ u v ^ 2 := by
    have := inner_frame hv u u
    rw [real_inner_self_eq_norm_sq] at this
    linarith
  have hle : ‖u‖ ≤ |inner ℝ u (perp v)| + |inner ℝ u v| := by
    have ha := abs_nonneg (inner ℝ u (perp v))
    have hb := abs_nonneg (inner ℝ u v)
    have hsa := sq_abs (inner ℝ u (perp v))
    have hsb := sq_abs (inner ℝ u v)
    nlinarith [norm_nonneg u]
  rw [dist_eq_norm]
  linarith

section Energy

variable {τ : Type*} [DecidableEq τ]

/-- The column energy of classes `J` with pins `Ut`, columns along `v` of width `w`. -/
noncomputable def tubeEnergy (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (J : Finset (E2 × E2)) (Ut : Finset E2) (v : Plane) (w : ℝ) : ℝ :=
  ∑ j ∈ J, ∑ c ∈ Ut.image (tubeCol v w), ((cellPins D cls Ut (tubeCol v w) j c).card : ℝ) ^ 2

theorem tubeEnergy_eq (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (J : Finset (E2 × E2)) (Ut : Finset E2) (v : Plane) (w : ℝ) :
    tubeEnergy D cls J Ut v w =
      ∑ p ∈ Ut, ∑ p' ∈ Ut.filter (fun p' => tubeCol v w p' = tubeCol v w p),
        ((J.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card : ℝ) := by
  unfold tubeEnergy
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun c _ => cell_energy_eq D cls J Ut (tubeCol v w) c)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := tubeCol v w) (s := Ut)
    (t := Ut.image (tubeCol v w)) (fun p hp => Finset.mem_image_of_mem _ hp)]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro p hp
  have hpc := (Finset.mem_filter.mp hp).2
  rw [hpc]

theorem incid_le_tubeEnergy (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (J : Finset (E2 × E2)) (Ut : Finset E2) (v : Plane) (w : ℝ) :
    ∑ j ∈ J, ((pinsOf D cls j ∩ Ut).card : ℝ) ≤ tubeEnergy D cls J Ut v w := by
  unfold tubeEnergy
  apply Finset.sum_le_sum
  intro j _
  rw [card_pins_eq_sum_cellPins D cls Ut (tubeCol v w) j]
  apply Finset.sum_le_sum
  intro c _
  have h : (cellPins D cls Ut (tubeCol v w) j c).card ≤
      (cellPins D cls Ut (tubeCol v w) j c).card ^ 2 := Nat.le_self_pow (by norm_num) _
  exact_mod_cast h

/-- **The column energies of all tubes are at most the ball energy.** -/
theorem sum_tubeEnergy_le {r w : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (hw : 0 < w)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2} (hP4 : ∀ p ∈ P, ‖p‖ ≤ 4) (Bd : ℝ → ℝ)
    (hBd : ∀ ρ ρ', r ≤ ρ → ρ ≤ ρ' → Bd ρ ≤ Bd ρ')
    (hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ Bd ρ)
    {U : Finset E2} (hU : U ⊆ P)
    (T : Finset τ) (tube : E2 × E2 → τ) (v : τ → Plane) (Ut : τ → Finset E2)
    (hv : ∀ t ∈ T, ‖v t‖ = 1)
    (htrans : ∀ t ∈ T, ∀ j ∈ J₀.filter (fun j => tube j = t),
      1 / 2 ≤ |inner ℝ j.2 (perp (v t))|)
    (hUt : ∀ t ∈ T, Ut t ⊆ U) :
    ∑ t ∈ T, tubeEnergy D cls (J₀.filter (fun j => tube j = t)) (Ut t) (v t) w ≤
      ∑ p ∈ U, ∑ p' ∈ U.filter (fun p' => dist p p' ≤ 6 * w + 36 * r),
        2 * Bd (91 * r / max (dist p p') (40 * r)) := by
  classical
  set w' := 6 * w + 36 * r with hw'
  -- the classes of a tube through two pins of one column are `w'`-close pins
  have hA : ∀ t ∈ T, tubeEnergy D cls (J₀.filter (fun j => tube j = t)) (Ut t) (v t) w ≤
      ∑ p ∈ U, ∑ p' ∈ U, (((J₀.filter (fun j => tube j = t)).filter
        (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧ dist p p' ≤ w')).card : ℝ) := by
    intro t ht
    rw [tubeEnergy_eq]
    calc _ ≤ ∑ p ∈ Ut t, ∑ p' ∈ (Ut t).filter
            (fun p' => tubeCol (v t) w p' = tubeCol (v t) w p),
            (((J₀.filter (fun j => tube j = t)).filter
              (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧ dist p p' ≤ w')).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p _
          apply Finset.sum_le_sum
          intro p' hp'
          have hcol := (Finset.mem_filter.mp hp').2
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro j hj
          obtain ⟨hjt, hpj, hp'j⟩ := Finset.mem_filter.mp hj
          refine Finset.mem_filter.mpr ⟨hjt, hpj, hp'j, ?_⟩
          have hjJ := (Finset.mem_filter.mp hjt).1
          have hn := (hnorm j (hJ₀ hjJ)).2
          exact dist_le_of_same_tubeCol (hv t ht) hw hn (htrans t ht j hjt)
            (pin_near hr hcls hJ₀ hnorm hpj) (pin_near hr hcls hJ₀ hnorm hp'j) hcol.symm
      _ ≤ ∑ p ∈ Ut t, ∑ p' ∈ U, (((J₀.filter (fun j => tube j = t)).filter
              (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧ dist p p' ≤ w')).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p _
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact (Finset.filter_subset _ _).trans (hUt t ht)
          · intro _ _ _; exact Nat.cast_nonneg _
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (hUt t ht)
          intro _ _ _
          exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  -- the tubes partition the classes
  have hB : ∀ p p' : E2, ∑ t ∈ T, (((J₀.filter (fun j => tube j = t)).filter
      (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧ dist p p' ≤ w')).card : ℝ) ≤
      ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧
        dist p p' ≤ w')).card : ℝ) := by
    intro p p'
    set S := (J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧
      dist p p' ≤ w')).filter (fun j => tube j ∈ T) with hS
    have hfib := Finset.card_eq_sum_card_fiberwise (f := tube) (s := S) (t := T)
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have hSle : S.card ≤ (J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧
        dist p p' ≤ w')).card := Finset.card_le_card (Finset.filter_subset _ _)
    have heq : ∀ t ∈ T, S.filter (fun j => tube j = t) = (J₀.filter (fun j => tube j = t)).filter
        (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧ dist p p' ≤ w') := by
      intro t ht
      ext j
      simp only [hS, Finset.mem_filter]
      constructor
      · rintro ⟨⟨⟨hj, hφ⟩, _⟩, htj⟩
        exact ⟨⟨hj, htj⟩, hφ⟩
      · rintro ⟨⟨hj, htj⟩, hφ⟩
        exact ⟨⟨⟨hj, hφ⟩, htj ▸ ht⟩, htj⟩
    rw [Finset.sum_congr rfl (fun t ht => by rw [← heq t ht])]
    have : (∑ t ∈ T, ((S.filter (fun j => tube j = t)).card : ℝ)) = (S.card : ℝ) := by
      rw [hfib]; push_cast; rfl
    rw [this]
    exact_mod_cast hSle
  -- two pins share few classes
  have hC : ∀ p ∈ U, ∀ p' ∈ U, ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧
      dist p p' ≤ w')).card : ℝ) ≤
      if dist p p' ≤ w' then 2 * Bd (91 * r / max (dist p p') (40 * r)) else 0 := by
    intro p hp p' hp'
    split_ifs with hd
    · have hsub : J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧
          dist p p' ≤ w') ⊆ J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j) := by
        intro j hj
        obtain ⟨hjJ, h1, h2, _⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hjJ, h1, h2⟩
      refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ?_
      exact common_classes_le_capBound hr hr4 hcls hJ₀ hnorm Bd hBd hcap (hU hp) (hP4 p (hU hp))
        (hP4 p' (hU hp'))
    · have : J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧
          dist p p' ≤ w') = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j _ h
        exact hd h.2.2
      rw [this]; simp
  calc ∑ t ∈ T, tubeEnergy D cls (J₀.filter (fun j => tube j = t)) (Ut t) (v t) w
      ≤ ∑ t ∈ T, ∑ p ∈ U, ∑ p' ∈ U, (((J₀.filter (fun j => tube j = t)).filter
        (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧ dist p p' ≤ w')).card : ℝ) :=
        Finset.sum_le_sum hA
    _ = ∑ p ∈ U, ∑ p' ∈ U, ∑ t ∈ T, (((J₀.filter (fun j => tube j = t)).filter
        (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j ∧ dist p p' ≤ w')).card : ℝ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ U, ∑ p' ∈ U,
        (if dist p p' ≤ w' then 2 * Bd (91 * r / max (dist p p') (40 * r)) else 0) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro p' hp'
        exact (hB p p').trans (hC p hp p' hp')
    _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_filter]

/-- The (column, class) pairs of a tube, counted class by class. -/
theorem card_col_pairs_eq (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (J : Finset (E2 × E2)) (Ut : Finset E2) (v : Plane) (w : ℝ) :
    ((((Ut.image (tubeCol v w)) ×ˢ J).filter
      (fun p : ℝ × (E2 × E2) => ∃ x ∈ Ut, x ∈ pinsOf D cls p.2 ∧ tubeCol v w x = p.1)).card : ℝ) =
    ∑ j ∈ J, ((cellsHit D cls Ut (tubeCol v w) j).card : ℝ) := by
  classical
  have hset : ∀ j, cellsHit D cls Ut (tubeCol v w) j = (Ut.image (tubeCol v w)).filter
      (fun c => ∃ x ∈ Ut, x ∈ pinsOf D cls j ∧ tubeCol v w x = c) := by
    intro j
    ext c
    simp only [cellsHit, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨x, ⟨hxp, hxU⟩, rfl⟩
      exact ⟨⟨x, hxU, rfl⟩, x, hxU, hxp, rfl⟩
    · rintro ⟨_, x, hxU, hxp, rfl⟩
      exact ⟨x, ⟨hxp, hxU⟩, rfl⟩
  rw [Finset.card_filter, Finset.sum_product_right]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [hset j, Finset.card_filter]
  push_cast
  rfl

/-- **A column-dense tube.** -/
theorem exists_dense_column_tube {r w I E X : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (hw : 0 < w)
    (hI : 0 < I) (hE : 0 < E) (hX : 0 < X)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2} (hP4 : ∀ p ∈ P, ‖p‖ ≤ 4) (Bd : ℝ → ℝ)
    (hBd : ∀ ρ ρ', r ≤ ρ → ρ ≤ ρ' → Bd ρ ≤ Bd ρ')
    (hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ Bd ρ)
    {U : Finset E2} (hU : U ⊆ P)
    (T : Finset τ) (tube : E2 × E2 → τ) (v : τ → Plane) (Ut : τ → Finset E2)
    (hv : ∀ t ∈ T, ‖v t‖ = 1)
    (htrans : ∀ t ∈ T, ∀ j ∈ J₀.filter (fun j => tube j = t),
      1 / 2 ≤ |inner ℝ j.2 (perp (v t))|)
    (hUt : ∀ t ∈ T, Ut t ⊆ U)
    (hIsum : I ≤ ∑ t ∈ T, ∑ j ∈ J₀.filter (fun j => tube j = t),
      ((pinsOf D cls j ∩ Ut t).card : ℝ))
    (hEsum : ∑ p ∈ U, ∑ p' ∈ U.filter (fun p' => dist p p' ≤ 6 * w + 36 * r),
      2 * Bd (91 * r / max (dist p p') (40 * r)) ≤ E)
    (hXsum : ∑ t ∈ T, (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
      ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤ X) :
    ∃ t ∈ T, (J₀.filter (fun j => tube j = t)).Nonempty ∧ (Ut t).Nonempty ∧
      I ^ 2 / (E * X) * (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
        ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤
      (((((Ut t).image (tubeCol (v t) w)) ×ˢ (J₀.filter (fun j => tube j = t))).filter
        (fun p : ℝ × (E2 × E2) => ∃ x ∈ Ut t, x ∈ pinsOf D cls p.2 ∧
          tubeCol (v t) w x = p.1)).card : ℝ) := by
  classical
  set Ic : τ → ℝ := fun t => ∑ j ∈ J₀.filter (fun j => tube j = t),
    ((pinsOf D cls j ∩ Ut t).card : ℝ) with hIc
  set En : τ → ℝ := fun t => tubeEnergy D cls (J₀.filter (fun j => tube j = t)) (Ut t) (v t) w
    with hEn
  set Sz : τ → ℝ := fun t => (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
    ((J₀.filter (fun j => tube j = t)).card : ℝ) with hSz
  set T' := T.filter (fun t => 0 < Ic t) with hT'
  have hIc0 : ∀ t, 0 ≤ Ic t := fun t => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hEnIc : ∀ t, Ic t ≤ En t := fun t => incid_le_tubeEnergy _ _ _ _ _ _
  have hEn0 : ∀ t, 0 ≤ En t := fun t => (hIc0 t).trans (hEnIc t)
  have hT'T : T' ⊆ T := Finset.filter_subset _ _
  have hIsum' : I ≤ ∑ t ∈ T', Ic t := by
    rw [hT', Finset.sum_filter_of_ne]
    · exact hIsum
    · intro t _ hne
      exact lt_of_le_of_ne (hIc0 t) (Ne.symm hne)
  have hEsum' : ∑ t ∈ T', En t ≤ E := by
    refine le_trans ?_ ((sum_tubeEnergy_le hr hr4 hw hcls hJ₀ hnorm hP4 Bd hBd hcap hU T tube v Ut
      hv htrans hUt).trans hEsum)
    exact Finset.sum_le_sum_of_subset_of_nonneg hT'T (fun t _ _ => hEn0 t)
  have hXsum' : ∑ t ∈ T', Sz t ≤ X := by
    refine le_trans ?_ hXsum
    exact Finset.sum_le_sum_of_subset_of_nonneg hT'T (fun t _ _ => by positivity)
  obtain ⟨t, ht', hIt, hratio⟩ := exists_tube_energy_ratio T' Ic En Sz hI hE hX
    (fun t _ => hIc0 t)
    (fun t ht => lt_of_lt_of_le (Finset.mem_filter.mp ht).2 (hEnIc t))
    (fun t _ => by positivity) hIsum' hEsum' hXsum'
  have ht : t ∈ T := hT'T ht'
  have hEnt : 0 < En t := lt_of_lt_of_le hIt (hEnIc t)
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : Ic t = 0 := by simp only [hIc, hne, Finset.sum_empty]
    linarith
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : Ic t = 0 := by simp only [hIc, hne, Finset.inter_empty, Finset.card_empty,
      Nat.cast_zero, Finset.sum_const_zero]
    linarith
  · have hCS := incidences_sq_le D cls (J₀.filter (fun j => tube j = t)) (Ut t) (tubeCol (v t) w)
    have hCS' : Ic t ^ 2 ≤ (∑ j ∈ J₀.filter (fun j => tube j = t),
        ((cellsHit D cls (Ut t) (tubeCol (v t) w) j).card : ℝ)) * En t := hCS
    have hdiv : Ic t ^ 2 / En t ≤ ∑ j ∈ J₀.filter (fun j => tube j = t),
        ((cellsHit D cls (Ut t) (tubeCol (v t) w) j).card : ℝ) := by
      rw [div_le_iff₀ hEnt]; exact hCS'
    rw [card_col_pairs_eq]
    calc I ^ 2 / (E * X) * (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
          ((J₀.filter (fun j => tube j = t)).card : ℝ) = I ^ 2 / (E * X) * Sz t := by
          simp only [hSz]; ring
      _ ≤ Ic t ^ 2 / En t := hratio
      _ ≤ _ := hdiv

/-- **Case A at a coarse configuration.** -/
theorem caseA_false {τ : Type*} [DecidableEq τ] {e b β : ℝ} (he : 0 < e) (hb : 0 < b)
    (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (r Δs w K₀ A I E X : ℝ) (D J₀ : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
      (P U : Finset E2) (Bd : ℝ → ℝ) (T : Finset τ) (tube : E2 × E2 → τ) (v : τ → Plane)
      (cT aT M : τ → ℝ) (Ut : τ → Finset E2),
    0 < r → r ≤ 1 / 4 → 0 < Δs → 0 < w → 9 ≤ K₀ → 0 ≤ A → 4 * Δs * w ≤ 2 * (9 * r) →
    tubeTol (9 * r) Δs w ≤ δ₀ →
    K₀ ≤ (tubeTol (9 * r) Δs w) ^ (-η) → A ≤ (tubeTol (9 * r) Δs w) ^ (-η) →
    0 < I → 0 < E → 0 < X → (tubeTol (9 * r) Δs w) ^ η ≤ I ^ 2 / (E * X) →
    (∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q)) →
    J₀ ⊆ D → (∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1) →
    (∀ j ∈ J₀, ∀ j' ∈ J₀, j ≠ j' → StripSep r j j') →
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
  intro r Δs w K₀ A I E X D J₀ cls P U Bd T tube v cT aT M Ut hr hr4 hΔs hw hK₀ hA0 hwι hδ
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
  apply hmain (v t) (cT t) (aT t) r (9 * r) Δs w (M t) d K₀ A hvt hr (by positivity) hΔs hw hMt
    (by linarith) hA0 hwι (by nlinarith) hδ hK₀δ hAδ (le_min hdδ hδ1) (min_le_right _ _)
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

end Energy

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/CaseA.lean
