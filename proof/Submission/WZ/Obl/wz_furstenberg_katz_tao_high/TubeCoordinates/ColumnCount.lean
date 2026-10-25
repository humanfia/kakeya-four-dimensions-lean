-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.ColumnCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/TubeCoordinates/ColumnCount.lean (82de8bd).
-- Ported from workspace o157, branch x0572 (commit 9dec67f), TubeCoordinates/ColumnCount.lean;
-- SP references re-pointed to the accepted o223 (SP), o142 (covers) and o143 (cover counting) modules.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.Quantization
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealSeparatedCounts

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open WangZahlLot.Obl.wz_square_frostman_graph_projection

open scoped BigOperators

/-- If every point in one coarse column is incident to many nearly parallel
fine lines, that column has few distinct transverse grid heights. -/
theorem column_height_card_of_error (P L : Finset (ℝ × ℝ)) {r Δ c M : ℝ}
    (hr : 0 < r) (hΔ : 0 < Δ)
    (herror : ∀ p ∈ P, ∀ l ∈ L, |p.2 - height l p.1| ≤ r →
      |p.2 / Δ - height (rescale Δ l) c| ≤ 2 * (r / Δ))
    (hdegree : ∀ p ∈ P,
      M ≤ ((L.filter (fun l => |p.2 - height l p.1| ≤ r)).card : ℝ)) :
    M * ((P.image (fun p => rounded (r / Δ) (p.2 / Δ))).card : ℝ) ≤ 8 * (L.card : ℝ) := by
  classical
  let h := r / Δ
  have hh : 0 < h := div_pos hr hΔ
  let A := P.image (fun p => rounded h (p.2 / Δ))
  let R (a : ℝ) (l : ℝ × ℝ) : Prop :=
    ∃ p ∈ P, rounded h (p.2 / Δ) = a ∧ |p.2 - height l p.1| ≤ r
  have hrow (a : ℝ) (ha : a ∈ A) : M ≤ ((L.filter (R a)).card : ℝ) := by
    obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp ha
    apply (hdegree p hp).trans
    exact_mod_cast Finset.card_le_card (show L.filter (fun l => |p.2 - height l p.1| ≤ r) ⊆
      L.filter (R a) from fun l hl => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hl).1, p, hp, hpa, (Finset.mem_filter.mp hl).2⟩)
  have hcol (l : ℝ × ℝ) (hl : l ∈ L) : ((A.filter (fun a => R a l)).card : ℝ) ≤ 8 := by
    have hsep : ∀ a ∈ A.filter (fun a => R a l), ∀ b ∈ A.filter (fun a => R a l),
        a ≠ b → h ≤ dist a b := by
      intro a ha b hb hab
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).1
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hb).1
      exact rounded_separated hh hab
    have hball (a : ℝ) (ha : a ∈ A.filter (fun a => R a l)) :
        dist a (height (rescale Δ l) c) ≤ 3 * h := by
      obtain ⟨p, hp, rfl, hinc⟩ := (Finset.mem_filter.mp ha).2
      have hn := herror p hp l hl hinc
      have he := rounded_error hh (p.2 / Δ)
      have he' : dist (rounded h (p.2 / Δ)) (p.2 / Δ) ≤ h := by
        rw [dist_comm, Real.dist_eq, abs_of_nonneg he.1]
        exact he.2.le
      have hn' : dist (p.2 / Δ) (height (rescale Δ l) c) ≤ 2 * h := by
        simpa only [Real.dist_eq] using hn
      exact (dist_triangle _ _ _).trans (by linarith)
    have hc := SP.real_separated_ball_card hh (by positivity : 0 ≤ 3 * h)
      (A.filter (fun a => R a l)) hsep hball
    apply (mul_le_mul_iff_left₀ hh).mp
    convert hc using 1 <;> ring
  have hdouble : (∑ a ∈ A, ((L.filter (R a)).card : ℝ)) =
      ∑ l ∈ L, ((A.filter (fun a => R a l)).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  calc
    M * (A.card : ℝ) = ∑ _a ∈ A, M := by simp [mul_comm]
    _ ≤ ∑ a ∈ A, ((L.filter (R a)).card : ℝ) := Finset.sum_le_sum hrow
    _ = ∑ l ∈ L, ((A.filter (fun a => R a l)).card : ℝ) := hdouble
    _ ≤ ∑ _l ∈ L, (8 : ℝ) := Finset.sum_le_sum hcol
    _ = 8 * (L.card : ℝ) := by simp [mul_comm]

/-- Cardinality bound with independently chosen column width. -/
theorem column_height_card_at_width (P L : Finset (ℝ × ℝ)) {r Δ w c M : ℝ}
    (hr : 0 < r) (hΔ : 0 < Δ) (hscale : Δ * w ≤ r)
    (hcolumn : ∀ p ∈ P, |p.1 - c| ≤ w)
    (hslope : ∀ l ∈ L, |l.1| ≤ Δ)
    (hdegree : ∀ p ∈ P,
      M ≤ ((L.filter (fun l => |p.2 - height l p.1| ≤ r)).card : ℝ)) :
    M * ((P.image (fun p => rounded (r / Δ) (p.2 / Δ))).card : ℝ) ≤ 8 * (L.card : ℝ) := by
  refine column_height_card_of_error P L (c := c) hr hΔ ?_ hdegree
  intro p hp l hl hi
  exact rescaled_column_incidence_of_width hΔ hscale hi (hcolumn p hp) (hslope l hl)

/-- Equal column and transverse scales suffice when the coarse scale squared
is at most the fine incidence width. -/
theorem column_height_card (P L : Finset (ℝ × ℝ)) {r Δ c M : ℝ}
    (hr : 0 < r) (hΔ : 0 < Δ) (hscale : Δ ^ 2 ≤ r)
    (hcolumn : ∀ p ∈ P, |p.1 - c| ≤ Δ)
    (hslope : ∀ l ∈ L, |l.1| ≤ Δ)
    (hdegree : ∀ p ∈ P,
      M ≤ ((L.filter (fun l => |p.2 - height l p.1| ≤ r)).card : ℝ)) :
    M * ((P.image (fun p => rounded (r / Δ) (p.2 / Δ))).card : ℝ) ≤ 8 * (L.card : ℝ) :=
  column_height_card_at_width P L hr hΔ (by simpa only [pow_two] using hscale)
    hcolumn hslope hdegree

/-- A column of high-degree pins has a small cover by transverse intervals at
the rescaled fine resolution. -/
theorem column_height_cover_at_width (P L : Finset (ℝ × ℝ)) {r Δ w c M : ℝ}
    (hr : 0 < r) (hΔ : 0 < Δ) (hscale : Δ * w ≤ r) (hM : 0 < M)
    (hcolumn : ∀ p ∈ P, |p.1 - c| ≤ w)
    (hslope : ∀ l ∈ L, |l.1| ≤ Δ)
    (hdegree : ∀ p ∈ P,
      M ≤ ((L.filter (fun l => |p.2 - height l p.1| ≤ r)).card : ℝ)) :
    ∃ m : ℕ, ∃ cc : Fin m → ℝ,
      Covers (r / Δ) ((fun p : ℝ × ℝ => p.2 / Δ) '' (↑P : Set (ℝ × ℝ))) cc ∧
      (m : ℝ) ≤ 8 * (L.card : ℝ) / M := by
  classical
  let A := P.image (fun p => rounded (r / Δ) (p.2 / Δ))
  let e := Fintype.equivFin A
  refine ⟨Fintype.card A, fun i => (e.symm i).val, ?_, ?_⟩
  · rintro z ⟨p, hp, rfl⟩
    have ha : rounded (r / Δ) (p.2 / Δ) ∈ A := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    refine Set.mem_iUnion.mpr ⟨e ⟨_, ha⟩, ?_⟩
    simp only [Equiv.symm_apply_apply, Metric.mem_closedBall, Real.dist_eq]
    have he := rounded_error (div_pos hr hΔ) (p.2 / Δ)
    rw [abs_of_nonneg he.1]
    exact he.2.le
  · have hc := column_height_card_at_width P L hr hΔ hscale hcolumn hslope hdegree
    rw [Fintype.card_coe]
    apply (le_div_iff₀ hM).mpr
    simpa only [A, mul_comm] using hc

/-- The original equal-width specialization. -/
theorem column_height_cover (P L : Finset (ℝ × ℝ)) {r Δ c M : ℝ}
    (hr : 0 < r) (hΔ : 0 < Δ) (hscale : Δ ^ 2 ≤ r) (hM : 0 < M)
    (hcolumn : ∀ p ∈ P, |p.1 - c| ≤ Δ)
    (hslope : ∀ l ∈ L, |l.1| ≤ Δ)
    (hdegree : ∀ p ∈ P,
      M ≤ ((L.filter (fun l => |p.2 - height l p.1| ≤ r)).card : ℝ)) :
    ∃ m : ℕ, ∃ cc : Fin m → ℝ,
      Covers (r / Δ) ((fun p : ℝ × ℝ => p.2 / Δ) '' (↑P : Set (ℝ × ℝ))) cc ∧
      (m : ℝ) ≤ 8 * (L.card : ℝ) / M :=
  column_height_cover_at_width P L hr hΔ (by simpa only [pow_two] using hscale)
    hM hcolumn hslope hdegree

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
