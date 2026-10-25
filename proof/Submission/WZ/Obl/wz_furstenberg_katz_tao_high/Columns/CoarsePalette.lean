-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.CoarsePalette.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o222/x0720 Columns/CoarsePalette.lean (ccadf1f, 8169359).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.PaletteEnergy

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators Classical

/-- A bound at just one angular radius suffices for a coarse pair. -/
theorem coarse_common_classes_le_of_cap {r R m θ V : ℝ}
    (hrR : r ≤ R) (hR : 0 < R) (hR1 : R ≤ 1) (hm : 0 < m)
    {D J : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < R ∨ dist q.2 (-(cls q).2) < R))
    {p p' : E2} (hp : ‖p‖ ≤ 4) (hp' : ‖p'‖ ≤ 4)
    (hθ : 288 * R / max (dist p p') (144 * R) ≤ θ)
    (hcap : ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter fun e => dist e u ≤ θ).card : ℝ) ≤ V)
    (hmin : ∀ j ∈ J, p ∈ pinsOf D cls j →
      m ≤ (((bushOf D p).filter fun e => cls (p, e) = j).card : ℝ)) :
    ((J.filter fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j).card : ℝ) ≤ 2 * V / m := by
  let Bd (ρ : ℝ) := if ρ ≤ θ then V else ((bushOf D p).card : ℝ)
  have hcap' : ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter fun e => dist e u ≤ ρ).card : ℝ) ≤ Bd ρ := by
    intro u hu ρ hρ
    dsimp [Bd]
    split_ifs with hρθ
    · refine le_trans ?_ (hcap u hu)
      exact Nat.cast_le.mpr (Finset.card_le_card (by
        intro e he
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2.trans hρθ⟩))
    · exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have hh := coarse_common_classes_le hrR hR hR1 hm hunit hgeo Bd hp hp' hcap' hmin
  simpa only [Bd, hθ, ite_true] using hh

/-- The angular radius associated with one distance shell, including the
terminal shell which contains all distances below the last palette scale. -/
noncomputable def paletteCapRadius (R : ℝ) (ρ : ℕ → ℝ) (a i : ℕ) : ℝ :=
  if i = a then 2 else 288 * R / max (ρ (i + 1)) (144 * R)

theorem coarse_radius_le_palette {R : ℝ} (hR : 0 < R) (ρ : ℕ → ℝ)
    {a i : ℕ} {d : ℝ} (hshell : i = a ∨ ρ (i + 1) < d) :
    288 * R / max d (144 * R) ≤ paletteCapRadius R ρ a i := by
  have hden : 0 < max d (144 * R) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  unfold paletteCapRadius
  split_ifs with hia
  · rw [div_le_iff₀ hden]
    have hh := le_max_right d (144 * R)
    linarith
  · have hlo : ρ (i + 1) ≤ d := (hshell.resolve_left hia).le
    exact div_le_div_of_nonneg_left (by positivity)
      (lt_of_lt_of_le (by positivity) (le_max_right _ _)) (max_le_max_right _ hlo)

/-- Actual cap counts at the reflected palette radii give the full coarse
cell energy. All pins and normals remain at the original fine scale. -/
theorem coarse_cell_energy_le_palette {ι : Type*} [DecidableEq ι]
    {r R m : ℝ} (hrR : r ≤ R) (hR : 0 < R) (hR1 : R ≤ 1) (hm : 0 < m)
    (D J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (P : Finset E2) (cell : E2 → ι) (ρ M V : ℕ → ℝ)
    {h a : ℕ} (hha : h ≤ a)
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < R ∨ dist q.2 (-(cls q).2) < R))
    (hP : ∀ p ∈ P, ‖p‖ ≤ 4)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, cell p = cell q → dist p q ≤ ρ h)
    (hV : ∀ i ∈ Finset.Icc h a, 0 ≤ V i)
    (hM : ∀ p ∈ P, ∀ i ∈ Finset.Icc h a,
      ((P.filter fun q => dist p q ≤ ρ i).card : ℝ) ≤ M i)
    (hcap : ∀ p ∈ P, ∀ i ∈ Finset.Icc h a, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter fun e => dist e u ≤ paletteCapRadius R ρ a i).card : ℝ) ≤ V i)
    (hmin : ∀ p ∈ P, ∀ j ∈ J, p ∈ pinsOf D cls j →
      m ≤ (((bushOf D p).filter fun e => cls (p, e) = j).card : ℝ)) :
    (∑ j ∈ J, ∑ c ∈ P.image cell, ((cellPins D cls P cell j c).card : ℝ) ^ 2) ≤
      P.card * ∑ i ∈ Finset.Icc h a, M i * (2 * V i / m) := by
  apply cell_energy_le_palette D J cls P cell ρ M (fun i => 2 * V i / m) hha hdiam
  · intro i hi
    exact div_nonneg (mul_nonneg (by norm_num) (hV i hi)) hm.le
  · exact hM
  · intro p hp q hq i hi hdist hshell
    exact coarse_common_classes_le_of_cap hrR hR hR1 hm hunit hgeo (hP p hp) (hP q hq)
      (coarse_radius_le_palette hR ρ hshell) (hcap p hp i hi) (hmin p hp)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
