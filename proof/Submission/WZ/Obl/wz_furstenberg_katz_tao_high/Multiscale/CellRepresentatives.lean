-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.CellRepresentatives.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.BalancedQuotients

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open WangZahlLot.Obl.wz_tower_balanced_refinement
open WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
open WangZahlLot.Obl.wz_normalized_projection_coarse_fine

attribute [local instance] Classical.propDecidable

/-- Balanced cells have actual, distinct point representatives with a
normalized linear Frostman bound. Their maximal pin mass is also explicit. -/
theorem balanced_cell_representatives {E ι : Type*} [PseudoMetricSpace E]
    [DecidableEq E] [DecidableEq ι]
    (P : Finset E) (hP : P.Nonempty) (cell : E → ι)
    {r Δ C K : ℝ} (hΔ : 0 < Δ) (hrΔ : r ≤ Δ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hbal : Balanced P cell K)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, cell p = cell q → dist p q ≤ 2 * Δ)
    (hcount : ∀ x ρ, r ≤ ρ →
      ((P.filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤ C * ρ * P.card) :
    ∃ point : ι → E,
      (∀ c ∈ P.image cell, point c ∈ P ∧ cell (point c) = c) ∧
      Set.InjOn point (↑(P.image cell) : Set ι) ∧
      (∀ p ∈ P, dist p (point (cell p)) ≤ 2 * Δ) ∧
      (∀ x ρ, Δ ≤ ρ →
        ((((P.image cell).image point).filter (fun y => dist y x ≤ ρ)).card : ℝ) ≤
          (3 * K * C) * ρ * (P.image cell).card) ∧
      ∀ c ∈ P.image cell,
        ((P.filter (fun p => cell p = c)).card : ℝ) ≤
          K * P.card / (P.image cell).card := by
  classical
  obtain ⟨p₀, hp₀⟩ := hP
  have hPne : P.Nonempty := ⟨p₀, hp₀⟩
  have hwit : ∀ c ∈ P.image cell, ∃ p ∈ P, cell p = c := by
    intro c hc
    exact Finset.mem_image.mp hc
  let point (c : ι) : E := if hc : c ∈ P.image cell then (hwit c hc).choose else p₀
  have hpoint : ∀ c ∈ P.image cell, point c ∈ P ∧ cell (point c) = c := by
    intro c hc
    simpa only [point, dite_eq_left hc] using (hwit c hc).choose_spec
  have hinj : Set.InjOn point (↑(P.image cell) : Set ι) := by
    intro c hc d hd heq
    exact (hpoint c hc).2.symm.trans ((congrArg cell heq).trans (hpoint d hd).2)
  have hclose : ∀ p ∈ P, dist p (point (cell p)) ≤ 2 * Δ := by
    intro p hp
    have hh := hpoint (cell p) (Finset.mem_image_of_mem cell hp)
    exact hdiam p hp _ hh.1 hh.2.symm
  refine ⟨point, hpoint, hinj, hclose, ?_, ?_⟩
  · intro x ρ hρ
    have heq : ((P.image cell).image point).filter (fun y => dist y x ≤ ρ) =
        ((P.image cell).filter (fun c => dist (point c) x ≤ ρ)).image point := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨c, hc, rfl⟩, hdist⟩
        exact ⟨c, ⟨hc, hdist⟩, rfl⟩
      · rintro ⟨c, ⟨hc, hdist⟩, rfl⟩
        exact ⟨⟨c, hc, rfl⟩, hdist⟩
    rw [heq, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    have hh := balanced_quantized_count P hPne cell id point hK hbal
      (show 0 ≤ 2 * Δ by positivity) hclose (σ := 1)
      (by simpa only [Real.rpow_one, id_eq] using hcount) x ρ (hrΔ.trans hρ)
    simp only [Real.rpow_one] at hh
    calc
      _ ≤ K * (C * (ρ + 2 * Δ)) * (P.image cell).card := hh
      _ ≤ K * (C * (3 * ρ)) * (P.image cell).card := by
        gcongr
        linarith
      _ = _ := by ring
  · intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    have hpos : (0 : ℝ) < (P.image cell).card := Nat.cast_pos.mpr (hPne.image cell).card_pos
    rw [le_div_iff₀ hpos]
    have hh := (balanced_fiber_card_bounds P cell hbal hp).1
    rw [mul_comm]
    convert hh using 1 <;> congr

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
