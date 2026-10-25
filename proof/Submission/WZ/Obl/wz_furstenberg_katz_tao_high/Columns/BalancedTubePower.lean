-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.BalancedTubePower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.TubePower
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.TubeSecondMoment
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.CellRepresentatives

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Balanced original pins supply the coarse-cell second moment directly.
Representatives, their Frostman bound and the logarithmic cutoff are all
constructed here, uniformly over the coarse scale. -/
theorem balanced_tube_cells_second_moment_power {A d ν : ℝ}
    (hA : 1 ≤ A) (hd : 0 < d) (hν : 0 < ν) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ Δ w C K : ℝ, 0 < δ → δ ≤ δ₀ → δ ≤ Δ → Δ ≤ w →
        w ≤ 1 / 2 → w ≤ A * Δ → 0 ≤ C → 0 ≤ K →
      ∀ {ι : Type*} [DecidableEq ι],
      ∀ (D J : Finset (E2 × E2)) (cls tube : E2 × E2 → E2 × E2)
        (P : Finset E2) (cell : E2 → ι),
        P.Nonempty → (P.card : ℝ) ≤ δ ^ (-d) →
        (∀ p ∈ P, ‖p‖ ≤ 4) → Balanced P cell K →
        (∀ p ∈ P, ∀ q ∈ P, cell p = cell q → dist p q ≤ 2 * Δ) →
        (∀ x ρ, δ ≤ ρ →
          ((P.filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤ C * ρ * P.card) →
        (∀ t ∈ J.image tube, ‖t.1‖ ≤ 4 ∧ ‖t.2‖ = 1) →
        (J.image tube : Set (E2 × E2)).Pairwise
          (WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep Δ) →
        (∀ j ∈ J, ∀ p ∈ pinsOf D cls j ∩ P,
          |inner ℝ (p - (tube j).1) (tube j).2| < w - 2 * Δ) →
        (∑ t ∈ J.image tube, ((tubeCells D cls P cell J tube t).card : ℝ) ^ 2) ≤
          (3 * K * C) * δ ^ (-ν) * ((P.image cell).card : ℝ) ^ 2 := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hcoeff⟩ := tube_second_moment_power_coefficient hA hd hν
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ Δ w C K hδ hsmall hδΔ hΔw hw2 hwA hC hK ι _
    D J cls tube P cell hP hPcard hP4 hbal hdiam hcount hT hsep hinc
  have hΔ : 0 < Δ := hδ.trans_le hδΔ
  obtain ⟨point, hpoint, hinj, hclose, hFr, _⟩ :=
    Multiscale.balanced_cell_representatives P hP cell hΔ hδΔ hC hK hbal hdiam hcount
  have hcellcard : ((P.image cell).card : ℝ) ≤ δ ^ (-d) :=
    (Nat.cast_le.mpr (Finset.card_image_le)).trans hPcard
  obtain ⟨hL, hcoef⟩ := hcoeff δ Δ w hδ hsmall hΔ (hδΔ.trans hΔw) hw2 hwA
    (P.image cell).card hcellcard
  have hcellinc : ∀ t ∈ J.image tube, ∀ c ∈ tubeCells D cls P cell J tube t,
      |inner ℝ (point c - t.1) t.2| < w := by
    intro t ht c hc
    obtain ⟨j, hj, hcj⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨hjJ, hjt⟩ := Finset.mem_filter.mp hj
    obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hcj
    have hdist := hclose p (Finset.mem_inter.mp hp).2
    rw [hpc] at hdist
    have hgeom := hinc j hjJ p hp
    rw [hjt] at hgeom
    have herr : |inner ℝ (point c - p) t.2| ≤ 2 * Δ := by
      calc
        _ ≤ ‖point c - p‖ * ‖t.2‖ := abs_real_inner_le_norm _ _
        _ = dist p (point c) := by rw [(hT t ht).2, mul_one, ← dist_eq_norm, dist_comm]
        _ ≤ 2 * Δ := hdist
    have heq : point c - t.1 = (point c - p) + (p - t.1) := by abel
    rw [heq, inner_add_left]
    exact (abs_add_le _ _).trans_lt (by linarith)
  have hh := tube_cells_second_moment D J cls tube P cell point hP hinj hΔ hΔw hw2
    (show 0 ≤ 3 * K * C by positivity)
    (fun c hc => hP4 _ (hpoint c hc).1)
    (by simpa only [Metric.mem_closedBall] using hFr) hT hsep hcellinc
    (Nat.log 2 (P.image cell).card + 1) hL
  calc
    _ ≤ 64000 * (64 * w / Δ + 2) * (36 * w / Δ + 2) *
        (3 * K * C) * (1 + Real.log (1 / w)) *
          (2 * ((Nat.log 2 (P.image cell).card + 1 : ℕ) : ℝ) + 1) *
            ((P.image cell).card : ℝ) ^ 2 := hh
    _ = (3 * K * C) * (64000 * (64 * w / Δ + 2) * (36 * w / Δ + 2) *
        (1 + Real.log (1 / w)) * (2 * ((Nat.log 2 (P.image cell).card + 1 : ℕ) : ℝ) + 1)) *
          ((P.image cell).card : ℝ) ^ 2 := by ring
    _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
