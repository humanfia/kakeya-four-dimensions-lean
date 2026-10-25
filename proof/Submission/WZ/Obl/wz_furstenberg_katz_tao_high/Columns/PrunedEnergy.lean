-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.PrunedEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.DenseTube
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.HighDegreePruning

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open scoped BigOperators
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- Count the incidences in one cell by their pins instead of their classes. -/
theorem cell_incidence_mass_eq {ι : Type*} [DecidableEq ι]
    (D J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (U : Finset E2) (cell : E2 → ι) (c : ι) :
    (∑ j ∈ J, ((cellPins D cls U cell j c).card : ℝ)) =
      ∑ p ∈ U.filter (fun p => cell p = c),
        ((J.filter (fun j => p ∈ pinsOf D cls j)).card : ℝ) := by
  classical
  have heq : ∀ j, cellPins D cls U cell j c =
      (U.filter (fun p => cell p = c)).filter (fun p => p ∈ pinsOf D cls j) := by
    intro j
    ext p
    simp only [cellPins, Finset.mem_filter, Finset.mem_inter]
    tauto
  simp_rw [heq, Finset.card_filter]
  push_cast
  exact Finset.sum_comm

/-- A cell has at most its pin count times the largest degree of a pin. -/
theorem cell_incidence_mass_le {ι : Type*} [DecidableEq ι]
    (D J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (U : Finset E2) (cell : E2 → ι) (c : ι) {n M : ℝ} (hM : 0 ≤ M)
    (hn : ((U.filter (fun p => cell p = c)).card : ℝ) ≤ n)
    (hpin : ∀ p ∈ U.filter (fun p => cell p = c),
      ((J.filter (fun j => p ∈ pinsOf D cls j)).card : ℝ) ≤ M) :
    (∑ j ∈ J, ((cellPins D cls U cell j c).card : ℝ)) ≤ n * M := by
  rw [cell_incidence_mass_eq]
  calc
    (∑ p ∈ U.filter (fun p => cell p = c),
        ((J.filter (fun j => p ∈ pinsOf D cls j)).card : ℝ)) ≤
        ∑ _p ∈ U.filter (fun p => cell p = c), M := Finset.sum_le_sum hpin
    _ = ((U.filter (fun p => cell p = c)).card : ℝ) * M := by simp
    _ ≤ n * M := mul_le_mul_of_nonneg_right hn hM

/-- A uniform pin-class incidence bound in each cell gives the weight
bound used to discard coarse tubes with too many cells. -/
theorem tube_mass_le_of_cell_bound {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]
    (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ) (t : τ)
    {W : ℝ}
    (hcell : ∀ c ∈ tubeCells D cls U cell J₀ tube t,
      (∑ j ∈ J₀.filter (fun j => tube j = t), ((cellPins D cls U cell j c).card : ℝ)) ≤ W) :
    (∑ j ∈ J₀.filter (fun j => tube j = t), ((pinsOf D cls j ∩ U).card : ℝ)) ≤
      W * (tubeCells D cls U cell J₀ tube t).card := by
  classical
  let T := tubeCells D cls U cell J₀ tube t
  let mass (c : ι) : ℝ :=
    ∑ j ∈ J₀.filter (fun j => tube j = t), ((cellPins D cls U cell j c).card : ℝ)
  have hTU : T ⊆ U.image cell := by
    intro c hc
    obtain ⟨j, hj, hcj⟩ := Finset.mem_biUnion.mp hc
    exact cellsHit_subset D cls U cell j hcj
  have hzero : ∀ c ∈ U.image cell, c ∉ T → mass c = 0 := by
    intro c _ hc
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : c ∉ cellsHit D cls U cell j := fun hcj =>
      hc (Finset.mem_biUnion.mpr ⟨j, hj, hcj⟩)
    rw [cellPins_eq_empty_of_not_mem D cls U cell j hnot]
    simp
  have hsum : (∑ c ∈ T, mass c) = ∑ c ∈ U.image cell, mass c :=
    Finset.sum_subset hTU hzero
  calc
    (∑ j ∈ J₀.filter (fun j => tube j = t), ((pinsOf D cls j ∩ U).card : ℝ)) =
        ∑ c ∈ U.image cell, mass c := by
      simp_rw [card_pins_eq_sum_cellPins D cls U cell]
      exact Finset.sum_comm
    _ = ∑ c ∈ T, mass c := hsum.symm
    _ ≤ ∑ _c ∈ T, W := Finset.sum_le_sum hcell
    _ = W * T.card := by simp [mul_comm]

/-- Coarse-tube second moments control the full fine class-cell energy
after retaining half the pin-class incidences. No class or tube balance
is assumed: the weight bound is per occupied cell. -/
theorem incidence_energy_of_tube_second_moment {ι τ : Type*}
    [DecidableEq ι] [DecidableEq τ]
    (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ)
    {W E B : ℝ} (hW : 0 ≤ W) (hB : 0 < B)
    (hweight : ∀ t ∈ J₀.image tube,
      (∑ j ∈ J₀.filter (fun j => tube j = t), ((pinsOf D cls j ∩ U).card : ℝ)) ≤
        W * (tubeCells D cls U cell J₀ tube t).card)
    (hsecond : (∑ t ∈ J₀.image tube, ((tubeCells D cls U cell J₀ tube t).card : ℝ) ^ 2) ≤ E)
    (hbudget : 2 * W * E ≤ B * ∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) :
    (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) ^ 2 ≤
      4 * B * J₀.card *
        ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 := by
  classical
  let deg (t : τ) : ℝ := (tubeCells D cls U cell J₀ tube t).card
  let w (j : E2 × E2) : ℝ := (pinsOf D cls j ∩ U).card
  let mass (t : τ) : ℝ := ∑ j ∈ J₀.filter (fun j => tube j = t), w j
  let J := J₀.filter (fun j => deg (tube j) ≤ B)
  have hJJ : J ⊆ J₀ := Finset.filter_subset _ _
  have htotal : ∑ t ∈ J₀.image tube, mass t = ∑ j ∈ J₀, w j :=
    (sum_classes_eq_sum_tubes J₀ tube w).symm
  have hT : J.image tube = (J₀.image tube).filter (fun t => deg t ≤ B) := by
    ext t
    simp only [J, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, ⟨hj, hd⟩, rfl⟩
      exact ⟨⟨j, hj, rfl⟩, hd⟩
    · rintro ⟨⟨j, hj, rfl⟩, hd⟩
      exact ⟨j, ⟨hj, hd⟩, rfl⟩
  have hfiber : ∀ t ∈ (J₀.image tube).filter (fun t => deg t ≤ B),
      J.filter (fun j => tube j = t) = J₀.filter (fun j => tube j = t) := by
    intro t ht
    have htB := (Finset.mem_filter.mp ht).2
    ext j
    simp only [J, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hj, hjt⟩
      exact ⟨⟨hj, by rwa [hjt]⟩, hjt⟩
  have hretained : ∑ t ∈ (J₀.image tube).filter (fun t => deg t ≤ B), mass t =
      ∑ j ∈ J, w j := by
    rw [sum_classes_eq_sum_tubes J tube w, hT]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hfiber t ht]
  have hkeep := half_mass_of_second_moment (J₀.image tube) deg mass hW hB
    (fun _ _ => Nat.cast_nonneg _) hweight hsecond (by rwa [htotal])
  rw [htotal, hretained] at hkeep
  have hcs := incidences_sq_le D cls J U cell
  have hcells : (∑ j ∈ J, ((cellsHit D cls U cell j).card : ℝ)) ≤ B * J₀.card := by
    calc
      (∑ j ∈ J, ((cellsHit D cls U cell j).card : ℝ)) ≤ ∑ _j ∈ J, B := by
        apply Finset.sum_le_sum
        intro j hj
        have hjB : deg (tube j) ≤ B := (Finset.mem_filter.mp hj).2
        have hsub := cellsHit_subset_tubeCells D cls U cell J₀ tube (hJJ hj)
        exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hjB
      _ = B * J.card := by simp [mul_comm]
      _ ≤ B * J₀.card := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card hJJ)) hB.le
  have henergy : (∑ j ∈ J, ∑ c ∈ U.image cell,
      ((cellPins D cls U cell j c).card : ℝ) ^ 2) ≤
        ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hJJ
      (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hbound : (∑ j ∈ J, w j) ^ 2 ≤ B * J₀.card *
      ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 := by
    refine hcs.trans ?_
    exact mul_le_mul hcells henergy
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      (mul_nonneg hB.le (Nat.cast_nonneg _))
  have htotal0 : 0 ≤ ∑ j ∈ J₀, w j := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsquare := pow_le_pow_left₀ (div_nonneg htotal0 (by norm_num)) hkeep 2
  change (∑ j ∈ J₀, w j) ^ 2 ≤ _
  nlinarith only [hsquare, hbound]

/-- Eliminate the degree cutoff from the pruning bound. The point mass
can be the original fine-pin mass even when the classes are coarsened. -/
theorem incidence_cubic_of_tube_second_moment {ι τ : Type*}
    [DecidableEq ι] [DecidableEq τ]
    (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ)
    {W E : ℝ} (hW : 0 < W) (hE : 0 < E)
    (hI : 0 < ∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ))
    (hweight : ∀ t ∈ J₀.image tube,
      (∑ j ∈ J₀.filter (fun j => tube j = t), ((pinsOf D cls j ∩ U).card : ℝ)) ≤
        W * (tubeCells D cls U cell J₀ tube t).card)
    (hsecond : (∑ t ∈ J₀.image tube, ((tubeCells D cls U cell J₀ tube t).card : ℝ) ^ 2) ≤ E) :
    (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) ^ 3 ≤
      8 * W * E * J₀.card *
        ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 := by
  classical
  let I : ℝ := ∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)
  have hI0 : 0 < I := hI
  have hB : 0 < 2 * W * E / I := by positivity
  have hh := incidence_energy_of_tube_second_moment D cls U cell J₀ tube hW.le hB
    hweight hsecond (by change 2 * W * E ≤ (2 * W * E / I) * I; simp [hI0.ne'])
  have hm := mul_le_mul_of_nonneg_right hh hI0.le
  convert hm using 1 <;> dsimp only [I] at * <;> field_simp <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
