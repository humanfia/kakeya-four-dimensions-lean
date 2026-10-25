-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.CellEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.CommonClasses

/-!
# Line classes meet many cells (Kaufman's energy inside a cell)

Fix a set `U` of pins and a map `cell : E2 → ι` (for instance the `Δ`-squares of a grid).
For a line class `j` write `cellPins j c` for its pins in `U` lying in the cell `c`, and
`cellsHit j` for the set of cells containing pins of `j`.

* `incidences_sq_le`: Cauchy–Schwarz over the pairs (class, cell):
  `(∑_j #(pins j ∩ U))² ≤ (∑_j #cellsHit j) · ∑_j ∑_c #(cellPins j c)²`.
* `cell_energy_eq`: inside one cell, `∑_j #(cellPins j c)²` is the number of
  (pin, pin, class) triples, i.e. the sum over pairs of pins of the cell of their common
  classes.
* `cell_energy_le_rpow`: with `(K, s)`-Katz–Tao bushes, every pair of pins of a cell
  contributes at most `2 K (91 / max (dist p p') (40 r)) ^ s` (`common_classes_le_rpow`).
* `layer_cake_rpow`: a dyadic layer-cake bound for `∑_q max (dist p q) r₀ ^ (-s)` in terms of
  the counts of the balls `B(p, r₀ 2^(k+1))`.

Together: classes meet at least `(∑_j #(pins j ∩ U))² / (cell energy)` cells in total.  When
the cells are relatively `s'`-Frostman with `s' > s` the energy of a cell with `n` pins is
`≲ K n² Δ^(-s)`, which is the column-density count of x0658's o222 post (12:41Z).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open scoped BigOperators

section Cells

variable {ι : Type*} [DecidableEq ι]

/-- The pins of the class `j` among `U` that lie in the cell `c`. -/
noncomputable def cellPins (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (j : E2 × E2) (c : ι) : Finset E2 :=
  (pinsOf D cls j ∩ U).filter (fun p => cell p = c)

/-- The cells containing pins of the class `j` among `U`. -/
noncomputable def cellsHit (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (j : E2 × E2) : Finset ι :=
  (pinsOf D cls j ∩ U).image cell

theorem cellsHit_subset (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (j : E2 × E2) : cellsHit D cls U cell j ⊆ U.image cell := by
  classical
  intro c hc
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
  exact Finset.mem_image.mpr ⟨p, (Finset.mem_inter.mp hp).2, rfl⟩

/-- The pins of `j` in `U` are the union of their cell pieces. -/
theorem card_pins_eq_sum_cellPins (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (U : Finset E2) (cell : E2 → ι) (j : E2 × E2) :
    ((pinsOf D cls j ∩ U).card : ℝ) =
      ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := cell) (s := pinsOf D cls j ∩ U)
    (t := U.image cell) (fun p hp => Finset.mem_image.mpr ⟨p, (Finset.mem_inter.mp hp).2, rfl⟩)
  rw [h]
  push_cast
  rfl

/-- A cell piece is empty outside the cells hit. -/
theorem cellPins_eq_empty_of_not_mem (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (U : Finset E2) (cell : E2 → ι) (j : E2 × E2) {c : ι}
    (hc : c ∉ cellsHit D cls U cell j) : cellPins D cls U cell j c = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  exact hc (Finset.mem_image.mpr ⟨p, hp'.1, hp'.2⟩)

/-- For one class: the sum over all cells equals the sum over the cells hit. -/
theorem sum_cells_eq_sum_hit (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (U : Finset E2) (cell : E2 → ι) (j : E2 × E2) (f : ℕ → ℝ) (hf : f 0 = 0) :
    ∑ c ∈ U.image cell, f (cellPins D cls U cell j c).card =
      ∑ c ∈ cellsHit D cls U cell j, f (cellPins D cls U cell j c).card := by
  classical
  symm
  apply Finset.sum_subset (cellsHit_subset D cls U cell j)
  intro c _ hc
  rw [cellPins_eq_empty_of_not_mem D cls U cell j hc, Finset.card_empty, hf]

/-- **Cauchy–Schwarz over (class, cell) pairs.** -/
theorem incidences_sq_le (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (J₀ : Finset (E2 × E2))
    (U : Finset E2) (cell : E2 → ι) :
    (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) ^ 2 ≤
      (∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ)) *
        ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 := by
  classical
  set S := J₀.sigma (fun j => cellsHit D cls U cell j) with hS
  set x : (Σ _ : E2 × E2, ι) → ℝ := fun jc => ((cellPins D cls U cell jc.1 jc.2).card : ℝ) with hx
  have hsum : ∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ) = ∑ jc ∈ S, x jc := by
    rw [hS, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    rw [card_pins_eq_sum_cellPins D cls U cell j]
    exact sum_cells_eq_sum_hit D cls U cell j (fun n => (n : ℝ)) (by simp)
  have hsq : ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 =
      ∑ jc ∈ S, x jc ^ 2 := by
    rw [hS, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    exact sum_cells_eq_sum_hit D cls U cell j (fun n => (n : ℝ) ^ 2) (by simp)
  have hcard : (S.card : ℝ) = ∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ) := by
    rw [hS, Finset.card_sigma]
    push_cast
    rfl
  rw [hsum, hsq, ← hcard]
  exact sq_sum_le_card_mul_sum_sq

/-- Inside one cell, `∑_j #(cellPins j c)²` counts the common classes of pairs of pins. -/
theorem cell_energy_eq (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (J₀ : Finset (E2 × E2))
    (U : Finset E2) (cell : E2 → ι) (c : ι) :
    ∑ j ∈ J₀, ((cellPins D cls U cell j c).card : ℝ) ^ 2 =
      ∑ p ∈ U.filter (fun p => cell p = c), ∑ p' ∈ U.filter (fun p => cell p = c),
        ((J₀.filter (fun j => p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j)).card : ℝ) := by
  classical
  set V := U.filter (fun p => cell p = c) with hV
  have hpiece : ∀ j, cellPins D cls U cell j c = V.filter (fun p => p ∈ pinsOf D cls j) := by
    intro j
    ext p
    simp only [cellPins, hV, Finset.mem_filter, Finset.mem_inter]
    tauto
  have hsq : ∀ j ∈ J₀, ((cellPins D cls U cell j c).card : ℝ) ^ 2 =
      ∑ p ∈ V, ∑ p' ∈ V,
        (if p ∈ pinsOf D cls j ∧ p' ∈ pinsOf D cls j then (1 : ℝ) else 0) := by
    intro j _
    rw [hpiece j, sq, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro p' _
    by_cases h1 : p ∈ pinsOf D cls j <;> by_cases h2 : p' ∈ pinsOf D cls j <;> simp [h1, h2]
  rw [Finset.sum_congr rfl hsq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p' _
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

/-- **Cell energy** with `(K, s)`-Katz–Tao bushes: every pair of pins of a cell contributes at
most `2 K (91 / max (dist p p') (40 r)) ^ s`. -/
theorem cell_energy_le_rpow {r s K : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (hs : 0 ≤ s)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2} (hP4 : ∀ p ∈ P, ‖p‖ ≤ 4)
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ K * (ρ / r) ^ s)
    {U : Finset E2} (hU : U ⊆ P) (cell : E2 → ι) :
    ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 ≤
      ∑ c ∈ U.image cell, ∑ p ∈ U.filter (fun p => cell p = c),
        ∑ p' ∈ U.filter (fun p => cell p = c), 2 * K * (91 / max (dist p p') (40 * r)) ^ s := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  rw [cell_energy_eq D cls J₀ U cell c]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro p' hp'
  have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
  have hp'U : p' ∈ U := (Finset.mem_filter.mp hp').1
  exact common_classes_le_rpow hr hr4 hs hcls hJ₀ hnorm hDkt (hU hpU) (hP4 _ (hU hpU))
    (hP4 _ (hU hp'U))

/-- **Classes meet many cells.**  If the cell energy is at most `E` (and positive), then the
classes meet at least `(∑_j #(pins j ∩ U))² / E` cells in total. -/
theorem sum_cellsHit_ge {r s K E : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (hs : 0 ≤ s) (hE : 0 < E)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2} (hP4 : ∀ p ∈ P, ‖p‖ ≤ 4)
    (hDkt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ K * (ρ / r) ^ s)
    {U : Finset E2} (hU : U ⊆ P) (cell : E2 → ι)
    (henergy : ∑ c ∈ U.image cell, ∑ p ∈ U.filter (fun p => cell p = c),
        ∑ p' ∈ U.filter (fun p => cell p = c), 2 * K * (91 / max (dist p p') (40 * r)) ^ s ≤ E) :
    (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) ^ 2 / E ≤
      ∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ) := by
  classical
  have h1 := incidences_sq_le D cls J₀ U cell
  have h2 := cell_energy_le_rpow hr hr4 hs hcls hJ₀ hnorm hP4 hDkt hU cell
  have hH : 0 ≤ ∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [div_le_iff₀ hE]
  calc (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) ^ 2
      ≤ (∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ)) *
          ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 := h1
    _ ≤ (∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ)) * E :=
        mul_le_mul_of_nonneg_left (h2.trans henergy) hH

/-- **Cell energy for an arbitrary cap bound** `Bd` (monotone on `[r, ∞)`). -/
theorem cell_energy_le_capBound {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2} (hP4 : ∀ p ∈ P, ‖p‖ ≤ 4) (Bd : ℝ → ℝ)
    (hBd : ∀ ρ ρ', r ≤ ρ → ρ ≤ ρ' → Bd ρ ≤ Bd ρ')
    (hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ Bd ρ)
    {U : Finset E2} (hU : U ⊆ P) (cell : E2 → ι) :
    ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 ≤
      ∑ c ∈ U.image cell, ∑ p ∈ U.filter (fun p => cell p = c),
        ∑ p' ∈ U.filter (fun p => cell p = c), 2 * Bd (91 * r / max (dist p p') (40 * r)) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  rw [cell_energy_eq D cls J₀ U cell c]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro p' hp'
  have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
  have hp'U : p' ∈ U := (Finset.mem_filter.mp hp').1
  exact common_classes_le_capBound hr hr4 hcls hJ₀ hnorm Bd hBd hcap (hU hpU) (hP4 _ (hU hpU))
    (hP4 _ (hU hp'U))

/-- **Classes meet many cells**, for an arbitrary cap bound. -/
theorem sum_cellsHit_ge_capBound {r E : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (hE : 0 < E)
    {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ D, cls q ∈ J₀ ∧ (q = cls q ∨ ¬ StripSep r q (cls q) ∨ ¬ StripSep r (cls q) q))
    (hJ₀ : J₀ ⊆ D) (hnorm : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1)
    {P : Finset E2} (hP4 : ∀ p ∈ P, ‖p‖ ≤ 4) (Bd : ℝ → ℝ)
    (hBd : ∀ ρ ρ', r ≤ ρ → ρ ≤ ρ' → Bd ρ ≤ Bd ρ')
    (hcap : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ Bd ρ)
    {U : Finset E2} (hU : U ⊆ P) (cell : E2 → ι)
    (henergy : ∑ c ∈ U.image cell, ∑ p ∈ U.filter (fun p => cell p = c),
        ∑ p' ∈ U.filter (fun p => cell p = c), 2 * Bd (91 * r / max (dist p p') (40 * r)) ≤ E) :
    (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) ^ 2 / E ≤
      ∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ) := by
  classical
  have h1 := incidences_sq_le D cls J₀ U cell
  have h2 := cell_energy_le_capBound hr hr4 hcls hJ₀ hnorm hP4 Bd hBd hcap hU cell
  have hH : 0 ≤ ∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [div_le_iff₀ hE]
  calc (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) ^ 2
      ≤ (∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ)) *
          ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2 := h1
    _ ≤ (∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ)) * E :=
        mul_le_mul_of_nonneg_left (h2.trans henergy) hH

end Cells

/-- **Dyadic layer cake.**  If every point of `S` is within `d ≤ r₀ 2^(N+1)` of `p` and the
balls `B(p, r₀ 2^(k+1))` contain at most `M k` points of `S`, then
`∑_{q ∈ S} max (dist p q) r₀ ^ (-s) ≤ ∑_{k ≤ N} M k (r₀ 2^k) ^ (-s)`. -/
theorem layer_cake_rpow {r₀ s d : ℝ} (hr₀ : 0 < r₀) (hs : 0 ≤ s) (S : Finset E2) (p : E2)
    (N : ℕ) (hN : d ≤ r₀ * 2 ^ (N + 1)) (hSd : ∀ q ∈ S, dist p q ≤ d) (M : ℕ → ℝ)
    (hM : ∀ k : ℕ, ((S.filter (fun q => dist p q ≤ r₀ * 2 ^ (k + 1))).card : ℝ) ≤ M k) :
    ∑ q ∈ S, (max (dist p q) r₀) ^ (-s) ≤
      ∑ k ∈ Finset.range (N + 1), M k * (r₀ * 2 ^ k) ^ (-s) := by
  classical
  have hpt : ∀ q ∈ S, (max (dist p q) r₀) ^ (-s) ≤
      ∑ k ∈ Finset.range (N + 1),
        (if dist p q ≤ r₀ * 2 ^ (k + 1) then (r₀ * 2 ^ k) ^ (-s) else 0) := by
    intro q hq
    have hexq : ∃ k : ℕ, dist p q ≤ r₀ * 2 ^ (k + 1) := ⟨N, (hSd q hq).trans hN⟩
    set k₀ := Nat.find hexq with hk₀def
    have hk₀ : dist p q ≤ r₀ * 2 ^ (k₀ + 1) := Nat.find_spec hexq
    have hk₀N : k₀ ≤ N := Nat.find_min' hexq ((hSd q hq).trans hN)
    have hlow : r₀ * 2 ^ k₀ ≤ max (dist p q) r₀ := by
      by_cases h0 : k₀ = 0
      · rw [h0, pow_zero, mul_one]; exact le_max_right _ _
      · have hmin := Nat.find_min hexq (Nat.sub_lt (Nat.pos_of_ne_zero h0) one_pos)
        rw [← hk₀def] at hmin
        push Not at hmin
        have e : k₀ - 1 + 1 = k₀ := Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)
        rw [e] at hmin
        exact hmin.le.trans (le_max_left _ _)
    have hpos : 0 < r₀ * 2 ^ k₀ := by positivity
    have hterm : (max (dist p q) r₀) ^ (-s) ≤ (r₀ * 2 ^ k₀) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
    have hmem : k₀ ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk₀N)
    have hnonneg : ∀ k ∈ Finset.range (N + 1),
        0 ≤ (if dist p q ≤ r₀ * 2 ^ (k + 1) then (r₀ * 2 ^ k) ^ (-s) else 0) := by
      intro k _
      split_ifs
      · exact Real.rpow_nonneg (by positivity) _
      · exact le_refl 0
    calc (max (dist p q) r₀) ^ (-s) ≤ (r₀ * 2 ^ k₀) ^ (-s) := hterm
      _ = (if dist p q ≤ r₀ * 2 ^ (k₀ + 1) then (r₀ * 2 ^ k₀) ^ (-s) else 0) := by
          simp [hk₀]
      _ ≤ ∑ k ∈ Finset.range (N + 1),
            (if dist p q ≤ r₀ * 2 ^ (k + 1) then (r₀ * 2 ^ k) ^ (-s) else 0) :=
          Finset.single_le_sum hnonneg hmem
  calc ∑ q ∈ S, (max (dist p q) r₀) ^ (-s)
      ≤ ∑ q ∈ S, ∑ k ∈ Finset.range (N + 1),
          (if dist p q ≤ r₀ * 2 ^ (k + 1) then (r₀ * 2 ^ k) ^ (-s) else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ k ∈ Finset.range (N + 1),
          ((S.filter (fun q => dist p q ≤ r₀ * 2 ^ (k + 1))).card : ℝ) * (r₀ * 2 ^ k) ^ (-s) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.range (N + 1), M k * (r₀ * 2 ^ k) ^ (-s) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hM k) (Real.rpow_nonneg (by positivity) _)

/-- Geometric sum `∑_{k ≤ N} q ^ k ≤ q ^ (N+1) / (q - 1)` for `q > 1`. -/
theorem geom_sum_le_of_one_lt {q : ℝ} (hq : 1 < q) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), q ^ k ≤ q ^ (N + 1) / (q - 1) := by
  have hq1 : 0 < q - 1 := by linarith
  rw [geom_sum_eq hq.ne' (N + 1), div_le_div_iff_of_pos_right hq1]
  linarith

/-- **Relatively Frostman cells.**  If all points of `V` are within `d` of `p` and every ball
`B(p, ρ)`, `ρ ≥ r₀`, holds at most `A (ρ / Δ) ^ s' #V` of them, with `0 ≤ s < s'`, then
`∑_{q ∈ V} max (dist p q) r₀ ^ (-s) ≤ A #V 2^s' (4 d)^(s' - s) Δ^(-s') / (2^(s' - s) - 1)`. -/
theorem frostman_cell_sum {r₀ s s' A Δ d : ℝ} (hr₀ : 0 < r₀) (hs : 0 ≤ s) (hss' : s < s')
    (hΔ : 0 < Δ) (hd : r₀ ≤ d) (hA0 : 0 ≤ A) (V : Finset E2) (p : E2)
    (hVd : ∀ q ∈ V, dist p q ≤ d)
    (hA : ∀ ρ : ℝ, r₀ ≤ ρ → ((V.filter (fun q => dist p q ≤ ρ)).card : ℝ) ≤
      A * (ρ / Δ) ^ s' * V.card) :
    ∑ q ∈ V, (max (dist p q) r₀) ^ (-s) ≤
      A * V.card * 2 ^ s' * (4 * d) ^ (s' - s) * Δ ^ (-s') / (2 ^ (s' - s) - 1) := by
  classical
  have hex : ∃ N : ℕ, d ≤ r₀ * 2 ^ (N + 1) := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (d / r₀) (by norm_num : (1 : ℝ) < 2)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ hr₀] at hN
    have : (2 : ℝ) ^ N ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ N)
    nlinarith
  set N := Nat.find hex with hNdef
  have hN : d ≤ r₀ * 2 ^ (N + 1) := Nat.find_spec hex
  have hNtop : r₀ * 2 ^ (N + 1) ≤ 4 * d := by
    by_cases hN0 : N = 0
    · rw [hN0]; norm_num; linarith
    · have hmin := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)
      rw [← hNdef] at hmin
      push Not at hmin
      have e : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)
      rw [e] at hmin
      have : (2 : ℝ) ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
      rw [this]; nlinarith
  set q : ℝ := 2 ^ (s' - s) with hqdef
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by linarith)
  set M : ℕ → ℝ := fun k => A * ((r₀ * 2 ^ (k + 1)) / Δ) ^ s' * V.card with hMdef
  have hlc := layer_cake_rpow hr₀ hs V p N hN hVd M (fun k => by
    have hk : r₀ ≤ r₀ * 2 ^ (k + 1) := by
      have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    exact hA _ hk)
  refine hlc.trans ?_
  have hterm : ∀ k ∈ Finset.range (N + 1), M k * (r₀ * 2 ^ k) ^ (-s) =
      A * V.card * 2 ^ s' * Δ ^ (-s') * r₀ ^ (s' - s) * q ^ k := by
    intro k _
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have e1 : ((r₀ * 2 ^ (k + 1)) / Δ) ^ s' = r₀ ^ s' * 2 ^ s' * (2 ^ k : ℝ) ^ s' * Δ ^ (-s') := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hr₀.le (by positivity), pow_succ, Real.mul_rpow h2k.le (by norm_num),
        Real.inv_rpow hΔ.le, Real.rpow_neg hΔ.le]
      ring
    have e2 : (r₀ * 2 ^ k) ^ (-s) = r₀ ^ (-s) * (2 ^ k : ℝ) ^ (-s) :=
      Real.mul_rpow hr₀.le h2k.le
    have e3 : (2 ^ k : ℝ) ^ s' * (2 ^ k : ℝ) ^ (-s) = q ^ k := by
      rw [← Real.rpow_add h2k, hqdef, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    have e4 : r₀ ^ s' * r₀ ^ (-s) = r₀ ^ (s' - s) := by
      rw [← Real.rpow_add hr₀]; ring_nf
    simp only [hMdef]
    rw [e1, e2]
    calc A * (r₀ ^ s' * 2 ^ s' * (2 ^ k : ℝ) ^ s' * Δ ^ (-s')) * ↑V.card *
          (r₀ ^ (-s) * (2 ^ k : ℝ) ^ (-s))
        = A * V.card * 2 ^ s' * Δ ^ (-s') * (r₀ ^ s' * r₀ ^ (-s)) *
            ((2 ^ k : ℝ) ^ s' * (2 ^ k : ℝ) ^ (-s)) := by ring
      _ = A * V.card * 2 ^ s' * Δ ^ (-s') * r₀ ^ (s' - s) * q ^ k := by rw [e3, e4]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hC : 0 ≤ A * V.card * 2 ^ s' * Δ ^ (-s') * r₀ ^ (s' - s) := by positivity
  have hgeom := geom_sum_le_of_one_lt hq N
  have htop : r₀ ^ (s' - s) * q ^ (N + 1) ≤ (4 * d) ^ (s' - s) := by
    have e : r₀ ^ (s' - s) * q ^ (N + 1) = (r₀ * 2 ^ (N + 1)) ^ (s' - s) := by
      rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        Real.mul_rpow hr₀.le (by positivity), ← Real.rpow_natCast (2 : ℝ) (N + 1),
        ← Real.rpow_mul (by norm_num)]
      ring_nf
    rw [e]
    exact Real.rpow_le_rpow (by positivity) hNtop (by linarith)
  have hq1 : 0 < q - 1 := by linarith
  calc A * V.card * 2 ^ s' * Δ ^ (-s') * r₀ ^ (s' - s) * ∑ k ∈ Finset.range (N + 1), q ^ k
      ≤ A * V.card * 2 ^ s' * Δ ^ (-s') * r₀ ^ (s' - s) * (q ^ (N + 1) / (q - 1)) :=
        mul_le_mul_of_nonneg_left hgeom hC
    _ = A * V.card * 2 ^ s' * Δ ^ (-s') * (r₀ ^ (s' - s) * q ^ (N + 1)) / (q - 1) := by ring
    _ ≤ A * V.card * 2 ^ s' * Δ ^ (-s') * (4 * d) ^ (s' - s) / (q - 1) := by
        apply div_le_div_of_nonneg_right _ hq1.le
        exact mul_le_mul_of_nonneg_left htop (by positivity)
    _ = A * V.card * 2 ^ s' * (4 * d) ^ (s' - s) * Δ ^ (-s') / (2 ^ (s' - s) - 1) := by
        rw [hqdef]; ring

/-- **Energy of a relatively Frostman cell.**  If the pins `V` of a cell are pairwise within `d`
and relatively `s'`-Frostman around each of them at scales `ρ ≥ 40 r` (constant `A`, scale `Δ`),
with `0 ≤ s < s'`, then their common-class energy bound is at most
`2 K 91^s A #V² 2^s' (4 d)^(s'-s) Δ^(-s') / (2^(s'-s) - 1)`. -/
theorem frostman_cell_energy {r s s' K A Δ d : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (hss' : s < s')
    (hK : 0 ≤ K) (hΔ : 0 < Δ) (hd : 40 * r ≤ d) (hA0 : 0 ≤ A) (V : Finset E2)
    (hVd : ∀ p ∈ V, ∀ q ∈ V, dist p q ≤ d)
    (hA : ∀ p ∈ V, ∀ ρ : ℝ, 40 * r ≤ ρ → ((V.filter (fun q => dist p q ≤ ρ)).card : ℝ) ≤
      A * (ρ / Δ) ^ s' * V.card) :
    ∑ p ∈ V, ∑ p' ∈ V, 2 * K * (91 / max (dist p p') (40 * r)) ^ s ≤
      2 * K * 91 ^ s * (A * V.card * 2 ^ s' * (4 * d) ^ (s' - s) * Δ ^ (-s') /
        (2 ^ (s' - s) - 1)) * V.card := by
  classical
  have hr₀ : 0 < 40 * r := by positivity
  have hrow : ∀ p ∈ V, ∑ p' ∈ V, 2 * K * (91 / max (dist p p') (40 * r)) ^ s ≤
      2 * K * 91 ^ s * (A * V.card * 2 ^ s' * (4 * d) ^ (s' - s) * Δ ^ (-s') /
        (2 ^ (s' - s) - 1)) := by
    intro p hp
    have hsum := frostman_cell_sum hr₀ hs hss' hΔ hd hA0 V p (hVd p hp) (hA p hp)
    have hterm : ∀ p' ∈ V, 2 * K * (91 / max (dist p p') (40 * r)) ^ s =
        2 * K * 91 ^ s * (max (dist p p') (40 * r)) ^ (-s) := by
      intro p' _
      have hm : 0 < max (dist p p') (40 * r) := lt_of_lt_of_le hr₀ (le_max_right _ _)
      rw [Real.div_rpow (by norm_num) hm.le, Real.rpow_neg hm.le, div_eq_mul_inv]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  calc ∑ p ∈ V, ∑ p' ∈ V, 2 * K * (91 / max (dist p p') (40 * r)) ^ s
      ≤ ∑ _p ∈ V, 2 * K * 91 ^ s * (A * V.card * 2 ^ s' * (4 * d) ^ (s' - s) * Δ ^ (-s') /
          (2 ^ (s' - s) - 1)) := Finset.sum_le_sum hrow
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
