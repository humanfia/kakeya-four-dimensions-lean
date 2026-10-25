-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.AbstractCaseA.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.CaseASep

/-!
# Case A for an abstract pin relation

The column-energy route of `CaseA.lean` uses the class structure only through the pin sets of
the classes, their width, and a bound on the common classes of two pins. Here the pins are an
arbitrary `pinsF : E2 × E2 → Finset E2`, of width `ι` about their classes
(`|⟪x - j.1, j.2⟫| ≤ ι`), and the common classes of two pins are bounded by an arbitrary weight
`W p p'`. This lets any class family (for instance the tubes `J₁ a` of x0675's `HighConfig`, with
pins through `tb a ∘ cls`) be used directly, whatever its labels.

* `cellPinsA`, `cellsHitA`, `incidences_sq_leA`, `cell_energy_eqA`: Cauchy–Schwarz over
  (class, cell) pairs and the cell energy as pair counts (as in `Columns/CellEnergy`).
* `sum_tubeEnergy_leA`: the column energies of all tubes are at most
  `∑_{p ∈ U} ∑_{p' ∈ U, dist p p' ≤ 6 w + 4 ι} W p p'`.
* `exists_dense_column_tubeA`, `caseA_abstract`: as `exists_dense_column_tube`, `caseA_false_sep`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

open scoped BigOperators

section AbstractCells

variable {ι : Type*} [DecidableEq ι]

/-- The pins of the class `j` among `U` that lie in the cell `c`. -/
noncomputable def cellPinsA (pinsF : E2 × E2 → Finset E2) (U : Finset E2)
    (cell : E2 → ι) (j : E2 × E2) (c : ι) : Finset E2 :=
  (pinsF j ∩ U).filter (fun p => cell p = c)

/-- The cells containing pins of the class `j` among `U`. -/
noncomputable def cellsHitA (pinsF : E2 × E2 → Finset E2) (U : Finset E2)
    (cell : E2 → ι) (j : E2 × E2) : Finset ι :=
  (pinsF j ∩ U).image cell

theorem cellsHit_subsetA (pinsF : E2 × E2 → Finset E2) (U : Finset E2)
    (cell : E2 → ι) (j : E2 × E2) : cellsHitA pinsF U cell j ⊆ U.image cell := by
  classical
  intro c hc
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
  exact Finset.mem_image.mpr ⟨p, (Finset.mem_inter.mp hp).2, rfl⟩

/-- The pins of `j` in `U` are the union of their cell pieces. -/
theorem card_pins_eq_sum_cellPinsA (pinsF : E2 × E2 → Finset E2)
    (U : Finset E2) (cell : E2 → ι) (j : E2 × E2) :
    ((pinsF j ∩ U).card : ℝ) =
      ∑ c ∈ U.image cell, ((cellPinsA pinsF U cell j c).card : ℝ) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := cell) (s := pinsF j ∩ U)
    (t := U.image cell) (fun p hp => Finset.mem_image.mpr ⟨p, (Finset.mem_inter.mp hp).2, rfl⟩)
  rw [h]
  push_cast
  rfl

/-- A cell piece is empty outside the cells hit. -/
theorem cellPins_eq_empty_of_not_memA (pinsF : E2 × E2 → Finset E2)
    (U : Finset E2) (cell : E2 → ι) (j : E2 × E2) {c : ι}
    (hc : c ∉ cellsHitA pinsF U cell j) : cellPinsA pinsF U cell j c = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  exact hc (Finset.mem_image.mpr ⟨p, hp'.1, hp'.2⟩)

/-- For one class: the sum over all cells equals the sum over the cells hit. -/
theorem sum_cells_eq_sum_hitA (pinsF : E2 × E2 → Finset E2)
    (U : Finset E2) (cell : E2 → ι) (j : E2 × E2) (f : ℕ → ℝ) (hf : f 0 = 0) :
    ∑ c ∈ U.image cell, f (cellPinsA pinsF U cell j c).card =
      ∑ c ∈ cellsHitA pinsF U cell j, f (cellPinsA pinsF U cell j c).card := by
  classical
  symm
  apply Finset.sum_subset (cellsHit_subsetA pinsF U cell j)
  intro c _ hc
  rw [cellPins_eq_empty_of_not_memA pinsF U cell j hc, Finset.card_empty, hf]

/-- **Cauchy–Schwarz over (class, cell) pairs.** -/
theorem incidences_sq_leA (pinsF : E2 × E2 → Finset E2) (J₀ : Finset (E2 × E2))
    (U : Finset E2) (cell : E2 → ι) :
    (∑ j ∈ J₀, ((pinsF j ∩ U).card : ℝ)) ^ 2 ≤
      (∑ j ∈ J₀, ((cellsHitA pinsF U cell j).card : ℝ)) *
        ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPinsA pinsF U cell j c).card : ℝ) ^ 2 := by
  classical
  set S := J₀.sigma (fun j => cellsHitA pinsF U cell j) with hS
  set x : (Σ _ : E2 × E2, ι) → ℝ := fun jc => ((cellPinsA pinsF U cell jc.1 jc.2).card : ℝ) with hx
  have hsum : ∑ j ∈ J₀, ((pinsF j ∩ U).card : ℝ) = ∑ jc ∈ S, x jc := by
    rw [hS, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    rw [card_pins_eq_sum_cellPinsA pinsF U cell j]
    exact sum_cells_eq_sum_hitA pinsF U cell j (fun n => (n : ℝ)) (by simp)
  have hsq : ∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPinsA pinsF U cell j c).card : ℝ) ^ 2 =
      ∑ jc ∈ S, x jc ^ 2 := by
    rw [hS, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    exact sum_cells_eq_sum_hitA pinsF U cell j (fun n => (n : ℝ) ^ 2) (by simp)
  have hcard : (S.card : ℝ) = ∑ j ∈ J₀, ((cellsHitA pinsF U cell j).card : ℝ) := by
    rw [hS, Finset.card_sigma]
    push_cast
    rfl
  rw [hsum, hsq, ← hcard]
  exact sq_sum_le_card_mul_sum_sq

/-- Inside one cell, `∑_j #(cellPinsA j c)²` counts the common classes of pairs of pins. -/
theorem cell_energy_eqA (pinsF : E2 × E2 → Finset E2) (J₀ : Finset (E2 × E2))
    (U : Finset E2) (cell : E2 → ι) (c : ι) :
    ∑ j ∈ J₀, ((cellPinsA pinsF U cell j c).card : ℝ) ^ 2 =
      ∑ p ∈ U.filter (fun p => cell p = c), ∑ p' ∈ U.filter (fun p => cell p = c),
        ((J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j)).card : ℝ) := by
  classical
  set V := U.filter (fun p => cell p = c) with hV
  have hpiece : ∀ j, cellPinsA pinsF U cell j c = V.filter (fun p => p ∈ pinsF j) := by
    intro j
    ext p
    simp only [cellPinsA, hV, Finset.mem_filter, Finset.mem_inter]
    tauto
  have hsq : ∀ j ∈ J₀, ((cellPinsA pinsF U cell j c).card : ℝ) ^ 2 =
      ∑ p ∈ V, ∑ p' ∈ V,
        (if p ∈ pinsF j ∧ p' ∈ pinsF j then (1 : ℝ) else 0) := by
    intro j _
    rw [hpiece j, sq, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro p' _
    by_cases h1 : p ∈ pinsF j <;> by_cases h2 : p' ∈ pinsF j <;> simp [h1, h2]
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

end AbstractCells

/-- Two points within `ι` of one transverse line and in one column are `6 w + 4 ι`-close. -/
theorem dist_le_of_same_tubeCol' {v n p p' a : Plane} {w ι : ℝ} (hv : ‖v‖ = 1) (hw : 0 < w)
    (hn : ‖n‖ = 1) (hnv : 1 / 2 ≤ |inner ℝ n (perp v)|)
    (hp : |inner ℝ (p - a) n| ≤ ι) (hp' : |inner ℝ (p' - a) n| ≤ ι)
    (hcol : tubeCol v w p = tubeCol v w p') : dist p p' ≤ 6 * w + 4 * ι := by
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
  have h2 : |inner ℝ u n| ≤ 2 * ι := by
    have e : inner ℝ u n = inner ℝ (p - a) n - inner ℝ (p' - a) n := by
      rw [hu, ← inner_sub_left]; congr 1; abel
    rw [e]
    calc |inner ℝ (p - a) n - inner ℝ (p' - a) n|
        ≤ |inner ℝ (p - a) n| + |inner ℝ (p' - a) n| := abs_sub _ _
      _ ≤ ι + ι := add_le_add hp hp'
      _ = 2 * ι := by ring
  have hframe := inner_frame hv u n
  have hnv1 : |inner ℝ n v| ≤ 1 := by
    have := abs_real_inner_le_norm n v
    rw [hn, hv] at this; linarith
  have h3 : |inner ℝ u (perp v)| * |inner ℝ n (perp v)| ≤ 2 * ι + 2 * w := by
    rw [← abs_mul]
    have e : inner ℝ u (perp v) * inner ℝ n (perp v) = inner ℝ u n - inner ℝ u v * inner ℝ n v := by
      linarith [hframe]
    rw [e]
    calc |inner ℝ u n - inner ℝ u v * inner ℝ n v|
        ≤ |inner ℝ u n| + |inner ℝ u v * inner ℝ n v| := abs_sub _ _
      _ ≤ 2 * ι + 2 * w := by
          rw [abs_mul]
          have := mul_le_mul h1 hnv1 (abs_nonneg _) (by linarith)
          linarith
  have h4 : |inner ℝ u (perp v)| ≤ 4 * ι + 4 * w := by
    have ha := abs_nonneg (inner ℝ u (perp v))
    nlinarith
  have hle : ‖u‖ ≤ |inner ℝ u (perp v)| + |inner ℝ u v| := by
    have hsq : ‖u‖ ^ 2 = inner ℝ u (perp v) ^ 2 + inner ℝ u v ^ 2 := by
      have := inner_frame hv u u
      rw [real_inner_self_eq_norm_sq] at this
      linarith
    have ha := abs_nonneg (inner ℝ u (perp v))
    have hb := abs_nonneg (inner ℝ u v)
    have hsa := sq_abs (inner ℝ u (perp v))
    have hsb := sq_abs (inner ℝ u v)
    nlinarith [norm_nonneg u]
  rw [dist_eq_norm]
  linarith

section AbstractEnergy

variable {τ : Type*} [DecidableEq τ]

/-- The column energy of classes `J` with pins `Ut`, columns along `v` of width `w`. -/
noncomputable def tubeEnergyA (pinsF : E2 × E2 → Finset E2)
    (J : Finset (E2 × E2)) (Ut : Finset E2) (v : Plane) (w : ℝ) : ℝ :=
  ∑ j ∈ J, ∑ c ∈ Ut.image (tubeCol v w), ((cellPinsA pinsF Ut (tubeCol v w) j c).card : ℝ) ^ 2

theorem tubeEnergy_eqA (pinsF : E2 × E2 → Finset E2)
    (J : Finset (E2 × E2)) (Ut : Finset E2) (v : Plane) (w : ℝ) :
    tubeEnergyA pinsF J Ut v w =
      ∑ p ∈ Ut, ∑ p' ∈ Ut.filter (fun p' => tubeCol v w p' = tubeCol v w p),
        ((J.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j)).card : ℝ) := by
  unfold tubeEnergyA
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun c _ => cell_energy_eqA pinsF J Ut (tubeCol v w) c)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := tubeCol v w) (s := Ut)
    (t := Ut.image (tubeCol v w)) (fun p hp => Finset.mem_image_of_mem _ hp)]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro p hp
  have hpc := (Finset.mem_filter.mp hp).2
  rw [hpc]

theorem incid_le_tubeEnergyA (pinsF : E2 × E2 → Finset E2)
    (J : Finset (E2 × E2)) (Ut : Finset E2) (v : Plane) (w : ℝ) :
    ∑ j ∈ J, ((pinsF j ∩ Ut).card : ℝ) ≤ tubeEnergyA pinsF J Ut v w := by
  unfold tubeEnergyA
  apply Finset.sum_le_sum
  intro j _
  rw [card_pins_eq_sum_cellPinsA pinsF Ut (tubeCol v w) j]
  apply Finset.sum_le_sum
  intro c _
  have h : (cellPinsA pinsF Ut (tubeCol v w) j c).card ≤
      (cellPinsA pinsF Ut (tubeCol v w) j c).card ^ 2 := Nat.le_self_pow (by norm_num) _
  exact_mod_cast h

/-- **The column energies of all tubes are at most the `W`-ball energy.** -/
theorem sum_tubeEnergy_leA {ι w : ℝ} (hw : 0 < w) (pinsF : E2 × E2 → Finset E2)
    (J₀ : Finset (E2 × E2)) (hJ : ∀ j ∈ J₀, ‖j.2‖ = 1)
    (hwidth : ∀ j ∈ J₀, ∀ x ∈ pinsF j, |inner ℝ (x - j.1) j.2| ≤ ι)
    (U : Finset E2) (W : E2 → E2 → ℝ)
    (hW : ∀ p ∈ U, ∀ p' ∈ U,
      ((J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j)).card : ℝ) ≤ W p p')
    (T : Finset τ) (tube : E2 × E2 → τ) (v : τ → Plane) (Ut : τ → Finset E2)
    (hv : ∀ t ∈ T, ‖v t‖ = 1)
    (htrans : ∀ t ∈ T, ∀ j ∈ J₀.filter (fun j => tube j = t),
      1 / 2 ≤ |inner ℝ j.2 (perp (v t))|)
    (hUt : ∀ t ∈ T, Ut t ⊆ U) :
    ∑ t ∈ T, tubeEnergyA pinsF (J₀.filter (fun j => tube j = t)) (Ut t) (v t) w ≤
      ∑ p ∈ U, ∑ p' ∈ U.filter (fun p' => dist p p' ≤ 6 * w + 4 * ι), W p p' := by
  classical
  set w' := 6 * w + 4 * ι with hw'
  have hA : ∀ t ∈ T, tubeEnergyA pinsF (J₀.filter (fun j => tube j = t)) (Ut t) (v t) w ≤
      ∑ p ∈ U, ∑ p' ∈ U, (((J₀.filter (fun j => tube j = t)).filter
        (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w')).card : ℝ) := by
    intro t ht
    rw [tubeEnergy_eqA]
    calc _ ≤ ∑ p ∈ Ut t, ∑ p' ∈ (Ut t).filter
            (fun p' => tubeCol (v t) w p' = tubeCol (v t) w p),
            (((J₀.filter (fun j => tube j = t)).filter
              (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w')).card : ℝ) := by
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
          exact dist_le_of_same_tubeCol' (hv t ht) hw (hJ j hjJ) (htrans t ht j hjt)
            (hwidth j hjJ p hpj) (hwidth j hjJ p' hp'j) hcol.symm
      _ ≤ ∑ p ∈ Ut t, ∑ p' ∈ U, (((J₀.filter (fun j => tube j = t)).filter
              (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w')).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p _
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact (Finset.filter_subset _ _).trans (hUt t ht)
          · intro _ _ _; exact Nat.cast_nonneg _
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (hUt t ht)
          intro _ _ _
          exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hB : ∀ p p' : E2, ∑ t ∈ T, (((J₀.filter (fun j => tube j = t)).filter
      (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w')).card : ℝ) ≤
      ((J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w')).card : ℝ) := by
    intro p p'
    set S := (J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧
      dist p p' ≤ w')).filter (fun j => tube j ∈ T) with hS
    have hfib := Finset.card_eq_sum_card_fiberwise (f := tube) (s := S) (t := T)
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have hSle : S.card ≤ (J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧
        dist p p' ≤ w')).card := Finset.card_le_card (Finset.filter_subset _ _)
    have heq : ∀ t ∈ T, S.filter (fun j => tube j = t) = (J₀.filter (fun j => tube j = t)).filter
        (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w') := by
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
  have hC : ∀ p ∈ U, ∀ p' ∈ U, ((J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧
      dist p p' ≤ w')).card : ℝ) ≤ if dist p p' ≤ w' then W p p' else 0 := by
    intro p hp p' hp'
    split_ifs with hd
    · have hsub : J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w') ⊆
          J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j) := by
        intro j hj
        obtain ⟨hjJ, h1, h2, _⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hjJ, h1, h2⟩
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hW p hp p' hp')
    · have : J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w') = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j _ h
        exact hd h.2.2
      rw [this]; simp
  calc ∑ t ∈ T, tubeEnergyA pinsF (J₀.filter (fun j => tube j = t)) (Ut t) (v t) w
      ≤ ∑ t ∈ T, ∑ p ∈ U, ∑ p' ∈ U, (((J₀.filter (fun j => tube j = t)).filter
        (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w')).card : ℝ) :=
        Finset.sum_le_sum hA
    _ = ∑ p ∈ U, ∑ p' ∈ U, ∑ t ∈ T, (((J₀.filter (fun j => tube j = t)).filter
        (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j ∧ dist p p' ≤ w')).card : ℝ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ U, ∑ p' ∈ U, (if dist p p' ≤ w' then W p p' else 0) := by
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
theorem card_col_pairs_eqA (pinsF : E2 × E2 → Finset E2)
    (J : Finset (E2 × E2)) (Ut : Finset E2) (v : Plane) (w : ℝ) :
    ((((Ut.image (tubeCol v w)) ×ˢ J).filter
      (fun p : ℝ × (E2 × E2) => ∃ x ∈ Ut, x ∈ pinsF p.2 ∧ tubeCol v w x = p.1)).card : ℝ) =
    ∑ j ∈ J, ((cellsHitA pinsF Ut (tubeCol v w) j).card : ℝ) := by
  classical
  have hset : ∀ j, cellsHitA pinsF Ut (tubeCol v w) j = (Ut.image (tubeCol v w)).filter
      (fun c => ∃ x ∈ Ut, x ∈ pinsF j ∧ tubeCol v w x = c) := by
    intro j
    ext c
    simp only [cellsHitA, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
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
theorem exists_dense_column_tubeA {ι w I E X : ℝ} (hw : 0 < w)
    (hI : 0 < I) (hE : 0 < E) (hX : 0 < X)
    (pinsF : E2 × E2 → Finset E2) (J₀ : Finset (E2 × E2)) (hJ : ∀ j ∈ J₀, ‖j.2‖ = 1)
    (hwidth : ∀ j ∈ J₀, ∀ x ∈ pinsF j, |inner ℝ (x - j.1) j.2| ≤ ι)
    (U : Finset E2) (W : E2 → E2 → ℝ)
    (hW : ∀ p ∈ U, ∀ p' ∈ U,
      ((J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j)).card : ℝ) ≤ W p p')
    (T : Finset τ) (tube : E2 × E2 → τ) (v : τ → Plane) (Ut : τ → Finset E2)
    (hv : ∀ t ∈ T, ‖v t‖ = 1)
    (htrans : ∀ t ∈ T, ∀ j ∈ J₀.filter (fun j => tube j = t),
      1 / 2 ≤ |inner ℝ j.2 (perp (v t))|)
    (hUt : ∀ t ∈ T, Ut t ⊆ U)
    (hIsum : I ≤ ∑ t ∈ T, ∑ j ∈ J₀.filter (fun j => tube j = t),
      ((pinsF j ∩ Ut t).card : ℝ))
    (hEsum : ∑ p ∈ U, ∑ p' ∈ U.filter (fun p' => dist p p' ≤ 6 * w + 4 * ι), W p p' ≤ E)
    (hXsum : ∑ t ∈ T, (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
      ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤ X) :
    ∃ t ∈ T, (J₀.filter (fun j => tube j = t)).Nonempty ∧ (Ut t).Nonempty ∧
      I ^ 2 / (E * X) * (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
        ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤
      (((((Ut t).image (tubeCol (v t) w)) ×ˢ (J₀.filter (fun j => tube j = t))).filter
        (fun p : ℝ × (E2 × E2) => ∃ x ∈ Ut t, x ∈ pinsF p.2 ∧
          tubeCol (v t) w x = p.1)).card : ℝ) := by
  classical
  set Ic : τ → ℝ := fun t => ∑ j ∈ J₀.filter (fun j => tube j = t),
    ((pinsF j ∩ Ut t).card : ℝ) with hIc
  set En : τ → ℝ := fun t => tubeEnergyA pinsF (J₀.filter (fun j => tube j = t)) (Ut t) (v t) w
    with hEn
  set Sz : τ → ℝ := fun t => (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
    ((J₀.filter (fun j => tube j = t)).card : ℝ) with hSz
  set T' := T.filter (fun t => 0 < Ic t) with hT'
  have hIc0 : ∀ t, 0 ≤ Ic t := fun t => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hEnIc : ∀ t, Ic t ≤ En t := fun t => incid_le_tubeEnergyA _ _ _ _ _
  have hEn0 : ∀ t, 0 ≤ En t := fun t => (hIc0 t).trans (hEnIc t)
  have hT'T : T' ⊆ T := Finset.filter_subset _ _
  have hIsum' : I ≤ ∑ t ∈ T', Ic t := by
    rw [hT', Finset.sum_filter_of_ne]
    · exact hIsum
    · intro t _ hne
      exact lt_of_le_of_ne (hIc0 t) (Ne.symm hne)
  have hEsum' : ∑ t ∈ T', En t ≤ E := by
    refine le_trans ?_ ((sum_tubeEnergy_leA hw pinsF J₀ hJ hwidth U W hW T tube v Ut
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
  · have hCS := incidences_sq_leA pinsF (J₀.filter (fun j => tube j = t)) (Ut t) (tubeCol (v t) w)
    have hCS' : Ic t ^ 2 ≤ (∑ j ∈ J₀.filter (fun j => tube j = t),
        ((cellsHitA pinsF (Ut t) (tubeCol (v t) w) j).card : ℝ)) * En t := hCS
    have hdiv : Ic t ^ 2 / En t ≤ ∑ j ∈ J₀.filter (fun j => tube j = t),
        ((cellsHitA pinsF (Ut t) (tubeCol (v t) w) j).card : ℝ) := by
      rw [div_le_iff₀ hEnt]; exact hCS'
    rw [card_col_pairs_eqA]
    calc I ^ 2 / (E * X) * (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
          ((J₀.filter (fun j => tube j = t)).card : ℝ) = I ^ 2 / (E * X) * Sz t := by
          simp only [hSz]; ring
      _ ≤ Ic t ^ 2 / En t := hratio
      _ ≤ _ := hdiv


/-- **Case A for an abstract pin relation.** Classes `J₀` (unit normals, `‖j.1‖ ≤ 4`, pairwise
`StripSep rs`), pins `pinsF j` within `ι ≤ K₀ rs` of their class, common classes of two pins at
most `W p p'`; tubes, columns and per-tube data as in `caseA_false`. -/
theorem caseA_abstract {τ : Type*} [DecidableEq τ] {e b β : ℝ} (he : 0 < e) (hb : 0 < b)
    (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (ι rs Δs w K₀ A I E X : ℝ) (J₀ : Finset (E2 × E2)) (pinsF : E2 × E2 → Finset E2)
      (U : Finset E2) (W : E2 → E2 → ℝ) (T : Finset τ) (tube : E2 × E2 → τ) (v : τ → Plane)
      (cT aT M : τ → ℝ) (Ut : τ → Finset E2),
    0 < ι → 0 < rs → ι ≤ K₀ * rs → 0 < Δs → 0 < w → 1 ≤ K₀ → 0 ≤ A → 4 * Δs * w ≤ 2 * ι →
    tubeTol ι Δs w ≤ δ₀ →
    K₀ ≤ (tubeTol ι Δs w) ^ (-η) → A ≤ (tubeTol ι Δs w) ^ (-η) →
    0 < I → 0 < E → 0 < X → (tubeTol ι Δs w) ^ η ≤ I ^ 2 / (E * X) →
    (∀ j ∈ J₀, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4) →
    (∀ j ∈ J₀, ∀ j' ∈ J₀, j ≠ j' → StripSep rs j j') →
    (∀ j ∈ J₀, ∀ x ∈ pinsF j, |inner ℝ (x - j.1) j.2| ≤ ι) →
    (∀ x ∈ U, ‖x‖ ≤ 4) →
    (∀ p ∈ U, ∀ p' ∈ U,
      ((J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j)).card : ℝ) ≤ W p p') →
    I ≤ ∑ t ∈ T, ∑ j ∈ J₀.filter (fun j => tube j = t), ((pinsF j ∩ Ut t).card : ℝ) →
    ∑ p ∈ U, ∑ p' ∈ U.filter (fun p' => dist p p' ≤ 6 * w + 4 * ι), W p p' ≤ E →
    ∑ t ∈ T, (((Ut t).image (tubeCol (v t) w)).card : ℝ) *
      ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤ X →
    (∀ t ∈ T, ‖v t‖ = 1 ∧ Ut t ⊆ U ∧ 0 < M t ∧
      8 * ((J₀.filter (fun j => tube j = t)).card : ℝ) / M t ≤
        (tubeTol ι Δs w) ^ (-(1 - e)) ∧
      64 * ((J₀.filter (fun j => tube j = t)).card : ℝ) ≤ K₀ * M t ^ 2 ∧
      (∀ j ∈ J₀.filter (fun j => tube j = t),
        1 / 2 ≤ |inner ℝ j.2 (perp (v t))| ∧ |(lineChart (v t) j).1| ≤ Δs) ∧
      (∀ x ∈ Ut t, M t ≤ (((J₀.filter (fun j => tube j = t)).filter
        (fun j => x ∈ pinsF j)).card : ℝ)) ∧
      (∀ j ∈ J₀.filter (fun j => tube j = t), ∀ y ∈ (Ut t).image (tubeCol (v t) w),
        |lineHeight (tubeLine (v t) (cT t) (aT t) (4 * Δs) j) y| ≤ 7 / 2) ∧
      (∀ j ∈ J₀.filter (fun j => tube j = t), ∀ z ρ : ℝ, tubeTol ι Δs w ≤ ρ →
        ((((Ut t).image (tubeCol (v t) w)).filter (fun y =>
          (∃ x ∈ Ut t, x ∈ pinsF j ∧ tubeCol (v t) w x = y) ∧ |y - z| ≤ ρ)).card : ℝ) ≤
        A * ρ ^ β * ((((Ut t).image (tubeCol (v t) w)).filter (fun y =>
          ∃ x ∈ Ut t, x ∈ pinsF j ∧ tubeCol (v t) w x = y)).card : ℝ)) ∧
      (∀ c a ρ : ℝ, tubeTol ι Δs w ≤ ρ →
        (((J₀.filter (fun j => tube j = t)).filter (fun j =>
          |(tubeLine (v t) (cT t) (aT t) (4 * Δs) j).1 - c| ≤ ρ ∧
          |(tubeLine (v t) (cT t) (aT t) (4 * Δs) j).2 - a| ≤ ρ)).card : ℝ) ≤
        K₀ * ρ ^ (1 + b) * ((J₀.filter (fun j => tube j = t)).card : ℝ))) →
    False := by
  obtain ⟨η, δ₀, hη, hδ₀, hδ₀2, hmain⟩ := tube_two_ends_false he hb hβ
  refine ⟨η, δ₀, hη, hδ₀, hδ₀2, ?_⟩
  intro ι rs Δs w K₀ A I E X J₀ pinsF U W T tube v cT aT M Ut hι hrs hιK hΔs hw hK₀ hA0 hwι hδ
    hK₀δ hAδ hI hE hX hdδ hJn hsep hwidth hU4 hW hIsum hEsum hXsum htube
  obtain ⟨t, ht, hJne, hUne, hdens⟩ := exists_dense_column_tubeA hw hI hE hX pinsF J₀
    (fun j hj => (hJn j hj).1) hwidth U W hW T tube v Ut (fun t ht => (htube t ht).1)
    (fun t ht j hj => ((htube t ht).2.2.2.2.2.1 j hj).1) (fun t ht => (htube t ht).2.1)
    hIsum hEsum hXsum
  obtain ⟨hvt, hUtU, hMt, hF, hquad, hJnorm, hdeg, hheight, htwo, hline⟩ := htube t ht
  have hδpos : 0 < tubeTol ι Δs w := tubeTol_pos hι hΔs hw
  have hδ1 : (tubeTol ι Δs w) ^ η ≤ 1 :=
    Real.rpow_le_one hδpos.le (by linarith) hη.le
  set d := min (I ^ 2 / (E * X)) 1 with hd
  have hdle : d ≤ I ^ 2 / (E * X) := min_le_left _ _
  apply hmain (v t) (cT t) (aT t) rs ι Δs w (M t) d K₀ A hvt hrs hι hΔs hw hMt
    hK₀ hA0 hwι hιK hδ hK₀δ hAδ (le_min hdδ hδ1) (min_le_right _ _)
    (J₀.filter (fun j => tube j = t)) (Ut t) (fun j x => x ∈ pinsF j) hJne hUne hF
  · intro j hj
    have hjJ := (Finset.mem_filter.mp hj).1
    exact ⟨(hJn j hjJ).1, (hJn j hjJ).2, (hJnorm j hj).1, (hJnorm j hj).2⟩
  · intro j hj j' hj' hne
    exact hsep j (Finset.mem_filter.mp hj).1 j' (Finset.mem_filter.mp hj').1 hne
  · intro j hj x _ hx
    exact hwidth j (Finset.mem_filter.mp hj).1 x hx
  · intro x hx
    exact hU4 x (hUtU hx)
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

/-- **Case A for an abstract pin relation, with coarse tubes** in `tube_geo` form at scale `Δ`
(axis `perp t.2`, centre `(0, (lineChart (perp t.2) t).2)`, `Δs = 4 Δ`): the geometric per-tube
hypotheses are automatic. -/
theorem caseA_coarse_abstract {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (ι rs Δ w K₀ A I E X : ℝ) (J₀ : Finset (E2 × E2)) (pinsF : E2 × E2 → Finset E2)
      (U : Finset E2) (W : E2 → E2 → ℝ) (JΔ : Finset (E2 × E2)) (clsΔ : E2 × E2 → E2 × E2)
      (M : E2 × E2 → ℝ) (Ut : E2 × E2 → Finset E2),
    0 < ι → 0 < rs → ι ≤ K₀ * rs → 0 < Δ → Δ ≤ 1 → 0 < w → 1 ≤ K₀ → 0 ≤ A →
    16 * Δ * w ≤ 2 * ι → tubeTol ι (4 * Δ) w ≤ δ₀ →
    K₀ ≤ (tubeTol ι (4 * Δ) w) ^ (-η) → A ≤ (tubeTol ι (4 * Δ) w) ^ (-η) →
    0 < I → 0 < E → 0 < X → (tubeTol ι (4 * Δ) w) ^ η ≤ I ^ 2 / (E * X) →
    (∀ j ∈ J₀, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4) →
    (∀ j ∈ J₀, ∀ j' ∈ J₀, j ≠ j' → StripSep rs j j') →
    (∀ j ∈ J₀, ∀ x ∈ pinsF j, |inner ℝ (x - j.1) j.2| ≤ ι) →
    (∀ x ∈ U, ‖x‖ ≤ 4) →
    (∀ p ∈ U, ∀ p' ∈ U,
      ((J₀.filter (fun j => p ∈ pinsF j ∧ p' ∈ pinsF j)).card : ℝ) ≤ W p p') →
    (∀ j ∈ J₀, clsΔ j ∈ JΔ ∧ |inner ℝ (j.1 - (clsΔ j).1) (clsΔ j).2| < 9 * Δ ∧
      (dist j.2 (clsΔ j).2 < Δ ∨ dist j.2 (-(clsΔ j).2) < Δ)) →
    (∀ c ∈ JΔ, ‖c.1‖ ≤ 4 ∧ ‖c.2‖ = 1) →
    I ≤ ∑ t ∈ JΔ, ∑ j ∈ J₀.filter (fun j => clsΔ j = t), ((pinsF j ∩ Ut t).card : ℝ) →
    ∑ p ∈ U, ∑ p' ∈ U.filter (fun p' => dist p p' ≤ 6 * w + 4 * ι), W p p' ≤ E →
    ∑ t ∈ JΔ, (((Ut t).image (tubeCol (perp t.2) w)).card : ℝ) *
      ((J₀.filter (fun j => clsΔ j = t)).card : ℝ) ≤ X →
    (∀ t ∈ JΔ, Ut t ⊆ U ∧ 0 < M t ∧
      8 * ((J₀.filter (fun j => clsΔ j = t)).card : ℝ) / M t ≤
        (tubeTol ι (4 * Δ) w) ^ (-(1 - e)) ∧
      64 * ((J₀.filter (fun j => clsΔ j = t)).card : ℝ) ≤ K₀ * M t ^ 2 ∧
      (∀ x ∈ Ut t, M t ≤ (((J₀.filter (fun j => clsΔ j = t)).filter
        (fun j => x ∈ pinsF j)).card : ℝ)) ∧
      (∀ j ∈ J₀.filter (fun j => clsΔ j = t), ∀ z ρ : ℝ, tubeTol ι (4 * Δ) w ≤ ρ →
        ((((Ut t).image (tubeCol (perp t.2) w)).filter (fun y =>
          (∃ x ∈ Ut t, x ∈ pinsF j ∧ tubeCol (perp t.2) w x = y) ∧
            |y - z| ≤ ρ)).card : ℝ) ≤
        A * ρ ^ β * ((((Ut t).image (tubeCol (perp t.2) w)).filter (fun y =>
          ∃ x ∈ Ut t, x ∈ pinsF j ∧ tubeCol (perp t.2) w x = y)).card : ℝ)) ∧
      (∀ c a ρ : ℝ, tubeTol ι (4 * Δ) w ≤ ρ →
        (((J₀.filter (fun j => clsΔ j = t)).filter (fun j =>
          |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (4 * (4 * Δ)) j).1 - c| ≤ ρ ∧
          |(tubeLine (perp t.2) 0 (lineChart (perp t.2) t).2 (4 * (4 * Δ)) j).2 - a| ≤ ρ)).card :
            ℝ) ≤
        K₀ * ρ ^ (1 + b) * ((J₀.filter (fun j => clsΔ j = t)).card : ℝ))) →
    False := by
  obtain ⟨η, δ₀, hη, hδ₀, hδ₀2, hmain⟩ := caseA_abstract (τ := E2 × E2) he hb hβ
  refine ⟨η, δ₀, hη, hδ₀, hδ₀2, ?_⟩
  intro ι rs Δ w K₀ A I E X J₀ pinsF U W JΔ clsΔ M Ut hι hrs hιK hΔ hΔ1 hw hK₀ hA0 hwι hδ
    hK₀δ hAδ hI hE hX hdδ hJn hsep hwidth hU4 hW hclsΔ hJΔ hIsum hEsum hXsum htube
  refine hmain ι rs (4 * Δ) w K₀ A I E X J₀ pinsF U W JΔ clsΔ (fun t => perp t.2) (fun _ => 0)
    (fun t => (lineChart (perp t.2) t).2) M Ut hι hrs hιK (by positivity) hw hK₀ hA0
    (by linarith) hδ hK₀δ hAδ hI hE hX hdδ hJn hsep hwidth hU4 hW hIsum hEsum hXsum ?_
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
    have hc := (hclsΔ j hjJ).2
    rw [hjt] at hc
    exact coarse_class_tube_geom hΔ hΔ1 ht2 ht1 (hJn j hjJ).1 (hJn j hjJ).2 hc.1 hc.2
  refine ⟨hvt, hUt, hM, hF, hquad, fun j hj => ⟨(hgeom j hj).1, (hgeom j hj).2.1⟩, hdeg, ?_,
    htwo, hline⟩
  intro j hj y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact (hgeom j hj).2.2 _ (abs_tubeCol_le hvt hw (hU4 x (hUt hx)))

end AbstractEnergy

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/AbstractCaseA.lean
