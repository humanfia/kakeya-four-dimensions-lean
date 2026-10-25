-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.DenseTube.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.CellEnergy

/-!
# A coarse tube whose classes meet a dense set of its cells

Group the classes `J₀` into coarse tubes by a map `tube : E2 × E2 → τ`.  The cells of a coarse
tube `t` are the cells met by the pins (in `U`) of its classes, `tubeCells t`.  Every class meets
only cells of its tube (`cellsHit_subset_tubeCells`).

`exists_dense_tube`: if the classes meet at least `L > 0` cells in total (for instance from
`sum_cellsHit_ge`) while `∑_j #tubeCells (tube j) ≤ U`, then some coarse tube `t` (holding a class)
has class/cell density at least `L / U`:

  `(L / U) · ∑_{j ∈ J₀, tube j = t} #tubeCells t ≤ ∑_{j ∈ J₀, tube j = t} #cellsHit j`.

This is the input of x0603's `dense_endpoint_family` (Multiscale/EndpointSelection.lean), applied
to the relation "class `j` of `t` meets cell `c` of `t`".
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open scoped BigOperators

section DenseTube

variable {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]

/-- The cells met by the classes of the coarse tube `t`. -/
noncomputable def tubeCells (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ) (t : τ) : Finset ι :=
  (J₀.filter (fun j => tube j = t)).biUnion (fun j => cellsHit D cls U cell j)

theorem cellsHit_subset_tubeCells (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (U : Finset E2) (cell : E2 → ι) (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ)
    {j : E2 × E2} (hj : j ∈ J₀) :
    cellsHit D cls U cell j ⊆ tubeCells D cls U cell J₀ tube (tube j) := by
  classical
  intro c hc
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩, hc⟩

/-- Summing over classes is summing over tubes of the sums over their classes. -/
theorem sum_classes_eq_sum_tubes (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ) (f : E2 × E2 → ℝ) :
    ∑ j ∈ J₀, f j = ∑ t ∈ J₀.image tube, ∑ j ∈ J₀.filter (fun j => tube j = t), f j := by
  classical
  rw [Finset.sum_image']
  intro _j _hj
  rfl

/-- **A dense coarse tube.**  If the classes meet at least `L > 0` cells in total while
`∑_j #tubeCells (tube j) ≤ U`, then some coarse tube holding a class has class/cell density at
least `L / U`. -/
theorem exists_dense_tube (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ) {L Ub : ℝ} (hL : 0 < L)
    (hlow : L ≤ ∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ))
    (hup : ∑ j ∈ J₀, ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ) ≤ Ub) :
    ∃ t ∈ J₀.image tube,
      (L / Ub) * ∑ j ∈ J₀.filter (fun j => tube j = t),
          ((tubeCells D cls U cell J₀ tube t).card : ℝ) ≤
        ∑ j ∈ J₀.filter (fun j => tube j = t), ((cellsHit D cls U cell j).card : ℝ) := by
  classical
  have hUpos : 0 < Ub := by
    have h0 : 0 ≤ ∑ j ∈ J₀, ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    by_contra hU
    push Not at hU
    have hle : ∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ) ≤
        ∑ j ∈ J₀, ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact_mod_cast Finset.card_le_card (cellsHit_subset_tubeCells D cls U cell J₀ tube hj)
    linarith
  by_contra hno
  push Not at hno
  -- every tube is sparse, so the total is below `L`
  have hsum : ∑ j ∈ J₀, ((cellsHit D cls U cell j).card : ℝ) <
      (L / Ub) * ∑ j ∈ J₀, ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ) := by
    rw [sum_classes_eq_sum_tubes J₀ tube (fun j => ((cellsHit D cls U cell j).card : ℝ)),
      sum_classes_eq_sum_tubes J₀ tube
        (fun j => ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ)), Finset.mul_sum]
    have hne : (J₀.image tube).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty, Finset.image_eq_empty] at he
      rw [he, Finset.sum_empty] at hlow
      linarith
    apply Finset.sum_lt_sum_of_nonempty hne
    intro t ht
    have hrw : ∑ j ∈ J₀.filter (fun j => tube j = t),
        ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ) =
        ∑ j ∈ J₀.filter (fun j => tube j = t), ((tubeCells D cls U cell J₀ tube t).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    rw [hrw]
    exact hno t ht
  have hfinal : (L / Ub) * ∑ j ∈ J₀, ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ) ≤ L := by
    calc (L / Ub) * ∑ j ∈ J₀, ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ)
        ≤ (L / Ub) * Ub := mul_le_mul_of_nonneg_left hup (div_nonneg hL.le hUpos.le)
      _ = L := by field_simp
  linarith

end DenseTube

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open scoped BigOperators

section CoarseSide

variable {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]

/-- **Coarse side.**  If every coarse tube holds at most `Nmax` classes and every cell of `U`
lies in the cells of at most `B` coarse tubes, then
`∑_j #tubeCells (tube j) ≤ Nmax · B · #cells`. -/
theorem sum_tubeCells_le (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ) {Nmax B : ℝ} (hNmax : 0 ≤ Nmax)
    (hN : ∀ t ∈ J₀.image tube, (((J₀.filter (fun j => tube j = t)).card : ℕ) : ℝ) ≤ Nmax)
    (hB : ∀ c ∈ U.image cell,
      (((J₀.image tube).filter (fun t => c ∈ tubeCells D cls U cell J₀ tube t)).card : ℝ) ≤ B) :
    ∑ j ∈ J₀, ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ) ≤
      Nmax * (B * ((U.image cell).card : ℝ)) := by
  classical
  -- group by tubes
  rw [sum_classes_eq_sum_tubes J₀ tube
    (fun j => ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ))]
  have hgroup : ∀ t ∈ J₀.image tube, ∑ j ∈ J₀.filter (fun j => tube j = t),
      ((tubeCells D cls U cell J₀ tube (tube j)).card : ℝ) =
      ((J₀.filter (fun j => tube j = t)).card : ℝ) *
        ((tubeCells D cls U cell J₀ tube t).card : ℝ) := by
    intro t _
    rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hgroup]
  calc ∑ t ∈ J₀.image tube, ((J₀.filter (fun j => tube j = t)).card : ℝ) *
          ((tubeCells D cls U cell J₀ tube t).card : ℝ)
      ≤ ∑ t ∈ J₀.image tube, Nmax * ((tubeCells D cls U cell J₀ tube t).card : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_right (hN t ht) (Nat.cast_nonneg _)
    _ = Nmax * ∑ t ∈ J₀.image tube, ((tubeCells D cls U cell J₀ tube t).card : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ Nmax * (B * ((U.image cell).card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hNmax
        -- double count (tube, cell) incidences
        have hsub : ∀ t ∈ J₀.image tube, tubeCells D cls U cell J₀ tube t ⊆ U.image cell := by
          intro t _ c hc
          obtain ⟨j, _, hcj⟩ := Finset.mem_biUnion.mp hc
          exact cellsHit_subset D cls U cell j hcj
        have hswap : ∑ t ∈ J₀.image tube, ((tubeCells D cls U cell J₀ tube t).card : ℝ) =
            ∑ c ∈ U.image cell,
              (((J₀.image tube).filter (fun t => c ∈ tubeCells D cls U cell J₀ tube t)).card : ℝ) := by
          have h1 : ∀ t ∈ J₀.image tube, ((tubeCells D cls U cell J₀ tube t).card : ℝ) =
              ∑ c ∈ U.image cell, (if c ∈ tubeCells D cls U cell J₀ tube t then (1 : ℝ) else 0) := by
            intro t ht
            rw [Finset.sum_boole]
            congr 2
            ext c
            simp only [Finset.mem_filter]
            constructor
            · intro hc; exact ⟨hsub t ht hc, hc⟩
            · intro hc; exact hc.2
          rw [Finset.sum_congr rfl h1, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_boole]
        rw [hswap]
        calc ∑ c ∈ U.image cell,
              (((J₀.image tube).filter (fun t => c ∈ tubeCells D cls U cell J₀ tube t)).card : ℝ)
            ≤ ∑ _c ∈ U.image cell, B := Finset.sum_le_sum hB
          _ = B * ((U.image cell).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end CoarseSide

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
