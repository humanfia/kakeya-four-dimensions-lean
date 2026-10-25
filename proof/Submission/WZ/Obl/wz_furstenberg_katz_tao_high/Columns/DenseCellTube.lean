-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.DenseCellTube.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.PrunedEnergy
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.HighDegreePruning

/-!
# A dense tube after pruning

`exists_dense_cell_tube`: under the hypotheses of x0651's `incidence_energy_of_tube_second_moment`
(per-tube incidence mass at most `W` times its cell count, second moment of the cell counts at
most `E`, cutoff `Bc` with `2 W E ≤ Bc I`) and a cell-energy bound `Ecell`, some tube `t` with at
most `Bc` cells has (class, cell) density at least `I² / (4 Bc #J₀ Ecell)`:
`I² / (4 Bc #J₀ Ecell) · #J_t · #cells(t) ≤ ∑_{j ∈ J_t} #cellsHit j`.
This is the pigeonhole form of that pruning bound (`exists_dense_tube` on the retained tubes).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators

/-- **A dense tube among the tubes with few cells.** -/
theorem exists_dense_cell_tube {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]
    (D : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2) (U : Finset E2)
    (cell : E2 → ι) (J₀ : Finset (E2 × E2)) (tube : E2 × E2 → τ)
    {W E Bc Ecell : ℝ} (hW : 0 ≤ W) (hBc : 0 < Bc) (hEc : 0 < Ecell)
    (hI : 0 < ∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ))
    (hweight : ∀ t ∈ J₀.image tube,
      (∑ j ∈ J₀.filter (fun j => tube j = t), ((pinsOf D cls j ∩ U).card : ℝ)) ≤
        W * (tubeCells D cls U cell J₀ tube t).card)
    (hsecond : (∑ t ∈ J₀.image tube, ((tubeCells D cls U cell J₀ tube t).card : ℝ) ^ 2) ≤ E)
    (hbudget : 2 * W * E ≤ Bc * ∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ))
    (henergy : (∑ j ∈ J₀, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2) ≤
      Ecell) :
    ∃ t ∈ J₀.image tube, ((tubeCells D cls U cell J₀ tube t).card : ℝ) ≤ Bc ∧
      (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) ^ 2 / (4 * Bc * J₀.card * Ecell) *
          (((J₀.filter (fun j => tube j = t)).card : ℝ) *
            (tubeCells D cls U cell J₀ tube t).card) ≤
        ∑ j ∈ J₀.filter (fun j => tube j = t), ((cellsHit D cls U cell j).card : ℝ) := by
  classical
  let deg (t : τ) : ℝ := (tubeCells D cls U cell J₀ tube t).card
  let w (j : E2 × E2) : ℝ := (pinsOf D cls j ∩ U).card
  let mass (t : τ) : ℝ := ∑ j ∈ J₀.filter (fun j => tube j = t), w j
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∑ j ∈ J₀, w j := ⟨_, rfl⟩
  let J := J₀.filter (fun j => deg (tube j) ≤ Bc)
  have hJJ : J ⊆ J₀ := Finset.filter_subset _ _
  have htotal : ∑ t ∈ J₀.image tube, mass t = I := by
    rw [hIdef]; exact (sum_classes_eq_sum_tubes J₀ tube w).symm
  have hT : J.image tube = (J₀.image tube).filter (fun t => deg t ≤ Bc) := by
    ext t
    simp only [J, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, ⟨hj, hd⟩, rfl⟩
      exact ⟨⟨j, hj, rfl⟩, hd⟩
    · rintro ⟨⟨j, hj, rfl⟩, hd⟩
      exact ⟨j, ⟨hj, hd⟩, rfl⟩
  have hfiber : ∀ t ∈ (J₀.image tube).filter (fun t => deg t ≤ Bc),
      J.filter (fun j => tube j = t) = J₀.filter (fun j => tube j = t) := by
    intro t ht
    have htB := (Finset.mem_filter.mp ht).2
    ext j
    simp only [J, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hj, hjt⟩
      exact ⟨⟨hj, by rwa [hjt]⟩, hjt⟩
  have hretained : ∑ t ∈ (J₀.image tube).filter (fun t => deg t ≤ Bc), mass t =
      ∑ j ∈ J, w j := by
    rw [sum_classes_eq_sum_tubes J tube w, hT]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hfiber t ht]
  have hkeep := half_mass_of_second_moment (J₀.image tube) deg mass hW hBc
    (fun _ _ => Nat.cast_nonneg _) hweight hsecond (by rw [htotal, hIdef]; exact hbudget)
  rw [htotal, hretained] at hkeep
  -- the retained classes: Cauchy–Schwarz
  have hcs := incidences_sq_le D cls J U cell
  have henJ : (∑ j ∈ J, ∑ c ∈ U.image cell, ((cellPins D cls U cell j c).card : ℝ) ^ 2) ≤
      Ecell := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hJJ
        (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) henergy
  have hIJ0 : 0 < ∑ j ∈ J, w j := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (∑ j ∈ J, w j) ^ 2 / Ecell := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; exact div_pos (pow_pos hIJ0 2) hEc
  have hlow : L ≤ ∑ j ∈ J, ((cellsHit D cls U cell j).card : ℝ) := by
    rw [hL, div_le_iff₀ hEc]
    refine hcs.trans ?_
    exact mul_le_mul_of_nonneg_left henJ
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  -- tube cells of the retained classes
  have htc : ∀ j ∈ J, tubeCells D cls U cell J tube (tube j) =
      tubeCells D cls U cell J₀ tube (tube j) := by
    intro j hj
    have hmem : tube j ∈ (J₀.image tube).filter (fun t => deg t ≤ Bc) :=
      Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem tube (hJJ hj), (Finset.mem_filter.mp hj).2⟩
    unfold tubeCells
    rw [hfiber _ hmem]
  have hup : ∑ j ∈ J, ((tubeCells D cls U cell J tube (tube j)).card : ℝ) ≤ Bc * J₀.card := by
    calc ∑ j ∈ J, ((tubeCells D cls U cell J tube (tube j)).card : ℝ)
        ≤ ∑ _j ∈ J, Bc := Finset.sum_le_sum (fun j hj => by
          rw [htc j hj]; exact (Finset.mem_filter.mp hj).2)
      _ = Bc * J.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ Bc * J₀.card := mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (Finset.card_le_card hJJ)) hBc.le
  obtain ⟨t, ht, hdense⟩ := exists_dense_tube D cls U cell J tube hL0 hlow hup
  have htm : t ∈ (J₀.image tube).filter (fun t => deg t ≤ Bc) := by rw [← hT]; exact ht
  have hfib := hfiber t htm
  have htcells : tubeCells D cls U cell J tube t = tubeCells D cls U cell J₀ tube t := by
    unfold tubeCells; rw [hfib]
  have hIeq : (∑ j ∈ J₀, ((pinsOf D cls j ∩ U).card : ℝ)) = I := hIdef.symm
  refine ⟨t, (Finset.mem_filter.mp htm).1, (Finset.mem_filter.mp htm).2, ?_⟩
  rw [hIeq]
  rw [hfib, htcells] at hdense
  rw [Finset.sum_const, nsmul_eq_mul] at hdense
  -- compare the densities
  have hJ0card : (0 : ℝ) < J₀.card := by
    have : J₀.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty] at hI
      exact lt_irrefl _ hI
    exact_mod_cast this.card_pos
  have hratio : I ^ 2 / (4 * Bc * J₀.card * Ecell) ≤ L / (Bc * J₀.card) := by
    rw [hL, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hI0' : 0 ≤ I := by rw [hIdef]; exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hsq : (I / 2) ^ 2 ≤ (∑ j ∈ J, w j) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hkeep 2
    have : I ^ 2 * (Ecell * (Bc * J₀.card)) = 4 * ((I / 2) ^ 2 * (Ecell * (Bc * J₀.card))) := by
      ring
    rw [this]
    have h4 : (∑ j ∈ J, w j) ^ 2 * (4 * Bc * J₀.card * Ecell) =
        4 * ((∑ j ∈ J, w j) ^ 2 * (Ecell * (Bc * J₀.card))) := by ring
    rw [h4]
    have hpos : 0 ≤ Ecell * (Bc * J₀.card) := by positivity
    nlinarith
  have hnn : 0 ≤ ((J₀.filter (fun j => tube j = t)).card : ℝ) *
      (tubeCells D cls U cell J₀ tube t).card := by positivity
  calc I ^ 2 / (4 * Bc * J₀.card * Ecell) *
        (((J₀.filter (fun j => tube j = t)).card : ℝ) * (tubeCells D cls U cell J₀ tube t).card)
      ≤ L / (Bc * J₀.card) *
        (((J₀.filter (fun j => tube j = t)).card : ℝ) * (tubeCells D cls U cell J₀ tube t).card) :=
        mul_le_mul_of_nonneg_right hratio hnn
    _ ≤ _ := hdense


/-- The profile sum is at most `B^(e - m₀)` when every term has exponent at least `m₀`. -/
theorem profile_sum_le {B e m₀ : ℝ} (hB : 1 < B) {S : Finset ℕ} (f : ℕ → ℝ)
    (hS : (S.card : ℝ) ≤ B ^ e) (hf : ∀ i ∈ S, m₀ ≤ f i) :
    ∑ i ∈ S, B ^ (-(f i)) ≤ B ^ (e - m₀) := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  calc ∑ i ∈ S, B ^ (-(f i)) ≤ ∑ _i ∈ S, B ^ (-m₀) := Finset.sum_le_sum (fun i hi =>
        Real.rpow_le_rpow_of_exponent_le hB.le (by linarith [hf i hi]))
    _ = S.card * B ^ (-m₀) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B ^ e * B ^ (-m₀) := mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hB0.le _)
    _ = B ^ (e - m₀) := by rw [← Real.rpow_add hB0]; ring_nf

/-- **Case A density at a right-min window.** Under the counting hypotheses of x0651's
`profile_witness_of_tube_energy`, if `h` is a right-min of `G - s·id` on `[h, a]` and the bush
profile is near-linear (`|F t - s t| ≤ dn`), some tube with at most `2 W E / I` cells has
(class, cell) density at least `B^-(3 dn + 9 e) / 8`. -/
theorem dense_cell_tube_of_profiles {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]
    (D J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (P : Finset E2) (cell : E2 → ι) (tube : E2 × E2 → τ) (F G : ℕ → ℝ)
    {h a : ℕ} (hha : h ≤ a) {B N e W E s dn : ℝ} (hB : 1 < B) (hW : 0 < W) (hE : 0 < E)
    (hweight : ∀ t ∈ J.image tube,
      (∑ j ∈ J.filter (fun j => tube j = t), ((pinsOf D cls j ∩ P).card : ℝ)) ≤
        W * (tubeCells D cls P cell J tube t).card)
    (hsecond : (∑ t ∈ J.image tube, ((tubeCells D cls P cell J tube t).card : ℝ) ^ 2) ≤ E)
    (hWprofile : W ≤ B ^ (N - G h + F a - F h + e))
    (hEprofile : E ≤ B ^ (2 * G h + e))
    (hclasses : (J.card : ℝ) ≤ B ^ (2 * F a + e))
    (hI : B ^ (N + F a - e) ≤ ∑ j ∈ J, ((pinsOf D cls j ∩ P).card : ℝ))
    (henergy : (∑ j ∈ J, ∑ c ∈ P.image cell, ((cellPins D cls P cell j c).card : ℝ) ^ 2) ≤
      B ^ (2 * N + F a + 2 * e) * ∑ i ∈ Finset.Icc h a, B ^ (-(G i + F (a - i))))
    (hpalette : ((Finset.Icc h a).card : ℝ) ≤ B ^ e)
    (hright : ∀ i ∈ Finset.Icc h a, G h - s * h ≤ G i - s * i)
    (hFa : F a ≤ s * a + dn) (hFh : s * h - dn ≤ F h)
    (hFlow : ∀ i ∈ Finset.Icc h a, s * ((a - i : ℕ) : ℝ) - dn ≤ F (a - i)) :
    ∃ t ∈ J.image tube, ((tubeCells D cls P cell J tube t).card : ℝ) ≤
        2 * W * E / ∑ j ∈ J, ((pinsOf D cls j ∩ P).card : ℝ) ∧
      B ^ (-(3 * dn + 9 * e)) / 8 *
          (((J.filter (fun j => tube j = t)).card : ℝ) * (tubeCells D cls P cell J tube t).card) ≤
        ∑ j ∈ J.filter (fun j => tube j = t), ((cellsHit D cls P cell j).card : ℝ) := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  set I := ∑ j ∈ J, ((pinsOf D cls j ∩ P).card : ℝ) with hIdef
  have hI0 : 0 < I := lt_of_lt_of_le (Real.rpow_pos_of_pos hB0 _) hI
  set m₀ : ℝ := G h - s * h + s * a - dn with hm₀
  have hterm : ∀ i ∈ Finset.Icc h a, m₀ ≤ G i + F (a - i) := by
    intro i hi
    have hia : i ≤ a := (Finset.mem_Icc.mp hi).2
    have h1 := hright i hi
    have h2 := hFlow i hi
    have hcast : ((a - i : ℕ) : ℝ) = (a : ℝ) - i := by push_cast [hia]; ring
    rw [hcast] at h2
    rw [hm₀]; nlinarith
  have hsum := profile_sum_le hB (fun i => G i + F (a - i)) hpalette hterm
  set Ecell := B ^ (2 * N + F a + 2 * e) * B ^ (e - m₀) with hEcell
  have hEc0 : 0 < Ecell := by rw [hEcell]; exact mul_pos (Real.rpow_pos_of_pos hB0 _) (Real.rpow_pos_of_pos hB0 _)
  have henergy' : (∑ j ∈ J, ∑ c ∈ P.image cell, ((cellPins D cls P cell j c).card : ℝ) ^ 2) ≤
      Ecell := henergy.trans (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hB0.le _))
  have hBc : 0 < 2 * W * E / I := div_pos (mul_pos (mul_pos two_pos hW) hE) hI0
  obtain ⟨t, ht, hcells, hdense⟩ := exists_dense_cell_tube D cls P cell J tube hW.le hBc hEc0
    hI0 hweight hsecond (by rw [div_mul_cancel₀ _ hI0.ne']) henergy'
  refine ⟨t, ht, hcells, le_trans ?_ hdense⟩
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  -- the density constant
  have hJpos : (0 : ℝ) < J.card := by
    have : J.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hIdef, hne, Finset.sum_empty] at hI0
      exact lt_irrefl _ hI0
    exact_mod_cast this.card_pos
  have hform : I ^ 2 / (4 * (2 * W * E / I) * J.card * Ecell) =
      I ^ 3 / (8 * W * E * J.card * Ecell) := by
    field_simp; ring
  have hden : 0 < 8 * W * E * J.card * Ecell := by
    have := mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 8) hW) hE) hJpos) hEc0
    exact this
  rw [hform, div_le_div_iff₀ (by norm_num) hden]
  -- `B^-(3dn+9e) · 8 W E #J Ecell ≤ 8 I³`
  have hX : W * E * J.card * Ecell ≤
      B ^ (N - G h + F a - F h + e) * B ^ (2 * G h + e) * B ^ (2 * F a + e) * Ecell := by
    have h1 := mul_le_mul hWprofile hEprofile hE.le (Real.rpow_nonneg hB0.le _)
    have h2 := mul_le_mul h1 hclasses (Nat.cast_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hB0.le _) (Real.rpow_nonneg hB0.le _))
    exact mul_le_mul_of_nonneg_right h2 hEc0.le
  have hI3 : B ^ (3 * (N + F a - e)) ≤ I ^ 3 := by
    rw [show 3 * (N + F a - e) = (N + F a - e) * (3 : ℕ) by push_cast; ring,
      Real.rpow_mul hB0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.rpow_pos_of_pos hB0 _).le hI 3
  have hexp : -(3 * dn + 9 * e) + ((N - G h + F a - F h + e) + (2 * G h + e) + (2 * F a + e) +
      ((2 * N + F a + 2 * e) + (e - m₀))) ≤ 3 * (N + F a - e) := by
    rw [hm₀]; nlinarith
  have hcomb : B ^ (-(3 * dn + 9 * e)) *
      (B ^ (N - G h + F a - F h + e) * B ^ (2 * G h + e) * B ^ (2 * F a + e) * Ecell) ≤
      B ^ (3 * (N + F a - e)) := by
    rw [hEcell, ← Real.rpow_add hB0, ← Real.rpow_add hB0, ← Real.rpow_add hB0,
      ← Real.rpow_add hB0, ← Real.rpow_add hB0]
    exact Real.rpow_le_rpow_of_exponent_le hB.le hexp
  have hBpos : 0 ≤ B ^ (-(3 * dn + 9 * e)) := Real.rpow_nonneg hB0.le _
  calc B ^ (-(3 * dn + 9 * e)) * (8 * W * E * J.card * Ecell)
      = 8 * (B ^ (-(3 * dn + 9 * e)) * (W * E * J.card * Ecell)) := by ring
    _ ≤ 8 * (B ^ (-(3 * dn + 9 * e)) *
        (B ^ (N - G h + F a - F h + e) * B ^ (2 * G h + e) * B ^ (2 * F a + e) * Ecell)) := by
        gcongr
    _ ≤ 8 * B ^ (3 * (N + F a - e)) := by gcongr
    _ ≤ 8 * I ^ 3 := by gcongr
    _ = I ^ 3 * 8 := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/Columns/DenseCellTube.lean
