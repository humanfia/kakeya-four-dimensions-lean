-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.StrongEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.CoarsePalette
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.TubeSecondMoment
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.ProfileEnergyCounts

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators

attribute [local instance] Classical.propDecidable

-- The energy upper-bound assembly is adapted from workspace o222/x0720,
-- Columns/ProfileCounts.lean, commit 8169359. It retains the original pins.
/-- Actual point-ball and angular-cap counts give the profile bound for
the full coarse class-cell energy. -/
theorem coarse_cell_energy_profile_bound {ι : Type*} [DecidableEq ι]
    {r R m : ℝ} (hrR : r ≤ R) (hR : 0 < R) (hR1 : R ≤ 1) (hm : 0 < m)
    (D J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (P : Finset E2) (cell : E2 → ι) (ρ M V F G : ℕ → ℝ)
    {h a : ℕ} (hha : h ≤ a) {B N e : ℝ} (hB : 1 < B)
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 32 * R ∧
      (dist q.2 (cls q).2 < R ∨ dist q.2 (-(cls q).2) < R))
    (hP : ∀ p ∈ P, ‖p‖ ≤ 4)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, cell p = cell q → dist p q ≤ ρ h)
    (hV : ∀ i ∈ Finset.Icc h a, 0 ≤ V i)
    (hM : ∀ p ∈ P, ∀ i ∈ Finset.Icc h a,
      ((P.filter fun q => dist p q ≤ ρ i).card : ℝ) ≤ M i)
    (hcap : ∀ p ∈ P, ∀ i ∈ Finset.Icc h a, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter fun v => dist v u ≤ paletteCapRadius R ρ a i).card : ℝ) ≤ V i)
    (hmin : ∀ p ∈ P, ∀ j ∈ J, p ∈ pinsOf D cls j →
      m ≤ (((bushOf D p).filter fun v => cls (p, v) = j).card : ℝ))
    (hPcard : (P.card : ℝ) ≤ B ^ N)
    (hpoint : ∀ i ∈ Finset.Icc h a, M i ≤ B ^ (N - G i + e))
    (hangular : ∀ i ∈ Finset.Icc h a, 2 * V i / m ≤ B ^ (F a - F (a - i) + e)) :
    (∑ j ∈ J, ∑ c ∈ P.image cell, ((cellPins D cls P cell j c).card : ℝ) ^ 2) ≤
      B ^ (2 * N + F a + 2 * e) *
        ∑ i ∈ Finset.Icc h a, B ^ (-(G i + F (a - i))) := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  have henergy := coarse_cell_energy_le_palette hrR hR hR1 hm D J cls P cell ρ M V hha
    hunit hgeo hP hdiam hV hM hcap hmin
  have hprod : ∀ i ∈ Finset.Icc h a,
      M i * (2 * V i / m) ≤ B ^ (N - G i + e) * B ^ (F a - F (a - i) + e) := by
    intro i hi
    exact mul_le_mul (hpoint i hi) (hangular i hi)
      (div_nonneg (mul_nonneg (by norm_num) (hV i hi)) hm.le) (Real.rpow_nonneg hB0.le _)
  calc
    _ ≤ P.card * ∑ i ∈ Finset.Icc h a, M i * (2 * V i / m) := henergy
    _ ≤ P.card * ∑ i ∈ Finset.Icc h a,
        B ^ (N - G i + e) * B ^ (F a - F (a - i) + e) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hprod) (Nat.cast_nonneg _)
    _ ≤ B ^ N * ∑ i ∈ Finset.Icc h a,
        B ^ (N - G i + e) * B ^ (F a - F (a - i) + e) :=
      mul_le_mul_of_nonneg_right hPcard
        (Finset.sum_nonneg fun _ _ => mul_nonneg (Real.rpow_nonneg hB0.le _) (Real.rpow_nonneg hB0.le _))
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Real.rpow_add hB0, ← Real.rpow_add hB0, ← Real.rpow_add hB0]
      congr 1
      ring

/-- The strong energy witness from a tube second moment. In particular no
bound on the number of cells met by an individual coarse class is assumed.
Weighted high-degree pruning is performed inside the proof. -/
theorem profile_witness_of_tube_energy {ι τ : Type*} [DecidableEq ι] [DecidableEq τ]
    (D J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (P : Finset E2) (cell : E2 → ι) (tube : E2 × E2 → τ) (F G : ℕ → ℝ)
    {h a : ℕ} (hha : h ≤ a) {B N e W E : ℝ} (hB : 1 < B) (hW : 0 < W) (hE : 0 < E)
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
    (hpalette : ((Finset.Icc h a).card : ℝ) ≤ B ^ e) (h8 : 8 ≤ B ^ e) :
    ∃ y ∈ Finset.Icc h a, G y + F (a - y) ≤ F a + G h - F h + 10 * e := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hI0 : 0 < ∑ j ∈ J, ((pinsOf D cls j ∩ P).card : ℝ) :=
    (Real.rpow_pos_of_pos hB0 _).trans_le hI
  have hcubic := incidence_cubic_of_tube_second_moment D cls P cell J tube hW hE hI0
    hweight hsecond
  obtain ⟨y, hy, hvalue⟩ := Multiscale.profile_energy_witness_of_cubic_errors
    (Finset.Icc h a) (fun y => G y + F (a - y))
    (Finset.nonempty_Icc.mpr hha) hB hW.le hE.le (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    hpalette h8 hI hcubic hWprofile hEprofile hclasses henergy
  exact ⟨y, hy, by linarith⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
