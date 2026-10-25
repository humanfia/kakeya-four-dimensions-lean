-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.EnergyGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.PaletteArithmetic
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.BalancedTubePower
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.BalancedCells

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- Label balance in bushes and cells gives balance of the distinct pins. -/
theorem HighConfig.pin_cell_balanced
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {i : ℕ} (hi : i ≤ n) :
    Balanced (S.image Prod.fst) (cellOf (palScale r n i)) (r ^ (-2 * ε)) := by
  have hr := H.fail.r_pos
  have hh := Multiscale.balanced_image S Prod.fst (cellOf (palScale r n i))
    (Real.rpow_nonneg hr.le _) H.bal_pin (H.bal_cell i hi)
  have heq : (r ^ (-ε)) ^ (2 : ℕ) = r ^ (-2 * ε) := by
    rw [← Real.rpow_mul_natCast hr.le]
    congr 1
    norm_num
    ring
  rwa [heq] at hh

/-- The absolute Katz--Tao bound and the pin-mass lower bound normalize to
a linear Frostman bound, uniformly on the retained original pins. -/
theorem HighConfig.normalized_point_count
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (x : E2) {ρ : ℝ} (hρ : r ≤ ρ) :
    (((S.image Prod.fst).filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤
      r ^ (-2 * ε) * ρ * (S.image Prod.fst).card := by
  have hr := H.fail.r_pos
  have hρ0 : 0 ≤ ρ := hr.le.trans hρ
  have heq : r ^ (-2 * ε) * r ^ (ε - 1) = r ^ (-ε) / r := by
    calc
      _ = r ^ (-ε - 1) := by rw [← Real.rpow_add hr]; congr 1; ring
      _ = _ := by rw [Real.rpow_sub hr, Real.rpow_one]
  calc
    _ ≤ r ^ (-ε) * (ρ / r) := H.failS.P_kt x ρ hρ
    _ = r ^ (-2 * ε) * ρ * r ^ (ε - 1) := by
      calc
        _ = (r ^ (-ε) / r) * ρ := by ring
        _ = _ := by rw [← heq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left H.failS.P_card
      (mul_nonneg (Real.rpow_nonneg hr.le _) hρ0)

/-- Polynomial cardinality bound needed only to absorb the dyadic
second-moment logarithm. -/
theorem HighConfig.pin_card_le_cube
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr4 : r ≤ 1 / 4) (hε : ε ≤ 1) :
    ((S.image Prod.fst).card : ℝ) ≤ r ^ (-3 : ℝ) := by
  have hr := H.fail.r_pos
  have hr1 : r ≤ 1 := by linarith
  have hpow : r ^ (-ε) ≤ r⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have h4 : 4 ≤ r⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ hr]; linarith
  calc
    _ ≤ r ^ (-ε) * (4 / r) := H.failS.P_card_le (by linarith)
    _ ≤ r⁻¹ * (r⁻¹ / r) := by gcongr
    _ = r ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = -1 + -1 + -1 by norm_num,
        Real.rpow_add hr, Real.rpow_add hr, Real.rpow_neg_one]
      ring

/-- The concrete point-ball count required by the reflected energy
palette, expressed using the measured number of occupied cells. -/
theorem HighConfig.point_ball_count
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {i : ℕ} (hi : i ≤ n)
    (x : E2) :
    (((S.image Prod.fst).filter (fun p => dist p x ≤ 2 * palScale r n i)).card : ℝ) ≤
      36 * r ^ (-2 * ε) * (S.image Prod.fst).card /
        cellCount (S.image Prod.fst) (palScale r n i) := by
  have hr := H.fail.r_pos
  have hΔ : 0 < palScale r n i := Real.rpow_pos_of_pos (palBase_pos hr) _
  have hh := Multiscale.balanced_grid_ball_count (S.image Prod.fst) H.failS.P_ne x
    hΔ (show 0 ≤ 2 * palScale r n i by positivity) (Real.rpow_nonneg hr.le _)
    (H.pin_cell_balanced hi)
  have hratio : 2 * (2 * palScale r n i) / palScale r n i + 2 = 6 := by
    field_simp
    ring
  change _ ≤ r ^ (-2 * ε) * (2 * (2 * palScale r n i) / palScale r n i + 2) ^ 2 *
    (S.image Prod.fst).card / cellCount (S.image Prod.fst) (palScale r n i) at hh
  rw [hratio] at hh
  convert hh using 1 <;> ring

/-- Coarse representatives are still members of the original fine family. -/
theorem HighConfig.coarse_class_mem
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {a : ℕ} (ha : a ≤ n) {q : E2 × E2} (hq : q ∈ S) :
    tb a (cls q) ∈ J₀ :=
  H.tubes_sub a (H.tube_mem a ha (cls q) (H.cls_mem q (H.sub hq)))

/-- The two assignments, first to a fine line and then to an `a`-tube,
give width `26 palScale a` on the original pins. -/
theorem HighConfig.coarse_class_incidence
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {a : ℕ} (ha : a ≤ n)
    {q : E2 × E2} (hq : q ∈ S) :
    |inner ℝ (q.1 - (tb a (cls q)).1) (tb a (cls q)).2| < 26 * palScale r n a := by
  have hqD := H.sub hq
  have hc := H.cls_mem q hqD
  have hgeo := H.tube_geo a ha (cls q) hc
  have hh := Columns.assigned_tube_incidence
    (H.fail.P_norm q.1 (H.fail.D_mem q hqD).1)
    (H.fail.P_norm (cls q).1 (H.fail.D_mem (cls q) (H.lines_sub hc)).1)
    (H.cls_geo q hqD).1 hgeo.1 hgeo.2
  have hrR := r_le_palScale H.fail.r_pos hr1 hn ha
  linarith

/-- The geometric second moment for the actual coarse classes of a
`HighConfig`. All logarithms and representative choices are discharged. -/
theorem highConfig_tube_second_moment (ν : ℝ) (hν : 0 < ν) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 4 ∧
      ∀ (r s ε₀ ε κ : ℝ) (n : ℕ) (P : Finset E2) (D S J₀ : Finset (E2 × E2))
        (cls : E2 × E2 → E2 × E2) (J₁ : ℕ → Finset (E2 × E2))
        (tb : ℕ → E2 × E2 → E2 × E2),
      r ≤ r₀ → ε ≤ 1 → 128 ≤ palBase r n →
      HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb →
      ∀ h a : ℕ, 0 < h → h ≤ a → a ≤ n →
      (∑ t ∈ (S.image (fun q => tb a (cls q))).image (tb h),
        ((Columns.tubeCells S (fun q => tb a (cls q)) (S.image Prod.fst)
          (cellOf (palScale r n h)) (S.image (fun q => tb a (cls q))) (tb h) t).card : ℝ) ^ 2)
        ≤ 3 * r ^ (-(4 * ε + ν)) * (cellCount (S.image Prod.fst) (palScale r n h) : ℝ) ^ 2 := by
  obtain ⟨r₀, hr₀, _, henergy⟩ :=
    Columns.balanced_tube_cells_second_moment_power
      (by norm_num : (1 : ℝ) ≤ 64) (by norm_num : (0 : ℝ) < 3) hν
  refine ⟨min r₀ (1 / 4), by positivity, min_le_right _ _, ?_⟩
  intro r s ε₀ ε κ n P D S J₀ cls J₁ tb hsmall hε hbase H h a hh hha han
  have hr := H.fail.r_pos
  have hr4 : r ≤ 1 / 4 := hsmall.trans (min_le_right _ _)
  have hr1 : r < 1 := by linarith
  have hn : 0 < n := hh.trans_le (hha.trans han)
  have hhn : h ≤ n := hha.trans han
  have hΔ := palScale_pos (n := n) hr h
  have hRΔ := palScale_antitone hr hr1 hn hha
  have hwidth : 64 * palScale r n h ≤ 1 / 2 := by
    have hbasepos := palBase_pos (n := n) hr
    have hscale := palScale_le_inv_base hr hr1 hn hh
    have hinv : (palBase r n)⁻¹ ≤ (128 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) hbase
    linarith [hscale.trans hinv]
  have hclass : ∀ j ∈ S.image (fun q => tb a (cls q)), j ∈ J₀ := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact H.coarse_class_mem han hq
  have hTsub : (S.image (fun q => tb a (cls q))).image (tb h) ⊆ J₁ h := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact H.tube_mem h hhn j (hclass j hj)
  have hE := henergy r (palScale r n h) (64 * palScale r n h)
    (r ^ (-2 * ε)) (r ^ (-2 * ε)) hr (hsmall.trans (min_le_left _ _))
    (r_le_palScale hr hr1 hn hhn) (by linarith) hwidth (by rfl)
    (by positivity) (by positivity)
    S (S.image (fun q => tb a (cls q))) (fun q => tb a (cls q)) (tb h)
    (S.image Prod.fst) (cellOf (palScale r n h)) H.failS.P_ne
    (H.pin_card_le_cube hr4 hε) H.failS.P_norm (H.pin_cell_balanced hhn)
    (fun _ _ _ _ heq => dist_le_of_cellOf_eq hΔ heq)
    (fun x ρ hρ => H.normalized_point_count x hρ)
    (by
      intro t ht
      have htD := H.lines_sub (H.tubes_sub h (hTsub ht))
      exact ⟨H.fail.P_norm t.1 (H.fail.D_mem t htD).1, (H.fail.D_mem t htD).2⟩)
    (by
      intro t ht u hu hne
      exact H.tubes_sep h hhn t (hTsub ht) u (hTsub hu) hne)
    (by
      intro j hj p hp
      obtain ⟨e, heS, heq⟩ := mem_pinsOf.mp (Finset.mem_inter.mp hp).1
      have hinc := H.coarse_class_incidence hr1 hn han heS
      change |inner ℝ (p - (tb a (cls (p, e))).1) (tb a (cls (p, e))).2| < _ at hinc
      rw [heq] at hinc
      have htgeom := H.tube_geo h hhn j (hclass j hj)
      have hhinc := Columns.assigned_tube_incidence
        (H.failS.P_norm p (Finset.mem_inter.mp hp).2)
        (H.fail.P_norm j.1 (H.fail.D_mem j (H.lines_sub (hclass j hj))).1)
        hinc htgeom.1 htgeom.2
      linarith)
  have hcoeff : (3 * r ^ (-2 * ε) * r ^ (-2 * ε)) * r ^ (-ν) =
      3 * r ^ (-(4 * ε + ν)) := by
    calc
      _ = 3 * (r ^ (-2 * ε) * r ^ (-2 * ε) * r ^ (-ν)) := by ring
      _ = _ := by rw [← Real.rpow_add hr, ← Real.rpow_add hr]; congr 2; ring
  rw [hcoeff] at hE
  exact hE

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
