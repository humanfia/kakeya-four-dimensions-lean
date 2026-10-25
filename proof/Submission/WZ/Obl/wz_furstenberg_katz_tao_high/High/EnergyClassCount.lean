-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.EnergyClassCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.EnergyWeights
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CoarseAngularCount

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

attribute [local instance] Classical.propDecidable

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- Full line Frostman gives a far half at any power scale whose exponent
beats its constant. No new subset or regularization is performed. -/
theorem HighConfig.far_half
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r ≤ 1) {ℓ : ℝ} (hℓ1 : ℓ ≤ 1)
    (hsmall : r ^ (-κ + ℓ * (1 - s)) ≤ 1 / 2) :
    ∀ q ∈ S, 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
      (fun q' => dist q'.1 q.1 < r ^ ℓ)).card : ℝ)) ≤
        (S.filter (fun q' => cls q' = cls q)).card := by
  have hr := H.fail.r_pos
  have hrc : r ≤ r ^ ℓ := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hr hr1 hℓ1
  intro q hq
  have hh := H.line_frostman q hq (r ^ ℓ) hrc
  rw [← Real.rpow_mul hr.le, ← Real.rpow_add hr] at hh
  have hh' := mul_le_mul_of_nonneg_right hsmall
    (show (0 : ℝ) ≤ (S.filter (fun q' => cls q' = cls q)).card by positivity)
  linarith

/-- The coarse class bound in terms of the actual reference angular
profile, with an explicit power loss. -/
theorem HighConfig.coarse_class_count
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    {ℓ : ℝ} (hℓ1 : ℓ ≤ 1) (hsmall : r ^ (-κ + ℓ * (1 - s)) ≤ 1 / 2)
    {a : ℕ} (ha : a ≤ n) (hRsmall : palScale r n a ≤ 1 / 8)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) :
    ((S.image (fun q => tb a (cls q))).card : ℝ) ≤
      (67080 : ℝ) ^ (2 : ℕ) * 5200 * r ^ (-(12 * ε + ε₀ + ℓ * s)) *
        (cellCount (bushOf S p₀) (palScale r n a) : ℝ) ^ (2 : ℕ) := by
  have hr := H.fail.r_pos
  obtain ⟨e, he⟩ := H.bush_nonempty hp₀
  have hh := coarse_tube_count_le_arcs H.fail hs0 hs1
    (Real.rpow_pos_of_pos hr ℓ) (Real.rpow_pos_of_pos hr (-ε))
    (r_le_palScale hr hr1 hn ha) hRsmall H.cls_mem H.lines_sub
    (H.fail.few_lines J₀ H.lines_sub H.lines_sep).le H.cls_geo
    (H.tubes_sub a) (H.tubes_sep a ha) (H.tube_mem a ha) (H.tube_geo a ha)
    H.sub H.failS H.bal_cls (H.bal_pin_tube a ha)
    (H.far_half hr1.le hℓ1 hsmall) (mem_bushOf.mp he)
  have hcoef := coarse_count_coefficient_le (η := ε) (η' := ε) (ε₀ := ε₀)
    (k := ε) (ℓ := ℓ) hr hr1.le hs1 hε
  have hpow : -3 * ε - 7 * ε - ℓ * s - ε₀ - 2 * ε = -(12 * ε + ε₀ + ℓ * s) := by ring
  rw [hpow] at hcoef
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef (by positivity : (0 : ℝ) ≤ 67080 ^ (2 : ℕ)))
    (sq_nonneg (cellCount (bushOf S p₀) (palScale r n a) : ℝ))
  have hcount : ((bushOf S p₀).image (arcOf (palScale r n a))).card =
      cellCount (bushOf S p₀) (palScale r n a) := rfl
  dsimp only [Prod.fst] at hh
  rw [hcount] at hh
  apply hh.trans
  convert hmul using 1 <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
