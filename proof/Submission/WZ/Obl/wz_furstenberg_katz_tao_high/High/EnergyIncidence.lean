-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.EnergyIncidence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.EnergyWeights
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.SelectedMass

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- Every coarse class retains its original fine-pin incidences. The
reference bush size cancels, leaving the measured coarse angular count. -/
theorem HighConfig.coarse_incidence_lower
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {a : ℕ} (ha : a ≤ n)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) :
    (S.image Prod.fst).card * (cellCount (bushOf S p₀) (palScale r n a) : ℝ) /
        (72 * r ^ (-2 * ε)) ≤
      ∑ j ∈ S.image (fun q => tb a (cls q)),
        ((pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst).card : ℝ) := by
  have hr := H.fail.r_pos
  have hh := Columns.coarse_selected_incidence_lower (lam := 1)
    (palScale_pos (n := n) hr a) (Real.rpow_pos_of_pos hr (-ε)) (by norm_num)
    (fun j hj => (H.coarse_classes_norm ha hj).2)
    (fun q hq => H.coarse_class_angle hr1 hn ha hq)
    H.bal_pin (H.bal_pin_arc a ha) p₀ (H.bush_nonempty hp₀)
    (by
      rw [Finset.filter_eq_self.mpr (fun q hq => Finset.mem_image_of_mem _ hq), one_mul])
  have hpow : (r ^ (-ε)) ^ (2 : ℕ) = r ^ (-2 * ε) := by
    rw [← Real.rpow_mul_natCast hr.le]
    congr 1
    norm_num
    ring
  rw [one_mul, hpow] at hh
  have hinter : ∀ j, pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst =
      pinsOf S (fun q => tb a (cls q)) j := by
    intro j
    exact Finset.inter_eq_left.mpr (Columns.pinsOf_subset
      (fun q hq => Finset.mem_image_of_mem _ hq) _ j)
  simp_rw [hinter]
  rw [div_le_iff₀ (show 0 < 72 * r ^ (-2 * ε) by positivity)]
  convert hh using 1 <;> first | rfl | ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
