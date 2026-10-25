-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AlignmentRadialCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentNumerics
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ProjectionInterval

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem AlignmentScaleBudget.radial_cover_lower {δ ε η κ h w K : ℝ} {S : Set ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hh : 0 < h) (hw : 0 < w) (hK : 0 < K)
    (hratio : δ ^ (-ε / 2) ≤ h / w) (hKbound : K ≤ 8192 * δ ^ (-η - κ))
    (hcount : ∀ (m : ℕ) (cc : Fin m → ℝ), Covers w S cc →
      (δ ^ η) ^ (2 : ℕ) ≤
        (8 * K ^ (2 : ℕ) * energyConstant (1 - ε / 2) * (2 * w / h) ^ (1 - ε / 2)) * (m : ℝ)) :
    CoverLower w S ((160 * h / w) ^ (1 - ε)) := by
  have hnum := hb.radial_gain hδ hε hε1 (div_pos hh hw) hratio hK.le hKbound
  have hnum' : (160 * h / w) ^ (1 - ε) *
      (8 * K ^ (2 : ℕ) * energyConstant (1 - ε / 2) * (2 * w / h) ^ (1 - ε / 2)) ≤
        (δ ^ η) ^ (2 : ℕ) := by
    convert hnum using 1
    · congr 2
      · ring
      · congr 1
        field_simp
    · rw [← Real.rpow_mul_natCast hδ.le η 2]
      congr 1
      norm_num
      ring
  have hE : 0 < energyConstant (1 - ε / 2) := energyConstant_pos (by linarith)
  have hM : 0 < 8 * K ^ (2 : ℕ) * energyConstant (1 - ε / 2) * (2 * w / h) ^ (1 - ε / 2) := by positivity
  intro m cc hc
  apply (mul_le_mul_iff_left₀ hM).mp
  exact (hnum'.trans (hcount m cc hc)).trans_eq (mul_comm _ _)

theorem AlignmentScaleBudget.gain_length {δ ε η κ h w : ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ) (hw : 0 < w)
    (hη : η ≤ ε / 2) (hratio : δ ^ (-ε / 2) ≤ h / w) :
    δ ^ (-η) * w ≤ 2 * (80 * h) := by
  have hpow : δ ^ (-η) ≤ δ ^ (-ε / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hb.scale_le_one (by linarith)
  have hsmall : δ ^ (-η) * w ≤ h := (le_div_iff₀ hw).mp (hpow.trans hratio)
  have hh : 0 < h := (by positivity : 0 < δ ^ (-η) * w).trans_le hsmall
  nlinarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
