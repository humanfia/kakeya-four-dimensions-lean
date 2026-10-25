-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.Parameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs

/-! Choice of the small thickness and density losses. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

structure LengtheningParameters (ω ζ ε : ℝ) where
  thin : ℝ
  eta : ℝ
  thin_pos : 0 < thin
  thin_le_one : thin ≤ 1
  thin_omega : thin ≤ ω/1000
  thin_epsilon : thin ≤ ε/100
  eta_pos : 0 < eta
  eta_omega : eta ≤ ω/1000
  eta_beta_omega : eta ≤ (ω*ζ/100)*ω/1000
  eta_epsilon : eta ≤ ε/1000
  eta_beta_epsilon : eta ≤ (ω*ζ/100)*ε/1000

lemma lengthening_parameters {ω ζ ε : ℝ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hε : 0 < ε) :
    Nonempty (LengtheningParameters ω ζ ε) := by
  let b := min (ω/1000) (ε/1000)
  let eta := min (ω/1000) (min ((ω*ζ/100)*ω/1000)
    (min (ε/1000) ((ω*ζ/100)*ε/1000)))
  have hηω : eta ≤ ω/1000 := min_le_left _ _
  have hηβω : eta ≤ (ω*ζ/100)*ω/1000 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : eta ≤ ε/1000 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηβε : eta ≤ (ω*ζ/100)*ε/1000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨⟨b, eta, by dsimp [b]; positivity, ?_, min_le_left _ _, ?_,
    by dsimp [eta]; positivity, hηω, hηβω, hηε, hηβε⟩⟩
  · have hh : b ≤ ω/1000 := min_le_left _ _
    linarith
  · have hh : b ≤ ε/1000 := min_le_right _ _
    linarith

lemma broadness_exponent_bounds {ω ζ : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) :
    0 < ω*ζ/100 ∧ ω*ζ/100 ≤ 1 ∧ ω*ζ/100 ≤ ω/1000 := by
  have hζ1 : ζ ≤ 1/1000 := by linarith
  have hprod : ω*ζ ≤ ω*(1/1000) := mul_le_mul_of_nonneg_left hζ1 hω.le
  exact ⟨by positivity, by nlinarith, by nlinarith⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
