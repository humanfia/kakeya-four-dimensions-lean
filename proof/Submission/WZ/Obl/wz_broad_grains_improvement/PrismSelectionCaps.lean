-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.PrismSelectionCaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.PrismSelection
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedEndpoint

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- Normalized incidence caps survive a whole-prism selection and an angular
width change whenever the density budget pays for that change. -/
theorem caps_of_prism_selection {n : ℕ} {D D' : PrismData n}
    {d h h' ρ ρ' c : ℝ} (hd : 0 < d) (ha : 0 ≤ D.a) (hc : 0 ≤ c)
    (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ') (hbudget : d^h'*ρ' ≤ d^h*ρ)
    (hsel : PrismSelection D D') (hcap : D.HasCaps d h ρ c) :
    D'.HasCaps d h' ρ' c := by
  obtain ⟨haa, τ, _, _, _, hW⟩ := hsel
  obtain ⟨m, hm, hcount, havg⟩ := hcap
  refine ⟨m ∘ τ, fun j => hm (τ j), ?_, ?_⟩
  · intro j p
    simpa only [hW, Function.comp_apply] using hcount (τ j) p
  · intro j
    have hmj := hm (τ j)
    have hnew : volume (P D'.a (ρ'*c) c (D'.z j) (D'.e j)) = O (D.a*(ρ'*c)*c) := by
      rw [haa]
      exact WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha (mul_nonneg hρ' hc) hc _ _
    have hold : volume (P D.a (ρ*c) c (D.z (τ j)) (D.e (τ j))) = O (D.a*(ρ*c)*c) :=
      WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha (mul_nonneg hρ hc) hc _ _
    have hh := havg (τ j)
    change O (d^h'*m (τ j))*volume (P D'.a (ρ'*c) c (D'.z j) (D'.e j)) ≤ _
    simp_rw [hW, Function.comp_apply]
    apply le_trans (b := O (d^h*m (τ j))*volume (P D.a (ρ*c) c (D.z (τ j)) (D.e (τ j)))) ?_ hh
    rw [hnew, hold, ← ENNReal.ofReal_mul (by positivity : 0 ≤ d^h'*m (τ j)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ d^h*m (τ j))]
    apply ENNReal.ofReal_le_ofReal
    have hh' := mul_le_mul_of_nonneg_right hbudget
      (show 0 ≤ m (τ j)*D.a*c*c by positivity)
    nlinarith only [hh']

end WangZahlLot.Obl.wz_broad_grains_improvement
