-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripRadialFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripRadialGeometry

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Directions from a pin outside a narrow strip inherit a Frostman bound
at angular scales at least the strip width. Multiplicities are retained. -/
theorem IndexedFrostman.radial_of_strip {I : Type*} [Fintype I] {f : I → Plane}
    {δ ρ C c w s : ℝ} {b n : Plane} (hF : IndexedFrostman δ C f)
    (hρ : 0 ≤ ρ) (hδρ : δ ≤ ρ) (hC : 0 ≤ C) (hn : ‖n‖ = 1)
    (hs : 0 < s) (hs16 : s ≤ 16) (hwρ : w ≤ ρ)
    (hbf : ∀ i, b ≠ f i) (hstrip : ∀ i, |inner ℝ (f i) n - c| ≤ w)
    (hgap : ∀ i, s ≤ |inner ℝ (f i) n - inner ℝ b n|)
    (hfar : ∀ i, ‖b - f i‖ ≤ 16) :
    IndexedFrostman ρ (2048 * C / s) (fun i => radialDirection b (f i)) := by
  classical
  intro z r hρr
  have hr : 0 ≤ r := hρ.trans hρr
  have hrR : r ≤ 2048 * r / s := (le_div_iff₀ hs).mpr (by nlinarith)
  have hcount := hF.card_of_diameter
    (Finset.univ.filter (fun i => dist (radialDirection b (f i)) z ≤ r))
    hC (by positivity : 0 ≤ 2048 * r / s) (hδρ.trans (hρr.trans hrR)) (by
      intro i hi j hj
      exact strip_radial_cap_diameter hn hs hr (hwρ.trans hρr) (hbf i) (hbf j)
        (hstrip i) (hstrip j) (hgap j) (hfar i) (hfar j)
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
  convert hcount using 1 <;> ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
