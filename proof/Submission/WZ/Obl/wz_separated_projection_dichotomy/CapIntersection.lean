-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CapIntersection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedGeometry
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialTransverse

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

attribute [local instance] Classical.propDecidable

/-- Frostman control of two radial caps away from the line joining their pins. -/
theorem radial_cap_intersection_count {J : Type*} [Fintype J] {f : J → Plane}
    {δ C q s r : ℝ} {b b' u v : Plane}
    (hF : IndexedFrostman δ C f) (hC : 0 ≤ C) (hq : 0 < q) (hs : 0 < s)
    (hr : 0 ≤ r) (hsmall : r ≤ q * s / 256) (hδrad : δ ≤ 4096 * r / (q * s))
    (hsep : q ≤ ‖b' - b‖) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpoints : ∀ j, b ≠ f j ∧ b' ≠ f j ∧ ‖b - f j‖ ≤ 8 ∧ ‖b' - f j‖ ≤ 8) :
    ((Finset.univ.filter (fun j =>
      s * ‖b' - b‖ ≤ |area (f j - b) (b' - b)| ∧
      dist (radialDirection b (f j)) u ≤ r ∧ dist (radialDirection b' (f j)) v ≤ r)).card : ℝ) ≤
      C * (4096 * r / (q * s)) * (Fintype.card J : ℝ) := by
  classical
  let S := Finset.univ.filter (fun j =>
    s * ‖b' - b‖ ≤ |area (f j - b) (b' - b)| ∧
    dist (radialDirection b (f j)) u ≤ r ∧ dist (radialDirection b' (f j)) v ≤ r)
  apply hF.card_of_diameter S hC (by positivity) hδrad
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  have hang := radial_cap_transverse (hpoints j).1 (hpoints j).2.1 hu hv hq.le hs.le
    hsmall hsep (hpoints j).2.2.1 (hpoints j).2.2.2 hj'.1 hj'.2.1 hj'.2.2
  have hd := radial_cap_diameter hu hv hr (by positivity : 0 < q * s / 128)
    hang (hpoints j) (hpoints k) hj'.2.1 hj'.2.2 hk'.2.1 hk'.2.2
  convert hd using 1 <;> field_simp <;> ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
