-- Adapted from this LOT tree o173/x0598, commit b7284666,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PacketCertificate.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.BranchFitting
import Submission.Obl.k4_clean_cover_graph_atlas.SelectedRootTransfer
import Submission.Obl.k4_clean_cover_graph_atlas.RepresentativeBins
import Submission.Obl.k4_clean_cover_graph_atlas.GroupCoords

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial Submission.Lib.K4XInterface

/-- A sheet certificate in the group's coordinates gives the exact physical root
and signed derivative window required by the merged-bin geometric tests. -/
theorem packet_root_of_normalized_certificate {T j : ℕ}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} {B : ℝ}
    (hQ : Q.det ≠ 0) (hB : 0 < B) (R : MvPolynomial (Fin 4) ℝ)
    (flat : Bool) (F : RealSheet 2) (centre : Real3) {radius : ℝ} (hradius : 0 < radius)
    (σ : ℝ) (hcert : NormalizedRootCertificate (normPoly T j c u Q B R) flat F centre radius σ)
    (l : ℕ × (Fin 6 → ℝ)) (t δ' : ℝ)
    (hbase : ‖groupBase T j c u Q centre radius (obs B δ' (l, t))‖ ≤ 1) :
    let x := groupBase T j c u Q centre radius (obs B δ' (l, t))
    let w := (F.f (emb x)).re / B
    let s := selectedSlopeFactor flat B * |σ|
    0 < s ∧
      eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (selectedSheetTest flat R) = 0 ∧
      if decide (0 ≤ σ) then
        19 / 20 * s ≤ eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat R)) ∧
        eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat R)) ≤ 21 / 20 * s
      else
        19 / 20 * s ≤ -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat R)) ∧
        -eval (Fin.snoc (Fin.init (gx l t)) w : Fin 4 → ℝ) (pderiv 3 (selectedSheetTest flat R)) ≤ 21 / 20 * s := by
  let x := groupBase T j c u Q centre radius (obs B δ' (l, t))
  let w := (F.f (emb x)).re
  let k := selectedSlopeFactor flat B
  have hk : 0 < k := selectedSlopeFactor_pos flat hB
  obtain ⟨hroot, hlo, hhi, hsign⟩ := hcert.2 x hbase
  have hupdate : Function.update (normPt T j c u Q B l t) (3 : Fin 4) w =
      comparisonCurvePoint centre radius x w := by
    unfold comparisonCurvePoint
    rw [update_three_eq_snoc, ← normBase_eq_init,
      normBase_eq_center_add hradius.ne' B δ' (l, t)]
  have hnroot : eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (selectedSheetTest flat (normPoly T j c u Q B R)) = 0 := by rw [hupdate]; exact hroot
  have hnlo : 19 / 20 * |σ| ≤ |eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (pderiv 3 (selectedSheetTest flat (normPoly T j c u Q B R)))| := by rw [hupdate]; exact hlo
  have hnhi : |eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (pderiv 3 (selectedSheetTest flat (normPoly T j c u Q B R)))| ≤ 21 / 20 * |σ| := by
    rw [hupdate]; exact hhi
  have hnsign : 0 < eval (Function.update (normPt T j c u Q B l t) (3 : Fin 4) w)
      (pderiv 3 (selectedSheetTest flat (normPoly T j c u Q B R))) * σ := by rw [hupdate]; exact hsign
  obtain ⟨hphysroot, hphyslo, hphyshi, hphyssign⟩ := selected_root_physical_certificate
    flat hQ hB R l t w σ hnroot hnlo hnhi hnsign
  have habs : |k * σ| = k * |σ| := by rw [abs_mul, abs_of_pos hk]
  have hlow : 19 / 20 * |k * σ| ≤
      |eval (Function.update (gx l t) (3 : Fin 4) (w / B)) (pderiv 3 (selectedSheetTest flat R))| := by
    simpa only [habs] using hphyslo
  have hhigh :
      |eval (Function.update (gx l t) (3 : Fin 4) (w / B)) (pderiv 3 (selectedSheetTest flat R))| ≤
        21 / 20 * |k * σ| := by simpa only [habs] using hphyshi
  have hwindow := signed_window_of_abs hlow hhigh hphyssign
  have hbit : decide (0 ≤ k * σ) = decide (0 ≤ σ) := by
    by_cases hσ : 0 ≤ σ
    · simp only [hσ, mul_nonneg hk.le hσ]
    · have hneg : k * σ < 0 := mul_neg_of_pos_of_neg hk (not_le.mp hσ)
      simp only [hσ, not_le.mpr hneg]
  refine ⟨mul_pos hk hcert.1, ?_, ?_⟩
  · simpa only [update_three_eq_snoc] using hphysroot
  · simpa only [hbit, habs, update_three_eq_snoc] using hwindow

end Submission.Obl.k4_clean_cover_graph_atlas
