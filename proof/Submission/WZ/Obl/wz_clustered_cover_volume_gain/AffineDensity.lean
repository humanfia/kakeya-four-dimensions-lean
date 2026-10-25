-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AffineDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)

lemma upper_ball_density_mass {F U E : Set Space} {r lam : ℝ}
    (hr : 0 < r) (hF : TotallyBounded F) (hE : MeasurableSet E) (hFU : F ⊆ U)
    (hupper : ∀ p ∈ F, volume (U ∩ ball p r) ≤ ENNReal.ofReal (lam * r ^ 3))
    (hballs : ∀ p ∈ F, ball p (r / 4) ⊆ E) :
    volume F ≤ ENNReal.ofReal (64 * lam) * volume E := by
  have hglobal := local_mass_to_global (E := E) (show 0 < r / 8 by positivity) hF hE
    (m := ENNReal.ofReal (lam * r ^ 3)) (q := ENNReal.ofReal ((r / 4) ^ 3))
    (by
      intro x hx
      apply le_trans (measure_mono ?_) (hupper x hx)
      intro y hy
      refine ⟨hFU hy.1, ?_⟩
      have hh : dist y x ≤ 4 * (r / 8) := hy.2
      change dist y x < r
      linarith)
    (by
      intro x hx
      apply (ball_volume_lower x (show 0 ≤ r / 4 by positivity)).trans
      apply measure_mono
      intro y hy
      refine ⟨hballs x hx hy, ?_⟩
      change dist y x < 2 * (r / 8)
      change dist y x < r / 4 at hy
      linarith)
  have hq : 0 < ENNReal.ofReal ((r / 4) ^ 3) := ENNReal.ofReal_pos.mpr (by positivity)
  apply (ENNReal.mul_le_mul_iff_right hq.ne' ENNReal.ofReal_ne_top).mp
  convert hglobal using 1
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (r / 4) ^ 3)]
  congr 2
  ring

/-- Local density is measured in the physical metric, while a convenient
box may be described after an affine normalization. -/
lemma affine_ball_density_mass_in_box {F U : Set Space} {r lam L : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L) (hF : TotallyBounded F) (hFU : F ⊆ U)
    (f : Space ≃ᵃ[ℝ] Space) (w : Fin 3 → ℝ) (c : Space)
    (u : OrthonormalBasis (Fin 3) ℝ Space)
    (hLip : ∀ p q, dist (f.symm p) (f.symm q) ≤ L * dist p q)
    (hbox : F ⊆ f '' orthogonalBox w c u)
    (hupper : ∀ p ∈ F, volume (U ∩ ball p r) ≤ ENNReal.ofReal (lam * r ^ 3)) :
    volume F ≤ ENNReal.ofReal (64 * lam) *
      volume (f '' orthogonalBox (fun j => w j + L * r) c u) := by
  apply upper_ball_density_mass hr hF
    (f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (orthogonalBox_closed _ _ _).measurableSet) hFU hupper
  intro p hp q hq
  have hpbox : f.symm p ∈ orthogonalBox w c u := by
    obtain ⟨p', hp', rfl⟩ := hbox hp
    simpa using hp'
  refine ⟨f.symm q, ?_, f.apply_symm_apply q⟩
  intro j
  have he : f.symm q - c = (f.symm q - f.symm p) + (f.symm p - c) := by abel
  rw [he, inner_add_right]
  have hi := abs_real_inner_le_norm (u j) (f.symm q - f.symm p)
  rw [u.norm_eq_one, one_mul, ← dist_eq_norm] at hi
  have hd : dist q p ≤ r := (show dist q p < r / 4 from hq).le.trans (by linarith)
  have hh := (hLip q p).trans (mul_le_mul_of_nonneg_left hd hL)
  exact (abs_add_le _ _).trans (by linarith [hpbox j])

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
