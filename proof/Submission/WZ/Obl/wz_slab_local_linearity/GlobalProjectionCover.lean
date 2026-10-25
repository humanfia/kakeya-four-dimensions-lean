-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.GlobalProjectionCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.TotalCover
import Submission.WZ.Obl.wz_slab_local_linearity.CoverUpper
import Submission.WZ.Obl.wz_slab_local_linearity.CubeHeights

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set

lemma global_projection_bound {s z₀ c₀ : ℝ} {f : ℝ → ℝ} {p : Space3}
    (hy : |p 1| ≤ 1) (hz : p 2 ∈ Icc z₀ (z₀ + s))
    (hf : |f (p 2) - f z₀| ≤ |p 2 - z₀|)
    (hstrip : |p 0 + f z₀ * p 1 - c₀| ≤ s) :
    |p 0 + f (p 2) * p 1 - c₀| ≤ 2 * s := by
  have hdist : |p 2 - z₀| ≤ s := by rw [abs_of_nonneg (sub_nonneg.mpr hz.1)]; linarith [hz.2]
  have hh : |(f (p 2) - f z₀) * p 1| ≤ s := by
    rw [abs_mul]
    calc |f (p 2) - f z₀| * |p 1| ≤ |f (p 2) - f z₀| * 1 :=
          mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ ≤ s := by simpa only [mul_one] using hf.trans hdist
  have he : p 0 + f (p 2) * p 1 - c₀ =
      (p 0 + f z₀ * p 1 - c₀) + (f (p 2) - f z₀) * p 1 := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

/-- The global slab width turns the slice AD hypothesis into a uniform cover. -/
theorem global_slice_cover {ρ s z₀ c₀ α C z : ℝ} {E : Set Space3} {f : ℝ → ℝ}
    (hscale : ρ ≤ 4 * s)
    (hf : ∀ x ∈ Icc z₀ (z₀ + s), ∀ y ∈ Icc z₀ (z₀ + s), |f x - f y| ≤ |x - y|)
    (hE : ∀ p ∈ E, |p 1| ≤ 1 ∧ p 2 ∈ Icc z₀ (z₀ + s) ∧
      |p 0 + f z₀ * p 1 - c₀| ≤ s)
    (hAD : IntervalAD ρ α C {u : ℝ | ∃ p ∈ E, p 2 = z ∧ u = p 0 + f z * p 1}) :
    CoverUpper {u : ℝ | ∃ p ∈ E, p 2 = z ∧ u = p 0 + f z * p 1}
      ρ (C * (4 * s / ρ) ^ α) := by
  apply hAD.cover_bounded hscale (a := c₀ - 2 * s)
  intro u hu
  obtain ⟨p, hp, hpz, rfl⟩ := hu
  obtain ⟨hy, hz, hstrip⟩ := hE p hp
  have hs : 0 ≤ s := by linarith [hz.1, hz.2]
  have hh := global_projection_bound hy hz (hf _ hz _ ⟨le_rfl, by linarith⟩) hstrip
  rw [hpz, abs_le] at hh
  constructor <;> linarith [hh.1, hh.2]

end WangZahlLot.Obl.wz_slab_local_linearity
