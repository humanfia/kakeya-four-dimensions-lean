import Submission.Obl.k4_finite_affine_parent_sources.SourceWindowGeometry

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- Every clamped source depth precedes its original window's intermediate level. -/
theorem TangentWindows.source_depth_range {m : ℕ} {sg : ℕ → ℝ} {D unit mesh : ℝ}
    (q : TangentWindows m sg D unit mesh) (hu : 0 ≤ unit)
    (hstrict : StrictMonoOn sg (Iio m)) {i : ℕ} (hi : i < q.count) (x : ℝ) :
    q.level i ≤ sourceDepth m sg (q.level i) unit x ∧
      sourceDepth m sg (q.level i) unit x ≤ q.middle i := by
  have hm : 0 < m := Nat.zero_lt_of_lt (q.level_lt i)
  refine ⟨sourceDepth_ge sg (q.level_lt i) hu x, ?_⟩
  apply q.model_level_le_middle (fun j k hjk hkm =>
    hstrict (lt_trans hjk hkm) hkm hjk) hi (sourceDepth_lt hm sg _ _ _)
  have hcl0 : 0 ≤ max 0 (min x 1) := le_max_left _ _
  have hcl1 : max 0 (min x 1) ≤ 1 := max_le (by norm_num) (min_le_right _ _)
  have hbase : sg (q.level i) ≤ sg (q.level i) + unit * max 0 (min x 1) := by
    nlinarith
  have ht := gridDepth_le_target (q.level_lt i) hbase
  change sg (gridDepth m sg (sg (q.level i) + unit * max 0 (min x 1))) ≤ _
  exact ht.trans (by nlinarith)

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → MeasureTheory.Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The original parent and intermediate depths, and every tested composed depth,
remain inside the original density grid's domain. -/
theorem sample_window_depth_room {D unit mesh T : ℝ}
    (q : TangentWindows m sg D unit mesh)
    (hstrict : StrictMonoOn sg (Iio m)) (hL : 0 ≤ L)
    (hu : 0 ≤ unit) (hu1 : unit ≤ 1 / 64) (hδ : δ₀ ≤ 1 / 64)
    (hT : 0 ≤ T) (hTu : unit * T ≤ 1 / 64)
    {i : ℕ} (hi : i < q.count) :
    (0 ≤ p.r (q.middle i) ∧ p.r (q.middle i) ≤ L) ∧
      p.r (q.level (i + 1)) + 2 * (unit / 100) * L ≤ L ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ T →
        0 ≤ p.r (q.level i) + unit * L * t ∧
          p.r (q.level i) + unit * L * t ≤ L) := by
  have hmid : sg (q.middle i) ≤ 1 / 4 :=
    (hstrict.monotoneOn (q.middle_lt i hi) (q.level_lt (i + 1)) (q.between i hi).2).trans
      (q.parent_band (i + 1)).2
  have hparent := abs_le.mp (hp.level_bounds (q.level i) (q.level_lt i)).1
  have hmiddle := abs_le.mp (hp.level_bounds (q.middle i) (q.middle_lt i hi)).1
  have hend := abs_le.mp (hp.level_bounds (q.level (i + 1)) (q.level_lt (i + 1))).1
  have hδL := mul_le_mul_of_nonneg_right hδ hL
  have hmidL := mul_le_mul_of_nonneg_right hmid hL
  have hparL := mul_le_mul_of_nonneg_right (q.parent_band i).2 hL
  have hendL := mul_le_mul_of_nonneg_right (q.parent_band (i + 1)).2 hL
  have huL := mul_le_mul_of_nonneg_right hu1 hL
  refine ⟨⟨(hp.level_bounds _ (q.middle_lt i hi)).2.1.le, by nlinarith⟩,
    by nlinarith, ?_⟩
  intro t ht0 htT
  have htu : unit * t ≤ unit * T := mul_le_mul_of_nonneg_left htT hu
  have htL := mul_le_mul_of_nonneg_right (htu.trans hTu) hL
  exact ⟨add_nonneg (hp.level_bounds _ (q.level_lt i)).2.1.le
    (mul_nonneg (mul_nonneg hu hL) ht0), by nlinarith⟩

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
