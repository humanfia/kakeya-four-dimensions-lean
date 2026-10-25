-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.SquareRootPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyMultiplicity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- A lower volume bound improves the square-root packing coefficient from
`m` to `sqrt m`. This is useful when bodies are enlarged before applying E. -/
theorem sqrt_packing_of_convex_count {n : ℕ} {U : Fin n → Set Space} {w m : ℝ}
    (hw : 0 < w) (hm : 0 < m) (hvol : ∀ i, ENNReal.ofReal w ≤ volume (U i))
    (hc : BodyConvexCount U w m) : BodyPacking U w (Real.sqrt m) := by
  classical
  intro Q hQ
  have hm0 : ENNReal.ofReal (Real.sqrt m) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hm))
  by_cases hQtop : volume Q = ⊤
  · simp [hQtop, ENNReal.mul_top, hm0]
  let S : Set (Fin n) := {i | U i ⊆ Q}
  by_cases hk : S.ncard = 0
  · change ENNReal.ofReal (Real.sqrt (S.ncard : ℝ) * w) ≤ _
    simp [hk]
  obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero hk
  have hwV : w ≤ (volume Q).toReal := (ENNReal.ofReal_le_iff_le_toReal hQtop).mp
    ((hvol i).trans (measure_mono hi))
  have hcount : (S.ncard : ℝ) * w ≤ m * (volume Q).toReal := by
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQtop) (hc Q hQ)
    change (ENNReal.ofReal ((S.ncard : ℝ) * w)).toReal ≤
      (ENNReal.ofReal m * volume Q).toReal at ht
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (S.ncard : ℝ) * w),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.le] using ht
  have hs : Real.sqrt (S.ncard : ℝ) * w ≤ Real.sqrt m * (volume Q).toReal := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      _ = (S.ncard : ℝ) * w ^ 2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _) ]
      _ ≤ m * (volume Q).toReal ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_right hcount hw.le
        have h2 := mul_le_mul_of_nonneg_left hwV
          (mul_nonneg hm.le ENNReal.toReal_nonneg : 0 ≤ m * (volume Q).toReal)
        nlinarith
      _ = _ := by rw [mul_pow, Real.sq_sqrt hm.le]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt m * (volume Q).toReal) := ENNReal.ofReal_le_ofReal hs
    _ = _ := by rw [ENNReal.ofReal_mul (Real.sqrt_nonneg m), ENNReal.ofReal_toReal hQtop]

theorem body_weight_sqrt_packing {σ w m l n : ℝ}
    (hw : 0 < w) (hm : 0 < m) (hl : 0 < l) (hn : 0 < n) :
    bodyWeight σ w m l (Real.sqrt m) n =
      m ^ (-1 + σ) * l ^ (-σ) * n ^ (1 - σ) * w ^ (1 - σ / 2) := by
  unfold bodyWeight
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_sqrt]
  ring

/-- Enlargement gains a power of the ratio of body volumes; the original
count coefficient appears separately and is small in the intended use. -/
theorem enlarged_body_weight {σ w W m l n : ℝ}
    (hw : 0 < w) (hW : 0 < W) (hm : 0 < m) (hl : 0 < l) (hn : 0 < n) :
    bodyWeight σ W (m * W / w) l (Real.sqrt (m * W / w)) n =
      m ^ (-1 + σ) * l ^ (-σ) * n ^ (1 - σ) * w ^ (1 - σ / 2) * (W / w) ^ (σ / 2) := by
  rw [body_weight_sqrt_packing hW (by positivity) hl hn]
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
