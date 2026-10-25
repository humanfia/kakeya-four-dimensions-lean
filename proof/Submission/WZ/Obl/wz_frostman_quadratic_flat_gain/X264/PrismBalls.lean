-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PrismBalls.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Geometry
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PrismBalls.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

/-- Every point of a prism has a fixed fraction of an a-ball inside the prism. -/
lemma prism_inter_ball_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    {c e₁ e₂ e₃ p : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hp : p ∈ prism a b c e₁ e₂ e₃) :
    ENNReal.ofReal (a ^ 3 / 4000) ≤ volume (prism a b c e₁ e₂ e₃ ∩ ball p a) := by
  let t := inner ℝ e₃ (p - c)
  let s : ℝ := max (-(999 / 1000 : ℝ)) (min (999 / 1000) t)
  have ht : -1 ≤ t ∧ t ≤ 1 := abs_le.mp hp.2.2
  have hs : |s| ≤ 999 / 1000 := by
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hts : |t - s| ≤ 1 / 1000 := by
    by_cases hl : -(999 / 1000 : ℝ) ≤ t
    · by_cases hu : t ≤ 999 / 1000
      · have hs' : s = t := by simp [s, min_eq_right hu, max_eq_right hl]
        rw [hs', sub_self, abs_zero]
        norm_num
      · have hs' : s = 999 / 1000 := by
          simp [s, min_eq_left (le_of_not_ge hu), max_eq_right (by norm_num : -(999 / 1000 : ℝ) ≤ 999 / 1000)]
        rw [hs', abs_le]
        constructor <;> linarith [ht.1, ht.2]
    · have hs' : s = -(999 / 1000 : ℝ) := by
        have htl : t ≤ -(999 / 1000 : ℝ) := le_of_not_ge hl
        dsimp [s]
        rw [min_eq_right (htl.trans (by norm_num)), max_eq_left htl]
      rw [hs', abs_le]
      constructor <;> linarith [ht.1, ht.2]
  let c' := c + s • e₃
  have hin (q : Space) (k : Fin 3) :
      inner ℝ ((![e₁, e₂, e₃] : Fin 3 → Space) k) (q - c') =
        inner ℝ ((![e₁, e₂, e₃] : Fin 3 → Space) k) (q - c) -
          s * (if k = 2 then 1 else 0) := by
    have hvec : q - c' = (q - c) - s • e₃ := by dsimp [c']; abel
    rw [hvec, inner_sub_right, inner_smul_right]
    have h := orthonormal_iff_ite.mp he k 2
    change inner ℝ ((![e₁, e₂, e₃] : Fin 3 → Space) k) e₃ = _ at h
    rw [h]
  have h₁ (q : Space) : inner ℝ e₁ (q - c') = inner ℝ e₁ (q - c) := by
    simpa using hin q 0
  have h₂ (q : Space) : inner ℝ e₂ (q - c') = inner ℝ e₂ (q - c) := by
    simpa using hin q 1
  have h₃ (q : Space) : inner ℝ e₃ (q - c') = inner ℝ e₃ (q - c) - s := by
    simpa using hin q 2
  let Q := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism a b c' ![e₁, e₂, e₃]
  have hpQ : p ∈ Q := by
    change |inner ℝ e₁ (p - c')| ≤ a ∧ |inner ℝ e₂ (p - c')| ≤ b ∧
      |inner ℝ e₃ (p - c')| ≤ 1 / 1000
    rw [h₁, h₂, h₃]
    exact ⟨hp.1, hp.2.1, hts⟩
  have hQP : Q ⊆ prism a b c e₁ e₂ e₃ := by
    intro q hq
    change |inner ℝ e₁ (q - c')| ≤ a ∧ |inner ℝ e₂ (q - c')| ≤ b ∧
      |inner ℝ e₃ (q - c')| ≤ 1 / 1000 at hq
    rw [h₁, h₂, h₃] at hq
    refine ⟨hq.1, hq.2.1, ?_⟩
    have htri := abs_add_le (inner ℝ e₃ (q - c) - s) s
    rw [sub_add_cancel] at htri
    linarith [hq.2.2, hs]
  have hvol := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.volume_prism_inter_ball_ge
    ha.le (ha.le.trans hab) he hpQ ha
  have hm₁ : min a (a / 2) = a / 2 := min_eq_right (by linarith)
  have hm₂ : min b (a / 2) = a / 2 := min_eq_right (by linarith)
  have hm₃ : a / 1000 ≤ min (1 / 1000) (a / 2) := le_min (by linarith) (by linarith)
  rw [hm₁, hm₂] at hvol
  calc
    ENNReal.ofReal (a ^ 3 / 4000) ≤
        ENNReal.ofReal ((a / 2) * (a / 2) * min (1 / 1000) (a / 2)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (a / 2) * (a / 2) * (a / 1000) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hm₃ (by positivity)
    _ ≤ volume (Q ∩ ball p a) := hvol
    _ ≤ _ := measure_mono (Set.inter_subset_inter_left _ hQP)

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
