-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.SlabFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ClusteredFilling
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

theorem prism_neighborhood_in_slab {a b R : ℝ} (hR : 0 ≤ R)
    {c c₀ y p : V} {u u₀ : Fin 3 → V}
    (hy₀ : y ∈ prism a b c₀ u₀) (hy : y ∈ prism a b c u)
    (hp : p ∈ prism a b c u) (hd : dist p y ≤ b)
    (hangle : pd (u₀ 0) (u 0) ≤ R) :
    |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + R * b := by
  have hshort : |inner ℝ (u 0) (p - y)| ≤ 2 * a := by
    have hh := abs_sub (inner ℝ (u 0) (p - c)) (inner ℝ (u 0) (y - c))
    have he : inner ℝ (u 0) (p - c) - inner ℝ (u 0) (y - c) =
        inner ℝ (u 0) (p - y) := by simp only [inner_sub_right]; ring
    rw [he] at hh
    linarith [hp.1, hy.1]
  have hn : ‖p - y‖ ≤ b := by simpa only [dist_eq_norm] using hd
  have hm := mul_le_mul hangle hn (norm_nonneg _) hR
  have hi := abs_inner_le_projective (u₀ 0) (u 0) (p - y)
  have he : inner ℝ (u₀ 0) (p - c₀) =
      inner ℝ (u₀ 0) (p - y) + inner ℝ (u₀ 0) (y - c₀) := by
    simp only [inner_sub_right]
    ring
  rw [he]
  have hh := abs_add_le (inner ℝ (u₀ 0) (p - y)) (inner ℝ (u₀ 0) (y - c₀))
  change min ‖u₀ 0 - u 0‖ ‖u₀ 0 + u 0‖ * ‖p - y‖ ≤ R * b at hm
  linarith [hy₀.1]

/-- Clustered transverse filling takes place in the thin slab determined by
the upper angular bound. For `R` comparable to `θ` and `a ≤ b*θ`, both the
volume lower bound and the containing slab have one factor of `θ`. -/
theorem clustered_slab_filling {n : ℕ} (K : Finset (Fin n))
    {a b h θ r R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r) (hR : 0 ≤ R)
    (c : Fin n → V) (u : Fin n → Fin 3 → V) (H : Fin n → Set V)
    (c₀ x w v : V) (u₀ : Fin 3 → V) (A : Set V)
    (hu : ∀ i ∈ K, Orthonormal ℝ (u i))
    (hHm : ∀ i ∈ K, MeasurableSet (H i))
    (hHU : ∀ i ∈ K, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i ∈ K, ∀ p ∈ H i,
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hframe : Orthonormal ℝ ![u₀ 0, w, v])
    (hA : A ⊆ prism a b c₀ u₀ ∩ ball x b)
    (hcover : A ⊆ ⋃ i ∈ K, H i) (hmass : O (r * a * b ^ 2) ≤ μ A)
    (htrans : ∀ i ∈ K, θ / 4 ≤ inner ℝ (sgnNormal (u i 0)) v)
    (hclose : ∀ i ∈ K, ∀ j ∈ K, ‖sgnNormal (u i 0) - sgnNormal (u j 0)‖ ≤ θ / 4)
    (hangle : ∀ i ∈ K, pd (u₀ 0) (u i 0) ≤ R) :
    O (r * h ^ 2 * θ * b ^ 3 / (409600000 * (1 + Real.log (b / a)))) ≤
      μ ({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + R * b} ∩
        (ball x (2 * b) ∩ ⋃ i ∈ K, H i)) := by
  have hslab : MeasurableSet {p : V | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + R * b} :=
    (isClosed_le ((continuous_const.inner (continuous_id.sub continuous_const)).abs)
      continuous_const).measurableSet
  apply clustered_filling_in_container K ha hab hb hh hθ hθ1 hr c u H c₀ x w v u₀ A _
    hu hHm hHU hregular hu₀ hframe hA hcover hmass htrans hclose
    (hslab.inter (measurableSet_ball.inter (Finset.measurableSet_biUnion K hHm)))
    (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (inter_subset_right.trans inter_subset_left)))
  intro i hi y hyA hyH p hp
  refine ⟨prism_neighborhood_in_slab hR (hA hyA).1 (hHU _ hi hyH) (hHU _ hi hp.1)
    (Metric.mem_ball.mp hp.2).le (hangle i hi), ?_, mem_iUnion₂.mpr ⟨i, hi, hp.1⟩⟩
  have hp' : dist p y < b := hp.2
  have hy' : dist y x < b := (hA hyA).2
  change dist p x < 2 * b
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
