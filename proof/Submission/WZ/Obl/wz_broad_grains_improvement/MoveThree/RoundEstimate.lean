-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.RoundEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/RoundEstimate.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 7652d3d, RoundEstimate.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PackedEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.VolumeWidth

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube closedTube_compact closedTube_convex closedTube_endpoints
    closedTube_volume_bounds tube_subset_closedTube ball_subset_tube)

/-- Compact unit tubes satisfy the body geometry at every smaller base scale. -/
theorem round_body_geometry {n : ℕ} {δ R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hδR : δ ≤ R) (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, closedTube R (x i) (v i) ⊆ ball (0 : V) 1) :
    BodyGeometry (fun i => closedTube R (x i) (v i)) x δ (R / 16) (R ^ 2) := by
  have hc (i) := closedTube_compact ((tube_subset_closedTube R (x i) (v i)).trans (hball i))
  have hint (i) : ball (x i) R ⊆ closedTube R (x i) (v i) :=
    (ball_subset_tube (x i) (v i)).trans (tube_subset_closedTube R (x i) (v i))
  refine ⟨hc, fun i => closedTube_convex R (x i) (v i),
    fun i => (hball i).trans ball_subset_closedBall,
    fun i => (ball_subset_ball hδR).trans (hint i), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hx, hxv⟩ := closedTube_endpoints hR (x i) (v i)
    refine ⟨x i, hx, x i + v i, hxv, ?_⟩
    simp [dist_eq_norm, hv i] <;> norm_num
  · intro i
    have H := WangZahlLot.Obl.wz_clustered_cover_volume_gain.wideSection_of_volume
      (hc i) (closedTube_convex R (x i) (v i)) hR (hint i)
      ((hball i).trans ball_subset_closedBall) (sq_pos_of_pos hR)
      (closedTube_volume_bounds hR hR1 (x i) (v i) (hv i)).1
    simpa only [Real.sqrt_sq hR.le] using H
  · exact fun i => closedTube_volume_bounds hR hR1 (x i) (v i) (hv i)

/-- Convex counting passes from whole fine bodies to their equal, disjoint carrier
fibres. Closing the carriers does not increase the count. -/
theorem balanced_carrier_convex_count {n N q : ℕ} {U : Fin n → Set V}
    {w M R : ℝ} (hw : 0 < w) (hM : 0 ≤ M) (hR : 0 < R) (hq : 0 < q)
    (x v : Fin N → V) (F : Fin N → Finset (Fin n))
    (hcard : ∀ j, (F j).card = q) (hdisj : ∀ j k, j ≠ k → Disjoint (F j) (F k))
    (hwhole : ∀ j, ∀ i ∈ F j, U i ⊆ T R (x j) (v j))
    (hK : BodyConvexCount U w M) :
    BodyConvexCount (fun j => closedTube R (x j) (v j)) (R ^ 2)
      (M * R ^ 2 / ((q : ℝ) * w)) := by
  have H := body_convex_transfer hw hM (by norm_num : (0 : ℝ) < 1) hR hq
    (AffineEquiv.refl ℝ V) x v F hcard hdisj
    (by simpa using hwhole) (by intro Q; simp) hK
  intro Q hQ
  have hcount : Set.ncard {i | closedTube R (x i) (v i) ⊆ Q} ≤
      Set.ncard {i | T R (x i) (v i) ⊆ Q} :=
    ncard_mono (fun i hi => (tube_subset_closedTube R (x i) (v i)).trans hi)
  apply (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) (sq_nonneg R))).trans
  simpa only [mul_one] using H Q hQ

/-- Independent packing of the new round carriers turns saturated convex count
into a positive power of its coefficient. -/
theorem saturated_round_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (N : ℕ) (x v : Fin N → V)
        (Y : Fin N → Set V) (R M τ : ℝ),
      0 < N → (N : ℝ) ≤ δ ^ (-100 : ℝ) → 16 * δ ≤ R → R ≤ 1 → 1 ≤ M → 0 < τ →
      (∀ i, ‖v i‖ = 1) → (∀ i, closedTube R (x i) (v i) ⊆ ball (0 : V) 1) →
      X R N x v → (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ closedTube R (x i) (v i)) →
      (∀ i, O (δ ^ η) * μ (closedTube R (x i) (v i)) ≤ μ (Y i)) →
      BodyConvexCount (fun i => closedTube R (x i) (v i)) (R ^ 2) M →
      τ * M ≤ (N : ℝ) * R ^ 2 →
      O (A * τ * δ ^ ε * R ^ (ω + σ) * M ^ (σ / 2)) ≤ μ (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, HE⟩ :=
    packed_convex_body_estimate (body_estimate_of_tube_estimate hσ hσhalf hω hE) ε hε
  refine ⟨A * (16 : ℝ) ^ (-ω) * (1000 : ℝ) ^ (-σ), η, d₀,
    by positivity, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd N x v Y R M τ hN hNmax hδR hR1 hM hτ hv hball hX hYm hYU hden hK hsat
  have hR : 0 < R := (by positivity : 0 < 16 * δ).trans_le hδR
  have hgeom := round_body_geometry hR hR1 (by linarith : δ ≤ R) x v hv hball
  have H := HE δ hδ hδd N (fun i => closedTube R (x i) (v i)) Y x
    (R / 16) (R ^ 2) M 1000 hN hNmax (by linarith) (sq_pos_of_pos hR) hM
    (by norm_num) hgeom hball hYm hYU hden hK (closedTube_packing hR x v hv hX)
  have hscalar0 := saturated_packed_body_scalar hA.le hδ.le
    (by positivity : 0 ≤ R / 16) (zero_lt_one.trans_le hM)
    (by norm_num : (0 : ℝ) < 1000) (sq_pos_of_pos hR) (by norm_num : (0 : ℝ) < 1)
    (show M * τ ≤ 1 * (N : ℝ) * R ^ 2 by nlinarith only [hsat])
    (σ := σ) (ω := ω) (A := A) (ε := ε)
  have hscalar : A * τ * δ ^ ε * (R / 16) ^ ω * M ^ (σ / 2) *
      (1000 : ℝ) ^ (-σ) * (R ^ 2) ^ (σ / 2) * 1 ≤
      A * δ ^ ε * (R / 16) ^ ω * M ^ (-1 + σ / 2) * (1000 : ℝ) ^ (-σ) *
        (N : ℝ) * (R ^ 2) ^ (1 + σ / 2) := by
    convert hscalar0 using 1 <;> ring
  apply (ENNReal.ofReal_le_ofReal (show
    (A * (16 : ℝ) ^ (-ω) * (1000 : ℝ) ^ (-σ)) * τ * δ ^ ε *
      R ^ (ω + σ) * M ^ (σ / 2) ≤ _ from ?_)).trans H
  apply le_trans (le_of_eq ?_) hscalar
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow,
    Real.log_one]
  ring

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
