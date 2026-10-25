-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.VolumeRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.VolumeWidth

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- A convex family of fixed long diameter can be refined using its volume weight
alone. The exponent of the weight is half the desired middle-radius exponent. -/
theorem convex_body_refinement_of_volume {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (w m D : ℝ),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → 256 * δ ^ 2 ≤ w → 1 ≤ m → 0 < D →
      1536 * δ ^ η ≤ D →
      (∀ i, IsCompact (U i)) → (∀ i, Convex ℝ (U i)) → (∀ i, U i ⊆ ball (0 : Space) 1) →
      (∀ i, ball (x i) δ ⊆ U i) →
      (∀ i, ∃ p ∈ U i, ∃ q ∈ U i, (1 / 16 : ℝ) ≤ dist p q) →
      (∀ i, ENNReal.ofReal w ≤ volume (U i) ∧ volume (U i) ≤ ENNReal.ofReal (384 * w)) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      ENNReal.ofReal (D * n * w) ≤ ∑ i, volume (Y i) → BodyConvexCount U w m →
      ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ C * δ ^ (-ε) * D⁻¹ * m ^ (1 + σ / 2) * w ^ (-(ω + σ) / 2) := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    convex_body_refinement hσ hσhalf hω hE ε hε
  refine ⟨C * (16 : ℝ) ^ ω, η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x w m D hn hcount hscale hm hD htD hUc hU hball hint hdiam hvol hYm hYU hden hK
  have hw : 0 < w := (by positivity : 0 < 256 * δ ^ 2).trans_le hscale
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hsqrt : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hwidth : δ ≤ Real.sqrt w / 16 := by
    have hh := Real.sq_sqrt hw.le
    nlinarith
  have hG : BodyGeometry U x δ (Real.sqrt w / 16) w := {
    compact := hUc, convex := hU,
    bounded := fun i => (hball i).trans ball_subset_closedBall,
    interior := hint, diameter := hdiam,
    width := fun i => wideSection_of_volume (hUc i) (hU i) hδ (hint i)
      ((hball i).trans ball_subset_closedBall) hw (hvol i).1,
    volume_bounds := hvol }
  obtain ⟨Z, hZY, hmass, hmult⟩ := H δ hδ hδd n U Y x (Real.sqrt w / 16) w m D
    hn hcount hwidth hw hm hD htD hG hball hYm hYU hden hK
  refine ⟨Z, hZY, hmass, fun p => (hmult p).trans_eq ?_⟩
  rw [Real.sqrt_eq_rpow]
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_inv]
  ring

/-- A lower volume weight equal to a squared radius preserves the middle exponent. -/
theorem volume_radius_factor {w δ r C D m σ ω ε v : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 ≤ D) (hm : 0 ≤ m)
    (hσ : 0 ≤ σ) (hω : 0 ≤ ω) (hw : δ ^ v * r ^ 2 ≤ w) :
    C * δ ^ (-ε) * D⁻¹ * m ^ (1 + σ / 2) * w ^ (-(ω + σ) / 2) ≤
      C * δ ^ (-(ε + v * (ω + σ) / 2)) * D⁻¹ * m ^ (1 + σ / 2) * r ^ (-ω - σ) := by
  have hwp : 0 < w := (by positivity : 0 < δ ^ v * r ^ 2).trans_le hw
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < δ ^ v * r ^ 2) hw
    (by linarith : -(ω + σ) / 2 ≤ 0)
  apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq
  have he : δ ^ (-ε) * (δ ^ v * r ^ 2) ^ (-(ω + σ) / 2) =
      δ ^ (-(ε + v * (ω + σ) / 2)) * r ^ (-ω - σ) := by
    apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
      (by simp only [mem_Ioi]; positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow]
    ring
  calc
    _ = C * D⁻¹ * m ^ (1 + σ / 2) *
        (δ ^ (-ε) * (δ ^ v * r ^ 2) ^ (-(ω + σ) / 2)) := by ring
    _ = _ := by rw [he]; ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
