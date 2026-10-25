-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.BodyMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyEstimate
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyTransport

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- The convex count also bounds the square-root count used by the body estimate. -/
theorem packing_of_convex_count {n : ℕ} {U : Fin n → Set Space} {w m : ℝ}
    (hw : 0 ≤ w) (hc : BodyConvexCount U w m) : BodyPacking U w m := by
  intro Q hQ
  apply (ENNReal.ofReal_le_ofReal _).trans (hc Q hQ)
  apply mul_le_mul_of_nonneg_right _ hw
  let k := Set.ncard {i | U i ⊆ Q}
  change Real.sqrt (k : ℝ) ≤ k
  by_cases hk : k = 0
  · simp [hk]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, by nlinarith⟩

/-- Testing a slab count on a slab containing the unit ball normalizes its coefficient. -/
theorem body_slab_coefficient_ge_one {n : ℕ} (hn : 0 < n)
    {U : Fin n → Set Space} {l : ℝ}
    (hball : ∀ i, U i ⊆ ball (0 : Space) 1) (hl : 0 ≤ l)
    (hslab : BodySlabCount U l) : 1 ≤ l := by
  let u : Space := EuclideanSpace.single 0 1
  have hu : ‖u‖ = 1 := by simp [u]
  have hset : {i : Fin n | U i ⊆ {p | |inner ℝ u p - 0| ≤ 1}} = univ := by
    apply eq_univ_of_forall
    intro i p hp
    have hp1 : ‖p‖ < 1 := by simpa using hball i hp
    simp only [sub_zero]
    calc
      |inner ℝ u p| ≤ ‖u‖ * ‖p‖ := abs_real_inner_le_norm u p
      _ ≤ 1 := by simpa only [hu, one_mul] using hp1.le
  have hh := hslab u 0 1 hu zero_lt_one
  rw [hset] at hh
  simp only [ncard_univ, Nat.card_fin, mul_one] at hh
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ l * n)).mp hh
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  nlinarith

/-- The Frostman coefficient supplied by convex counting cancels the body count
from the nonlinear factor. -/
theorem body_weight_of_convex_count {σ w m n : ℝ}
    (hw : 0 < w) (hm : 0 < m) (hn : 0 < n) :
    bodyWeight σ w m (8 * m / (w * n)) m n =
      (8 : ℝ) ^ (-σ) * m ^ (-1 - σ / 2) * n * w ^ (1 + σ / 2) := by
  unfold bodyWeight
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

/-- `E` for normalized convex bodies needs only a convex count. No separation or
independent Frostman hypothesis is required in this form. -/
theorem convex_body_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (B w m : ℝ),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m →
      BodyGeometry U x δ B w → (∀ i, U i ⊆ ball (0 : Space) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      (∀ i, ENNReal.ofReal (δ ^ η) * volume (U i) ≤ volume (Y i)) →
      BodyConvexCount U w m →
      ENNReal.ofReal (A * δ ^ ε * B ^ ω * m ^ (-1 - σ / 2) * n * w ^ (1 + σ / 2)) ≤
        volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ :=
    body_estimate_of_tube_estimate hσ hσhalf hω hE ε hε
  refine ⟨A * (8 : ℝ) ^ (-σ), η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x B w m hn hcount hδB hw hm hG hball hYm hYU hden hK
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hslab := body_slab_of_convex_count hn hw hm0.le hball hK
  have hl := body_slab_coefficient_ge_one hn hball (by positivity) hslab
  have hbound := H δ hδ hδd n U Y x B w m (8 * m / (w * n)) m
    hn hcount hδB hw hm hl hm hG hYm hYU hden hK hslab (packing_of_convex_count hw.le hK)
  rw [body_weight_of_convex_count hw hm0 hn0] at hbound
  convert hbound using 1 <;> congr 1 <;> ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
