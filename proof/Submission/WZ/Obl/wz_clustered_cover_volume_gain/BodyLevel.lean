-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.BodyLevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyMultiplicity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- Integrating a lower level of the pointwise finite count bounds the union mass. -/
theorem body_level_mul_volume_le_mass {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) {M : ℝ}
    (hM : ∀ p ∈ ⋃ i, Y i, M ≤ ({i : Fin n | p ∈ Y i}.ncard : ℝ)) :
    ENNReal.ofReal M * volume (⋃ i, Y i) ≤ ∑ i, volume (Y i) := by
  classical
  calc
    _ = ∫⁻ p, (⋃ i, Y i).indicator (fun _ => ENNReal.ofReal M) p :=
      (lintegral_indicator_const (MeasurableSet.iUnion hY) _).symm
    _ ≤ ∫⁻ p, ∑ i, (Y i).indicator (fun _ => (1 : ENNReal)) p := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ ⋃ i, Y i
      · rw [indicator_of_mem hp]
        have hh := ENNReal.ofReal_le_ofReal (hM p hp)
        simpa [ncard_eq_toFinset_card', Set.indicator, Finset.sum_boole] using hh
      · rw [indicator_of_notMem hp]
        exact bot_le
    _ = _ := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_indicator_const (hY i), one_mul]
      · intro i _
        exact measurable_const.indicator (hY i)

/-- A lower union-volume bound for bodies yields the corresponding upper
multiplicity level. This only uses the uniform upper body volume. -/
theorem body_level_bound_of_union_lower {n : ℕ} {U Y : Fin n → Set Space}
    {w c M : ℝ} (hn : 0 < n) (hw : 0 < w) (hc : 0 < c) (hM : 0 ≤ M)
    (hY : ∀ i, MeasurableSet (Y i)) (hYU : ∀ i, Y i ⊆ U i)
    (hvolU : ∀ i, volume (U i) ≤ ENNReal.ofReal (384 * w))
    (hlevel : ∀ p ∈ ⋃ i, Y i, M ≤ ({i : Fin n | p ∈ Y i}.ncard : ℝ))
    (hvol : ENNReal.ofReal (c * (n * w)) ≤ volume (⋃ i, Y i)) :
    M ≤ 384 / c := by
  have hmass : ∑ i, volume (Y i) ≤ ENNReal.ofReal (384 * (n * w)) := by
    calc
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (384 * w) :=
        Finset.sum_le_sum fun i _ => (measure_mono (hYU i)).trans (hvolU i)
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hh : ENNReal.ofReal (M * (c * (n * w))) ≤ ENNReal.ofReal (384 * (n * w)) := by
    rw [ENNReal.ofReal_mul hM]
    exact (mul_le_mul_right hvol _).trans
      ((body_level_mul_volume_le_mass hY hlevel).trans hmass)
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hnw : 0 < (n : ℝ) * w := mul_pos (Nat.cast_pos.mpr hn) hw
  apply (le_div_iff₀ hc).mpr
  apply (mul_le_mul_iff_left₀ hnw).mp
  simpa only [mul_assoc] using hr

/-- The middle-scale multiplicity estimate for normalized convex bodies.
When `B` is their radius and `w` its square, the radius exponent is `-ω-σ`. -/
theorem convex_body_multiplicity {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (U Y : Fin n → Set Space)
        (x : Fin n → Space) (B w m : ℝ),
      0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → δ ≤ B → 0 < w → 1 ≤ m →
      BodyGeometry U x δ B w → (∀ i, U i ⊆ ball (0 : Space) 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ U i) →
      (∀ i, ENNReal.ofReal (δ ^ η) * volume (U i) ≤ volume (Y i)) →
      BodyConvexCount U w m → ∀ M : ℝ, 0 ≤ M →
      (∀ p ∈ ⋃ i, Y i, M ≤ ({i : Fin n | p ∈ Y i}.ncard : ℝ)) →
      M ≤ C * δ ^ (-ε) * B ^ (-ω) * m ^ (1 + σ / 2) * w ^ (-σ / 2) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ :=
    convex_body_estimate hσ hσhalf hω hE ε hε
  refine ⟨384 / A, η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n U Y x B w m hn hcount hδB hw hm hG hball hYm hYU hden hK M hM hlevel
  have hB : 0 < B := hδ.trans_le hδB
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  let c := A * δ ^ ε * B ^ ω * m ^ (-1 - σ / 2) * w ^ (σ / 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hv := H δ hδ hδd n U Y x B w m hn hcount hδB hw hm hG hball hYm hYU hden hK
  have hv' : ENNReal.ofReal (c * (n * w)) ≤ volume (⋃ i, Y i) := by
    convert hv using 1
    congr 1
    dsimp [c]
    rw [Real.rpow_add hw, Real.rpow_one]
    ring
  have hh := body_level_bound_of_union_lower hn hw hc hM hYm hYU
    (fun i => (hG.volume_bounds i).2) hlevel hv'
  apply hh.trans_eq
  dsimp only [c]
  rw [div_eq_mul_inv, mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev,
    ← Real.rpow_neg hw.le, ← Real.rpow_neg hm0.le,
    ← Real.rpow_neg hB.le, ← Real.rpow_neg hδ.le]
  rw [show -(-1 - σ / 2) = 1 + σ / 2 by ring, show -(σ / 2) = -σ / 2 by ring]
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
