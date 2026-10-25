-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.AssemblyHelpers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Packets
import Submission.WZ.Obl.wz_separated_scales_gain.Padding
import Submission.WZ.Obl.wz_separated_scales_gain.MiddleCells
import Submission.WZ.Obl.wz_separated_scales_gain.UniformFine
import Submission.WZ.Obl.wz_separated_scales_gain.UniformOuter
import Submission.WZ.Obl.wz_separated_scales_gain.ProductWeights

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- The explicit scalar hypotheses used to apply the three estimates. -/
structure ScaleConditions (δ τ ρ lam θ L R ηF ηM ηO : ℝ) (K : ℕ) : Prop where
  fineCut : 288 * θ ^ K * τ ^ 2 ≤ lam * δ ^ 2 / 2
  middleCut : 288 * θ ^ K * ρ ^ 2 ≤ (lam / (2048 * K)) * τ ^ 2 / 2
  fineDensity : δ / τ ≤ R → (fineRadius δ τ) ^ ηF ≤ fineContraction * lam / (64 * K)
  middleDensity : (fineRadius τ ρ) ^ ηM ≤ fineContraction * (lam / (2048 * K)) / (64 * K)
  middleConvex : 16 * L / fineContraction ≤ (fineRadius τ ρ) ^ (-ηM)
  middleSlab : 224 * K * L ^ 2 / (fineContraction ^ 3 * retainedFraction * (lam / (2048 * K))) ≤
    (fineRadius τ ρ) ^ (-ηM)
  outerDensity : ρ ≤ R → (fineRadius ρ 1) ^ ηO ≤
    fineContraction * (lam / (2048 * K) / (2048 * K)) / 16

theorem paddedShading_density {b lam : ℝ} (hb : 0 < b) {K : ℕ}
    (s : Finset (Fin 3 → ℤ)) (x v : Space)
    (hmeet : ∀ z ∈ s, (tube b x v ∩ gridCell b z).Nonempty)
    (hmass : ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s)) :
    ENNReal.ofReal (lam / (2048 * K) * b ^ 2) ≤ volume (paddedShading b s x v) := by
  have hh := hmass.trans (grid_volume_le_paddedShading hb s x v hmeet)
  have he : lam / (32 * K) * b ^ 2 = 64 * (lam / (2048 * K) * b ^ 2) := by ring
  rw [he] at hh
  exact ofReal_cancel_factor (by norm_num : (0 : ℝ) < 64) (by simpa using hh)

theorem middle_slab_bound {τ ρ L lam M : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ)
    (hL : 0 < L) (hlam : 0 < lam) (hM : 0 < M) {K : ℕ} (hK : 0 < K)
    (hsat : L⁻¹ ≤ M * (τ / ρ) ^ 2) :
    L / (τ ^ 2 * (fineContraction ^ 3 * ρ⁻¹ ^ 2) *
      (retainedFraction * (lam / (224 * K) * M))) ≤
      224 * K * L ^ 2 / (fineContraction ^ 3 * retainedFraction * lam) := by
  have hκ : 0 < fineContraction := by norm_num
  have hfrac := retainedFraction_pos
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have he : τ ^ 2 * (fineContraction ^ 3 * ρ⁻¹ ^ 2) *
      (retainedFraction * (lam / (224 * K) * M)) =
      (fineContraction ^ 3 * retainedFraction * lam / (224 * K)) * (M * (τ / ρ) ^ 2) := by
    field_simp
  rw [he]
  calc
    _ ≤ L / ((fineContraction ^ 3 * retainedFraction * lam / (224 * K)) * L⁻¹) := by
      apply div_le_div_of_nonneg_left hL.le (by positivity)
      exact mul_le_mul_of_nonneg_left hsat (by positivity)
    _ = _ := by field_simp

/-- The dependence of the middle weight on cardinality is increasing for sigma at most one. -/
theorem middle_weight_mono {N M r σ : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hNM : N ≤ M) (hσ1 : σ ≤ 1) :
    (N * r ^ 2) * (N * r) ^ (-σ) ≤ (M * r ^ 2) * (M * r) ^ (-σ) := by
  have hh := count_power_mono hr hN hNM hσ1
  have hp := mul_le_mul_of_nonneg_right hh (sq_nonneg r)
  simpa only [mul_comm, mul_left_comm, mul_assoc] using (show
    N * (r * N) ^ (-σ) * r ^ 2 ≤ M * (r * M) ^ (-σ) * r ^ 2 from hp)

/-- Choose the actual minimum fibre, retaining any uniform lower cardinality bound. -/
theorem balanced_cover_minimum_lower {n q : ℕ} (hq : 0 < q) (R : Fin n → Fin q → Prop)
    {D a : ℝ} (hD : 0 ≤ D) (hcover : ∀ i, ∃ j, R i j)
    (hpos : ∀ j, 0 < Set.ncard {i | R i j})
    (hbalance : ∀ j k, (Set.ncard {i | R i j} : ℝ) ≤ D * Set.ncard {i | R i k})
    (hlower : ∀ j, a ≤ Set.ncard {i | R i j}) :
    ∃ N : ℕ, 0 < N ∧ (∀ j, N ≤ Set.ncard {i | R i j}) ∧
      (n : ℝ) ≤ q * D * N ∧ a ≤ N := by
  classical
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ (fun j => Set.ncard {i | R i j})
    Finset.univ_nonempty
  obtain ⟨N, _, hNle, _, hsum⟩ := balanced_cover_minimum hq R hD hcover hpos hbalance
  refine ⟨Set.ncard {i | R i j}, hpos j, (fun k => hj k (Finset.mem_univ k)), ?_, hlower j⟩
  exact hsum.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hNle j)) (by positivity))

end WangZahlLot.Obl.wz_separated_scales_gain
