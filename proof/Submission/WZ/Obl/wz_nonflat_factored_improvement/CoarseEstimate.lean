-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.CoarseEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineNormalized
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridUnion

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

/-- Apply `D` to the contracted coarse shadings and restore the original volume units. -/
theorem coarse_cell_estimate {σ ω : ℝ} (hD : EstimateD σ ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ b lam : ℝ, 0 < b → b ≤ 1 → 0 < lam →
      ∀ K : ℕ, 0 < K →
      (coarseRadius b) ^ η ≤ coarseContraction * lam / (4608 * K) →
      ∀ M : ℕ, ∀ (z w : Fin M → Space) (C : Fin M → Set Space),
      0 < M → (∀ i, ‖w i‖ = 1) → (∀ i, tube (coarseRadius b) (z i) (w i) ⊆ unitBall) →
      (∀ i j, i ≠ j → volume (tube (coarseRadius b) (z i) (w i) ∩
        tube (coarseRadius b) (z j) (w j)) ≤
          (1 / 2 : ENNReal) * volume (tube (coarseRadius b) (z i) (w i))) →
      (∀ i, MeasurableSet (C i)) →
      (∀ i, (fun p : Space => coarseContraction • p) '' C i ⊆ tube (coarseRadius b) (z i) (w i)) →
      (∀ i, ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (C i)) →
      ConvexCount (coarseRadius b) ((coarseRadius b) ^ (-η)) z w →
      SlabCount (coarseRadius b) ((coarseRadius b) ^ (-η)) z w →
      ENNReal.ofReal (A * b ^ (ω + ε) * ((M : ℝ) * b ^ 2) * ((M : ℝ) * b) ^ (-σ)) ≤
        volume (⋃ i, C i) := by
  obtain ⟨A, hA, η, hη, H⟩ := hD ε hε
  let k : ℝ := 12 * coarseContraction
  have hk : 0 < k := by norm_num [k]
  have hκ : 0 < coarseContraction := by norm_num
  let A' := A * k ^ (ω + ε) * k ^ 2 * k ^ (-σ) / coarseContraction ^ 3
  refine ⟨A', η, by dsimp [A']; positivity, hη, ?_⟩
  intro b lam hb hb1 hlam K hK hden M z w C hM hw hB hover hCm hCT hCden hconv hslab
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  let r := coarseRadius b
  have hr : 0 < r := by dsimp [r, coarseRadius]; positivity
  have hre : r = k * b := by dsimp [r, coarseRadius, k]; ring
  have hr100 : r ≤ 1 / 100 := by
    dsimp [r, coarseRadius, coarseContraction]
    linarith
  let Z : Fin M → Set Space := fun i => (fun p : Space => coarseContraction • p) '' C i
  have hZm : ∀ i, MeasurableSet (Z i) := by
    intro i
    exact (Homeomorph.smulOfNeZero coarseContraction hκ.ne').measurableEmbedding.measurableSet_image.mpr (hCm i)
  have hZd : ∀ i, ENNReal.ofReal (r ^ η * r ^ 2) ≤ volume (Z i) := by
    intro i
    rw [show volume (Z i) = ENNReal.ofReal (coarseContraction ^ 3) * volume (C i)
      from volume_smul_image hκ.le (C i)]
    calc
      _ ≤ ENNReal.ofReal ((coarseContraction * lam / (4608 * K)) * r ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hden (sq_nonneg r))
      _ = ENNReal.ofReal (coarseContraction ^ 3) * ENNReal.ofReal (lam / (32 * K) * b ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [r, coarseRadius]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (hCden i)
  have hh := H r hr hr100 M z w Z hM hw hB hover hZm hCT
    (subfamily_density hr.le (fun i => i) hZd) hconv hslab
  have hU : volume (⋃ i, Z i) = ENNReal.ofReal (coarseContraction ^ 3) * volume (⋃ i, C i) := by
    dsimp [Z]
    rw [← Set.image_iUnion, volume_smul_image hκ.le]
  rw [hU] at hh
  have hpow : r ^ (ω + ε) = k ^ (ω + ε) * b ^ (ω + ε) := by
    rw [hre, Real.mul_rpow hk.le hb.le]
  have hlast : ((M : ℝ) * r) ^ (-σ) = k ^ (-σ) * ((M : ℝ) * b) ^ (-σ) := by
    rw [show (M : ℝ) * r = k * ((M : ℝ) * b) by rw [hre]; ring,
      Real.mul_rpow hk.le (by positivity)]
  have he : A * r ^ (ω + ε) * ((M : ℝ) * r ^ 2) * ((M : ℝ) * r) ^ (-σ) =
      coarseContraction ^ 3 * (A' * b ^ (ω + ε) * ((M : ℝ) * b ^ 2) * ((M : ℝ) * b) ^ (-σ)) := by
    rw [hpow, hlast, hre]
    dsimp [A']
    field_simp
  dsimp only at hh
  rw [he] at hh
  exact ofReal_cancel_factor (by positivity) hh

end WangZahlLot.Obl.wz_nonflat_factored_improvement
