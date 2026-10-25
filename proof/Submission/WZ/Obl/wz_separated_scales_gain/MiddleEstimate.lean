-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.MiddleEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Basic
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineEstimate
import Submission.WZ.Obl.wz_nonflat_factored_improvement.RealWeight
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineNormalized

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

noncomputable abbrev retainedFraction : ℝ := min 1 fineRetainedFraction

theorem retainedFraction_pos : 0 < retainedFraction := lt_min zero_lt_one fineRetainedFraction_pos

theorem retainedFraction_le_one : retainedFraction ≤ 1 := min_le_left _ _

/-- The middle-scale use of `D`, with its density and counting requirements explicit. -/
theorem middle_estimate {σ ω : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hD : EstimateD σ ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ b δ lam m : ℝ, 0 < δ → δ ≤ b → b ≤ 1 → 0 ≤ lam → 0 ≤ m →
      (fineRadius δ b) ^ η ≤ fineContraction * lam / 16 →
      16 * m / fineContraction ≤ (fineRadius δ b) ^ (-η) →
      ∀ (e : AffineIsometryEquiv ℝ Space Space) (n : ℕ) (x v : Fin n → Space)
        (Y : Fin n → Set Space), 0 < n →
      m / (δ ^ 2 * (fineContraction ^ 3 * b⁻¹ ^ 2) * (retainedFraction * n)) ≤
        (fineRadius δ b) ^ (-η) →
      (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ e '' standardPrism b b) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → ConvexCount δ m x v →
      ENNReal.ofReal (A * (δ / b) ^ (ω + ε) * ((n : ℝ) * δ ^ 2) *
        ((n : ℝ) * (δ / b)) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  obtain ⟨A, hA, η, hη, H⟩ := hD ε hε
  let k : ℝ := 4 * fineContraction
  have hk : 0 < k := by norm_num [k]
  have hκ : 0 < fineContraction := by norm_num
  let A' := A * retainedFraction * k ^ (ω + ε) * k ^ 2 * k ^ (-σ) / fineContraction ^ 3
  refine ⟨A', η, by dsimp [A']; have := retainedFraction_pos; positivity, hη, ?_⟩
  intro b δ lam m hδ hδb hb1 hlam hm hden hconvbound e n x v Y hn hslabbound
    hv hT hover hYm hYT hind hconv
  have hb : 0 < b := hδ.trans_le hδb
  let r := fineRadius δ b
  let J := fineContraction ^ 3 * b⁻¹ ^ 2
  have hr : 0 < r := by dsimp [r, fineRadius]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hre : r = k * (δ / b) := by dsimp [r, fineRadius, k]; ring
  have hr100 : r ≤ 1 / 100 := by
    have hdb : δ / b ≤ 1 := (div_le_one hb).mpr hδb
    rw [hre]
    dsimp [k, fineContraction]
    linarith
  obtain ⟨M, j, z, w, hM, hj, hw, hB, hsep, hcover, hmass⟩ :=
    fine_prism_net hb hb1 le_rfl hδ hδb e hn x v hv hT hover
  have hsize : retainedFraction * (n : ℝ) ≤ M := by
    have hh : fineRetainedFraction * (n : ℝ) ≤ M := by
      rw [fineRetainedFraction, div_mul_eq_mul_div]
      exact (div_le_iff₀ (by norm_num : 0 < fineFiberBound)).mpr hmass
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n)).trans hh
  let f := fineAffine e b hb
  let Z : Fin M → Set Space := fun i => f '' Y (j i)
  have hZmeas : ∀ i, MeasurableSet (Z i) := fun i =>
    f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm (j i))
  have hZsub : ∀ i, Z i ⊆ tube r (z i) (w i) := fun i =>
    (image_mono (hYT (j i))).trans (hcover i)
  have hZden : ∀ i, ENNReal.ofReal (r ^ η * r ^ 2) ≤ volume (Z i) := by
    intro i
    rw [show volume (Z i) = ENNReal.ofReal J * volume (Y (j i)) from fineAffine_volume e hb _]
    calc
      _ ≤ ENNReal.ofReal ((fineContraction * lam / 16) * r ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hden (sq_nonneg r))
      _ = ENNReal.ofReal J * ENNReal.ofReal (lam * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul hJ.le]
        congr 1
        dsimp [r, J, fineRadius]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (hind (j i))
  have hraw := affine_count_transport f hJ (sq_pos_of_pos hδ) hm
    (fineAffine_volume e hb) x v z w j hj hcover hconv
  have hc : ConvexCount r (r ^ (-η)) z w := by
    apply convexCount_mono _ (convexCount_of_raw_count (by positivity : 0 ≤ m / (δ ^ 2 * J)) z w hraw)
    have he : m / (δ ^ 2 * J) * r ^ 2 = 16 * m / fineContraction := by
      dsimp [r, J, fineRadius]
      field_simp
      ring
    rwa [he]
  have hs : SlabCount r (r ^ (-η)) z w := by
    apply slabCount_mono _ (slabCount_of_raw_count hM z w hraw)
    have hMf : 0 < retainedFraction * (n : ℝ) := mul_pos retainedFraction_pos (Nat.cast_pos.mpr hn)
    calc
      m / (δ ^ 2 * J) / M ≤ m / (δ ^ 2 * J) / (retainedFraction * n) :=
        div_le_div_of_nonneg_left (by positivity) hMf hsize
      _ = m / (δ ^ 2 * J * (retainedFraction * n)) := by ring
      _ ≤ _ := hslabbound
  have hbound := H r hr hr100 M z w Z hM hw hB hsep hZmeas hZsub
    (subfamily_density hr.le (fun i => i) hZden) hc hs
  have hU : volume (⋃ i, Z i) ≤ ENNReal.ofReal J * volume (⋃ i, Y i) := by
    rw [← fineAffine_volume e hb]
    exact measure_mono (by
      rintro p ⟨_, ⟨i, rfl⟩, q, hq, rfl⟩
      exact ⟨q, mem_iUnion.mpr ⟨j i, hq⟩, rfl⟩)
  have hwgt := count_power_fraction hr (Nat.cast_pos.mpr hn)
    retainedFraction_pos retainedFraction_le_one hsize hσ0 hσ1
  have he (N : ℝ) : r * N = N * r := mul_comm _ _
  simp only [he] at hwgt
  have hbase : ENNReal.ofReal (A * retainedFraction * r ^ (ω + ε) * ((n : ℝ) * r ^ 2) *
      ((n : ℝ) * r) ^ (-σ)) ≤ ENNReal.ofReal J * volume (⋃ i, Y i) := by
    apply le_trans (b := ENNReal.ofReal (A * r ^ (ω + ε) * ((M : ℝ) * r ^ 2) *
      ((M : ℝ) * r) ^ (-σ))) _ (hbound.trans hU)
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left hwgt (by positivity : 0 ≤ A * r ^ (ω + ε) * r ^ 2)
    nlinarith only [hh]
  have hpow : r ^ (ω + ε) = k ^ (ω + ε) * (δ / b) ^ (ω + ε) := by
    rw [hre, Real.mul_rpow hk.le (by positivity)]
  have hnPow : ((n : ℝ) * r) ^ (-σ) = k ^ (-σ) * ((n : ℝ) * (δ / b)) ^ (-σ) := by
    rw [show (n : ℝ) * r = k * ((n : ℝ) * (δ / b)) by rw [hre]; ring,
      Real.mul_rpow hk.le (by positivity)]
  have hidentity : A * retainedFraction * r ^ (ω + ε) * ((n : ℝ) * r ^ 2) *
      ((n : ℝ) * r) ^ (-σ) = J * (A' * (δ / b) ^ (ω + ε) *
        ((n : ℝ) * δ ^ 2) * ((n : ℝ) * (δ / b)) ^ (-σ)) := by
    rw [hpow, hnPow, hre]
    dsimp [J, A']
    field_simp
  rw [hidentity] at hbase
  exact ofReal_cancel_factor hJ hbase

end WangZahlLot.Obl.wz_separated_scales_gain
