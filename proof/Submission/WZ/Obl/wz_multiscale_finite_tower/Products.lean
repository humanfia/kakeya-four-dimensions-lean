-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Products.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The normalized volume factor contributed by one scale interval. -/
noncomputable def volumeFactor (σ ω s N : ℝ) : ℝ :=
  s ^ ω * (N * s ^ 2) * (N * s) ^ (-σ)

/-- The three factors in the local estimate multiply separately. -/
theorem product_volumeFactor {ι : Type*} (S : Finset ι) (σ ω : ℝ) (s N : ι → ℝ)
    (hs : ∀ i ∈ S, 0 ≤ s i) (hN : ∀ i ∈ S, 0 ≤ N i) :
    (∏ i ∈ S, volumeFactor σ ω (s i) (N i)) =
      volumeFactor σ ω (∏ i ∈ S, s i) (∏ i ∈ S, N i) := by
  dsimp [volumeFactor]
  simp only [Finset.prod_mul_distrib]
  rw [Real.finsetProd_rpow S s hs ω, Finset.prod_pow,
    Real.finsetProd_rpow S (fun i => N i * s i) (fun i hi => mul_nonneg (hN i hi) (hs i hi)) (-σ),
    Finset.prod_mul_distrib]

/-- Successive ratios telescope, with nonvanishing only needed on the finite range. -/
theorem product_ratios (f : ℕ → ℝ) (J : ℕ) :
    (∀ j, j ≤ J → f j ≠ 0) → (∏ j ∈ Finset.range J, f (j + 1) / f j) = f J / f 0 := by
  induction J with
  | zero => intro hf; simp [hf 0 le_rfl]
  | succ J ih =>
    intro hf
    rw [Finset.prod_range_succ, ih (fun j hj => hf j (by omega))]
    field_simp [hf J (by omega), hf 0 (by omega)]

/-- Along a normalized tower the local factors give exactly the global volume expression. -/
theorem product_tower_factors (σ ω d n : ℝ) (J : ℕ) (r N : ℕ → ℝ)
    (hr : ∀ j, j ≤ J → 0 < r j) (hN : ∀ j, j ≤ J → 0 < N j)
    (hr0 : r 0 = 1) (hN0 : N 0 = 1) (hrJ : r J = d) (hNJ : N J = n) :
    (∏ j ∈ Finset.range J, volumeFactor σ ω (r (j + 1) / r j) (N (j + 1) / N j)) =
      d ^ ω * (n * d ^ 2) * (n * d) ^ (-σ) := by
  rw [product_volumeFactor (Finset.range J) σ ω _ _
      (fun j hj => div_nonneg (hr (j + 1) (by simpa using Finset.mem_range.mp hj)).le
        (hr j (Finset.mem_range.mp hj).le).le)
      (fun j hj => div_nonneg (hN (j + 1) (by simpa using Finset.mem_range.mp hj)).le
        (hN j (Finset.mem_range.mp hj).le).le),
    product_ratios r J (fun j hj => (hr j hj).ne'),
    product_ratios N J (fun j hj => (hN j hj).ne'), hr0, hN0, hrJ, hNJ, div_one, div_one]
  rfl

/-- A volume gain on one sufficiently large gap survives the global power losses. -/
theorem volume_bound_of_gap_gain {σ ω κ α loss h d s : ℝ} {n : ℕ}
    {Y : Fin n → Set Space} (hd : 0 < d) (hs : 0 < s) (hκ : 0 ≤ κ) (hα : 0 ≤ α)
    (hgap : s ≤ d ^ h)
    (hvol : ENNReal.ofReal (κ * d ^ loss * volumeFactor σ ω d n * s ^ (-α)) ≤ volume (⋃ i, Y i)) :
    VolumeBound σ ω κ (h * α - loss) d n Y := by
  have hgain : d ^ (-h * α) ≤ s ^ (-α) := by
    rw [show -h * α = h * (-α) by ring, Real.rpow_mul hd.le]
    exact Real.rpow_le_rpow_of_nonpos hs hgap (neg_nonpos.mpr hα)
  apply le_trans (ENNReal.ofReal_le_ofReal _) hvol
  calc
    κ * d ^ (ω - (h * α - loss)) * (n * d ^ 2) * (n * d) ^ (-σ) =
        κ * d ^ loss * volumeFactor σ ω d n * d ^ (-h * α) := by
      dsimp [volumeFactor]
      rw [show ω - (h * α - loss) = loss + ω + (-h * α) by ring,
        Real.rpow_add hd, Real.rpow_add hd]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgain (by dsimp [volumeFactor]; positivity)

end WangZahlLot.Obl.wz_multiscale_finite_tower
