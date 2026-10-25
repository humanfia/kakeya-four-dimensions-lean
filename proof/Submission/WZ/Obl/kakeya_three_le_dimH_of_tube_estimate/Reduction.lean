-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.Reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Selection

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate

open LeanEval.Analysis.WangZahlKakeya

abbrev TubeEstimate : Prop := (∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i j : Fin n, i ≠ j → δ ≤ ‖v i - v j‖ ∧ δ ≤ ‖v i + v j‖) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → (∀ i : Fin n, ENNReal.ofReal (lam * δ ^ 2) ≤ MeasureTheory.volume (Y i)) → ENNReal.ofReal (c * δ ^ ε * lam ^ κ * ((n : ℝ) * δ ^ 2)) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i))

/-- The discretized tube lower bound rules out every positive-dimensional
Hausdorff null cover below dimension three. -/
theorem hausdorffMeasure_ne_zero_of_tube_estimate (hTube : TubeEstimate)
    {K : Set Space} (hK : IsKakeya K) {s : ℝ} (hs : 0 < s) (hs3 : s < 3) :
    μH[s] K ≠ 0 := by
  intro hnull
  let ε : ℝ := (3 - s) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨κ, c, hc, δ₀, hδ₀, htube⟩ := hTube ε hε
  let γ : ℝ := (3 - s) / (4 * (|κ| + 1))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hexp : ε + γ * κ + γ ≤ 3 - s := by
    have habs : 0 < |κ| + 1 := by positivity
    have heq : γ * (|κ| + 1) = (3 - s) / 4 := by
      dsimp [γ]
      field_simp
    have hle : γ * κ + γ ≤ (3 - s) / 4 := by
      calc
        γ * κ + γ = γ * (κ + 1) := by ring
        _ ≤ γ * (|κ| + 1) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self κ]) hγ.le
        _ = _ := heq
    dsimp [ε]
    linarith
  obtain ⟨A, x, p, hA, hA0, hAfin, hx⟩ := exists_localized_directions hK
  let w : ℝ := (volume A).toReal
  have hw : 0 < w := ENNReal.toReal_pos hA0 hAfin
  have hwA : ENNReal.ofReal w ≤ volume A := (ENNReal.ofReal_toReal hAfin).le
  let a : ℝ := scaleCoefficient γ
  have ha : 0 < a := scaleCoefficient_pos hγ
  let B : ℝ := c * (a / 4) ^ κ * (w * a / 4)
  have hB : 0 < B := by dsimp [B]; positivity
  let η : ℝ := B / 128
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show 0 < min δ₀ (1 / 8 : ℝ) from lt_min hδ₀ (by norm_num))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hNδ : dyadic N ≤ δ₀ := hN.le.trans (min_le_left _ _)
  have hNsmall : dyadic N ≤ 1 / 8 := hN.le.trans (min_le_right _ _)
  let f : Space → Space := fun z => z - p
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro z z'
    simp only [f, dist_eq_norm]
    congr 1
    abel
  have hcompact : IsCompact (f '' K) := hK.1.image hf.continuous
  have hnull' : μH[s] (f '' K) = 0 := by
    rw [hf.hausdorffMeasure_image (Or.inl hs.le), hnull]
  obtain ⟨F, centers, ρ, hρ, hcover, hcost⟩ :=
    WangZahlLot.Seed.Kakeya.exists_finite_ball_cover_of_hausdorffMeasure_eq_zero
      hs hcompact hnull' (dyadic_pos N) hη
  let z : Plane → Space := fun u => x u - p
  have hz : ∀ u ∈ A, ‖z u + (1 / 2 : ℝ) • capDirection u‖ ≤ 1 / 8 := by
    intro u hu
    have h := (hx u hu).2
    rw [dist_eq_norm] at h
    have heq : z u + (1 / 2 : ℝ) • capDirection u =
        (x u + (1 / 2 : ℝ) • capDirection u) - p := by dsimp [z]; abel
    rwa [heq]
  have hzcover : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      z u + t • capDirection u ∈ ⋃ m ∈ F, ball (centers m) (ρ m) := by
    intro u hu t ht
    apply hcover
    refine ⟨x u + t • capDirection u, (hx u hu).1 t ht, ?_⟩
    dsimp [f, z]
    abel
  obtain ⟨k, hNk, n, z', v, Y, hv, hsep, hunit, hYm, hYsub, hYmass, hcount, hYcover⟩ :=
    exists_discrete_family A z hA hw hwA hγ hz F centers ρ N hNsmall hρ hzcover
  let r : ℝ := dyadic k
  have hr : 0 < r := dyadic_pos k
  have hr1 : r ≤ 1 := dyadic_le_one k
  have hrδ : r ≤ δ₀ := (dyadic_antitone hNk).trans hNδ
  have hrγ : 0 < r ^ γ := Real.rpow_pos_of_pos hr γ
  let lam : ℝ := a / 4 * r ^ γ
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlam1 : lam ≤ 1 := by
    have harg : r ^ γ ≤ 1 := Real.rpow_le_one hr.le hr1 hγ.le
    have ha1 : a ≤ 1 := scaleCoefficient_le_one γ
    dsimp [lam]
    nlinarith
  have ht := htube r hr hrδ lam hlam hlam1 n z' v Y hv hsep hunit hYm hYsub hYmass
  have hupper : c * r ^ ε * lam ^ κ * ((n : ℝ) * r ^ 2) ≤
      64 * η * r ^ (3 - s) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    exact ht.trans ((measure_mono hYcover).trans
      (volume_scaleEnlargement_le F centers ρ hs.le hs3.le
        (fun m hm => (hρ m hm).1) hcost.le k))
  have hcount' : w * a * r ^ γ / 4 ≤ (n : ℝ) * r ^ 2 := by
    change w * a * r ^ γ ≤ 4 * ((n : ℝ) * r ^ 2) at hcount
    linarith
  have hidentity : B * r ^ (ε + γ * κ + γ) =
      c * r ^ ε * lam ^ κ * (w * a * r ^ γ / 4) := by
    dsimp [B, lam]
    rw [Real.mul_rpow (by positivity) hrγ.le, ← Real.rpow_mul hr.le,
      Real.rpow_add hr, Real.rpow_add hr]
    ring
  have hlower : B * r ^ (3 - s) ≤ c * r ^ ε * lam ^ κ * ((n : ℝ) * r ^ 2) := by
    calc
      B * r ^ (3 - s) ≤ B * r ^ (ε + γ * κ + γ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1 hexp) hB.le
      _ = _ := hidentity
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount' (by positivity)
  have hpositive : 0 < B * r ^ (3 - s) := mul_pos hB (Real.rpow_pos_of_pos hr _)
  dsimp [η] at hupper
  nlinarith

end WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate
