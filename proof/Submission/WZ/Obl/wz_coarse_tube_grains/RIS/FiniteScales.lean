-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FiniteScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Arithmetic

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A shading of average density δ^η gives this elementary union bound. -/
theorem average_bound_of_dense {δ η : ℝ} {n : ℕ}
    {Y : Fin n → Set Space} (hn : 0 < n) (h : Dense δ η Y) :
    ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (⋃ i, Y i) := by
  have hsum : ∑ i, volume (Y i) ≤ (n : ENNReal) * volume (⋃ i, Y i) := by
    calc
      ∑ i, volume (Y i) ≤ ∑ _ : Fin n, volume (⋃ i, Y i) :=
        Finset.sum_le_sum fun i _ => measure_mono (Set.subset_iUnion Y i)
      _ = _ := by simp
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  apply (ENNReal.mul_le_mul_iff_right hn0 (by simp)).mp
  calc
    (n : ENNReal) * ENNReal.ofReal (δ ^ η * δ ^ 2) =
        ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) := by
      rw [show δ ^ η * (n : ℝ) * δ ^ 2 = (n : ℝ) * (δ ^ η * δ ^ 2) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ∑ i, volume (Y i) := h
    _ ≤ _ := hsum

theorem Hypotheses.average_bound {δ η m l : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Hypotheses δ η m l n x v Y) :
    ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (⋃ i, Y i) :=
  average_bound_of_dense h.1.1 h.2.1

/-- The total normalized tube count is bounded by the convex count of the unit ball. -/
theorem Hypotheses.count_bound {δ η l : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Hypotheses δ η (δ ^ (-η)) l n x v Y) (hδ : 0 < δ) :
    (n : ℝ) * δ ^ 2 ≤ δ ^ (-η) * wz_endpoint_bootstrap.ballConstant := by
  have hk := h.2.2.1 (Metric.ball (0 : Space) 1) (convex_ball _ _)
  have hset : {i : Fin n | Tube δ (x i) (v i) ⊆ Metric.ball 0 1} = Set.univ :=
    Set.eq_univ_of_forall fun i => (h.1.2.1 i).2.1
  change ENNReal.ofReal (({i : Fin n | Tube δ (x i) (v i) ⊆ Metric.ball 0 1}.ncard : ℝ) *
    δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * volume (Metric.ball (0 : Space) 1) at hk
  rw [hset] at hk
  simp only [Set.ncard_univ, Nat.card_fin] at hk
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top) hk
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (n : ℝ) * δ ^ 2),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _)] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg hδ.le _))

/-- On every range bounded away from zero, the first alternative holds for any
fixed exponent. Thus only the arbitrarily small scales need the grains argument. -/
theorem first_alternative_away_from_zero {σ η δ₀ : ℝ} (hσ : 0 ≤ σ)
    (hη : 0 ≤ η) (hδ₀ : 0 < δ₀) (w : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, δ₀ ≤ δ → δ ≤ 1 → ∀ n x v Y,
      Hypotheses δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ENNReal.ofReal (κ * δ ^ w * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        volume (⋃ i, Y i) := by
  let C := wz_endpoint_bootstrap.ballConstant
  let L := δ₀ ^ η * δ₀ ^ 2
  let B := δ₀ ^ (-|w|) * (δ₀ ^ (-η) * C) * δ₀ ^ (-σ)
  have hC : 0 < C := wz_endpoint_bootstrap.ballConstant_pos
  have hL : 0 < L := by positivity
  have hB : 0 < B := by positivity
  refine ⟨L / B, div_pos hL hB, ?_⟩
  intro δ hδlower hδupper n x v Y h
  have hδ : 0 < δ := hδ₀.trans_le hδlower
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast h.1.1
  have hnδ : δ₀ ≤ (n : ℝ) * δ :=
    hδlower.trans (by nlinarith)
  have hw : δ ^ w ≤ δ₀ ^ (-|w|) :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδupper (neg_abs_le w)).trans
      (Real.rpow_le_rpow_of_nonpos hδ₀ hδlower (by linarith [abs_nonneg w]))
  have hc : (n : ℝ) * δ ^ 2 ≤ δ₀ ^ (-η) * C :=
    (h.count_bound hδ).trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hδ₀ hδlower (neg_nonpos.mpr hη)) hC.le)
  have hs : ((n : ℝ) * δ) ^ (-σ) ≤ δ₀ ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hδ₀ hnδ (neg_nonpos.mpr hσ)
  have hlower : L ≤ δ ^ η * δ ^ 2 :=
    mul_le_mul (Real.rpow_le_rpow hδ₀.le hδlower hη)
      (pow_le_pow_left₀ hδ₀.le hδlower 2) (sq_nonneg _) (Real.rpow_nonneg hδ.le _)
  calc
    ENNReal.ofReal (L / B * δ ^ w * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        ENNReal.ofReal (L / B * B) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = L / B * (δ ^ w * (n * δ ^ 2) * (n * δ) ^ (-σ)) := by ring
        _ ≤ L / B * B := mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul hw hc (by positivity) (by positivity)) hs
            (by positivity) (by positivity)) (by positivity)
    _ = ENNReal.ofReal L := by rw [div_mul_cancel₀ _ hB.ne']
    _ ≤ ENNReal.ofReal (δ ^ η * δ ^ 2) := ENNReal.ofReal_le_ofReal hlower
    _ ≤ volume (⋃ i, Y i) := h.average_bound

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
