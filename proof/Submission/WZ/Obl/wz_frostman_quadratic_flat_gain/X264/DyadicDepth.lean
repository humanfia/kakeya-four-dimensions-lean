-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.DyadicDepth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file DyadicDepth.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open Filter Set
open scoped Topology

/-- Every fixed constant is absorbed by a positive power at sufficiently small scales. -/
lemma power_absorption (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C * δ ^ τ ≤ 1 := by
  have hp : Tendsto (fun δ : ℝ => δ ^ τ) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun δ : ℝ => δ ^ τ) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [Real.zero_rpow hτ.ne'] using
        (Real.continuousAt_rpow_const 0 τ (Or.inr hτ.le)).tendsto
    exact ht.mono_left nhdsWithin_le_nhds
  have hh : ∀ᶠ δ : ℝ in 𝓝[>] 0, C * δ ^ τ < 1 := by
    have ht := hp.const_mul C
    simp only [mul_zero] at ht
    exact ht.eventually_lt_const zero_lt_one
  obtain ⟨d, hd, h⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hh
  exact ⟨d, hd, fun δ hδ hδd => (h ⟨hδ, hδd⟩).le⟩

/-- A dyadic cutoff below a prescribed power needs fewer than any fixed inverse
power of the scale many classes. -/
lemma dyadic_depth (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) {τ : ℝ} (hτ : 0 < τ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∃ K : ℕ, 0 < K ∧ C * (1 / 2 : ℝ) ^ K ≤ δ ^ c ∧ (K : ℝ) ≤ δ ^ (-τ) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : Tendsto (fun δ : ℝ => δ ^ τ) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun δ : ℝ => δ ^ τ) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [Real.zero_rpow hτ.ne'] using
        (Real.continuousAt_rpow_const 0 τ (Or.inr hτ.le)).tendsto
    exact ht.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun δ : ℝ => (Real.log C / Real.log 2 + 2) * δ ^ τ -
        (c / Real.log 2) * (Real.log δ * δ ^ τ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using
      (hp.const_mul (Real.log C / Real.log 2 + 2)).sub
        ((tendsto_log_mul_rpow_nhdsGT_zero hτ).const_mul (c / Real.log 2))
  obtain ⟨d, hd, hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (hlim.eventually_lt_const zero_lt_one)
  refine ⟨min d 1, lt_min hd zero_lt_one, ?_⟩
  intro δ hδ hδd
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_right _ _)
  let r : ℝ := (Real.log C - c * Real.log δ) / Real.log 2
  have hr : 0 ≤ r := by
    apply div_nonneg _ hlog2.le
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hc
      (Real.log_nonpos hδ.le hδ1)).trans (Real.log_nonneg hC))
  let K : ℕ := ⌈r⌉₊ + 1
  have hrK : r ≤ (K : ℝ) := by
    exact (Nat.le_ceil r).trans (by dsimp [K]; push_cast; linarith)
  have hKlt : (K : ℝ) < r + 2 := by
    have hh := Nat.ceil_lt_add_one hr
    dsimp [K]
    push_cast
    linarith
  refine ⟨K, by dsimp [K]; omega, ?_, ?_⟩
  · have hexp : Real.log C - c * Real.log δ ≤ (K : ℝ) * Real.log 2 :=
      (div_le_iff₀ hlog2).mp hrK
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    calc
      C * (1 / 2 : ℝ) ^ K =
          Real.exp (Real.log C + Real.log (1 / 2 : ℝ) * K) := by
        rw [Real.exp_add, Real.exp_log hCpos,
          ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Real.rpow_natCast]
      _ ≤ Real.exp (Real.log δ * c) := by
        apply Real.exp_le_exp.mpr
        rw [hhalf]
        nlinarith
      _ = δ ^ c := (Real.rpow_def_of_pos hδ c).symm
  · have hh := hbound ⟨hδ, hδd.trans (min_le_left _ _)⟩
    have heq : (r + 2) * δ ^ τ =
        (Real.log C / Real.log 2 + 2) * δ ^ τ -
          (c / Real.log 2) * (Real.log δ * δ ^ τ) := by
      dsimp [r]
      ring
    have hKpow : (K : ℝ) * δ ^ τ ≤ 1 := by
      calc
        _ ≤ (r + 2) * δ ^ τ := mul_le_mul_of_nonneg_right hKlt.le
          (Real.rpow_nonneg hδ.le _)
        _ ≤ 1 := by rw [heq]; exact hh.le
    rw [Real.rpow_neg hδ.le, inv_eq_one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hδ τ)).mpr hKpow

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
