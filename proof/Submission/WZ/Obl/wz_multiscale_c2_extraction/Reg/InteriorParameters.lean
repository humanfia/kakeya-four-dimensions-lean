-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.InteriorParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomMain

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

/-- A geometric hierarchy can stop at `δ^(1-κ)` and use only interior scales.
Its depth and smoothing loss fit the prescribed C2 power budget. The local
selection loss `θ` can be paid at every level of the hierarchy. -/
theorem exists_interior_scale_parameters {κ C : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hC : 0 < C) :
    ∃ (N : ℕ) (ζ θ d₀ : ℝ),
      0 < N ∧ 0 < ζ ∧ 0 < θ ∧ θ ≤ κ ∧ (N : ℝ) * θ ≤ κ ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ 1 →
        (∀ k : Fin N,
          δ ^ (1 - θ) ≤ (δ ^ (1 - κ)) ^ (((k : ℝ) + 1) / N) ∧
          (δ ^ (1 - κ)) ^ (((k : ℝ) + 1) / N) ≤ δ ^ θ) ∧
        C * N * (δ ^ (1 - κ)) ^ (-(1 / (N : ℝ) + 2 * ζ)) ≤ δ ^ (-κ) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < κ / 4 by positivity)
  let N := n + 1
  have hN : 0 < N := Nat.succ_pos n
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hrecip : 1 / (N : ℝ) < κ / 4 := by simpa [N] using hn
  let ζ := κ / 8
  let θ := min (κ / (2 * N)) ((1 - κ) / (2 * N))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθκ : θ ≤ κ := by
    calc θ ≤ κ / (2 * N) := min_le_left _ _
      _ ≤ κ := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hθN : (N : ℝ) * θ ≤ κ := by
    have hh : θ * (2 * N) ≤ κ := (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
    nlinarith
  have hθa : θ ≤ (1 - κ) / N := by
    calc θ ≤ (1 - κ) / (2 * N) := min_le_right _ _
      _ ≤ (1 - κ) / N := by
        apply div_le_div_of_nonneg_left (by linarith) hNr
        linarith
  let p := 1 / (N : ℝ) + 2 * ζ
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hpκ : p < κ / 2 := by dsimp [p, ζ]; linarith
  have hgap : 0 < κ - (1 - κ) * p := by nlinarith
  obtain ⟨d₀, hd₀, hcut⟩ := cut_le_one hgap (C * N)
  refine ⟨N, ζ, θ, d₀, hN, hζ, hθ, hθκ, hθN, hd₀, ?_⟩
  intro δ hδ hδd hδ1
  constructor
  · intro k
    have hk : (k : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hratio1 : ((k : ℝ) + 1) / N ≤ 1 := (div_le_one hNr).mpr hk
    have hratio0 : 1 / (N : ℝ) ≤ ((k : ℝ) + 1) / N := by
      apply div_le_div_of_nonneg_right _ hNr.le
      linarith
    have helo : θ ≤ (1 - κ) * (((k : ℝ) + 1) / N) := by
      calc θ ≤ (1 - κ) / N := hθa
        _ = (1 - κ) * (1 / (N : ℝ)) := by ring
        _ ≤ (1 - κ) * (((k : ℝ) + 1) / N) :=
          mul_le_mul_of_nonneg_left hratio0 (by linarith)
    have hehi : (1 - κ) * (((k : ℝ) + 1) / N) ≤ 1 - θ := by
      have hh := mul_le_mul_of_nonneg_left hratio1 (show 0 ≤ 1 - κ by linarith)
      linarith
    rw [← Real.rpow_mul hδ.le]
    exact ⟨Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hehi,
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 helo⟩
  · have heq : (δ ^ (1 - κ)) ^ (-(1 / (N : ℝ) + 2 * ζ)) =
        δ ^ (κ - (1 - κ) * p) * δ ^ (-κ) := by
      rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      congr 1
      dsimp [p]
      ring
    rw [heq, ← mul_assoc]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (hcut δ hδ hδd) (Real.rpow_nonneg hδ.le (-κ))

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
