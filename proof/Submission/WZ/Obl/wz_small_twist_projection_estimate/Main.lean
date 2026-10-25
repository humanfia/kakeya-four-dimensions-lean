-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Core

/-!
# The small-twist projection estimate

Take `η = min(ε, 1) / 6`.  The core estimate gives
`δ^(3η) ≤ 150000 (K + 1) · area` with `5 ≤ 2^K δ ≤ 10`, and for `δ` below an explicit
threshold the logarithmic factor `K + 1` is absorbed by `δ^(-ε/2)`.
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Set Metric MeasureTheory
open scoped ENNReal

/-- A dyadic scale `K` with `5 ≤ 2^K δ ≤ 10`. -/
lemma exists_dyadic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, 5 ≤ 2 ^ K * δ ∧ 2 ^ K * δ ≤ 10 := by
  have hex : ∃ k : ℕ, 5 ≤ 2 ^ k * δ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (5 / δ) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, by rw [div_lt_iff₀ hδ] at hk; linarith⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have hspec := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero, one_mul] at hspec
    linarith
  · obtain ⟨K', hK'⟩ : ∃ K', Nat.find hex = K' + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ 5 ≤ 2 ^ K' * δ := Nat.find_min hex (by omega)
    push Not at hlt
    rw [hK', pow_succ]
    linarith

/-- The final arithmetic: the logarithmic loss is absorbed for small `δ`. -/
lemma final_arith {ε ε' δ : ℝ} {K : ℕ} (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hε'ε : ε' ≤ ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδd0 : δ ≤ (ε' / 12000000) ^ (4 / ε'))
    (hK : 2 ^ K * δ ≤ 10) :
    150000 * ((K : ℝ) + 1) * δ ^ ε ≤ δ ^ (3 * (ε' / 6)) := by
  set a := ε' / 4 with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by linarith
  have h1 : δ ^ ε ≤ δ ^ ε' := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hε'ε
  have h2 : ((K : ℝ) + 1) ≤ (2 / a) * ((2 : ℝ) ^ K) ^ a := nat_succ_le_rpow ha0 ha1 K
  have h3 : ((2 : ℝ) ^ K) ^ a * δ ^ a ≤ 10 := by
    rw [← Real.mul_rpow (by positivity) hδ.le]
    calc ((2 : ℝ) ^ K * δ) ^ a ≤ 10 ^ a := Real.rpow_le_rpow (by positivity) hK ha0.le
      _ ≤ 10 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
      _ = 10 := Real.rpow_one 10
  have hδa : 0 ≤ δ ^ a := by positivity
  have h4 : ((K : ℝ) + 1) * δ ^ a ≤ 80 / ε' := by
    calc ((K : ℝ) + 1) * δ ^ a ≤ (2 / a) * ((2 : ℝ) ^ K) ^ a * δ ^ a :=
          mul_le_mul_of_nonneg_right h2 hδa
      _ = (2 / a) * (((2 : ℝ) ^ K) ^ a * δ ^ a) := by ring
      _ ≤ (2 / a) * 10 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 80 / ε' := by
          rw [ha]
          field_simp
          ring
  have h5 : δ ^ a ≤ ε' / 12000000 := by
    calc δ ^ a ≤ ((ε' / 12000000) ^ (4 / ε')) ^ a := Real.rpow_le_rpow hδ.le hδd0 ha0.le
      _ = ε' / 12000000 := by
        rw [← Real.rpow_mul (by positivity)]
        have : 4 / ε' * a = 1 := by
          rw [ha]
          field_simp
        rw [this, Real.rpow_one]
  have h6 : δ ^ ε' = δ ^ a * δ ^ a * δ ^ (3 * (ε' / 6)) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    rw [ha]
    ring
  have hδb : 0 ≤ δ ^ (3 * (ε' / 6)) := by positivity
  have hK0 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  calc 150000 * ((K : ℝ) + 1) * δ ^ ε ≤ 150000 * ((K : ℝ) + 1) * δ ^ ε' := by gcongr
    _ = 150000 * (((K : ℝ) + 1) * δ ^ a) * δ ^ a * δ ^ (3 * (ε' / 6)) := by
        rw [h6]
        ring
    _ ≤ 150000 * (80 / ε') * (ε' / 12000000) * δ ^ (3 * (ε' / 6)) := by
        gcongr
    _ = δ ^ (3 * (ε' / 6)) := by
        field_simp
        ring

/-- The small-twist projection estimate, with the frozen hypotheses written out. -/
theorem small_twist_estimate : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    (0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, tube δ (x i) (v i) ⊆ Metric.ball 0 1) ∧
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) ∧
      (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ tube δ (x i) (v i)) ∧
      ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤
        Finset.sum Finset.univ (fun i => volume (Y i))) →
    (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
    CountF η δ n x v →
    ∀ f : ℝ → ℝ, SlopeN f →
    (100 < |f 0| ∧ 1 ≤ δ * (f 0) ^ 2 ∧ |f 0| < 2 + 6 / δ) →
    ENNReal.ofReal (δ ^ ε) ≤ volume (proj f (⋃ i, Y i)) := by
  intro ε hε
  set ε' := min ε 1 with hε'def
  have hε' : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  refine ⟨ε' / 6, by positivity, (ε' / 12000000) ^ (4 / ε'), by positivity, ?_⟩
  intro δ hδ hδd0 hδ1 n x v Y hH hv2 hF f hf hc
  obtain ⟨hn, hv, hT, -, hYm, hYT, hmass⟩ := hH
  obtain ⟨K, hK5, hK10⟩ := exists_dyadic hδ (by linarith)
  have hcore := core_estimate (η := ε' / 6) hδ hv hT hYm hYT hv2 hF hf hc.1 hc.2.1 K hK5
  set V := volume (proj f (⋃ i, Y i)) with hVdef
  set m := δ ^ (ε' / 6) * (n : ℝ) * δ ^ 2 with hmdef
  set Q := 150000 * ((K : ℝ) + 1) * (n : ℝ) ^ 2 * δ ^ 4 * δ ^ (-(ε' / 6)) with hQdef
  have h1 : ENNReal.ofReal (m ^ 2) ≤ V * ENNReal.ofReal Q := by
    rw [ENNReal.ofReal_pow (by positivity)]
    exact (pow_le_pow_left₀ zero_le hmass 2).trans hcore
  by_cases hVtop : V = ⊤
  · rw [hVtop]
    exact le_top
  have hV : V = ENNReal.ofReal V.toReal := (ENNReal.ofReal_toReal hVtop).symm
  rw [hV, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at h1
  have h2 : m ^ 2 ≤ V.toReal * Q :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  rw [hV]
  apply ENNReal.ofReal_le_ofReal
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h3 : δ ^ (3 * (ε' / 6)) ≤ V.toReal * (150000 * ((K : ℝ) + 1)) := by
    have hn2 : 0 < (n : ℝ) ^ 2 * δ ^ 4 := by positivity
    have hm2 : m ^ 2 = (δ ^ (ε' / 6)) ^ 2 * ((n : ℝ) ^ 2 * δ ^ 4) := by
      rw [hmdef]
      ring
    have hQ : V.toReal * Q =
        V.toReal * (150000 * ((K : ℝ) + 1)) * δ ^ (-(ε' / 6)) * ((n : ℝ) ^ 2 * δ ^ 4) := by
      rw [hQdef]
      ring
    rw [hm2, hQ] at h2
    have h4 : (δ ^ (ε' / 6)) ^ 2 ≤ V.toReal * (150000 * ((K : ℝ) + 1)) * δ ^ (-(ε' / 6)) :=
      le_of_mul_le_mul_right h2 hn2
    have h5 : δ ^ (-(ε' / 6)) * δ ^ (ε' / 6) = 1 := by
      rw [← Real.rpow_add hδ]
      simp
    have h6 : δ ^ (3 * (ε' / 6)) = (δ ^ (ε' / 6)) ^ 2 * δ ^ (ε' / 6) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      congr 1
      push_cast
      ring
    rw [h6]
    calc (δ ^ (ε' / 6)) ^ 2 * δ ^ (ε' / 6)
        ≤ V.toReal * (150000 * ((K : ℝ) + 1)) * δ ^ (-(ε' / 6)) * δ ^ (ε' / 6) := by
          gcongr
      _ = V.toReal * (150000 * ((K : ℝ) + 1)) := by
          rw [mul_assoc _ (δ ^ (-(ε' / 6))), h5, mul_one]
  have h7 := final_arith hε' hε'1 hε'ε hδ (by linarith) hδd0 hK10
  have hpos : 0 < 150000 * ((K : ℝ) + 1) := by positivity
  have h8 : 150000 * ((K : ℝ) + 1) * δ ^ ε ≤ 150000 * ((K : ℝ) + 1) * V.toReal := by
    linarith
  exact le_of_mul_le_mul_left h8 hpos

end WangZahlLot.Obl.wz_small_twist_projection_estimate
