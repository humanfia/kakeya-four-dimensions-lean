/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFirstJetBudget.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFirstJetBudget.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockFitConstants
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

/-! One subpower budget for mass, rows, Taylor constants, reading radii, and list counts. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Filter
open Submission.Obl.k4_discrete_of_terminal_charts

def scalarFirstJetBudget (steps : ℕ) (P Q : ℝ) : ℝ :=
  10000000000000000 * (steps + 2 : ℕ) * (P * Q) ^ 32

theorem scalarFirstJetBudget_bounds {steps : ℕ} {B P Q K : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hB : 0 ≤ B) (hBP : B ≤ P)
    (hK : 0 ≤ K) (hKP : K ≤ P) :
    1 ≤ scalarFirstJetBudget steps P Q ∧ B ≤ scalarFirstJetBudget steps P Q ∧
      40000 * B * P ^ 6 * Q ≤ scalarFirstJetBudget steps P Q ∧
      1000 * scalarBlockFitBound P ^ 2 ≤ scalarFirstJetBudget steps P Q ∧
      4 * B + 32 * (steps + 1 : ℕ) * B * P ≤ scalarFirstJetBudget steps P Q ∧
      1 + 64 * (steps + 1 : ℕ) * B * P * K ≤ scalarFirstJetBudget steps P Q := by
  let Z := P * Q
  let C : ℝ := 10000000000000000 * (steps + 2 : ℕ)
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hP hQ
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hPZ : P ≤ Z := by dsimp [Z]; nlinarith
  have hQZ : Q ≤ Z := by dsimp [Z]; nlinarith
  have hBZ : B ≤ Z := hBP.trans hPZ
  have hKZ : K ≤ Z := hKP.trans hPZ
  have hn : (0 : ℝ) ≤ steps := Nat.cast_nonneg _
  have hC : 1 ≤ C := by dsimp [C]; push_cast; nlinarith
  have hdom (c : ℝ) (p : ℕ) (hc : c ≤ C) (hp : p ≤ 32) :
      c * Z ^ p ≤ scalarFirstJetBudget steps P Q := by
    exact mul_le_mul hc (pow_le_pow_right₀ hZ hp) (pow_nonneg hZ0 _) (zero_le_one.trans hC)
  have hpow1 : Z ≤ Z ^ 32 := by simpa only [pow_one] using pow_le_pow_right₀ hZ (by norm_num : 1 ≤ 32)
  have hbase : 1 ≤ scalarFirstJetBudget steps P Q := by
    have hh := hdom 1 0 hC (by norm_num)
    simpa only [pow_zero, mul_one] using hh
  refine ⟨hbase, ?_, ?_, ?_, ?_, ?_⟩
  · exact hBZ.trans (hpow1.trans (by simpa only [one_mul] using hdom 1 32 hC le_rfl))
  · calc
      _ ≤ 40000 * Z * Z ^ 6 * Z := by gcongr
      _ = 40000 * Z ^ 8 := by ring
      _ ≤ _ := hdom 40000 8 (by dsimp [C]; push_cast; nlinarith) (by norm_num)
  · calc
      _ = 10000000000000 * P ^ 20 := by dsimp [scalarBlockFitBound]; ring
      _ ≤ 10000000000000 * Z ^ 20 := by gcongr
      _ ≤ _ := hdom 10000000000000 20 (by dsimp [C]; push_cast; nlinarith) (by norm_num)
  · have hZ2 : Z ≤ Z ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hZ (by norm_num : 1 ≤ 2)
    have hprod : B * P ≤ Z ^ 2 := by nlinarith [mul_le_mul hBZ hPZ hP0 hZ0]
    calc
      _ ≤ 4 * Z ^ 2 + 32 * (steps + 1 : ℕ) * Z ^ 2 := by nlinarith [hBZ.trans hZ2]
      _ = (4 + 32 * (steps + 1 : ℕ)) * Z ^ 2 := by ring
      _ ≤ _ := hdom _ 2 (by dsimp [C]; push_cast; nlinarith) (by norm_num)
  · have hprod : B * P * K ≤ Z ^ 3 := by
      calc
        _ ≤ Z * Z * Z := by gcongr
        _ = _ := by ring
    have hZ3 : 1 ≤ Z ^ 3 := one_le_pow₀ hZ
    calc
      _ ≤ Z ^ 3 + 64 * (steps + 1 : ℕ) * Z ^ 3 := by nlinarith
      _ = (1 + 64 * (steps + 1 : ℕ)) * Z ^ 3 := by ring
      _ ≤ _ := hdom _ 3 (by dsimp [C]; push_cast; nlinarith) (by norm_num)

/-- All losses in the common-row output remain subpower for every
fixed number of hierarchy bridge levels. -/
theorem scalarFirstJetBudget_subpower (N P Q : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hP : ∀ k, 1 ≤ P k) (hQ : ∀ k, 1 ≤ Q k)
    (hPsub : SubpowerBound N P) (hQsub : SubpowerBound N Q) (steps : ℕ) :
    (∀ k, 1 ≤ scalarFirstJetBudget steps (P k) (Q k)) ∧
      SubpowerBound N (fun k => scalarFirstJetBudget steps (P k) (Q k)) := by
  have hZ : Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower N (fun k => P k * Q k) :=
    ⟨fun k => one_le_mul_of_one_le_of_one_le (hP k) (hQ k),
      subpower_mul (fun k => zero_lt_one.trans_le (hN k))
        (fun k => zero_le_one.trans (hP k)) (fun k => zero_le_one.trans (hQ k)) hPsub hQsub⟩
  have h := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
    hN hNt hZ (A := 10000000000000000 * (steps + 2 : ℕ)) (by
      have hn : (0 : ℝ) ≤ steps := Nat.cast_nonneg _
      push_cast
      nlinarith) 32
  exact h

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
