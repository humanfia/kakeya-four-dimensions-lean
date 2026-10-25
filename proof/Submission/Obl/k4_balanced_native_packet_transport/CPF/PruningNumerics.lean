/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/PruningNumerics.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/PruningNumerics.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.CrossingLoss

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open scoped ENNReal

theorem crossingFactor_bound {κ : ℝ} (hκ : 1 ≤ κ) :
    crossingFactor κ * κ ≤ 40 * Real.pi * κ ^ 5 := by
  have hsq : 1 ≤ κ ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right (by linarith : 1 + 4 * κ ^ 2 ≤ 5 * κ ^ 2)
    (show 0 ≤ 8 * Real.pi * κ ^ 3 by positivity)
  unfold crossingFactor
  nlinarith

theorem crossing_relative_cost_bound {N κ σ f τ u : ℝ} (hN : 0 < N)
    (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ σ) :
    (ENNReal.ofReal (N ^ (-f + τ)) / ENNReal.ofReal (N ^ u)) *
      ENNReal.ofReal (crossingFactor κ * κ / N ^ (-f)) ≤
        ENNReal.ofReal (40 * Real.pi * N ^ (5 * σ + τ - u)) := by
  have hκpow : κ ^ 5 ≤ N ^ (5 * σ) := by
    calc
      _ ≤ (N ^ σ) ^ 5 := pow_le_pow_left₀ (by linarith) hκN 5
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; ring
  have hnum : crossingFactor κ * κ ≤ 40 * Real.pi * N ^ (5 * σ) :=
    (crossingFactor_bound hκ).trans (mul_le_mul_of_nonneg_left hκpow (by positivity))
  rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hN u),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have heq : (N ^ (-f + τ) / N ^ u) * (crossingFactor κ * κ / N ^ (-f)) =
      crossingFactor κ * κ * N ^ (τ - u) := by
    rw [Real.rpow_add hN, Real.rpow_sub hN]
    field_simp
  rw [heq]
  calc
    _ ≤ (40 * Real.pi * N ^ (5 * σ)) * N ^ (τ - u) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hN]; congr 2; ring

theorem Atlas.crossingLostMass_le_power {p : Data} {k M D : ℕ} {r σ τ u c : ℝ}
    (a : Atlas p k) (ha : a.TrueAt M D r) (hN : 0 < p.N k) (hκ : 1 ≤ a.κ)
    (hκN : a.κ ≤ p.N k ^ σ) (hB : ∀ γ, 0 < p.B k γ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (hmass : a.mass ≤ 1)
    (hg : ∀ γ, Measurable (p.g k γ r))
    (hmap : ∀ γ, Measure.map (obs (p.B k γ) (δ (p.N k) r))
      (((p.ν k γ).prod volume).restrict (p.E k γ)) =
        (volume.prod Measure.count).withDensity (p.g k γ r))
    (hbad : (∑ γ, ENNReal.ofReal (p.ω k γ) *
      (((p.ν k γ).prod volume).restrict (p.E k γ))
        {q | ENNReal.ofReal (p.N k ^ (-p.f r + τ)) <
          p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}) ≤ ENNReal.ofReal (p.N k ^ (-c))) :
    a.crossingLostMass r bins m (p.N k ^ u) ≤
      ENNReal.ofReal (p.N k ^ (-c) + 40 * Real.pi * p.N k ^ (5 * σ + τ - u)) := by
  have h := a.crossingLostMass_le ha hN hκ hB bins m (Real.rpow_pos_of_pos hN u)
    (ENNReal.ofReal (p.N k ^ (-p.f r + τ))) hg hmap
  calc
    _ ≤ _ := h
    _ ≤ ENNReal.ofReal (p.N k ^ (-c)) +
        ENNReal.ofReal (40 * Real.pi * p.N k ^ (5 * σ + τ - u)) := by
      apply add_le_add hbad
      calc
        _ ≤ ENNReal.ofReal (40 * Real.pi * p.N k ^ (5 * σ + τ - u)) * 1 :=
          mul_le_mul (crossing_relative_cost_bound hN hκ hκN) hmass zero_le zero_le
        _ = _ := mul_one _
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

theorem pruning_loss_small {N κ σ τ u c : ℝ} (hN : 0 < N) (hκ : 1 ≤ κ)
    (hκN : κ ≤ N ^ σ) (hbad : 4 * N ^ (-c) ≤ N ^ (-σ))
    (hcost : 160 * Real.pi * N ^ (5 * σ + τ - u) ≤ N ^ (-σ)) :
    N ^ (-c) + 40 * Real.pi * N ^ (5 * σ + τ - u) ≤ (2 * κ)⁻¹ := by
  have hκ0 : 0 < κ := by linarith
  have hi : N ^ (-σ) ≤ κ⁻¹ := by
    rw [Real.rpow_neg hN.le]
    exact inv_anti₀ hκ0 hκN
  have heq : (2 * κ)⁻¹ = κ⁻¹ / 2 := by field_simp
  rw [heq]
  nlinarith

end Submission.Obl.k4_balanced_native_packet_transport.CPF
