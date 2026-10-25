-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.BroadCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/BroadCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/BroadCells.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/BroadCells.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_mk_visibility
import Submission.Obl.k4_mk_finite_duality
import Submission.Obl.k4_mk_grid_transfer.Grid

/-!
Finite determinant budgets for the physical-velocity-graph argument in
Section 6. A broad family in each occupied cell forces a lower bound for
the number of cells, independently of the number of lines.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open scoped BigOperators
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

/-- The lattice form of the accepted determinant Kakeya estimate. -/
theorem lattice_kakeya_bound (n : ℕ) (hn : 3 ≤ n) (hn4 : n ≤ 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z : Fin m → Fin n → ℤ), Function.Injective z →
      ∀ (N : Fin n → ℕ)
        (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
        (w : (i : Fin n) → Fin (N i) → ℝ),
      (∀ i k, ‖e i k‖ = 1) → (∀ i k, 0 ≤ w i k) →
      (∑ q : Fin m, tubeSum 3 a e w (latticePoint (z q)) ^
        ((1 : ℝ) / ((n : ℝ) - 1))) ≤
        C * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
  obtain ⟨K, hK, hvisibility⟩ := Submission.k4_mk_visibility n hn hn4
  refine ⟨K ^ ((n : ℝ) / ((n : ℝ) - 1)), Real.rpow_pos_of_pos hK _, ?_⟩
  intro m z hz N a e w he hw
  let b : Fin m → (i : Fin n) → Fin (N i) → ℝ := fun q i k =>
    (lineTube 3 (a i k) (e i k)).indicator (fun _ => (1 : ℝ)) (latticePoint (z q))
  apply Submission.k4_mk_finite_duality n (by omega) K hK m N e b
    (fun q i k => Set.indicator_nonneg (fun _ _ => zero_le_one) _) ?_ w hw
  intro M hM hsum
  obtain ⟨A, hdet, hbudget⟩ := hvisibility m z hz M hM hsum
  exact ⟨A, hdet, fun i k => hbudget (a i k) (e i k) (he i k)⟩

/-- Power mean combines local lower bounds with a summed upper budget. -/
theorem finite_power_mean_budget {α : Type*} [Fintype α]
    (mass F : α → ℝ) (hmass : ∀ q, 0 ≤ mass q)
    (p c B : ℝ) (hp : 1 ≤ p) (hc : 0 ≤ c)
    (hcell : ∀ q, c * mass q ^ p ≤ F q) (hbudget : ∑ q, F q ≤ B) :
    c * (∑ q, mass q) ^ p ≤ (Fintype.card α : ℝ) ^ (p - 1) * B := by
  classical
  calc
    c * (∑ q, mass q) ^ p ≤
        c * ((Fintype.card α : ℝ) ^ (p - 1) * ∑ q, mass q ^ p) := by
      apply mul_le_mul_of_nonneg_left _ hc
      simpa using Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
        Finset.univ (f := mass) hp (fun q _ => hmass q)
    _ = (Fintype.card α : ℝ) ^ (p - 1) * (∑ q, c * mass q ^ p) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card α : ℝ) ^ (p - 1) * B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_le_sum (fun q _ => hcell q)).trans hbudget

/-- A cellwise determinant lower bound forces a cardinality constraint.
For the velocity-graph argument `θ` is the successful determinant fraction
and `mass` is the cell incidence mass divided by its crossing duration. -/
theorem broad_cell_power_budget {n m : ℕ} (hn : 2 ≤ n)
    (mass F : Fin m → ℝ) (hmass : ∀ q, 0 ≤ mass q)
    (θ B : ℝ) (hθ : 0 ≤ θ)
    (hcell : ∀ q, θ * mass q ^ n ≤ F q)
    (hbudget : ∑ q, F q ^ ((1 : ℝ) / ((n : ℝ) - 1)) ≤ B) :
    θ ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
      (∑ q, mass q) ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤
      (m : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) * B := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) - 1 := by linarith
  have hp : 1 ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    rw [le_div_iff₀ hn0]
    linarith
  have heq : (n : ℝ) / ((n : ℝ) - 1) - 1 = 1 / ((n : ℝ) - 1) := by
    field_simp
    ring
  have hlocal (q : Fin m) : θ ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
      mass q ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤ F q ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
    have h := Real.rpow_le_rpow (mul_nonneg hθ (pow_nonneg (hmass q) n))
      (hcell q) (by positivity : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1))
    rw [Real.mul_rpow hθ (pow_nonneg (hmass q) n),
      ← Real.rpow_natCast_mul (hmass q) n] at h
    simpa only [mul_one_div] using h
  have hmean := finite_power_mean_budget mass
    (fun q => F q ^ ((1 : ℝ) / ((n : ℝ) - 1))) hmass
    ((n : ℝ) / ((n : ℝ) - 1)) (θ ^ ((1 : ℝ) / ((n : ℝ) - 1))) B
    hp (Real.rpow_nonneg hθ _) hlocal hbudget
  simpa only [Fintype.card_fin, heq] using hmean

/-- The determinant cell constraint in dimension four, with all fractional
powers removed. -/
theorem broad_cell_constraint_four {m : ℕ}
    (mass F : Fin m → ℝ) (hmass : ∀ q, 0 ≤ mass q)
    (θ B : ℝ) (hθ : 0 ≤ θ)
    (hcell : ∀ q, θ * mass q ^ 4 ≤ F q)
    (hbudget : ∑ q, F q ^ ((1 : ℝ) / 3) ≤ B) :
    θ * (∑ q, mass q) ^ 4 ≤ (m : ℝ) * B ^ 3 := by
  have h := broad_cell_power_budget (n := 4) (by decide) mass F hmass θ B hθ hcell
    (by norm_num only [Nat.cast_ofNat, show (4 : ℝ) - 1 = 3 by norm_num]; exact hbudget)
  norm_num only [Nat.cast_ofNat, show (4 : ℝ) - 1 = 3 by norm_num] at h
  have hpow := pow_le_pow_left₀
    (mul_nonneg (Real.rpow_nonneg hθ _) (Real.rpow_nonneg (Finset.sum_nonneg (fun q _ => hmass q)) _)) h 3
  simp only [mul_pow] at hpow
  rw [← Real.rpow_mul_natCast hθ,
    ← Real.rpow_mul_natCast (Finset.sum_nonneg (fun q _ => hmass q)),
    ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ m)] at hpow
  norm_num at hpow
  exact hpow

/-- The base-filling step uses the corresponding three-dimensional moment. -/
theorem broad_cell_constraint_three {m : ℕ}
    (mass F : Fin m → ℝ) (hmass : ∀ q, 0 ≤ mass q)
    (θ B : ℝ) (hθ : 0 ≤ θ)
    (hcell : ∀ q, θ * mass q ^ 3 ≤ F q)
    (hbudget : ∑ q, F q ^ ((1 : ℝ) / 2) ≤ B) :
    θ * (∑ q, mass q) ^ 3 ≤ (m : ℝ) * B ^ 2 := by
  have h := broad_cell_power_budget (n := 3) (by decide) mass F hmass θ B hθ hcell
    (by norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num]; exact hbudget)
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] at h
  have hpow := pow_le_pow_left₀
    (mul_nonneg (Real.rpow_nonneg hθ _) (Real.rpow_nonneg
      (Finset.sum_nonneg (fun q _ => hmass q)) _)) h 2
  simp only [mul_pow] at hpow
  rw [← Real.rpow_mul_natCast hθ,
    ← Real.rpow_mul_natCast (Finset.sum_nonneg (fun q _ => hmass q)),
    ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ m)] at hpow
  norm_num at hpow
  exact hpow

/-- Cancellation of the cell mass gives the geometric support bound used
after duration pruning in a physical cube. -/
theorem broad_support_lower_bound_four
    {m : ℕ} {θ C K M b w : ℝ}
    (hM : 0 < M)
    (hb : 0 < b) (hw : 0 < w)
    (hbudget : θ * (M / b) ^ 4 ≤ (m : ℝ) * C ^ 3 * (K * M / w) ^ 4) :
    θ * (w / b) ^ 4 ≤ (m : ℝ) * C ^ 3 * K ^ 4 := by
  have hscale : 0 ≤ (w / M) ^ 4 := by positivity
  have h := mul_le_mul_of_nonneg_right hbudget hscale
  have hMn : M ≠ 0 := hM.ne'
  have hbn : b ≠ 0 := hb.ne'
  have hwn : w ≠ 0 := hw.ne'
  field_simp at h ⊢
  nlinarith

/-- Concrete four-dimensional broad-cell estimate. The cell count is the
only cardinality on the right; the line families have arbitrary sizes. -/
theorem four_dimensional_broad_lattice_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (N : Fin 4 → ℕ)
        (a e : (i : Fin 4) → Fin (N i) → EuclideanSpace ℝ (Fin 4))
        (w : (i : Fin 4) → Fin (N i) → ℝ),
      (∀ i k, ‖e i k‖ = 1) → (∀ i k, 0 ≤ w i k) →
      ∀ (mass : Fin m → ℝ) (θ : ℝ), (∀ q, 0 ≤ mass q) → 0 ≤ θ →
      (∀ q, θ * mass q ^ 4 ≤ tubeSum 3 a e w (latticePoint (z q))) →
      θ * (∑ q, mass q) ^ 4 ≤ (m : ℝ) * C ^ 3 * ∏ i : Fin 4, ∑ k : Fin (N i), w i k := by
  obtain ⟨C, hC, hgrid⟩ := lattice_kakeya_bound 4 (by decide) (by decide)
  refine ⟨C, hC, ?_⟩
  intro m z hz N a e w he hw mass θ hmass hθ hcell
  have hbudget : ∑ q : Fin m, tubeSum 3 a e w (latticePoint (z q)) ^ ((1 : ℝ) / 3) ≤
      C * ∏ i : Fin 4, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / 3) := by
    simpa only [Nat.cast_ofNat, show (4 : ℝ) - 1 = 3 by norm_num] using hgrid m z hz N a e w he hw
  have h := broad_cell_constraint_four mass (fun q => tubeSum 3 a e w (latticePoint (z q)))
    hmass θ _ hθ hcell hbudget
  have hcube : (∏ i : Fin 4, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / 3)) ^ 3 =
      ∏ i : Fin 4, ∑ k : Fin (N i), w i k := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_mul_natCast (Finset.sum_nonneg (fun k _ => hw i k))]
    norm_num
  rw [mul_pow, hcube] at h
  simpa only [mul_assoc] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
