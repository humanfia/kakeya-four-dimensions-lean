-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.LiteralRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/LiteralRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/LiteralRows.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.NativeVelocityGraph

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open Set MeasureTheory

noncomputable section

/-- Finite rows extend to the literal integer physical codes. -/
theorem exists_literal_row_extension {n : ℕ} (cell : Fin n → Fin 4 → ℤ)
    (hinj : Function.Injective cell) (G : Fin n → Fin 3 → ℝ)
    {bound : ℝ} (hbound : 0 ≤ bound) (hG : ∀ i j, |G i j| ≤ bound) :
    ∃ row : (Fin 4 → ℤ) → Fin 3 → ℝ, Measurable row ∧
      (∀ q j, |row q j| ≤ bound) ∧ ∀ i, row (cell i) = G i := by
  classical
  let row := Function.extend cell G (fun _ => 0)
  refine ⟨row, measurable_of_countable _, ?_, fun i => hinj.extend_apply _ _ i⟩
  intro q j
  by_cases hq : ∃ i, cell i = q
  · obtain ⟨i, rfl⟩ := hq
    rw [show row (cell i) = G i from hinj.extend_apply _ _ i]
    exact hG i j
  · simpa only [row, Function.extend_apply' G (fun _ => 0) q hq, Pi.zero_apply, abs_zero]
      using hbound

/-- The native MK4 construction produces measurable rows on literal
physical codes, with all losses still charged to its original law. -/
theorem anisotropic_native_literal_rows :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type} [MeasurableSpace X],
      ∀ a : AnisotropicVelocityData X, a.Valid →
      ∀ (state : X × ℝ → Fin 4 → ℤ) (P : Set (X × ℝ)),
        (∀ q ∈ P, a.cell (a.code q) = state q) →
      ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (T : Set (X × ℝ)),
        Measurable row ∧ MeasurableSet T ∧ (∀ q j, |row q j| ≤ 28 * a.bound ^ 6) ∧
        a.incidence.real Tᶜ ≤ a.broadMass + a.fraction * a.incidence.real univ ∧
        (a.fraction * a.liftRho / 4) ^ 4 * a.broadMass ^ 4 ≤
          256 * C ^ 3 * a.bound ^ 9 * a.priorScale ^ 4 * a.mesh ^ ((1 - a.dimension) / 3) ∧
        ∀ q ∈ T ∩ P, q ∈ a.bounded ∧
          |a.scalar q - ∑ j, row (state q) j * a.base q j| ≤ 80 * a.bound ^ 7 * a.liftRho := by
  obtain ⟨C, hC, hgraph⟩ := anisotropic_native_velocity_graph
  refine ⟨C, hC, ?_⟩
  intro X instX a ha state P hstate
  obtain ⟨G, T, hT, hGmeas, hG, hloss, hmoment, hfit⟩ := hgraph a ha
  obtain ⟨row, hrowMeas, hrow, heq⟩ := exists_literal_row_extension a.cell ha.cellInjective G
    (by positivity : 0 ≤ 28 * a.bound ^ 6) hG
  refine ⟨row, T, hrowMeas, hT, hrow, hloss, hmoment, ?_⟩
  intro q hq
  have hh := hfit q hq.1
  rw [← hstate q hq.2, heq]
  exact hh

/-- One constant is fixed for every original packet, before the source,
the path and its assigned-line subtype are chosen. -/
def nativeRowConstant : ℝ := Classical.choose anisotropic_native_literal_rows

theorem nativeRowConstant_pos : 0 < nativeRowConstant :=
  (Classical.choose_spec anisotropic_native_literal_rows).1

theorem native_literal_rows_fixed {X : Type} [MeasurableSpace X]
    (a : AnisotropicVelocityData X) (ha : a.Valid)
    (state : X × ℝ → Fin 4 → ℤ) (P : Set (X × ℝ))
    (hstate : ∀ q ∈ P, a.cell (a.code q) = state q) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (T : Set (X × ℝ)),
      Measurable row ∧ MeasurableSet T ∧ (∀ q j, |row q j| ≤ 28 * a.bound ^ 6) ∧
      a.incidence.real Tᶜ ≤ a.broadMass + a.fraction * a.incidence.real univ ∧
      (a.fraction * a.liftRho / 4) ^ 4 * a.broadMass ^ 4 ≤
        256 * nativeRowConstant ^ 3 * a.bound ^ 9 * a.priorScale ^ 4 *
          a.mesh ^ ((1 - a.dimension) / 3) ∧
      ∀ q ∈ T ∩ P, q ∈ a.bounded ∧
        |a.scalar q - ∑ j, row (state q) j * a.base q j| ≤ 80 * a.bound ^ 7 * a.liftRho :=
  (Classical.choose_spec anisotropic_native_literal_rows).2 a ha state P hstate

/-- A small numerical MK4 remainder bounds the bad mass relative to the
earlier coarse mass, including when that earlier mass is zero. -/
theorem bad_mass_le_of_quartic_remainder {bad M coefficient remainder ε : ℝ}
    (hbad : 0 ≤ bad) (hM : 0 ≤ M) (hc : 0 < coefficient) (hε : 0 ≤ ε)
    (hmoment : coefficient * bad ^ 4 ≤ remainder * M ^ 4)
    (hbudget : remainder ≤ coefficient * ε ^ 4) : bad ≤ ε * M := by
  have hh : coefficient * bad ^ 4 ≤ coefficient * (ε * M) ^ 4 := by
    refine hmoment.trans ((mul_le_mul_of_nonneg_right hbudget (pow_nonneg hM 4)).trans_eq ?_)
    ring
  have hp : bad ^ 4 ≤ (ε * M) ^ 4 := le_of_mul_le_mul_left hh hc
  exact (pow_le_pow_iff_left₀ hbad (mul_nonneg hε hM) (by decide : (4 : ℕ) ≠ 0)).mp hp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
