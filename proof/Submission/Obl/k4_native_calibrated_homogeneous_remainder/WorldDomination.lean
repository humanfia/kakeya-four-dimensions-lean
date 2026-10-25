import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WorldRestriction
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.RawDensities
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TypicalOperations

/-! Exact domination and normalization estimates for a retained world family. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_dyadic_crop_worlds (sum_equivFin)

theorem keptWeightSum_inv_bound {p : Data} (hp : RawValid p)
    (S : (k : ℕ) → Finset (Fin (p.W k))) (K : ℕ → ℝ)
    (hK : ∀ k, 0 < K k) (ht : ∀ k, 0 < keptWeightSum p S k)
    (hretain : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤
      ∑ b ∈ S k, ENNReal.ofReal (p.ω k b) * selected p k b univ) :
    ∀ k, (keptWeightSum p S k)⁻¹ ≤ K k := by
  have hp0 := hp
  obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hp
  intro k
  have hle : ENNReal.ofReal ((K k)⁻¹) ≤ ENNReal.ofReal (keptWeightSum p S k) := by
    apply (hretain k).trans
    calc
      _ ≤ ∑ b ∈ S k, ENNReal.ofReal (p.ω k b) :=
        Finset.sum_le_sum fun b _ => by
          simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal (p.ω k b)))
            (hp0.selected_mass_le_one k b)
      _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun b _ => (hfmt k).2.1 b)).symm
  have hre : (K k)⁻¹ ≤ keptWeightSum p S k :=
    (ENNReal.ofReal_le_ofReal_iff (ht k).le).mp hle
  calc
    _ ≤ ((K k)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (hK k)) hre
    _ = K k := inv_inv _

theorem keepWorlds_law_domination {p : Data} (hp : RawValid p)
    (S : (k : ℕ) → Finset (Fin (p.W k))) (K : ℕ → ℝ)
    (ht : ∀ k, 0 < keptWeightSum p S k) (k : ℕ)
    (A : Set (Fin (p.W k) × Incidence)) :
    worldLaw (fun b => ENNReal.ofReal ((keepWorlds p S K).ω k b))
      (selected (keepWorlds p S K) k)
      ((fun z => (keptWorldIndex (S k) z.1, z.2)) ⁻¹' A) ≤
        ENNReal.ofReal ((keptWeightSum p S k)⁻¹) *
          worldLaw (fun b => ENNReal.ofReal (p.ω k b)) (selected p k) A := by
  obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hp
  rw [worldLaw_apply, worldLaw_apply]
  change (∑ b : Fin (S k).card,
    ENNReal.ofReal (p.ω k (keptWorldIndex (S k) b) / keptWeightSum p S k) *
      selected p k (keptWorldIndex (S k) b) {z | (keptWorldIndex (S k) b, z) ∈ A}) ≤ _
  change (∑ b : Fin (S k).card,
    ENNReal.ofReal (p.ω k ((S k).equivFin.symm b).1 / keptWeightSum p S k) *
      selected p k ((S k).equivFin.symm b).1 {z | (((S k).equivFin.symm b).1, z) ∈ A}) ≤ _
  rw [sum_equivFin (S k) (fun b => ENNReal.ofReal (p.ω k b / keptWeightSum p S k) *
    selected p k b {z | (b, z) ∈ A})]
  have heq (b : Fin (p.W k)) : ENNReal.ofReal (p.ω k b / keptWeightSum p S k) =
      ENNReal.ofReal ((keptWeightSum p S k)⁻¹) * ENNReal.ofReal (p.ω k b) := by
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (inv_nonneg.mpr (ht k).le)]
  simp_rw [heq, mul_assoc]
  rw [← Finset.mul_sum]
  apply mul_le_mul' le_rfl
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ (S k))

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
