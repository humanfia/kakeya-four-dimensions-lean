-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ParameterLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ParameterLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ParameterLists.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ParameterLists.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_scalar_coefficient_clustering.Bins
import Submission.Obl.k4_matching_homogeneous_records.Offsets

/-!
Original coefficient-block floors and cell occupation floors give local
parameter lists. A quadratic coefficient block has a bounded derivative
palette in one physical time cell. These support lists survive later deletions.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_scalar_coefficient_clustering

noncomputable section

/-- Counting active parameter blocks pays for their ORIGINAL prior floors,
then for their cell-entry duration floors. -/
theorem parameter_block_palette {ι : Type*} (B : Finset ι)
    (prior entry : ι → ℝ) (K p mass : ℝ)
    (hK : 0 < K) (hp : 0 < p) (hmass : 0 < mass)
    (hprior : ∀ b ∈ B, mass / K ≤ prior b)
    (hentry : ∀ b ∈ B, p * prior b / K ≤ entry b)
    (hcap : ∑ b ∈ B, entry b ≤ K * p * mass) :
    (B.card : ℝ) ≤ K ^ 3 := by
  have hfloor (b : ι) (hb : b ∈ B) : p * mass ≤ K ^ 2 * entry b := by
    have h1 := (div_le_iff₀ hK).mp (hprior b hb)
    have h2 := (div_le_iff₀ hK).mp (hentry b hb)
    have hp1 := mul_le_mul_of_nonneg_left h1 hp.le
    have hK2 := mul_le_mul_of_nonneg_left h2 hK.le
    nlinarith only [hp1, hK2]
  have hsum : (B.card : ℝ) * (p * mass) ≤ K ^ 2 * (K * p * mass) := by
    calc
      _ = ∑ _b ∈ B, p * mass := by simp
      _ ≤ ∑ b ∈ B, K ^ 2 * entry b := Finset.sum_le_sum fun b hb => hfloor b hb
      _ = K ^ 2 * ∑ b ∈ B, entry b := (Finset.mul_sum _ _ _).symm
      _ ≤ K ^ 2 * (K * p * mass) := mul_le_mul_of_nonneg_left hcap (sq_nonneg _)
  apply (mul_le_mul_iff_left₀ (mul_pos hp hmass)).mp
  nlinarith only [hsum]

/-- In one coefficient block and one physical time cell, the derivative
of a bounded quadratic meets only boundedly many bins of the same width. -/
theorem derivative_bin_count (S : Finset ℤ)
    (a : ℤ → EuclideanSpace ℝ (Fin 3)) (t : ℤ → ℝ)
    (q : Fin 3 → ℤ) (qtime : ℤ) (p K : ℝ)
    (hp : 0 < p) (hK : 0 ≤ K)
    (hcoeff : ∀ z ∈ S, coefficientCode p (a z) = q)
    (htime : ∀ z ∈ S, ⌊t z / p⌋ = qtime)
    (ht : ∀ z ∈ S, t z ∈ Set.Icc (0 : ℝ) 1)
    (hquad : ∀ z ∈ S, |a z 2| ≤ K)
    (hbin : ∀ z ∈ S, ⌊(a z 1 + 2 * t z * a z 2) / p⌋ = z) :
    (S.card : ℝ) ≤ 4 * K + 10 := by
  have hdiam : ∀ z ∈ S, ∀ z' ∈ S, |(z : ℝ) - (z' : ℝ)| ≤ 2 * K + 4 := by
    intro z hz z' hz'
    have hac (j : Fin 3) : |a z j - a z' j| ≤ p := by
      have hq : ⌊a z j / p⌋ = ⌊a z' j / p⌋ :=
        congrFun ((hcoeff z hz).trans (hcoeff z' hz').symm) j
      have h := (Int.abs_sub_lt_one_of_floor_eq_floor hq).le
      simpa only [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp, one_mul] using h
    have hts : |t z - t z'| ≤ p := by
      have h := (Int.abs_sub_lt_one_of_floor_eq_floor
        ((htime z hz).trans (htime z' hz').symm)).le
      simpa only [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp, one_mul] using h
    have htz : |t z| ≤ 1 := by
      rw [abs_of_nonneg (ht z hz).1]
      exact (ht z hz).2
    have hvalue : |(a z 1 + 2 * t z * a z 2) -
        (a z' 1 + 2 * t z' * a z' 2)| ≤ (3 + 2 * K) * p := by
      rw [show (a z 1 + 2 * t z * a z 2) - (a z' 1 + 2 * t z' * a z' 2) =
        (a z 1 - a z' 1) + 2 * t z * (a z 2 - a z' 2) +
          2 * (t z - t z') * a z' 2 by ring]
      calc
        _ ≤ |a z 1 - a z' 1| + |2 * t z * (a z 2 - a z' 2)| +
            |2 * (t z - t z') * a z' 2| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ = |a z 1 - a z' 1| + 2 * |t z| * |a z 2 - a z' 2| +
            2 * |t z - t z'| * |a z' 2| := by simp only [abs_mul]; norm_num
        _ ≤ p + 2 * p + 2 * p * K := by
          have h2 := mul_le_mul htz (hac 2) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
          have h3 := mul_le_mul hts (hquad z' hz') (abs_nonneg _) hp.le
          nlinarith [hac 1]
        _ = (3 + 2 * K) * p := by ring
    have hscaled : |(a z 1 + 2 * t z * a z 2) / p -
        (a z' 1 + 2 * t z' * a z' 2) / p| ≤ 3 + 2 * K := by
      rwa [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have h := Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound
      ((a z 1 + 2 * t z * a z 2) / p) ((a z' 1 + 2 * t z' * a z' 2) / p)
    rw [hbin z hz, hbin z' hz', Int.cast_sub] at h
    linarith
  have h := card_int_grid_of_diameter S (show 0 ≤ 2 * K + 4 by positivity) hdiam
  linarith

/-- Local parameter lists give actual scalar derivative lists. Each
derivative bin is represented by an original occurrence, with its original
parameter-block label. -/
theorem derivative_list_of_parameter_palette {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (S : Finset ℤ) (block : ℤ → ι)
    (a : ℤ → EuclideanSpace ℝ (Fin 3)) (t : ℤ → ℝ)
    (q : ι → Fin 3 → ℤ) (qtime : ℤ) (p K : ℝ)
    (hp : 0 < p) (hK : 0 ≤ K)
    (hblock : ∀ z ∈ S, block z ∈ B)
    (hcoeff : ∀ z ∈ S, coefficientCode p (a z) = q (block z))
    (htime : ∀ z ∈ S, ⌊t z / p⌋ = qtime)
    (ht : ∀ z ∈ S, t z ∈ Set.Icc (0 : ℝ) 1)
    (hquad : ∀ z ∈ S, |a z 2| ≤ K)
    (hbin : ∀ z ∈ S, ⌊(a z 1 + 2 * t z * a z 2) / p⌋ = z) :
    (S.card : ℝ) ≤ (B.card : ℝ) * (4 * K + 10) := by
  have hc := Finset.card_eq_sum_card_fiberwise (f := block) (s := S) (t := B) hblock
  calc
    _ = ∑ b ∈ B, ((S.filter fun z => block z = b).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _b ∈ B, (4 * K + 10) := by
      apply Finset.sum_le_sum
      intro b _
      apply derivative_bin_count _ a t (q b) qtime p K hp hK
      · intro z hz
        obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
        simpa only [heq] using hcoeff z hz
      · exact fun z hz => htime z (Finset.mem_filter.mp hz).1
      · exact fun z hz => ht z (Finset.mem_filter.mp hz).1
      · exact fun z hz => hquad z (Finset.mem_filter.mp hz).1
      · exact fun z hz => hbin z (Finset.mem_filter.mp hz).1
    _ = (B.card : ℝ) * (4 * K + 10) := by simp only [Finset.sum_const, nsmul_eq_mul]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
