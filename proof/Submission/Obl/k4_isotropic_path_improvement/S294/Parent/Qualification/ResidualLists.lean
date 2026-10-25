-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ResidualLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ResidualLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ResidualLists.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ResidualLists.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterLists

/-!
The actual scalar residual derivative in a parameter zoom. Full coefficient
bins and the time-only row comparison give finite residual lists before
removing the velocity condition with original palette weights.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

noncomputable section

/-- Variation of the normalized residual derivative within one full
coefficient block and one time cell. The row may vary with time. -/
theorem residual_derivative_variation
    (a a' : EuclideanSpace ℝ (Fin 3)) (v v' F F' : Fin 2 → ℝ)
    (t t' p K : ℝ) (hp : 0 ≤ p) (hK : 1 ≤ K)
    (ha : ∀ j, |a j - a' j| ≤ p) (hv : ∀ j, |v j - v' j| ≤ p)
    (hvel : ∀ j, |v j| ≤ K) (hF : ∀ j, |F' j| ≤ K)
    (hrow : ∀ j, |F j - F' j| ≤ 2 * K * p)
    (ht : |t| ≤ 1) (hgap : |t - t'| ≤ p) (hquad : |a' 2| ≤ K) :
    |(a 1 + 2 * t * a 2 - ∑ j, F j * v j) -
      (a' 1 + 2 * t' * a' 2 - ∑ j, F' j * v' j)| ≤ 11 * K ^ 2 * p := by
  have hpoly : |(a 1 + 2 * t * a 2) - (a' 1 + 2 * t' * a' 2)| ≤
      (3 + 2 * K) * p := by
    rw [show (a 1 + 2 * t * a 2) - (a' 1 + 2 * t' * a' 2) =
      (a 1 - a' 1) + 2 * t * (a 2 - a' 2) + 2 * (t - t') * a' 2 by ring]
    calc
      _ ≤ |a 1 - a' 1| + |2 * t * (a 2 - a' 2)| + |2 * (t - t') * a' 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |a 1 - a' 1| + 2 * |t| * |a 2 - a' 2| + 2 * |t - t'| * |a' 2| := by
        simp only [abs_mul]; norm_num
      _ ≤ p + 2 * p + 2 * p * K := by
        have h2 := mul_le_mul ht (ha 2) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        have h3 := mul_le_mul hgap hquad (abs_nonneg _) hp
        nlinarith [ha 1]
      _ = _ := by ring
  have hterm (j : Fin 2) : |F j * v j - F' j * v' j| ≤ (2 * K ^ 2 + K) * p := by
    rw [show F j * v j - F' j * v' j = (F j - F' j) * v j + F' j * (v j - v' j) by ring]
    calc
      _ ≤ |(F j - F' j) * v j| + |F' j * (v j - v' j)| := abs_add_le _ _
      _ = |F j - F' j| * |v j| + |F' j| * |v j - v' j| := by simp only [abs_mul]
      _ ≤ (2 * K * p) * K + K * p := by
        gcongr
        · exact hrow j
        · exact hvel j
        · exact hF j
        · exact hv j
      _ = _ := by ring
  have hsum : |(∑ j, F j * v j) - ∑ j, F' j * v' j| ≤ (4 * K ^ 2 + 2 * K) * p := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : Fin 2, |F j * v j - F' j * v' j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 2, (2 * K ^ 2 + K) * p := Finset.sum_le_sum fun j _ => hterm j
      _ = _ := by simp; ring
  calc
    _ = |((a 1 + 2 * t * a 2) - (a' 1 + 2 * t' * a' 2)) -
      ((∑ j, F j * v j) - ∑ j, F' j * v' j)| := by congr 1; ring
    _ ≤ |(a 1 + 2 * t * a 2) - (a' 1 + 2 * t' * a' 2)| +
      |(∑ j, F j * v j) - ∑ j, F' j * v' j| := abs_sub _ _
    _ ≤ (3 + 2 * K) * p + (4 * K ^ 2 + 2 * K) * p := add_le_add hpoly hsum
    _ ≤ 11 * K ^ 2 * p := by
      have hKsq : K ≤ K ^ 2 := by nlinarith
      have hdiff : 3 + 4 * K ≤ 7 * K ^ 2 := by nlinarith
      nlinarith [mul_nonneg hp (sub_nonneg.mpr hdiff)]

/-- One full parameter block contributes only boundedly many scalar
residual bins in a zoom cell; the time-only row may be merely measurable. -/
theorem residual_bin_count (S : Finset ℤ)
    (a : ℤ → EuclideanSpace ℝ (Fin 3)) (v : ℤ → Fin 2 → ℝ) (t : ℤ → ℝ)
    (F : ℝ → Fin 2 → ℝ) (q : Fin 3 → ℤ) (qv : Fin 2 → ℤ) (qtime : ℤ)
    (p ρ K : ℝ) (hp : 0 < p) (hρp : ρ ≤ p) (hK : 1 ≤ K)
    (hcoeff : ∀ z ∈ S, Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode p (a z) = q)
    (hvelocity : ∀ z ∈ S, ∀ j, ⌊v z j / p⌋ = qv j)
    (htime : ∀ z ∈ S, ⌊t z / p⌋ = qtime)
    (ht : ∀ z ∈ S, |t z| ≤ 1) (hquad : ∀ z ∈ S, |a z 2| ≤ K)
    (hvel : ∀ z ∈ S, ∀ j, |v z j| ≤ K)
    (hF : ∀ z ∈ S, ∀ j, |F (t z) j| ≤ K)
    (hrow : ∀ z ∈ S, ∀ z' ∈ S, ∀ j,
      |F (t z) j - F (t z') j| ≤ K * (|t z - t z'| + ρ))
    (hbin : ∀ z ∈ S, ⌊(a z 1 + 2 * t z * a z 2 - ∑ j, F (t z) j * v z j) / p⌋ = z) :
    (S.card : ℝ) ≤ 22 * K ^ 2 + 5 := by
  have hdiam : ∀ z ∈ S, ∀ z' ∈ S, |(z : ℝ) - (z' : ℝ)| ≤ 11 * K ^ 2 + 1 := by
    intro z hz z' hz'
    have hac (j : Fin 3) : |a z j - a z' j| ≤ p := by
      have hq : ⌊a z j / p⌋ = ⌊a z' j / p⌋ :=
        congrFun ((hcoeff z hz).trans (hcoeff z' hz').symm) j
      have h := (Int.abs_sub_lt_one_of_floor_eq_floor hq).le
      simpa only [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp, one_mul] using h
    have hvc (j : Fin 2) : |v z j - v z' j| ≤ p := by
      have h := (Int.abs_sub_lt_one_of_floor_eq_floor
        ((hvelocity z hz j).trans (hvelocity z' hz' j).symm)).le
      simpa only [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp, one_mul] using h
    have hts : |t z - t z'| ≤ p := by
      have h := (Int.abs_sub_lt_one_of_floor_eq_floor
        ((htime z hz).trans (htime z' hz').symm)).le
      simpa only [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp, one_mul] using h
    have hrows (j : Fin 2) : |F (t z) j - F (t z') j| ≤ 2 * K * p := by
      calc
        _ ≤ K * (|t z - t z'| + ρ) := hrow z hz z' hz' j
        _ ≤ K * (p + p) := mul_le_mul_of_nonneg_left (add_le_add hts hρp) (by linarith)
        _ = _ := by ring
    have hvar := residual_derivative_variation (a z) (a z') (v z) (v z')
      (F (t z)) (F (t z')) (t z) (t z') p K hp.le hK hac hvc (hvel z hz)
      (hF z' hz') hrows (ht z hz) hts (hquad z' hz')
    have hscaled : |(a z 1 + 2 * t z * a z 2 - ∑ j, F (t z) j * v z j) / p -
        (a z' 1 + 2 * t z' * a z' 2 - ∑ j, F (t z') j * v z' j) / p| ≤ 11 * K ^ 2 := by
      rwa [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have h := Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound
      ((a z 1 + 2 * t z * a z 2 - ∑ j, F (t z) j * v z j) / p)
      ((a z' 1 + 2 * t z' * a z' 2 - ∑ j, F (t z') j * v z' j) / p)
    rw [hbin z hz, hbin z' hz', Int.cast_sub] at h
    linarith
  have h := Submission.Obl.k4_scalar_coefficient_clustering.card_int_grid_of_diameter S
    (show 0 ≤ 11 * K ^ 2 + 1 by positivity) hdiam
  linarith

/-- A full parameter palette produces the actual residual-velocity list
for a fixed finer velocity bin, with each bin witnessed by an occurrence. -/
theorem residual_list_of_parameter_palette {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (S : Finset ℤ) (block : ℤ → ι)
    (a : ℤ → EuclideanSpace ℝ (Fin 3)) (v : ℤ → Fin 2 → ℝ) (t : ℤ → ℝ)
    (F : ℝ → Fin 2 → ℝ) (q : ι → Fin 3 → ℤ) (qv : ι → Fin 2 → ℤ) (qtime : ℤ)
    (p ρ K : ℝ) (hp : 0 < p) (hρp : ρ ≤ p) (hK : 1 ≤ K)
    (hblock : ∀ z ∈ S, block z ∈ B)
    (hcoeff : ∀ z ∈ S, Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode p (a z) = q (block z))
    (hvelocity : ∀ z ∈ S, ∀ j, ⌊v z j / p⌋ = qv (block z) j)
    (htime : ∀ z ∈ S, ⌊t z / p⌋ = qtime)
    (ht : ∀ z ∈ S, |t z| ≤ 1) (hquad : ∀ z ∈ S, |a z 2| ≤ K)
    (hvel : ∀ z ∈ S, ∀ j, |v z j| ≤ K)
    (hF : ∀ z ∈ S, ∀ j, |F (t z) j| ≤ K)
    (hrow : ∀ z ∈ S, ∀ z' ∈ S, ∀ j,
      |F (t z) j - F (t z') j| ≤ K * (|t z - t z'| + ρ))
    (hbin : ∀ z ∈ S, ⌊(a z 1 + 2 * t z * a z 2 - ∑ j, F (t z) j * v z j) / p⌋ = z) :
    (S.card : ℝ) ≤ (B.card : ℝ) * (22 * K ^ 2 + 5) := by
  have hc := Finset.card_eq_sum_card_fiberwise (f := block) (s := S) (t := B) hblock
  calc
    _ = ∑ b ∈ B, ((S.filter fun z => block z = b).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _b ∈ B, (22 * K ^ 2 + 5) := by
      apply Finset.sum_le_sum
      intro b _
      apply residual_bin_count _ a v t F (q b) (qv b) qtime p ρ K hp hρp hK
      · intro z hz
        obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
        simpa only [heq] using hcoeff z hz
      · intro z hz j
        obtain ⟨hz, heq⟩ := Finset.mem_filter.mp hz
        simpa only [heq] using hvelocity z hz j
      · exact fun z hz => htime z (Finset.mem_filter.mp hz).1
      · exact fun z hz => ht z (Finset.mem_filter.mp hz).1
      · exact fun z hz => hquad z (Finset.mem_filter.mp hz).1
      · exact fun z hz => hvel z (Finset.mem_filter.mp hz).1
      · exact fun z hz => hF z (Finset.mem_filter.mp hz).1
      · exact fun z hz z' hz' => hrow z (Finset.mem_filter.mp hz).1 z' (Finset.mem_filter.mp hz').1
      · exact fun z hz => hbin z (Finset.mem_filter.mp hz).1
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
