-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.RowPalette, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/RowPalette.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/RowPalette.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/RowPalette.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Lib.K4IncidenceWitnesses
import Submission.Obl.k4_matching_homogeneous_records.Offsets

/-!
The coarse palette of a physical velocity row. Fixed bins for three
transverse base witnesses and their scalar derivatives give a bounded
number of row bins; weighted witnesses then bound the whole row palette.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Matrix
open Submission.Obl.k4_real_conic_restoration
open Submission.Lib.K4IncidenceWitnesses

noncomputable section

/-- Rows tested on nearby transverse bases, with nearby derivative values,
can occupy only a polynomially bounded number of bins at that same scale. -/
theorem row_bins_of_transverse_tests
    (S : Finset (Fin 3 → ℤ)) (g w : (Fin 3 → ℤ) → Fin 3 → ℝ)
    (A : (Fin 3 → ℤ) → Matrix (Fin 3) (Fin 3) ℝ) (K scale : ℝ)
    (hK : 1 ≤ K) (hscale : 0 < scale)
    (hrow : ∀ r ∈ S, ∀ j, |g r j| ≤ K)
    (hA : ∀ r ∈ S, ∀ i j, |A r i j| ≤ K)
    (hdet : ∀ r ∈ S, 1 ≤ K * |(A r).det|)
    (hbase : ∀ r ∈ S, ∀ r' ∈ S, ∀ i j, |A r i j - A r' i j| ≤ scale)
    (hderiv : ∀ r ∈ S, ∀ r' ∈ S, ∀ i, |w r i - w r' i| ≤ scale)
    (htest : ∀ r ∈ S, ∀ i, |((A r) *ᵥ g r) i - w r i| ≤ scale)
    (hbin : ∀ r ∈ S, ∀ j, ⌊g r j / scale⌋ = r j) :
    (S.card : ℝ) ≤ (72 * K ^ 4 + 5) ^ 3 := by
  have hK0 : 0 < K := by linarith
  have hdiam : ∀ r ∈ S, ∀ r' ∈ S, ∀ j,
      |(r j : ℝ) - (r' j : ℝ)| ≤ 36 * K ^ 4 + 1 := by
    intro r hr r' hr' j
    have hM (i : Fin 3) : |((A r' - A r) *ᵥ g r') i| ≤ 3 * K * scale := by
      have h := vecMul_bound (v := g r') (Q := (A r' - A r).transpose)
        (hrow r' hr') (fun i j => hbase r' hr' r hr j i)
      simpa only [Matrix.vecMul_transpose] using h i
    have hAn (i : Fin 3) : |((A r) *ᵥ (g r - g r')) i| ≤ 3 * scale + 3 * K * scale := by
      let terms : Fin 4 → ℝ := ![((A r) *ᵥ g r) i - w r i, w r i - w r' i,
        w r' i - ((A r') *ᵥ g r') i, ((A r' - A r) *ᵥ g r') i]
      have heq : ((A r) *ᵥ (g r - g r')) i = ∑ k : Fin 4, terms k := by
        simp [terms, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four]
        ring
      have h := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := terms)
      rw [← heq] at h
      simp [terms, Fin.sum_univ_four] at h
      have ht' := htest r' hr' i
      rw [abs_sub_comm] at ht'
      linarith [htest r hr i, hderiv r hr r' hr' i, hM i]
    have hd : (A r).det ≠ 0 := by
      intro hzero
      have h := hdet r hr
      norm_num [hzero] at h
    have hn := normal_base_bound (A r) (g r - g r') (fun _ => 0) 0 (2 * K ^ 3)
      (3 * scale + 3 * K * scale) hd (inverse_entry_bound hK0 (hA r hr) (hdet r hr))
      (fun _ => by simp; positivity) (fun i => by simpa only [mul_zero, add_zero] using hAn i)
    have hvalue : |g r j - g r' j| ≤ 36 * K ^ 4 * scale := by
      have hE : 3 * scale + 3 * K * scale ≤ 6 * K * scale := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hK) hscale.le]
      calc
        _ ≤ 3 * (2 * K ^ 3) * (3 * scale + 3 * K * scale) := by simpa using hn j
        _ ≤ 3 * (2 * K ^ 3) * (6 * K * scale) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
        _ = 36 * K ^ 4 * scale := by ring
    have hscaled : |g r j / scale - g r' j / scale| ≤ 36 * K ^ 4 := by
      rw [← sub_div, abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
      exact hvalue
    have h := Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound
      (g r j / scale) (g r' j / scale)
    rw [hbin r hr j, hbin r' hr' j, Int.cast_sub] at h
    linarith
  have h := card_pi_grid_of_diameter S (show 0 ≤ 36 * K ^ 4 + 1 by positivity) hdiam
  simp only [Fintype.card_fin] at h
  convert h using 1
  congr 1
  ring

/-- With the base bins fixed, a finite list for the three derivative
values gives the corresponding finite row list. -/
theorem row_bins_with_derivative_palette
    (S : Finset (Fin 3 → ℤ)) (g w : (Fin 3 → ℤ) → Fin 3 → ℝ)
    (A : (Fin 3 → ℤ) → Matrix (Fin 3) (Fin 3) ℝ)
    (L : ℕ) (F : Fin L → Fin 3 → ℝ) (K scale : ℝ)
    (hL : 0 < L) (hK : 1 ≤ K) (hscale : 0 < scale)
    (hrow : ∀ r ∈ S, ∀ j, |g r j| ≤ K)
    (hA : ∀ r ∈ S, ∀ i j, |A r i j| ≤ K)
    (hdet : ∀ r ∈ S, 1 ≤ K * |(A r).det|)
    (hbase : ∀ r ∈ S, ∀ r' ∈ S, ∀ i j, |A r i j - A r' i j| ≤ scale)
    (hlist : ∀ r ∈ S, ∃ k : Fin L, ∀ i, |w r i - F k i| ≤ scale / 2)
    (htest : ∀ r ∈ S, ∀ i, |((A r) *ᵥ g r) i - w r i| ≤ scale)
    (hbin : ∀ r ∈ S, ∀ j, ⌊g r j / scale⌋ = r j) :
    (S.card : ℝ) ≤ (L : ℝ) * (72 * K ^ 4 + 5) ^ 3 := by
  classical
  let color : (Fin 3 → ℤ) → Fin L := fun r =>
    if hr : r ∈ S then Classical.choose (hlist r hr) else ⟨0, hL⟩
  have hcolor (r : Fin 3 → ℤ) (hr : r ∈ S) (i : Fin 3) :
      |w r i - F (color r) i| ≤ scale / 2 := by
    simpa only [color, dite_eq_left hr] using Classical.choose_spec (hlist r hr) i
  have hc := Finset.card_eq_sum_card_fiberwise (f := color) (s := S)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  calc
    (S.card : ℝ) = ∑ k : Fin L, ((S.filter fun r => color r = k).card : ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ _k : Fin L, (72 * K ^ 4 + 5) ^ 3 := by
      apply Finset.sum_le_sum
      intro k _
      apply row_bins_of_transverse_tests _ g w A K scale hK hscale
      · exact fun r hr => hrow r (Finset.mem_filter.mp hr).1
      · exact fun r hr => hA r (Finset.mem_filter.mp hr).1
      · exact fun r hr => hdet r (Finset.mem_filter.mp hr).1
      · exact fun r hr r' hr' => hbase r (Finset.mem_filter.mp hr).1 r'
          (Finset.mem_filter.mp hr').1
      · intro r hr r' hr' i
        obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hr
        obtain ⟨hr', hc'⟩ := Finset.mem_filter.mp hr'
        have h1 := hcolor r hr i
        have h2 := hcolor r' hr' i
        rw [hc] at h1
        rw [hc'] at h2
        calc
          _ ≤ |w r i - F k i| + |F k i - w r' i| := abs_sub_le _ _ _
          _ ≤ scale := by rw [abs_sub_comm (F k i)]; linarith
      · exact fun r hr => htest r (Finset.mem_filter.mp hr).1
      · exact fun r hr => hbin r (Finset.mem_filter.mp hr).1
    _ = (L : ℝ) * (72 * K ^ 4 + 5) ^ 3 := by simp

/-- Weighted tuple witnesses bound a row palette without charging the
number of velocity bins. -/
theorem weighted_witness_count {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : Finset α) (V : Finset β) (W : α → Finset β) (π : β → ℝ)
    (η L : ℝ) (hπ : ∀ v ∈ V, 0 ≤ π v)
    (hsub : ∀ r ∈ R, W r ⊆ V)
    (hweight : ∀ r ∈ R, η ≤ ∑ v ∈ W r, π v)
    (hcount : ∀ v ∈ V, ((R.filter fun r => v ∈ W r).card : ℝ) ≤ L) :
    (R.card : ℝ) * η ≤ L * ∑ v ∈ V, π v := by
  have hexpand (r : α) (hr : r ∈ R) :
      ∑ v ∈ W r, π v = ∑ v ∈ V, if v ∈ W r then π v else 0 := by
    have hfilter : V.filter (fun v => v ∈ W r) = W r := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub r hr h, h⟩⟩
    rw [← Finset.sum_filter, hfilter]
  calc
    (R.card : ℝ) * η = ∑ _r ∈ R, η := by simp
    _ ≤ ∑ r ∈ R, ∑ v ∈ W r, π v := Finset.sum_le_sum fun r hr => hweight r hr
    _ = ∑ r ∈ R, ∑ v ∈ V, if v ∈ W r then π v else 0 :=
      Finset.sum_congr rfl fun r hr => hexpand r hr
    _ = ∑ v ∈ V, ∑ r ∈ R, if v ∈ W r then π v else 0 := Finset.sum_comm
    _ = ∑ v ∈ V, ((R.filter fun r => v ∈ W r).card : ℝ) * π v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ v ∈ V, L * π v := Finset.sum_le_sum fun v hv =>
      mul_le_mul_of_nonneg_right (hcount v hv) (hπ v hv)
    _ = L * ∑ v ∈ V, π v := (Finset.mul_sum _ _ _).symm

theorem palette_count_of_weighted_witnesses {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : Finset α) (V : Finset β) (W : α → Finset β) (π : β → ℝ)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L) (hπ : ∀ v ∈ V, 0 ≤ π v)
    (hmass : ∑ v ∈ V, π v ≤ 1) (hsub : ∀ r ∈ R, W r ⊆ V)
    (hweight : ∀ r ∈ R, η ≤ ∑ v ∈ W r, π v)
    (hcount : ∀ v ∈ V, ((R.filter fun r => v ∈ W r).card : ℝ) ≤ L) :
    (R.card : ℝ) ≤ L / η := by
  apply (le_div_iff₀ hη).mpr
  exact (weighted_witness_count R V W π η L hπ hsub hweight hcount).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass hL)

/-- A fixed velocity tuple can support several derivative-bin choices, but
only their finite number enters the palette count. -/
theorem palette_count_of_colored_witnesses {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : Finset α) (V : Finset β) (W : α → Finset β) (π : β → ℝ)
    (L : ℕ) (color : α → β → Fin L) (η B : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hπ : ∀ v ∈ V, 0 ≤ π v)
    (hmass : ∑ v ∈ V, π v ≤ 1) (hsub : ∀ r ∈ R, W r ⊆ V)
    (hweight : ∀ r ∈ R, η ≤ ∑ v ∈ W r, π v)
    (hcount : ∀ v ∈ V, ∀ i : Fin L,
      ((R.filter fun r => v ∈ W r ∧ color r v = i).card : ℝ) ≤ B) :
    (R.card : ℝ) ≤ ((L : ℝ) * B) / η := by
  apply palette_count_of_weighted_witnesses R V W π η ((L : ℝ) * B) hη
    (mul_nonneg (Nat.cast_nonneg L) hB) hπ hmass hsub hweight
  intro v hv
  let S := R.filter fun r => v ∈ W r
  have hcard := Finset.card_eq_sum_card_fiberwise (f := fun r => color r v) (s := S)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  calc
    (S.card : ℝ) = ∑ i : Fin L, ((S.filter fun r => color r v = i).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _i : Fin L, B := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [S, Finset.filter_filter] using hcount v hv i
    _ = (L : ℝ) * B := by simp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
