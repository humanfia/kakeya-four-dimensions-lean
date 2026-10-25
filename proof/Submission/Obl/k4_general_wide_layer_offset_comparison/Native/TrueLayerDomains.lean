-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/TrueLayerDomains.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/TrueLayerDomains.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.TrueDomainMenus
import Submission.Obl.k4_general_parent_projected_layers.Support.OriginalAssignmentBudget
import Submission.Obl.k4_row_cell_regularization.Palette
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem

/-! The original reference budget for the true labels of a prepared model. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers
open PreparedModel

noncomputable section

def blockLeft {α : Type} [MeasurableSpace α] (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) : ℝ :=
  (a.j k s i : ℝ) / (2 : ℝ) ^ a.T k s

theorem blockLeft_mem {α : Type} [MeasurableSpace α] (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) :
    blockLeft a k s i ∈ a.block k s i := by
  change (a.j k s i : ℝ) / (2 : ℝ) ^ a.T k s ∈
    Icc ((a.j k s i : ℝ) / (2 : ℝ) ^ a.T k s)
      (((a.j k s i : ℝ) + 1) / (2 : ℝ) ^ a.T k s)
  exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩

theorem blockLeft_mem_unit {α : Type} [MeasurableSpace α] (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) : blockLeft a k s i ∈ Icc (0 : ℝ) 1 := by
  have hj : (a.j k s i : ℝ) ≤ (2 : ℝ) ^ a.T k s := by
    exact_mod_cast (Nat.le_of_lt (a.j k s i).isLt)
  exact ⟨by unfold blockLeft; positivity,
    (div_le_one (by positivity)).mpr hj⟩

theorem block_distance_left {α : Type} [MeasurableSpace α] (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) {t : ℝ} (ht : t ∈ a.block k s i) :
    |t - blockLeft a k s i| ≤ a.q k s := by
  have hq : a.q k s = ((2 : ℝ) ^ a.T k s)⁻¹ := by simp [PreparedModel.q]
  have heq : ((a.j k s i : ℝ) + 1) / (2 : ℝ) ^ a.T k s =
      blockLeft a k s i + a.q k s := by rw [hq]; unfold blockLeft; ring
  change (a.j k s i : ℝ) / (2 : ℝ) ^ a.T k s ≤ t ∧
    t ≤ ((a.j k s i : ℝ) + 1) / (2 : ℝ) ^ a.T k s at ht
  rw [heq] at ht
  change blockLeft a k s i ≤ t ∧ t ≤ blockLeft a k s i + a.q k s at ht
  rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
  linarith [ht.2]

/-- The true prepared-label common domains have a total original reference at most
a fixed power of the old loss. No count of major velocity bins is charged. -/
theorem true_layer_common_domains {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {R s χ q m : ℝ} {k : ℕ} (hatlas : a.AtlasAt p R k s)
    (hq : 0 < q) (hqQ : q ≤ a.q k s) (hχ : 0 < χ)
    (hχQ : χ ≤ a.q k s) (hχQg : χ ≤ a.q k s * narrow p k s)
    (hm : 0 < m) (hmQg : m ≤ a.q k s * narrow p k s) :
    ∃ menus : Fin (a.n k s) → Finset Code,
      (∀ i l, l ∈ a.B k s i →
        |a.b k l 0| + |a.b k l 1| + |a.b k l 3| + |a.b k l 4| ≤ p.K k →
        ∀ t ∈ a.block k s i,
          code q χ (narrow p k s) m (a.b k l) t ∈ menus i) ∧
      (∑ i, ∑ c ∈ menus i, q * χ * m * (width p k s) ^ p.d *
        (a.pi k {w : ℝ | ⌊w / χ⌋ = c 1}).toReal) ≤ 237600 * p.K k ^ 5 := by
  classical
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hQ : 0 < a.q k s := by unfold PreparedModel.q; positivity
  have hQ1 : a.q k s ≤ 1 := by
    have hh : (1 : ℝ) ≤ (2 : ℝ) ^ a.T k s := one_le_pow₀ (by norm_num)
    simpa [PreparedModel.q] using inv_le_one_of_one_le₀ hh
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  have haw : 0 < (width p k s) ^ p.d :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _
  haveI : IsProbabilityMeasure (a.pi k) := (hcommon k).2.2.1
  have hex (i : Fin (a.n k s)) := true_domain_menu hK hQ hQ1 hq hqQ hχ hg hχQ hχQg hm hmQg
    (blockLeft_mem_unit a k s i) (a.c k s i) ((hatlas.2.2.2.2.1 i).2.2.2.1 4)
  choose V menus hbudget hsource using hex
  refine ⟨menus, ?_, ?_⟩
  · intro i l hl hb t ht
    have hA := (hatlas.2.2.1 i).2.2 hl
    have hgeo := (hatlas.2.2.2.2.1 i).2.2.2.2.2.1 l hA
      (blockLeft a k s i) (blockLeft_mem a k s i)
    have htunit : t ∈ Icc (0 : ℝ) 1 := by
      exact Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_subset_unit
        (a.T k s) (a.j k s i) ht
    apply hsource i (a.b k l) t htunit (block_distance_left a k s i ht) hb
    · simpa [PreparedModel.x, Submission.Lib.K4ContactNormalization.point, sub_sub] using hgeo.1
    · simpa [rowError, PreparedModel.x, Submission.Lib.K4ContactNormalization.point] using hgeo.2.1
    · exact hgeo.2.2
  · let w : ℤ → ℝ := fun v => (a.pi k {z : ℝ | ⌊z / χ⌋ = v}).toReal
    have hw : ∀ v, 0 ≤ w v := fun _ => ENNReal.toReal_nonneg
    have hsum (i : Fin (a.n k s)) : (∑ v ∈ V i, w v) ≤ 1 := by
      simpa only [w, ← Submission.Obl.k4_row_cell_regularization.velocityCell_eq_floor hχ,
        Submission.Obl.k4_row_cell_regularization.binWeight,
        Submission.Obl.k4_row_cell_regularization.velocityCell, measureReal_def] using
        Submission.Obl.k4_row_cell_regularization.sum_binWeight_le_one hχ (a.pi k) (V i)
    have hper (i : Fin (a.n k s)) := hbudget i w hw (hsum i)
    have hold := a.original_label_volume_budget p hp hcommon hatlas
    calc
      _ = (width p k s) ^ p.d * ∑ i, ∑ c ∈ menus i, q * χ * m * w (c 1) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro c hc
        dsimp [w]
        ring
      _ ≤ (width p k s) ^ p.d *
          ∑ _i : Fin (a.n k s), 237600 * p.K k ^ 4 * a.q k s ^ 3 * narrow p k s :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hper i) haw.le
      _ = (237600 * p.K k ^ 4) *
          (((a.n k s : ℝ) * (a.q k s ^ 3 * narrow p k s)) * (width p k s) ^ p.d) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        ring
      _ ≤ (237600 * p.K k ^ 4) * ((p.K k / (width p k s) ^ p.d) * (width p k s) ^ p.d) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hold haw.le) (by positivity)
      _ = _ := by field_simp

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
