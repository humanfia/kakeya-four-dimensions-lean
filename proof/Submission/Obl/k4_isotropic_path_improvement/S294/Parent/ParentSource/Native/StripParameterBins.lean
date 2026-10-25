-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripParameterBins, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripParameterBins.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripParameterBins.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripParameterBins.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripParameterBins.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAssignments

/-! A second, coarser parameter mesh removes the heavy-net cardinality from
the observation-list bound. Simultaneous reversal of normal and offset is
allowed throughout. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

def stripParametersClose (n : StripSpace) (b : ℝ) (m : StripSpace) (c r : ℝ) : Prop :=
  ‖n - m‖ + |b - c| ≤ r ∨ ‖n + m‖ + |b + c| ≤ r

private theorem strip_parameter_triangle (n m k : StripSpace) (b c d : ℝ) :
    ‖n - k‖ + |b - d| ≤ (‖n - m‖ + |b - c|) + (‖m - k‖ + |c - d|) := by
  have hn := norm_sub_le_norm_sub_add_norm_sub n m k
  have hb := abs_sub_le b c d
  linarith

theorem stripParametersClose_symm {n m : StripSpace} {b c r : ℝ}
    (h : stripParametersClose n b m c r) : stripParametersClose m c n b r := by
  simpa only [stripParametersClose, norm_sub_rev, abs_sub_comm, add_comm] using h

theorem stripParametersClose_trans {n m k : StripSpace} {b c d r s : ℝ}
    (h : stripParametersClose n b m c r) (h' : stripParametersClose m c k d s) :
    stripParametersClose n b k d (r + s) := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl ((strip_parameter_triangle n m k b c d).trans (by linarith))
  · apply Or.inr
    have ht := strip_parameter_triangle n m (-k) b c (-d)
    simp only [sub_neg_eq_add] at ht
    exact ht.trans (by linarith)
  · apply Or.inr
    have ht := strip_parameter_triangle n (-m) (-k) b (-c) (-d)
    have hn : ‖-m - -k‖ = ‖m - k‖ := by rw [neg_sub_neg, norm_sub_rev]
    have hb : |-c - -d| = |c - d| := by rw [neg_sub_neg, abs_sub_comm]
    rw [hn, hb] at ht
    simp only [sub_neg_eq_add] at ht
    exact ht.trans (by linarith)
  · apply Or.inl
    have ht := strip_parameter_triangle n (-m) k b (-c) d
    rw [show -m - k = -(m + k) by abel, norm_neg,
      show -c - d = -(c + d) by ring, abs_neg] at ht
    simp only [sub_neg_eq_add] at ht
    exact ht.trans (by linarith)

abbrev StripParameterCode := ℤ × ℤ × ℤ

def stripParameterCode (r : ℝ) (n : StripSpace) (b : ℝ) : StripParameterCode :=
  (⌊n 0 / r⌋, ⌊n 1 / r⌋, ⌊b / r⌋)

def stripParameterBox (r : ℝ) (n : StripSpace) (b : ℝ) (C : ℕ) :
    Finset StripParameterCode :=
  (Finset.Icc (⌊n 0 / r⌋ - C) (⌊n 0 / r⌋ + C)).product
    ((Finset.Icc (⌊n 1 / r⌋ - C) (⌊n 1 / r⌋ + C)).product
      (Finset.Icc (⌊b / r⌋ - C) (⌊b / r⌋ + C)))

theorem stripParameterBox_card (r : ℝ) (n : StripSpace) (b : ℝ) (C : ℕ) :
    (stripParameterBox r n b C).card = (2 * C + 1) ^ 3 := by
  have hc (z : ℤ) : (Finset.Icc (z - C) (z + C)).card = 2 * C + 1 := by
    rw [Int.card_Icc]
    have he : z + C + 1 - (z - C) = (2 * C + 1 : ℕ) := by omega
    rw [he, Int.toNat_natCast]
  unfold stripParameterBox
  have hprod (s : Finset ℤ) (t : Finset (ℤ × ℤ)) :
      (s.product t).card = s.card * t.card := Finset.card_product s t
  have hprod' (s t : Finset ℤ) :
      (s.product t).card = s.card * t.card := Finset.card_product s t
  rw [hprod, hprod', hc, hc, hc]
  ring

private theorem floor_mem_nearby {a b r : ℝ} {C : ℕ} (hr : 0 < r)
    (hab : |a - b| ≤ (C : ℝ) * r) :
    ⌊a / r⌋ ∈ Finset.Icc (⌊b / r⌋ - C) (⌊b / r⌋ + C) := by
  have hq : |a / r - b / r| ≤ (C : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    exact hab
  obtain ⟨hlo, hhi⟩ := abs_le.mp hq
  have hlo' : b / r - (C : ℝ) ≤ a / r := by linarith
  have hhi' : a / r ≤ b / r + (C : ℝ) := by linarith
  exact Finset.mem_Icc.mpr ⟨by simpa using Int.floor_mono hlo',
    by simpa using Int.floor_mono hhi'⟩

theorem stripParameterCode_mem_box {n m : StripSpace} {b c r : ℝ} {C : ℕ}
    (hr : 0 < r) (hclose : ‖n - m‖ + |b - c| ≤ (C : ℝ) * r) :
    stripParameterCode r m c ∈ stripParameterBox r n b C := by
  have hd : ‖n - m‖ ≤ (C : ℝ) * r := by linarith [abs_nonneg (b - c)]
  have hb : |c - b| ≤ (C : ℝ) * r := by
    rw [abs_sub_comm]
    linarith [norm_nonneg (n - m)]
  have hi (i : Fin 2) : |m i - n i| ≤ (C : ℝ) * r := by
    have h := PiLp.norm_apply_le (m - n) i
    have h' : |m i - n i| ≤ ‖n - m‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs, norm_sub_rev, abs_sub_comm] using h
    exact h'.trans hd
  exact Finset.mem_product.mpr ⟨floor_mem_nearby hr (hi 0),
    Finset.mem_product.mpr ⟨floor_mem_nearby hr (hi 1), floor_mem_nearby hr hb⟩⟩

def stripParameterList (r : ℝ) (n : StripSpace) (b : ℝ) (C : ℕ) :
    Finset StripParameterCode :=
  stripParameterBox r n b C ∪ stripParameterBox r (-n) (-b) C

theorem stripParameterList_card_le (r : ℝ) (n : StripSpace) (b : ℝ) (C : ℕ) :
    (stripParameterList r n b C).card ≤ 2 * (2 * C + 1) ^ 3 := by
  calc
    _ ≤ (stripParameterBox r n b C).card + (stripParameterBox r (-n) (-b) C).card :=
      Finset.card_union_le _ _
    _ = _ := by rw [stripParameterBox_card, stripParameterBox_card]; omega

theorem stripParameterCode_mem_list {n m : StripSpace} {b c r : ℝ} {C : ℕ}
    (hr : 0 < r) (hclose : stripParametersClose n b m c ((C : ℝ) * r)) :
    stripParameterCode r m c ∈ stripParameterList r n b C := by
  rcases hclose with h | h
  · exact Finset.mem_union.mpr (Or.inl (stripParameterCode_mem_box hr h))
  · apply Finset.mem_union.mpr
    apply Or.inr
    apply stripParameterCode_mem_box hr
    rwa [show -n - m = -(n + m) by abel, norm_neg,
      show -b - c = -(b + c) by ring, abs_neg]

/-- Parameter bins have uniformly bounded diameter. A unit representative
chosen from a bin may therefore replace every strip assigned to that bin. -/
theorem stripParametersClose_of_code_eq {n m : StripSpace} {b c r : ℝ}
    (hr : 0 < r) (hcode : stripParameterCode r n b = stripParameterCode r m c) :
    ‖n - m‖ + |b - c| ≤ 3 * r := by
  have he0 : ⌊n 0 / r⌋ = ⌊m 0 / r⌋ := congrArg Prod.fst hcode
  have he1 : ⌊n 1 / r⌋ = ⌊m 1 / r⌋ := congrArg (fun q => q.2.1) hcode
  have heb : ⌊b / r⌋ = ⌊c / r⌋ := congrArg (fun q => q.2.2) hcode
  have hc {a d : ℝ} (he : ⌊a / r⌋ = ⌊d / r⌋) : |a - d| ≤ r := by
    have h := Int.abs_sub_lt_one_of_floor_eq_floor he
    rw [← sub_div, abs_div, abs_of_pos hr, div_lt_iff₀ hr] at h
    simpa only [one_mul] using h.le
  have hn : ‖n - m‖ ≤ 2 * r := by
    have h := Submission.Lib.K4XInterface.norm_le_of_rows (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (n - m) (a := r) (b := r) (by simpa using hc he0) (by simpa using hc he1)
    simpa [two_mul] using h
  linarith [hc heb]

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
