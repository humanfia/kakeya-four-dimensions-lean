-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ReferenceRecordCharts, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.HistoryMenuRecords

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

open Set
open Submission.Lib.K4ListedExceptions

noncomputable section

/-- Membership in a fixed reference-cell option box bounds the actual
coordinate diameter. The estimate is independent of chart translations. -/
theorem reference_options_coordinate_diameter {n : ℕ}
    (mesh : Fin n → ℝ) (hmesh : ∀ j, 0 < mesh j)
    (q : Fin n → ℤ) (x y : Fin n → ℝ)
    (hx : (fun j => ⌊x j/mesh j⌋)∈referenceCellOptions mesh mesh q)
    (hy : (fun j => ⌊y j/mesh j⌋)∈referenceCellOptions mesh mesh q) :
    ∀ j, |x j-y j| ≤ 3*mesh j := by
  rw [referenceCellOptions,mem_integerCodeBox] at hx hy
  intro j
  have hxj := hx j
  have hyj := hy j
  have hlo : (⌊x j/mesh j⌋:ℝ) ≤ (⌊y j/mesh j⌋:ℝ)+2 := by
    exact_mod_cast (show ⌊x j/mesh j⌋ ≤ ⌊y j/mesh j⌋+2 by omega)
  have hhi : (⌊y j/mesh j⌋:ℝ) ≤ (⌊x j/mesh j⌋:ℝ)+2 := by
    exact_mod_cast (show ⌊y j/mesh j⌋ ≤ ⌊x j/mesh j⌋+2 by omega)
  have hxlo := (le_div_iff₀ (hmesh j)).mp (Int.floor_le (x j/mesh j))
  have hylo := (le_div_iff₀ (hmesh j)).mp (Int.floor_le (y j/mesh j))
  have hxhi := (div_lt_iff₀ (hmesh j)).mp (Int.lt_floor_add_one (x j/mesh j))
  have hyhi := (div_lt_iff₀ (hmesh j)).mp (Int.lt_floor_add_one (y j/mesh j))
  have hmullo := mul_le_mul_of_nonneg_right hlo (hmesh j).le
  have hmulhi := mul_le_mul_of_nonneg_right hhi (hmesh j).le
  rw [abs_le]
  constructor <;> nlinarith

/-- A record with one-cell coordinate diameter has81 four-dimensional
options and625 padding cells in any translated chart. Only actual
within-record differences are used; the partition precedes the query. -/
theorem exists_record_grid_menus {Ω Rec : Type*} {n : ℕ}
    (piece : Rec → Set Ω) (coords : Ω → Fin n → ℝ)
    (mesh : Fin n → ℝ) (hmesh : ∀ j, 0 < mesh j)
    (hdiam : ∀ r z, z∈piece r → ∀ w, w∈piece r → ∀ j,
      |coords z j-coords w j| ≤ mesh j) :
    ∃ options : Rec → Finset (Fin n → ℤ),
      (∀ r, (options r).card ≤ 3^n) ∧
      (∀ r z, z∈piece r → (fun j => ⌊coords z j/mesh j⌋)∈options r) ∧
      ∀ r q, q∈options r → ∀ z∈piece r,
        (fun j => ⌊coords z j/mesh j⌋)∈integerCodeBox 2 q := by
  classical
  have hmenu (r : Rec) : ∃ options : Finset (Fin n → ℤ),
      options.card ≤ 3^n ∧
      (∀ z∈piece r, (fun j => ⌊coords z j/mesh j⌋)∈options) ∧
      ∀ q∈options, ∀ z∈piece r,
        (fun j => ⌊coords z j/mesh j⌋)∈integerCodeBox 2 q := by
    by_cases hr : (piece r).Nonempty
    · obtain ⟨w,hw⟩ := hr
      let anchor := fun j => ⌊coords w j/mesh j⌋
      have hopt (z : Ω) (hz : z∈piece r) :
          (fun j => ⌊coords z j/mesh j⌋)∈integerCodeBox 1 anchor := by
        apply floor_code_mem_integerCodeBox 1 (coords z) (coords w) mesh hmesh
        intro j
        simpa only [Nat.cast_one,one_mul] using hdiam r z hz w hw j
      refine ⟨integerCodeBox 1 anchor,?_,hopt,?_⟩
      · simp [card_integerCodeBox]
      · intro q hq z hz
        have hzc := hopt z hz
        rw [mem_integerCodeBox] at hq hzc ⊢
        intro j
        have hqj := hq j
        have hzj := hzc j
        constructor <;> omega
    · exact ⟨∅,by simp,fun z hz => (hr ⟨z,hz⟩).elim,by simp⟩
  choose options hcard hcover hpadding using hmenu
  exact ⟨options,hcard,hcover,hpadding⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
