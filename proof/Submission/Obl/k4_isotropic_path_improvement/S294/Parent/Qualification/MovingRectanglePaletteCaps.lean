-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.MovingRectanglePaletteCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/MovingRectanglePaletteCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Lib.K4QuadraticSublevel
import Submission.Lib.K4QuadraticSheets

/-! # Cover a moving box by short original rectangles

The centers may have arbitrarily large constant offsets. Their motion over
one original time cell alone enters the cover. The palette event is unchanged.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- A box moving slowly over each original time cell is covered by at
most 4*s/base original rectangles. Only original numerator caps are summed. -/
theorem moving_rectangle_palette_cap {Ω V : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (time : Ω → ℝ) (pos : Ω → Fin 3 → ℝ)
    (control : Ω → V) (v : V) (center : ℝ → Fin 3 → ℝ) (offset : Fin 3 → ℝ)
    {base s p D t₀ : ℝ} (hbase : 0 < base) (hs : 0 < s) (hbs : base ≤ s)
    (hD : 0 ≤ D) (hsmall : D*base ≤ p)
    (hunit : ∀ z∈E, time z∈Icc (0 : ℝ) 1)
    (hmotion : ∀ t∈Icc (0 : ℝ) 1, ∀ t'∈Icc (0 : ℝ) 1, ∀ j,
      |center t j-center t' j| ≤ D*|t-t'|)
    (B : ENNReal)
    (hrect : ∀ τ (Y : Fin 3 → ℝ),
      μ {z | z∈E ∧ time z∈Icc τ (τ+base) ∧
        (∀ j, pos z j∈Icc (Y j) (Y j+3*p)) ∧ control z=v} ≤ B) :
    μ {z | z∈E ∧ time z∈Icc t₀ (t₀+s) ∧
      (∀ j, pos z j∈Icc (center (time z) j+offset j) (center (time z) j+offset j+p)) ∧
      control z=v} ≤ ENNReal.ofReal (4*s/base)*B := by
  classical
  let A := {z | z∈E ∧ time z∈Icc t₀ (t₀+s) ∧
    (∀ j, pos z j∈Icc (center (time z) j+offset j) (center (time z) j+offset j+p)) ∧
    control z=v}
  have hdiam : ∀ t∈time '' A, ∀ t'∈time '' A, dist t t' ≤ s := by
    rintro _ ⟨z,hz,rfl⟩ _ ⟨z',hz',rfl⟩
    rw [Real.dist_eq,abs_le]
    constructor <;> linarith [hz.2.1.1,hz.2.1.2,hz'.2.1.1,hz'.2.1.2]
  obtain ⟨hfinite,hcount⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (time '' A) hs.le hbase 0 hdiam
  simp only [sub_zero] at hfinite hcount
  let J := hfinite.toFinset
  have hJ : (J.card : ℝ) ≤ 4*s/base := by
    rw [← Set.ncard_eq_toFinset_card _ hfinite]
    apply hcount.trans
    apply (le_div_iff₀ hbase).mpr
    field_simp
    linarith
  have hwitness (j : J) : ∃ z∈A, (⌊time z/base⌋ : ℤ)=j.val := by
    obtain ⟨t,⟨z,hz,rfl⟩,hj⟩ := hfinite.mem_toFinset.mp j.property
    exact ⟨z,hz,hj⟩
  choose point hpoint using hwitness
  let Y := fun j : J => fun k => center (time (point j)) k+offset k-p
  let Rect := fun j : J => {z | z∈E ∧ time z∈Icc (base*(j.val : ℝ)) (base*(j.val : ℝ)+base) ∧
    (∀ k, pos z k∈Icc (Y j k) (Y j k+3*p)) ∧ control z=v}
  have hcover : A ⊆ ⋃ j : J, Rect j := by
    intro z hz
    have hzJ : (⌊time z/base⌋ : ℤ)∈J :=
      hfinite.mem_toFinset.mpr ⟨time z,⟨z,hz,rfl⟩,rfl⟩
    let j : J := ⟨⌊time z/base⌋,hzJ⟩
    refine mem_iUnion.mpr ⟨j,hz.1,?_,?_,hz.2.2.2⟩
    · have hlo := (le_div_iff₀ hbase).mp (Int.floor_le (time z/base))
      have hhi := (div_lt_iff₀ hbase).mp (Int.lt_floor_add_one (time z/base))
      dsimp only [j]
      constructor <;> nlinarith
    · have hdt : |time z-time (point j)| ≤ base :=
        (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hbase
          (hpoint j).2.symm).le
      intro k
      have hm := (hmotion (time z) (hunit z hz.1) (time (point j))
        (hunit (point j) (hpoint j).1.1) k).trans
          ((mul_le_mul_of_nonneg_left hdt hD).trans hsmall)
      have ha := abs_le.mp hm
      dsimp only [Y]
      constructor <;> linarith [(hz.2.2.1 k).1,(hz.2.2.1 k).2,ha.1,ha.2]
  calc
    _ ≤ μ (⋃ j : J, Rect j) := measure_mono hcover
    _ ≤ ∑ j : J, μ (Rect j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : J, B := Finset.sum_le_sum fun j _ => hrect (base*(j.val : ℝ)) (Y j)
    _ = (J.card : ENNReal)*B := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe]
    _ ≤ ENNReal.ofReal (4*s/base)*B := mul_le_mul' (by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hJ) le_rfl

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
