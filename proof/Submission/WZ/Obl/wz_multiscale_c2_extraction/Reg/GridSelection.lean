-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.GridSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.GridSamples

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

def LongGridIndex (D : Set ℝ) (h H a : ℝ) :=
  {j : ↥(heightGrid h) // a ≤
    sSup (gridHeightSamples D h H a j.1) - sInf (gridHeightSamples D h H a j.1)}

noncomputable scoped instance longGridIndexFintype (D : Set ℝ) (h H a : ℝ) :
    Fintype (LongGridIndex D h H a) := by
  classical
  unfold LongGridIndex
  infer_instance

def longGridSample (D : Set ℝ) (h H a : ℝ) (j : LongGridIndex D h H a) : Set ℝ :=
  gridHeightSamples D h H a j.1.1

theorem longGridSample_compact {D : Set ℝ} (hD : IsCompact D)
    (h H a : ℝ) (j : LongGridIndex D h H a) : IsCompact (longGridSample D h H a j) :=
  isCompact_gridHeightSamples hD h H a j.1.1

theorem longGridSample_nonempty {D : Set ℝ} {h H a : ℝ} (ha : 0 < a)
    (j : LongGridIndex D h H a) : (longGridSample D h H a j).Nonempty :=
  long_height_sample_nonempty ha j.2

theorem longGridSample_subset {D : Set ℝ} {h H a : ℝ} (j : LongGridIndex D h H a) :
    longGridSample D h H a j ⊆ D := gridHeightSamples_subset

theorem longGridSample_length {D : Set ℝ} {h H a : ℝ} (j : LongGridIndex D h H a) :
    a ≤ sSup (longGridSample D h H a j) - sInf (longGridSample D h H a j) := j.2

theorem longGridSample_separated {D : Set ℝ} (hD : IsCompact D)
    {h H a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    Pairwise fun i j : LongGridIndex D h H a =>
      Disjoint (Icc (sInf (longGridSample D h H a i) - a) (sSup (longGridSample D h H a i) + a))
        (Icc (sInf (longGridSample D h H a j) - a) (sSup (longGridSample D h H a j) + a)) := by
  intro i j hij
  apply padded_grid_sample_hulls_disjoint hD hh ha
  · intro he
    apply hij
    exact Subtype.ext (Subtype.ext he)
  · exact longGridSample_nonempty ha i
  · exact longGridSample_nonempty ha j

theorem longGridSample_in_cells {D : Set ℝ} (hD : IsCompact D)
    {h H a : ℝ} (hh : 0 < h) (hH : 0 < H) (ha : 0 < a)
    (j : LongGridIndex D h H a) :
    ∃ m : ℤ, Icc (sInf (longGridSample D h H a j)) (sSup (longGridSample D h H a j)) ⊆
      Icc ((j.1.1 : ℝ) * h) (((j.1.1 : ℝ) + 1) * h) ∩
        Icc ((m : ℝ) * H) (((m : ℝ) + 1) * H) :=
  grid_sample_hull_in_cells hD hh hH ha.le (longGridSample_nonempty ha j)

/-- The full cost of selecting long, padded, common-cell sample intervals is
controlled by the padding-to-width and fine-to-coarse ratios. -/
theorem longGridSamples_mass_error {μ : Measure ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hμ : ∀ l u : ℝ, μ (Icc l u) ≤ ENNReal.ofReal L * ENNReal.ofReal (u - l))
    {D : Set ℝ} (hD : IsCompact D) (hDbox : D ⊆ Icc (-1 : ℝ) 1)
    {h H a : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hH : 0 < H) (hH1 : H ≤ 1) (ha : 0 ≤ a) :
    μ (D \ ⋃ j : LongGridIndex D h H a, longGridSample D h H a j) ≤
      ENNReal.ofReal (55 * L * (a / h + h / H)) := by
  let S : ↥(heightGrid h) → Set ℝ := fun j => gridHeightSamples D h H a j.1
  let V : Set ℝ := ⋃ j : LongGridIndex D h H a, longGridSample D h H a j
  have hraw := gridHeightSamples_mass_error hμ hDbox hh hh1 hH ha
  have hshort := discard_short_height_samples (a := a) S
    (fun j => isCompact_gridHeightSamples hD h H a j.1) hμ (D := ⋃ j, S j) subset_rfl
  have hsub : D \ V ⊆ (D \ ⋃ j, S j) ∪ ((⋃ j, S j) \ V) := by
    intro z hz
    by_cases hs : z ∈ ⋃ j, S j
    · exact Or.inr ⟨hs, hz.2⟩
    · exact Or.inl ⟨hz.1, hs⟩
  have hbound : μ (D \ V) ≤
      (((heightGrid h).card : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal (4 * a) +
        ((heightGrid H).card : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal (4 * h)) +
      ((heightGrid h).card : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal a := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    apply add_le_add hraw
    simpa only [Fintype.card_coe, S, V, LongGridIndex, longGridSample] using hshort
  have hnum :
      (((heightGrid h).card : ℝ) * L * (4 * a) + ((heightGrid H).card : ℝ) * L * (4 * h)) +
        ((heightGrid h).card : ℝ) * L * a ≤ 55 * L * (a / h + h / H) := by
    have hch := heightGrid_card_bound hh hh1
    have hcH := heightGrid_card_bound hH hH1
    calc
      _ ≤ ((11 / h) * L * (4 * a) + (11 / H) * L * (4 * h)) + (11 / h) * L * a := by
        gcongr
      _ ≤ 55 * L * (a / h + h / H) := by
        have hq : 0 ≤ L * h / H := by positivity
        calc
          _ = 55 * L * (a / h + h / H) - 11 * (L * h / H) := by ring
          _ ≤ 55 * L * (a / h + h / H) := sub_le_self _ (mul_nonneg (by norm_num) hq)
  have hform :
      (((heightGrid h).card : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal (4 * a) +
        ((heightGrid H).card : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal (4 * h)) +
        ((heightGrid h).card : ℝ≥0∞) * ENNReal.ofReal L * ENNReal.ofReal a =
      ENNReal.ofReal
        ((((heightGrid h).card : ℝ) * L * (4 * a) + ((heightGrid H).card : ℝ) * L * (4 * h)) +
          ((heightGrid h).card : ℝ) * L * a) := by
    symm
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hL),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  exact hbound.trans (hform.le.trans (ENNReal.ofReal_le_ofReal hnum))

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
