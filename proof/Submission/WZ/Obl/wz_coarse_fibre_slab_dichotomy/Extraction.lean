-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.Extraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabExtraction
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.Tubes
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.Geometry

/-!
# One greedy slab extraction per coarse fibre (WZ Lemma 4.10)

We apply o067's `greedy_container_extraction` with the slab selector `select_slab_container`
to the closed tubes of one fibre. Every selected cell is a set of tubes inside a slab which is
near-maximal for the density `weight / width`; this gives the count bound
`#{tubes of the cell in a slab of half-width r} ≤ 3072 (r / width) #cell`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells

local notation "Sp" => LeanEval.Analysis.WangZahlKakeya.Space

/-- Per-fibre greedy slab extraction for closed unit tubes. -/
theorem fibre_extraction {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) {n : ℕ} (x v : Fin n → Sp)
    (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Sp) 1)
    (K : ℕ) (hK : (1536 * n : ℝ) ≤ 2 ^ K)
    (F : Finset (Fin n)) (Y : Fin n → Set Sp) (hYm : ∀ i ∈ F, MeasurableSet (Y i))
    (hYU : ∀ i ∈ F, Y i ⊆ tubeU δ (x i) (v i))
    (θ : ℝ≥0∞) (hdense : ∀ i ∈ F, θ * volume (tubeU δ (x i) (v i)) ≤ volume (Y i)) :
    ∃ (m : ℕ) (C : Fin m → ShadedCell (Fin n)),
      (∀ j, (C j).Valid F (fun i => tubeU δ (x i) (v i)) Y θ
        (SlabFamilyGood (fun i => tubeU δ (x i) (v i)))) ∧
      Pairwise (fun j k => Disjoint (C j).support (C k).support) ∧
      ∑ i ∈ F, volume (Y i) ≤ θ * ∑ i ∈ F, volume (tubeU δ (x i) (v i)) +
        ENNReal.ofReal (1 + 320 * K : ℝ) *
          ∑ j, ∑ i ∈ (C j).indices, volume (tubeU δ (x i) (v i)) := by
  classical
  set U : Fin n → Set Sp := fun i => tubeU δ (x i) (v i) with hU
  have hwle : ∀ i, (volume (U i)).toReal ≤ 1536 * δ ^ 2 := by
    intro i
    have h := volume_tubeU_le hδ hδ1 (x i) (hv i)
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have hwge : ∀ i, δ ^ 2 ≤ (volume (U i)).toReal := by
    intro i
    have h := volume_tubeU_ge hδ (x i) (hv i)
    exact (ENNReal.ofReal_le_iff_le_toReal (volume_tubeU_ne_top (hT i))).mp h
  have hsel : ∀ (F' : Finset (Fin n)), F'.Nonempty →
      ∃ (I : Finset (Fin n)) (W : Set Sp), I.Nonempty ∧ I ⊆ F' ∧ MeasurableSet W ∧
        SlabFamilyGood U I W ∧ (∀ i ∈ I, U i ⊆ W) ∧
        ∑ i ∈ F', volume (U i ∩ W) ≤ ENNReal.ofReal (1 + 320 * K : ℝ) * ∑ i ∈ I, volume (U i) := by
    intro F' hF'
    apply select_slab_container F' hF' U (fun i _ => tubeU_compact (hT i))
      (fun i _ => tubeU_convex δ (x i) (v i)) (fun i _ => volume_tubeU_ne_zero hδ (x i) (hv i))
      hδ (fun i _ => ⟨x i, ball_subset_tubeU hδ (x i) (v i)⟩)
      (fun i _ => tubeU_subset_closedBall (hT i)) K (δ ^ 2) (fun i _ => hwge i)
    have hsum : ∑ i ∈ F', (volume (U i)).toReal ≤ n * (1536 * δ ^ 2) := by
      calc ∑ i ∈ F', (volume (U i)).toReal ≤ ∑ i : Fin n, (volume (U i)).toReal :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => ENNReal.toReal_nonneg)
        _ ≤ ∑ _i : Fin n, 1536 * δ ^ 2 := Finset.sum_le_sum (fun i _ => hwle i)
        _ = n * (1536 * δ ^ 2) := by simp
    have h2K : (0 : ℝ) < 2 ^ K := by positivity
    calc (1 / 2 : ℝ) ^ K * ∑ i ∈ F', (volume (U i)).toReal
        ≤ (1 / 2 : ℝ) ^ K * (n * (1536 * δ ^ 2)) := by gcongr
      _ = (1536 * n) / 2 ^ K * δ ^ 2 := by rw [one_div_pow]; field_simp
      _ ≤ 1 * δ ^ 2 := by
          gcongr
          rw [div_le_one h2K]; exact hK
      _ = δ ^ 2 := one_mul _
  exact greedy_container_extraction U (SlabFamilyGood U) (ENNReal.ofReal (1 + 320 * K : ℝ)) θ
    hsel F Y hYm hYU hdense

lemma slabSpec_carrier_eq (S : SlabSpec) : S.carrier = slabQ S.normal S.offset S.width := by
  ext p
  simp [SlabSpec.carrier, slab, slabQ, innerSL_apply_apply]

open Classical in
/-- The count bound delivered by a near-maximal slab. -/
lemma count_of_slabFamilyGood {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) {n : ℕ}
    (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Sp) 1)
    {I : Finset (Fin n)} {W : Set Sp}
    (hG : SlabFamilyGood (fun i => tubeU δ (x i) (v i)) I W) :
    ∃ S : SlabSpec, W = S.carrier ∧ S.width ≤ 2 ∧
      ∀ (u : Sp) (t r : ℝ), ‖u‖ = 1 → 0 < r →
        ((I.filter (fun i => tubeU δ (x i) (v i) ⊆ slabQ u t r)).card : ℝ) ≤
          3072 * (r / S.width) * I.card := by
  classical
  obtain ⟨S, hW, hSw, hmax⟩ := hG
  refine ⟨S, hW, hSw, fun u t r hu hr => ?_⟩
  set U : Fin n → Set Sp := fun i => tubeU δ (x i) (v i) with hU
  have hwle : ∀ i, (volume (U i)).toReal ≤ 1536 * δ ^ 2 := by
    intro i
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (volume_tubeU_le hδ hδ1 (x i) (hv i))
  have hwge : ∀ i, δ ^ 2 ≤ (volume (U i)).toReal := by
    intro i
    exact (ENNReal.ofReal_le_iff_le_toReal (volume_tubeU_ne_top (hT i))).mp
      (volume_tubeU_ge hδ (x i) (hv i))
  let T : SlabSpec := ⟨u, t, r, hu, hr⟩
  have hTc : T.carrier = slabQ u t r := by rw [slabSpec_carrier_eq]
  have h := hmax T
  have hweight : δ ^ 2 * ((I.filter (fun i => U i ⊆ slabQ u t r)).card : ℝ) ≤
      T.weight I U (fun i => (volume (U i)).toReal) := by
    unfold SlabSpec.weight
    rw [hTc, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · simpa using hwge i
    · simp
  have htot : ∑ i ∈ I, (volume (U i)).toReal ≤ 1536 * δ ^ 2 * I.card := by
    calc ∑ i ∈ I, (volume (U i)).toReal ≤ ∑ _i ∈ I, 1536 * δ ^ 2 :=
          Finset.sum_le_sum (fun i _ => hwle i)
      _ = 1536 * δ ^ 2 * I.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hSpos := S.width_pos
  have hδ2 : 0 < δ ^ 2 := by positivity
  have key : δ ^ 2 * ((I.filter (fun i => U i ⊆ slabQ u t r)).card : ℝ) / r ≤
      2 * (1536 * δ ^ 2 * I.card) / S.width := by
    calc δ ^ 2 * ((I.filter (fun i => U i ⊆ slabQ u t r)).card : ℝ) / r
        ≤ T.weight I U (fun i => (volume (U i)).toReal) / T.width := by
          exact div_le_div_of_nonneg_right hweight hr.le
      _ ≤ 2 * (∑ i ∈ I, (volume (U i)).toReal) / S.width := h
      _ ≤ 2 * (1536 * δ ^ 2 * I.card) / S.width := by gcongr
  rw [div_le_div_iff₀ hr hSpos] at key
  rw [show 3072 * (r / S.width) * (I.card : ℝ) = (3072 * r * I.card) / S.width by ring,
    le_div_iff₀ hSpos]
  have key' : δ ^ 2 * (((I.filter (fun i => U i ⊆ slabQ u t r)).card : ℝ) * S.width) ≤
      δ ^ 2 * (3072 * r * I.card) := by linarith
  exact le_of_mul_le_mul_left key' hδ2

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
