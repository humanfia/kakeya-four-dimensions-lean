-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.OneScale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Basic
import Submission.WZ.Obl.wz_direction_density_transfer

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file OneScale.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory Metric
open scoped ENNReal

lemma tube_volume_lower {δ : ℝ} (hδ : 0 < δ) (x v : Space) (hv : ‖v‖ = 1) :
    ENNReal.ofReal (δ ^ 2) ≤ volume (Tube δ x v) :=
  WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ x v hv

lemma tube_volume_pos {δ : ℝ} (hδ : 0 < δ) (x v : Space) (hv : ‖v‖ = 1) :
    0 < volume (Tube δ x v) :=
  (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hδ)).trans_le (tube_volume_lower hδ x v hv)

lemma subset_iff_eq_of_distinct {n : ℕ} {A : Fin n → Set Space}
    (hA : Distinct A) (hpos : ∀ i, 0 < volume (A i)) (hfin : ∀ i, volume (A i) ≠ ⊤)
    (i j : Fin n) : A i ⊆ A j ↔ i = j := by
  constructor
  · intro hij
    by_contra hne
    have hh := hA i j hne
    rw [inter_eq_left.mpr hij] at hh
    have ht := ENNReal.mul_lt_mul_left (hpos i).ne' (hfin i)
      (show (1 / 2 : ENNReal) < 1 by norm_num)
    simpa using lt_irrefl _ (ht.trans_le (by simpa using hh))
  · rintro rfl
    exact Subset.rfl

lemma centered_unit_tube_contains_ball (v : Space) :
    ball (0 : Space) 1 ⊆ Tube 1 (-(1 / 2 : ℝ) • v) v := by
  apply ball_subset_thickening
  rw [segment_eq_image']
  refine ⟨1 / 2, by norm_num, ?_⟩
  module

lemma singleton_frostman {K : ℝ} (hK : 1 ≤ K) (W : Set Space)
    (hW : 1 ≤ volume W) : Frostman K (fun _ : Fin 1 => W) := by
  classical
  intro U _
  by_cases hsub : W ⊆ U
  · have he : {i : Fin 1 | W ⊆ U} = univ := by ext i; simp [hsub]
    rw [he]
    simpa using (hW.trans (measure_mono hsub)).trans
      (le_mul_of_one_le_left' (ENNReal.ofReal_one.ge.trans (ENNReal.ofReal_le_ofReal hK)))
  · simp [hsub]

/-- When the original tubes already have the required Katz--Tao coefficient,
branch (B) uses the original family at the fine scale and one unit tube at the top. -/
theorem separated_scales_of_katz_tao {δ ζ₁ ζ₂ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hζ₁ : ζ₁ ≤ 1) (hζ₂ : 0 ≤ ζ₂)
    {n : ℕ} (x v : Fin n → Space) (hn : 0 < n)
    (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (hKT : KatzTao δ (δ ^ (-ζ₂)) (fun i => Tube δ (x i) (v i)))
    (hnum : δ ^ ζ₂ * (1 / δ) ^ 2 ≤ (n : ℝ)) :
    SeparatedScales ζ₁ ζ₂ δ (fun i => Tube δ (x i) (v i)) := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  let R := Tube 1 (-(1 / 2 : ℝ) • v i₀) (v i₀)
  have hTR (i) : Tube δ (x i) (v i) ⊆ R :=
    (hball i).trans (centered_unit_tube_contains_ball _)
  have hK : 1 ≤ δ ^ (-ζ₂) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1.le (neg_nonpos.mpr hζ₂)
  have heq (i j) : Tube δ (x i) (v i) ⊆ Tube δ (x j) (v j) ↔ i = j :=
    subset_iff_eq_of_distinct hsep (fun i => tube_volume_pos hδ _ _ (hv i))
      (fun i => ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (hball i))) i j
  have hfiber (j) : ncard {i | Tube δ (x i) (v i) ⊆ Tube δ (x j) (v j)} = 1 := by
    simp_rw [heq]
    simp
  have hcoarse : ncard {j | Tube δ (x j) (v j) ⊆ R} = n := by
    simp [hTR]
  have hscale : δ ≤ δ ^ ζ₁ * 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le hζ₁
  refine ⟨δ, 1, le_rfl, hδ1, le_rfl, hscale, n, x, v, 1,
    (fun _ => -(1 / 2 : ℝ) • v i₀), (fun _ => v i₀), hv, (fun _ => hv i₀), hsep,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j j' hne
    exact (hne (Subsingleton.elim _ _)).elim
  · intro i
    exact ⟨i, Subset.rfl, fun j hj => ((heq i j).mp hj).symm⟩
  · intro j
    exact ⟨j, Subset.rfl⟩
  · intro j
    exact ⟨0, hTR j, fun _ _ => Subsingleton.elim _ _⟩
  · intro _
    exact ⟨i₀, hTR i₀⟩
  · intro j j'
    simpa only [hfiber, Nat.cast_one, mul_one] using hK
  · intro _ _
    change (ncard {j | Tube δ (x j) (v j) ⊆ R} : ℝ) ≤
      δ ^ (-ζ₂) * ncard {j | Tube δ (x j) (v j) ⊆ R}
    rw [hcoarse]
    exact le_mul_of_one_le_left (Nat.cast_nonneg n) hK
  · intro j W _
    rw [hfiber]
    simp only [Nat.cast_one, mul_one]
    by_cases hj : Tube δ (x j) (v j) ⊆ W
    · have he : {i | Tube δ (x i) (v i) ⊆ Tube δ (x j) (v j) ∧ Tube δ (x i) (v i) ⊆ W} = {j} := by
        ext i
        simp only [mem_ofPred_eq, heq, mem_singleton_iff]
        exact ⟨And.left, fun h => ⟨h, h ▸ hj⟩⟩
      rw [he, ncard_singleton, Nat.cast_one, one_mul]
      exact ((tube_volume_lower hδ _ _ (hv j)).trans (measure_mono hj)).trans
        (le_mul_of_one_le_left' (ENNReal.ofReal_one.ge.trans (ENNReal.ofReal_le_ofReal hK)))
    · have he : {i | Tube δ (x i) (v i) ⊆ Tube δ (x j) (v j) ∧ Tube δ (x i) (v i) ⊆ W} = ∅ := by
        ext i
        simp only [mem_ofPred_eq, heq, mem_empty_iff_false, iff_false, not_and]
        rintro rfl
        exact hj
      simp [he]
  · intro _ W hW
    change ENNReal.ofReal ((ncard {j | Tube δ (x j) (v j) ⊆ R ∧ Tube δ (x j) (v j) ⊆ W} : ℝ) * δ ^ 2) ≤ _
    simpa only [hTR, true_and] using hKT W hW
  · intro _
    change δ ^ ζ₂ * (1 / δ) ^ 2 ≤ (ncard {j | Tube δ (x j) (v j) ⊆ R} : ℝ)
    rwa [hcoarse]
  · apply singleton_frostman hK R
    simpa [R] using tube_volume_lower (show (0 : ℝ) < 1 by norm_num)
      (-(1 / 2 : ℝ) • v i₀) (v i₀) (hv i₀)

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
