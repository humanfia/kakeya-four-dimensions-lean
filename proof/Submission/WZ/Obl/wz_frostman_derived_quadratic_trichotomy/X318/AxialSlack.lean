-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.AxialSlack.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Endpoints
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.PrismGeometry
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file AxialSlack.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

lemma tube_projection_about_center {δ : ℝ} {x v e y : Space}
    (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (hy : y ∈ Tube δ x v) :
    |inner ℝ e (y - center x v)| < δ + 1 / 2 := by
  obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp hy
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hyz
  have hnear : |inner ℝ e (y - (x + t • v))| < δ :=
    (abs_real_inner_le_norm _ _).trans_lt (by simpa [he, ← dist_eq_norm] using hyz)
  have haxis : |inner ℝ e v| ≤ 1 := by
    simpa [he, hv] using abs_real_inner_le_norm e v
  have ht' : |t - 1 / 2| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hhalf : |(t - 1 / 2) * inner ℝ e v| ≤ (1 / 2 : ℝ) := by
    rw [abs_mul]
    nlinarith [abs_nonneg (t - 1 / 2), abs_nonneg (inner ℝ e v)]
  have hcoord : inner ℝ e (y - center x v) =
      inner ℝ e (y - (x + t • v)) + (t - 1 / 2) * inner ℝ e v := by
    simp only [center, inner_sub_right, inner_add_right, inner_smul_right]
    ring
  rw [hcoord]
  exact (abs_add_le _ _).trans_lt (by linarith)

lemma four_axis_centers {t : ℝ} (ht : |t| ≤ 1) :
    ∃ j : Fin 4, |t - (-(3 / 4 : ℝ) + (j : ℝ) / 2)| ≤ 1 / 4 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ht
  by_cases h₀ : t ≤ -(1 / 2 : ℝ)
  · refine ⟨0, ?_⟩
    norm_num
    rw [abs_le]
    constructor <;> linarith
  by_cases h₁ : t ≤ 0
  · refine ⟨1, ?_⟩
    norm_num
    rw [abs_le]
    constructor <;> linarith
  by_cases h₂ : t ≤ (1 / 2 : ℝ)
  · refine ⟨2, ?_⟩
    norm_num
    rw [abs_le]
    constructor <;> linarith
  · refine ⟨3, ?_⟩
    norm_num
    rw [abs_le]
    constructor <;> linarith

/-- Every unit tube in a prism belongs to one of four axial groups.  For that
group, the prism centre may subsequently move through an interval of length
one quarter without losing any point of the tube. -/
theorem tube_prism_axial_slack {δ a b : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    {x v c e₁ e₂ e₃ : Space} (hv : ‖v‖ = 1)
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hsub : Tube δ x v ⊆ Prism a b c e₁ e₂ e₃) :
    ∃ j : Fin 4, ∀ s : ℝ, |s| ≤ 1 / 8 →
      Tube δ x v ⊆ Prism a b
        (c + (-(3 / 4 : ℝ) + (j : ℝ) / 2 + s) • e₃) e₁ e₂ e₃ := by
  have hmid : center x v ∈ Tube δ x v := by
    apply Metric.self_subset_thickening hδ
    rw [segment_eq_image']
    refine ⟨1 / 2, by norm_num, ?_⟩
    simp [center]
  obtain ⟨j, hj⟩ := four_axis_centers (hsub hmid).2.2
  have h₁ : inner ℝ e₁ e₃ = 0 := by
    simpa using orthonormal_iff_ite.mp he (0 : Fin 3) 2
  have h₂ : inner ℝ e₂ e₃ = 0 := by
    simpa using orthonormal_iff_ite.mp he (1 : Fin 3) 2
  have h₃ : inner ℝ e₃ e₃ = 1 := by
    simpa using orthonormal_iff_ite.mp he (2 : Fin 3) 2
  have hn₃ : ‖e₃‖ = 1 := by simpa using he.norm_eq_one (2 : Fin 3)
  refine ⟨j, ?_⟩
  intro s hs y hy
  have hold := hsub hy
  have hproj := tube_projection_about_center hv hn₃ hy
  change |inner ℝ e₁ (y - (c + _ • e₃))| ≤ a ∧
    |inner ℝ e₂ (y - (c + _ • e₃))| ≤ b ∧
    |inner ℝ e₃ (y - (c + _ • e₃))| ≤ 1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [inner_sub_right, inner_add_right, inner_smul_right,
      h₁, mul_zero, add_zero] using hold.1
  · simpa only [inner_sub_right, inner_add_right, inner_smul_right,
      h₂, mul_zero, add_zero] using hold.2.1
  · have hcoord : inner ℝ e₃ (y - (c + (-(3 / 4 : ℝ) + (j : ℝ) / 2 + s) • e₃)) =
        inner ℝ e₃ (y - center x v) +
          (inner ℝ e₃ (center x v - c) - (-(3 / 4 : ℝ) + (j : ℝ) / 2)) - s := by
      simp only [inner_sub_right, inner_add_right, inner_smul_right, h₃, mul_one]
      ring
    rw [hcoord]
    exact (abs_sub _ _).trans (by
      have hsum := abs_add_le (inner ℝ e₃ (y - center x v))
        (inner ℝ e₃ (center x v - c) - (-(3 / 4 : ℝ) + (j : ℝ) / 2))
      linarith)

/-- Pigeonholing the four axial groups retains a quarter of a finite family and
makes the entire selected family compatible with the same axial displacement. -/
theorem exists_refinement_with_axial_slack {δ a b : ℝ}
    (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) {n : ℕ} (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1) {c e₁ e₂ e₃ : Space}
    (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (hsub : ∀ i, Tube δ (x i) (v i) ⊆ Prism a b c e₁ e₂ e₃) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ (n : ℝ) ≤ 4 * k ∧
      ∃ j : Fin 4, ∀ s : ℝ, |s| ≤ 1 / 8 → ∀ i,
        Tube δ (x (g i)) (v (g i)) ⊆ Prism a b
          (c + (-(3 / 4 : ℝ) + (j : ℝ) / 2 + s) • e₃) e₁ e₂ e₃ := by
  classical
  choose f hf using fun i => tube_prism_axial_slack hδ hδ8 (hv i) he (hsub i)
  obtain ⟨j, hj⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card (M := ℝ) f
    (b := (n : ℝ) / 4) (by simp [nsmul_eq_mul]; linarith)
  let S := Finset.univ.filter (fun i => f i = j)
  let g := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate S
  refine ⟨S.card, g, WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_injective S,
    ?_, j, ?_⟩
  · change (n : ℝ) / 4 ≤ (S.card : ℝ) at hj
    linarith
  · intro s hs i
    have hfi : f (g i) = j :=
      (Finset.mem_filter.mp (WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_mem S i)).2
    simpa only [hfi] using hf (g i) s hs

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
