/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/InterceptBinCount.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/InterceptBinCount.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_critical_intercept_concentration.Inherited.AffineContactFit

/-! Boundedly many hidden intercept bins per full true descendant. -/

namespace Submission.Obl.k4_critical_intercept_concentration.Inherited

noncomputable section

open Finset

/-- Scalar projection of the accepted three-coordinate grid count. -/
theorem scalar_floor_image_card_of_diameter {ι : Type*} (S : Finset ι) (y : ι → ℝ)
    {δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, |y i - y j| ≤ L) :
    ((S.image (fun i => ⌊y i / δ⌋)).card : ℝ) ≤ 32 * L / δ + 64 := by
  classical
  let embed : ℤ → Fin 3 → ℤ := fun z => ![z, 0, 0]
  have hembed : Function.Injective embed := by
    intro z w h
    exact congrFun h 0
  have h := Submission.Obl.k4_plank_projected_multiplicity.card_grid_codes_of_coordinate_diameters
    S (fun i => ![y i, 0, 0]) hδ ![L, 0, 0]
    (by intro j; fin_cases j <;> dsimp <;> positivity)
    (by
      intro i hi j hj k
      fin_cases k <;> dsimp
      · exact hdiam i hi j hj
      · simp
      · simp)
  have hcode (i : ι) : (fun j : Fin 3 => ⌊(![y i, 0, 0] : Fin 3 → ℝ) j / δ⌋) =
      embed ⌊y i / δ⌋ := by
    ext j
    fin_cases j <;> simp [embed]
  have hfunction : (fun i j => ⌊(![y i, 0, 0] : Fin 3 → ℝ) j / δ⌋) =
      (fun i => embed ⌊y i / δ⌋) := funext hcode
  rw [hfunction] at h
  have himage : S.image (fun i => embed ⌊y i / δ⌋) =
      (S.image (fun i => ⌊y i / δ⌋)).image embed := by rw [Finset.image_image]; rfl
  rw [himage, Finset.card_image_of_injective _ hembed] at h
  convert h using 1
  simp only [Fin.prod_univ_three]
  dsimp
  ring

theorem hidden_intercept_diameter_of_trueBox
    {ι : Type*} (S : Finset ι) (value : ι → ℝ) (point : ι → Fin 3 → ℝ)
    (c : Fin 5 → ℝ) (A : Fin 4 → ℝ) (m h K a : ℝ)
    (ha : 0 < a) (hK : 1 ≤ K) (hh : 0 ≤ h) (hsquare : h ^ 2 ≤ K * a)
    (hpoint : ∀ i ∈ S, point i ∈ horizontalTrueBox c m h K)
    (hfit : ∀ i ∈ S, |value i - affineBaseEval A (point i)| ≤ 2 * K * a)
    (hosc : ∀ q ∈ horizontalTrueBox c m h K, ∀ r ∈ horizontalTrueBox c m h K,
      |affineBaseEval A q - affineBaseEval A r| ≤ 64 * K ^ 5 * h ^ 2) :
    ∀ i ∈ S, ∀ j ∈ S, |value i - value j| ≤ 68 * K ^ 6 * a := by
  intro i hi j hj
  have hK0 : 0 ≤ K := by linarith
  have hKpow : K ≤ K ^ 6 := by
    calc
      K = K ^ 1 := by ring
      _ ≤ K ^ 6 := pow_le_pow_right₀ hK (by norm_num)
  have herror : |value i - value j| ≤ 4 * K * a + 64 * K ^ 5 * h ^ 2 := by
    calc
      _ = |(value i - affineBaseEval A (point i)) +
          (affineBaseEval A (point i) - affineBaseEval A (point j)) -
          (value j - affineBaseEval A (point j))| := by congr 1; ring
      _ ≤ |value i - affineBaseEval A (point i)| +
          |affineBaseEval A (point i) - affineBaseEval A (point j)| +
          |value j - affineBaseEval A (point j)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 2 * K * a + 64 * K ^ 5 * h ^ 2 + 2 * K * a :=
        add_le_add (add_le_add (hfit i hi) (hosc _ (hpoint i hi) _ (hpoint j hj))) (hfit j hj)
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 64 * K ^ 5)
  have hlinear := mul_le_mul_of_nonneg_right hKpow ha.le
  nlinarith only [herror, hscaled, hlinear]

/-- Whole-box affine comparison limits the hidden midpoint-intercept choices
attached to a true label, independently of its surviving mass. -/
theorem hidden_intercept_bin_count_of_trueBox
    {ι : Type*} (S : Finset ι) (value : ι → ℝ) (point : ι → Fin 3 → ℝ)
    (c : Fin 5 → ℝ) (A : Fin 4 → ℝ) (m h K a : ℝ)
    (ha : 0 < a) (hK : 1 ≤ K) (hh : 0 ≤ h) (hsquare : h ^ 2 ≤ K * a)
    (hpoint : ∀ i ∈ S, point i ∈ horizontalTrueBox c m h K)
    (hfit : ∀ i ∈ S, |value i - affineBaseEval A (point i)| ≤ 2 * K * a)
    (hosc : ∀ q ∈ horizontalTrueBox c m h K, ∀ r ∈ horizontalTrueBox c m h K,
      |affineBaseEval A q - affineBaseEval A r| ≤ 64 * K ^ 5 * h ^ 2) :
    ((S.image (fun i => ⌊value i / a⌋)).card : ℝ) ≤ 4096 * K ^ 6 := by
  have hdiam := hidden_intercept_diameter_of_trueBox S value point c A m h K a ha hK hh hsquare
    hpoint hfit hosc
  have hcard := scalar_floor_image_card_of_diameter S value ha
    (by positivity : 0 ≤ 68 * K ^ 6 * a) hdiam
  have hcancel : 32 * (68 * K ^ 6 * a) / a + 64 = 2176 * K ^ 6 + 64 := by field_simp; ring
  rw [hcancel] at hcard
  have hp : 1 ≤ K ^ 6 := one_le_pow₀ hK
  linarith only [hcard, hp]

theorem affineBaseEval_mesh_gap (A : Fin 4 → ℝ) (q r : Fin 3 → ℝ) (M δ : ℝ)
    (hM : 0 ≤ M) (hA : ∀ i : Fin 3, |A i.succ| ≤ M)
    (hgap : ∀ i, |q i - r i| ≤ δ) :
    |affineBaseEval A q - affineBaseEval A r| ≤ 3 * M * δ := by
  calc
    _ = |A 1 * (q 0 - r 0) + A 2 * (q 1 - r 1) + A 3 * (q 2 - r 2)| := by
      unfold affineBaseEval
      congr 1
      ring
    _ ≤ |A 1 * (q 0 - r 0)| + |A 2 * (q 1 - r 1)| + |A 3 * (q 2 - r 2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M * δ + M * δ + M * δ := by
      apply add_le_add
      · apply add_le_add <;> rw [abs_mul]
        · exact mul_le_mul (hA 0) (hgap 0) (abs_nonneg _) hM
        · exact mul_le_mul (hA 1) (hgap 1) (abs_nonneg _) hM
      · rw [abs_mul]
        exact mul_le_mul (hA 2) (hgap 2) (abs_nonneg _) hM
    _ = _ := by ring

/-- The critical upper count needs only the slope bound times the fine mesh.
The affine slope may include the parent factor 1/H. -/
theorem hidden_intercept_bin_count_per_base_cell
    {ι : Type*} (S : Finset ι) (value : ι → ℝ) (point : ι → Fin 3 → ℝ)
    (A : Fin 4 → ℝ) (a K M δ : ℝ) (j : Fin 3 → ℤ)
    (ha : 0 < a) (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hA : ∀ i : Fin 3, |A i.succ| ≤ M) (hmesh : 3 * M * δ ≤ K * a)
    (hpoint : ∀ i ∈ S, point i ∈ contactGridCell δ j)
    (hfit : ∀ i ∈ S, |value i - affineBaseEval A (point i)| ≤ 2 * K * a) :
    ((S.image (fun i => ⌊value i / a⌋)).card : ℝ) ≤ 256 * K := by
  have hdiam : ∀ i ∈ S, ∀ k ∈ S, |value i - value k| ≤ 5 * K * a := by
    intro i hi k hk
    have hlocal := affineBaseEval_mesh_gap A (point i) (point k) M δ hM hA
      (contactGridCell_coordinate_gap hδ (hpoint i hi) (hpoint k hk))
    calc
      _ = |(value i - affineBaseEval A (point i)) +
          (affineBaseEval A (point i) - affineBaseEval A (point k)) -
          (value k - affineBaseEval A (point k))| := by congr 1; ring
      _ ≤ |value i - affineBaseEval A (point i)| +
          |affineBaseEval A (point i) - affineBaseEval A (point k)| +
          |value k - affineBaseEval A (point k)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 2 * K * a + K * a + 2 * K * a :=
        add_le_add (add_le_add (hfit i hi) (hlocal.trans hmesh)) (hfit k hk)
      _ = _ := by ring
  have hcard := scalar_floor_image_card_of_diameter S value ha
    (by positivity : 0 ≤ 5 * K * a) hdiam
  have hcancel : 32 * (5 * K * a) / a + 64 = 160 * K + 64 := by field_simp; ring
  rw [hcancel] at hcard
  linarith only [hcard, hK]

end

end Submission.Obl.k4_critical_intercept_concentration.Inherited
