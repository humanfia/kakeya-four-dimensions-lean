-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalizedFactorization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoarseTranslation
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Extraction
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Factoring

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_concentrated_convex_factorization (Upper coefficient count)

/-- For comparable nonnegative masses, retaining a cardinality fraction retains a mass
fraction with just the comparability loss. This transfers the geometric extraction's
cardinality estimate to complete fine fibers. -/
theorem comparable_mass_of_card_retention {ι : Type*} [DecidableEq ι]
    (S R : Finset ι) (a : ι → ℝ) {r L : ℝ}
    (hR : R.Nonempty) (hRS : R ⊆ S) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (ha : ∀ i ∈ S, 0 ≤ a i)
    (hcmp : ∀ i ∈ S, ∀ j ∈ S, a i ≤ r * a j)
    (hcard : (S.card : ℝ) ≤ L * R.card) :
    (∑ i ∈ S, a i) ≤ r * L * ∑ i ∈ R, a i := by
  classical
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image R a hR
  have haj : 0 ≤ a j := ha j (hRS hj)
  have hRsum : (R.card : ℝ) * a j ≤ ∑ i ∈ R, a i := by
    calc
      _ = ∑ _i ∈ R, a j := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => hmin i hi
  calc
    _ ≤ ∑ _i ∈ S, r * a j := Finset.sum_le_sum fun i hi => hcmp i hi j (hRS hj)
    _ = r * a j * S.card := by simp [mul_comm]
    _ ≤ r * a j * (L * R.card) := mul_le_mul_of_nonneg_left hcard (mul_nonneg hr haj)
    _ = r * L * (R.card * a j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hRsum (mul_nonneg hr hL)

/-- The accepted geometric extraction applies inside any translated unit ball, with
exactly the same coefficient and all the same quantitative losses. -/
theorem extract_cover_in_translated_ball {ι : Type*} [DecidableEq ι] {ρ m r K : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : 1 ≤ m) (hr : 1 ≤ r) (hK : 0 < K)
    (q : ℕ) (hgrid : 2 ≤ ρ * r ^ q)
    (y w : ι → Space) (S : Finset ι) (hS : S.Nonempty) (z : Space)
    (hw : ∀ i ∈ S, ‖w i‖ = 1) (hball : ∀ i ∈ S, Tube ρ (y i) (w i) ⊆ Metric.ball z 1)
    (hu : Upper (fun i => Tube ρ (y i) (w i)) (ρ ^ 2) S m)
    (hstable : ∀ R ⊆ S, (S.card : ℝ) ≤ 2 * R.card →
      coefficient (fun i => Tube ρ (y i) (w i)) (ρ ^ 2) S ≤
        K * coefficient (fun i => Tube ρ (y i) (w i)) (ρ ^ 2) R) :
    let T := fun i => Tube ρ (y i) (w i)
    let c := coefficient T (ρ ^ 2) S
    let B := 1024 * K * r ^ 2
    ∃ (a b : ℝ) (R : Finset ι) (N : ℕ) (W : Fin N → Set Space),
      ρ ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ R ⊆ S ∧ R.Nonempty ∧ 0 < N ∧
      (S.card : ℝ) ≤ 4 * (q + 1 : ℝ) ^ 2 * R.card ∧
      (∀ j, ∃ e : AffineIsometryEquiv ℝ Space Space,
        W j = e '' {p : Space | |p 0| ≤ a ∧ |p 1| ≤ b ∧ |p 2| ≤ 2}) ∧
      (∀ j, Convex ℝ (W j) ∧ volume (W j) = ENNReal.ofReal (16 * a * b)) ∧
      (∀ i ∈ R, ∃ j, T i ⊆ W j) ∧
      (∀ i ∈ R, (ncard {j | T i ⊆ W j} : ℝ) ≤ 64 * B) ∧
      (∀ j, c * a * b ≤ 2 * B * (count T R (W j) : ℝ) * ρ ^ 2) := by
  dsimp only
  have hstable' : ∀ R ⊆ S, (S.card : ℝ) ≤ 2 * R.card →
      coefficient (fun i => Tube ρ (y i + -z) (w i)) (ρ ^ 2) S ≤
        K * coefficient (fun i => Tube ρ (y i + -z) (w i)) (ρ ^ 2) R := by
    simpa only [coefficient_tube_translation] using hstable
  obtain ⟨a, b, R, N, W, ha, hab, hb, hRS, hR, hN, hcard, hshape, hW, hcover, hdeg, hsat⟩ :=
    wz_concentrated_convex_factorization.extract_cover hρ hρ1 hm hr hK q hgrid
      (fun i => y i + -z) w S hS hw
      (fun i hi => translated_tube_in_unit_ball (hball i hi)) (upper_tube_translation hu (-z)) hstable'
  have ht (i : ι) : Tube ρ (y i) (w i) =
      (fun p : Space => p + z) '' Tube ρ (y i + -z) (w i) := by
    simpa only [neg_add_cancel_right] using
      wz_nsp_translation_model.tube_translate ρ (y i + -z) (w i) z
  have hinj : Function.Injective (fun p : Space => p + z) := fun _ _ h => add_right_cancel h
  refine ⟨a, b, R, N, fun j => (fun p => p + z) '' W j,
    ha, hab, hb, hRS, hR, hN, hcard, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨e, he⟩ := hshape j
    refine ⟨e.trans (AffineIsometryEquiv.vaddConst ℝ z), ?_⟩
    dsimp only
    rw [he, Set.image_image]
    rfl
  · intro j
    exact ⟨(hW j).1.affine_image (AffineEquiv.vaddConst ℝ z).toAffineMap,
      (volume_image_translation (W j) z).trans (hW j).2⟩
  · intro i hi
    obtain ⟨j, hj⟩ := hcover i hi
    exact ⟨j, by rw [ht]; exact Set.image_mono hj⟩
  · intro i hi
    have he : {j | Tube ρ (y i) (w i) ⊆ (fun p => p + z) '' W j} =
        {j | Tube ρ (y i + -z) (w i) ⊆ W j} := by
      ext j
      simp only [mem_ofPred_eq]
      rw [ht, Set.image_subset_image_iff hinj]
    rw [he]
    exact hdeg i hi
  · intro j
    simpa only [ht, count_image_translation, coefficient_image_translation] using hsat j

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
