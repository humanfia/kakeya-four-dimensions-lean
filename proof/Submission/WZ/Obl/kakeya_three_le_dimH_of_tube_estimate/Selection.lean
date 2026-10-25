-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.Selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Dyadic
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Localization

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate

open LeanEval.Analysis.WangZahlKakeya

noncomputable def scaleCoefficient (γ : ℝ) : ℝ := (1 - (1 / 2 : ℝ) ^ γ) / 2

theorem scaleCoefficient_pos {γ : ℝ} (hγ : 0 < γ) : 0 < scaleCoefficient γ := by
  apply half_pos
  exact sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hγ)

theorem scaleCoefficient_le_one (γ : ℝ) : scaleCoefficient γ ≤ 1 := by
  have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) γ
  dsimp [scaleCoefficient]
  linarith

/-- Two geometric pigeonholes and a finite net produce a family to which the
normalized tube estimate applies. -/
theorem exists_discrete_family
    (A : Set Plane) (x : Plane → Space) {w γ : ℝ}
    (hA : A ⊆ closedBall (0 : Plane) (1 / 4)) (hw : 0 < w)
    (hwA : ENNReal.ofReal w ≤ volume A) (hγ : 0 < γ)
    (hx : ∀ u ∈ A, ‖x u + (1 / 2 : ℝ) • capDirection u‖ ≤ 1 / 8)
    (F : Finset ℕ) (c : ℕ → Space) (ρ : ℕ → ℝ) (N : ℕ)
    (hN : dyadic N ≤ 1 / 8)
    (hρ : ∀ m ∈ F, 0 < ρ m ∧ ρ m ≤ dyadic N)
    (hcover : ∀ u ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      x u + t • capDirection u ∈ ⋃ m ∈ F, ball (c m) (ρ m)) :
    ∃ k : ℕ, N ≤ k ∧ ∃ (n : ℕ) (z v : Fin n → Space) (Y : Fin n → Set Space),
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → dyadic k ≤ ‖v i - v j‖ ∧ dyadic k ≤ ‖v i + v j‖) ∧
      (∀ i, thickening (dyadic k) (segment ℝ (z i) (z i + v i)) ⊆ ball (0 : Space) 1) ∧
      (∀ i, MeasurableSet (Y i)) ∧
      (∀ i, Y i ⊆ thickening (dyadic k) (segment ℝ (z i) (z i + v i))) ∧
      (∀ i, ENNReal.ofReal ((scaleCoefficient γ / 4 * dyadic k ^ γ) * dyadic k ^ 2) ≤
        volume (Y i)) ∧
      w * scaleCoefficient γ * dyadic k ^ γ ≤ 4 * ((n : ℝ) * dyadic k ^ 2) ∧
      (⋃ i, Y i) ⊆ scaleEnlargement F c ρ k := by
  classical
  let T : Plane → ℕ → Set ℝ := fun u k =>
    {t | t ∈ Icc 0 1 ∧ x u + t • capDirection u ∈ scaleCover F c ρ k}
  let D : ℕ → Set Plane := fun k =>
    {u | u ∈ A ∧ ENNReal.ofReal (scaleCoefficient γ * dyadic k ^ γ) ≤ volume (T u k)}
  have ha : 0 < scaleCoefficient γ := scaleCoefficient_pos hγ
  have hDcov : A ⊆ ⋃ k, D k := by
    intro u hu
    obtain ⟨k, hk⟩ := exists_scale_mass_geometric F c ρ
      (fun m hm => ⟨(hρ m hm).1, (hρ m hm).2.trans (dyadic_le_one N)⟩)
      (x u) (capDirection u) hγ (hcover u hu)
    exact mem_iUnion.mpr ⟨k, hu, hk⟩
  have hsum : ENNReal.ofReal w ≤ ∑' k, volume (D k) :=
    hwA.trans ((measure_mono hDcov).trans (measure_iUnion_le D))
  obtain ⟨k, hk⟩ := exists_geometric_mass hw
    (q := (1 / 2 : ℝ) ^ γ) (by positivity)
    (Real.rpow_lt_one (by norm_num) (by norm_num) hγ) hsum
  have hmass : ENNReal.ofReal (w * scaleCoefficient γ * dyadic k ^ γ) ≤ volume (D k) := by
    simpa only [scaleCoefficient, dyadic,
      Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hk
  have hrpos := dyadic_pos k
  have hrpow : 0 < dyadic k ^ γ := Real.rpow_pos_of_pos hrpos _
  have hDnonzero : volume (D k) ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hmass
  obtain ⟨u₀, hu₀⟩ := nonempty_of_measure_ne_zero hDnonzero
  have hNk : N ≤ k := by
    by_contra! hlt
    have hempty := scaleCover_eq_empty_of_lt (c := c) (fun m hm => (hρ m hm).2) hlt
    have hTzero : T u₀ k = ∅ := by ext t; simp [T, hempty]
    have hbad := hu₀.2
    rw [hTzero, measure_empty] at hbad
    have : 0 < ENNReal.ofReal (scaleCoefficient γ * dyadic k ^ γ) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact (not_le_of_gt this) hbad
  have hrsmall : dyadic k ≤ 1 / 8 := (dyadic_antitone hNk).trans hN
  have hDbounded : TotallyBounded (D k) :=
    (isCompact_closedBall (0 : Plane) (1 / 4)).totallyBounded.subset
      (fun u hu => hA hu.1)
  obtain ⟨P, hPD, hsep, hPcover⟩ := exists_finset_separated_cover hDbounded hrpos
  have hcount : w * scaleCoefficient γ * dyadic k ^ γ ≤
      4 * ((P.card : ℝ) * dyadic k ^ 2) := by
    have hle := hmass.trans (plane_volume_le_card_of_cover P hrpos.le hPcover)
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    nlinarith
  let e : Fin P.card ≃ ↥P := P.equivFin.symm
  let u : Fin P.card → Plane := fun i => (e i).val
  have hu : ∀ i, u i ∈ D k := fun i => hPD (e i).property
  have hunorm : ∀ i, ‖u i‖ ≤ 1 / 4 := by
    intro i
    simpa [mem_closedBall, dist_zero_right] using hA (hu i).1
  let Y : Fin P.card → Set Space := fun i =>
    thickening (dyadic k / 2) ((fun t : ℝ => x (u i) + t • capDirection (u i)) '' T (u i) k)
  have hTseg : ∀ i, ((fun t : ℝ => x (u i) + t • capDirection (u i)) '' T (u i) k) ⊆
      segment ℝ (x (u i)) (x (u i) + capDirection (u i)) := by
    intro i y hy
    obtain ⟨t, ht, rfl⟩ := hy
    rw [segment_eq_image']
    exact ⟨t, ht.1, by simp⟩
  refine ⟨k, hNk, P.card, (fun i => x (u i)), (fun i => capDirection (u i)), Y,
    (fun i => norm_capDirection (hunorm i)), ?_, ?_, ?_, ?_, ?_, hcount, ?_⟩
  · intro i j hij
    constructor
    · rw [← dist_eq_norm]
      apply le_trans _ (dist_le_dist_capDirection (u i) (u j))
      exact (hsep (u i) (e i).property (u j) (e j).property (by
        intro heq
        exact hij (e.injective (Subtype.ext heq)))).le
    · exact (by linarith : dyadic k ≤ 1).trans
        (one_le_norm_capDirection_add (hunorm i) (hunorm j))
  · intro i
    exact tube_subset_unit_ball (norm_capDirection (hunorm i)) (hx (u i) (hu i).1) hrsmall
  · intro i
    exact isOpen_thickening.measurableSet
  · intro i
    exact (thickening_subset_of_subset _ (hTseg i)).trans
      (thickening_mono (by linarith) _)
  · intro i
    have hlower := segment_shading_volume_lower (x (u i)) (capDirection (u i))
      (norm_capDirection (hunorm i)) (fun t ht => ht.1) hrpos (hu i).2
    have heq : (scaleCoefficient γ / 4 * dyadic k ^ γ) * dyadic k ^ 2 =
        (scaleCoefficient γ * dyadic k ^ γ) * dyadic k ^ 2 / 4 := by ring
    rw [heq]
    exact hlower
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    apply thickening_scaleCover_subset F c ρ k
    apply thickening_subset_of_subset _ (show
      ((fun t : ℝ => x (u i) + t • capDirection (u i)) '' T (u i) k) ⊆
        scaleCover F c ρ k from ?_) hi
    rintro _ ⟨t, ht, rfl⟩
    exact ht.2

end WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate
