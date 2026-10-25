-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.UnitCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (T F X)

/-- The cover predicate in initialization, with a separate optional clause. -/
def Cover (δ h : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
    (y w : Fin N → Space) (f : Fin n → Fin N) (b : Prop) : Prop :=
  (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧
  ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i ∈ S, volume (Z i) ∧
  (∀ k, ‖w k‖ = 1) ∧
  (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧
  F ρ (δ ^ (-h)) N y w ∧ b ∧
  (∀ k k', ({i | i ∈ S ∧ f i = k}.ncard : ℝ) ≤
    δ ^ (-h) * ({i | i ∈ S ∧ f i = k'}.ncard : ℝ)) ∧
  X ρ N y w ∧
  ∀ i ∈ S, ({k | T δ (x i) (v i) ⊆ T ρ (y k) (w k)}.ncard : ℝ) ≤ δ ^ (-h)

/-- At scale one, one carrier covers any family in the unit ball. The
above-slab count holds since that carrier is not itself inside the unit ball. -/
theorem unit_scale_cover_with_ball {δ h : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hYm : ∀ i, MeasurableSet (Y i))
    (hball : ∀ i, T δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) :
    ∃ y w : Fin 1 → Space,
      Cover δ h n x v Y Finset.univ Y 1 1 y w (fun _ => 0) True ∧
        ∀ k, Metric.ball (0 : Space) 1 ⊆ T 1 (y k) (w k) := by
  classical
  let w₀ : Space := EuclideanSpace.single 0 1
  have hw₀ : ‖w₀‖ = 1 := by simp [w₀]
  have hbig : Metric.ball (0 : Space) 1 ⊆ T 1 0 w₀ := by
    intro p hp
    apply Metric.mem_thickening_iff.mpr
    exact ⟨0, left_mem_segment ℝ _ _, by simpa using hp⟩
  have hcontained (i : Fin n) : T δ (x i) (v i) ⊆ T 1 0 w₀ := (hball i).trans hbig
  have hnot : ¬ T 1 0 w₀ ⊆ Metric.ball (0 : Space) 1 := by
    intro h
    have hwT : w₀ ∈ T 1 0 w₀ := by
      apply Metric.self_subset_thickening (by norm_num : (0 : ℝ) < 1)
      simpa only [zero_add] using right_mem_segment ℝ (0 : Space) (0 + w₀)
    have := h hwT
    simp [Metric.mem_ball, dist_zero_right, hw₀] at this
  have hp : δ ^ h ≤ 1 := Real.rpow_le_one hδ.le hδ1 hh
  have hneg : 1 ≤ δ ^ (-h) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hh)
  refine ⟨fun _ => 0, fun _ => w₀, ?_, fun _ => hbig⟩
  refine ⟨fun i => ⟨hYm i, Set.Subset.rfl, by simp⟩, ?_, fun _ => hw₀,
    fun i _ => hcontained i, ?_, trivial, ?_, ?_, ?_⟩
  · exact
      (mul_le_of_le_one_left (zero_le : (0 : ENNReal) ≤ ∑ i, volume (Y i))
        (show ENNReal.ofReal (δ ^ h) ≤ 1 by simpa using ENNReal.ofReal_le_ofReal hp))
  · intro u t r hu hr
    have he : ({k : Fin 1 | T 1 0 w₀ ⊆ Metric.ball (0 : Space) 1 ∩
        {p | |inner ℝ u p - t| ≤ r}} : Set (Fin 1)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hnot (hk.trans Set.inter_subset_left)
    change ENNReal.ofReal (({k : Fin 1 | T 1 0 w₀ ⊆ Metric.ball (0 : Space) 1 ∩
        {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ)) ≤ _
    rw [he, Set.ncard_empty, Nat.cast_zero, ENNReal.ofReal_zero]
    exact zero_le
  · intro k k'
    have he : k = k' := Subsingleton.elim _ _
    subst k'
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hneg
  · intro k k' hne
    exact (hne (Subsingleton.elim _ _)).elim
  · intro i _
    have hb := Set.ncard_le_card
      ({k : Fin 1 | T δ (x i) (v i) ⊆ T 1 0 w₀} : Set (Fin 1))
    have hb' : ({k : Fin 1 | T δ (x i) (v i) ⊆ T 1 0 w₀}.ncard : ℝ) ≤ 1 := by
      simp only [Nat.card_fin] at hb
      exact_mod_cast hb
    exact hb'.trans hneg

/-- The scale-one cover, without the additional ambient-ball clause. -/
theorem unit_scale_cover {δ h : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hYm : ∀ i, MeasurableSet (Y i))
    (hball : ∀ i, T δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) :
    ∃ y w : Fin 1 → Space,
      Cover δ h n x v Y Finset.univ Y 1 1 y w (fun _ => 0) True := by
  obtain ⟨y, w, hC, _⟩ := unit_scale_cover_with_ball hδ hδ1 hh x v Y hYm hball
  exact ⟨y, w, hC⟩

end WangZahlLot.Obl.wz_broad_grains_initialization
