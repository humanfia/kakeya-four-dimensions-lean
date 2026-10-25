-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.FineCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Mass
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex
import Submission.WZ.Obl.wz_convex_container_tube_packing

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts counts_compose)

/-- A uniform fiber cardinality bound implies a local convex-count bound by
testing the volume of any one tube counted in the convex set. -/
theorem fiber_counts_of_card_bound {δ M : ℝ} {n k : ℕ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (x v : Fin n → Space) (f : Fin n → Fin k)
    (hv : ∀ i, ‖v i‖ = 1)
    (hcard : ∀ j, (Set.ncard {i | f i = j} : ℝ) ≤ M) :
    ∀ j W, Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {i | f i = j ∧ Tube δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal M * volume W := by
  intro j W hW
  let S : Set (Fin n) := {i | f i = j ∧ Tube δ (x i) (v i) ⊆ W}
  change ENNReal.ofReal ((S.ncard : ℝ) * δ ^ 2) ≤ _
  rcases S.eq_empty_or_nonempty with he | ⟨i, hi⟩
  · simp only [he, Set.ncard_empty, Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]
    exact bot_le
  · have hc : (S.ncard : ℝ) ≤ M := by
      apply le_trans _ (hcard j)
      exact Nat.cast_le.mpr (Set.ncard_le_ncard (fun i hi => hi.1))
    have hl := (WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ (x i) (v i) (hv i)).trans
      (measure_mono hi.2)
    calc
      _ ≤ ENNReal.ofReal (M * δ ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc (sq_nonneg δ))
      _ = ENNReal.ofReal M * ENNReal.ofReal (δ ^ 2) := ENNReal.ofReal_mul hM
      _ ≤ ENNReal.ofReal M * volume W := mul_le_mul' le_rfl hl

/-- Essential distinctness bounds the number of fine tubes in one coarse tube.
The fine tubes remain inside the unit ball, as required by the packing lemma. -/
theorem fine_fiber_packing : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (δ ρ : ℝ), 0 < δ → δ ≤ (1 / 100 : ℝ) → 0 < ρ → ρ ≤ 1 →
    ∀ (n k : ℕ) (x v : Fin n → Space) (f : Fin n → Fin k) (y w : Space) (j : Fin k),
    ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i i', i ≠ i' → volume (Tube δ (x i) (v i) ∩ Tube δ (x i') (v i')) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
    (∀ i, f i = j → Tube δ (x i) (v i) ⊆ Tube ρ y w) →
    (Set.ncard {i | f i = j} : ℝ) * δ ^ 4 ≤ C * ρ ^ 4 := by
  classical
  obtain ⟨C, hC, hpack⟩ := WangZahlLot.wz_convex_container_tube_packing
  refine ⟨C * 384 ^ 2, by nlinarith, ?_⟩
  intro δ ρ hδ hδ100 hρ hρ1 n k x v f y w j hw hv hball hsep hsub
  let S : Finset (Fin n) := Finset.univ.filter fun i => f i = j
  let e := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate S
  have heS (i : Fin S.card) : e i ∈ S :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_mem S i
  have heinj : Function.Injective e :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_injective S
  let W := Tube ρ y w ∩ Metric.ball (0 : Space) 1
  have hp := hpack δ hδ hδ100 S.card (x ∘ e) (v ∘ e) W
    (((convex_segment y (y + w)).thickening ρ).inter (convex_ball _ _))
    inter_subset_right (fun i => hv (e i))
    (fun i => subset_inter (hsub (e i) (Finset.mem_filter.mp (heS i)).2) (hball (e i)))
    (fun i i' hne => hsep (e i) (e i') (fun heq => hne (heinj heq)))
  have hvol : volume W ≤ ENNReal.ofReal (384 * ρ ^ 2) :=
    (measure_mono inter_subset_left).trans
      (WangZahlLot.Obl.wz_affine_packet_counting_transfer.tube_volume_upper hρ hρ1 y w hw)
  have hh : ENNReal.ofReal ((S.card : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal (C * 384 ^ 2 * ρ ^ 4) := by
    calc
      _ ≤ ENNReal.ofReal C * (volume W) ^ 2 := hp
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (384 * ρ ^ 2)) ^ 2 := by gcongr
      _ = ENNReal.ofReal (C * 384 ^ 2 * ρ ^ 4) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by linarith)]
        congr 1
        ring
  have hc : Set.ncard {i | f i = j} = S.card := by
    simp only [S, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [hc]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

/-- Transfer the convex count of a coarse cover to an essentially distinct
fine family, losing only the fourth power of the ratio of radii. -/
theorem counts_from_coarse_cover : ∃ C : ℝ, 0 < C ∧
    ∀ (δ ρ L : ℝ), 0 < δ → δ ≤ (1 / 100 : ℝ) → 0 < ρ → ρ ≤ 1 → 0 ≤ L →
    ∀ (n k : ℕ) (x v : Fin n → Space) (y w : Fin k → Space) (f : Fin n → Fin k),
    (∀ i, ‖v i‖ = 1) → (∀ i, ‖w i‖ = 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i i', i ≠ i' → volume (Tube δ (x i) (v i) ∩ Tube δ (x i') (v i')) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
    (∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i))) →
    Counts ρ L k y w → Counts δ (C * L * ρ ^ 4 / δ ^ 4) n x v := by
  obtain ⟨C, hC, hpack⟩ := fine_fiber_packing
  refine ⟨131072 * C, by positivity, ?_⟩
  intro δ ρ L hδ hδ100 hρ hρ1 hL n k x v y w f hv hw hball hsep hsub hcoarse
  let M := C * ρ ^ 4 / δ ^ 4
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcard (i : Fin k) : (Set.ncard {s | f s = i} : ℝ) ≤ M := by
    apply (le_div_iff₀ (pow_pos hδ 4)).mpr
    exact hpack δ ρ hδ hδ100 hρ hρ1 n k x v f (y i) (w i) i (hw i) hv hball hsep
      (fun s hs => by simpa only [hs] using hsub s)
  have hlocal := fiber_counts_of_card_bound hδ hM x v f hv hcard
  have hc := counts_compose hδ hρ hρ1 hL hM x v y w f hv hw hsub hcoarse hlocal
  convert hc using 1
  dsimp [M]
  ring

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
