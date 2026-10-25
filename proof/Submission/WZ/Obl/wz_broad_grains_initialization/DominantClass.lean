-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.DominantClass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.PointwiseRefinement
import Submission.WZ.Obl.wz_separated_cover_refinement.Selection

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (bodyCount)
open scoped Classical

/-- A finite direction class can be chosen globally while remaining a
pointwise dominant class on its retained region. Two finite pigeonhole
factors suffice, independently of the number of tubes. -/
theorem dominant_shading_class {n K : ℕ} (hK : 0 < K) (f : Fin n → Fin K)
    (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i)) :
    ∃ (k : Fin K) (Z : Fin n → Set Space),
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ ((Z i).Nonempty → f i = k)) ∧
      (∑ i, volume (Y i)) ≤ ENNReal.ofReal ((K : ℝ) ^ 2) * ∑ i, volume (Z i) ∧
      ∀ p ∈ ⋃ i, Z i, bodyCount Y p ≤ (K : ℝ) * bodyCount Z p := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hchoose (S : Finset (Fin n)) : ∃ k : Fin K,
      (S.card : ℝ) ≤ (K : ℝ) * ((S.filter fun i => f i = k).card : ℝ) := by
    obtain ⟨k, hk⟩ := wz_separated_cover_refinement.heavy_fibre f
      (fun i => if i ∈ S then (1 : ℝ) else 0)
    refine ⟨k, ?_⟩
    convert hk using 1
    · simp [Finset.sum_boole]
    · simp only [Fintype.card_fin]
      congr 1
      rw [Finset.sum_boole]
      congr 2
      ext i
      simp [and_comm]
  choose a ha using hchoose
  let pattern : Space → Finset (Fin n) := fun p => Finset.univ.filter (fun i => p ∈ Y i)
  have hpat (p : Space) (i : Fin n) : i ∈ pattern p ↔ p ∈ Y i := by simp [pattern]
  let U : Fin n → Set Space := fun i => {p | p ∈ Y i ∧ f i = a (pattern p)}
  let Z : Fin K → Fin n → Set Space :=
    fun k i => {p | p ∈ Y i ∧ f i = k ∧ a (pattern p) = k}
  have hUm (i : Fin n) : MeasurableSet (U i) := by
    have h := wz_measurable_angular_selection.measurableSet_pattern hY pattern hpat
      (fun S => i ∈ S ∧ f i = a S)
    simpa only [hpat] using h
  have hZm (k : Fin K) (i : Fin n) : MeasurableSet (Z k i) := by
    have h := wz_measurable_angular_selection.measurableSet_pattern hY pattern hpat
      (fun S => i ∈ S ∧ f i = k ∧ a S = k)
    simpa only [hpat] using h
  have hYcount (p : Space) : bodyCount Y p = ((pattern p).card : ℝ) := by
    simp [bodyCount, pattern, Set.ncard_eq_toFinset_card']
  have hUcount (p : Space) : bodyCount U p =
      (((pattern p).filter fun i => f i = a (pattern p)).card : ℝ) := by
    have he : {i | p ∈ U i} = ((pattern p).filter (fun i => f i = a (pattern p)) : Set (Fin n)) := by
      ext i
      simp [U, hpat]
    simp only [bodyCount, he, Set.ncard_coe_finset]
  have hpoint (p : Space) : bodyCount Y p ≤ (K : ℝ) * bodyCount U p := by
    rw [hYcount, hUcount]
    exact ha (pattern p)
  have hmass := wz_clustered_cover_volume_gain.body_mass_le_mul_of_count hY hUm
    (Nat.cast_nonneg K) hpoint
  have hcover (i : Fin n) : U i ⊆ ⋃ k, Z k i := by
    intro p hp
    exact Set.mem_iUnion.mpr ⟨a (pattern p), hp.1, hp.2, rfl⟩
  have hsum : (∑ i, volume (U i)) ≤ ∑ k, ∑ i, volume (Z k i) := by
    calc
      _ ≤ ∑ i, ∑ k, volume (Z k i) := Finset.sum_le_sum fun i _ =>
        (measure_mono (hcover i)).trans (by simpa only [tsum_fintype] using measure_iUnion_le (fun k => Z k i))
      _ = _ := Finset.sum_comm
  obtain ⟨k, _, hkmax⟩ := Finset.exists_max_image Finset.univ
    (fun k => ∑ i, volume (Z k i)) Finset.univ_nonempty
  refine ⟨k, Z k, fun i => ⟨hZm k i, fun _ hp => hp.1, fun ⟨p, hp⟩ => hp.2.1⟩, ?_, ?_⟩
  · calc
      _ ≤ ENNReal.ofReal (K : ℝ) * ∑ i, volume (U i) := hmass
      _ ≤ ENNReal.ofReal (K : ℝ) * (∑ l, ∑ i, volume (Z l i)) := mul_le_mul' le_rfl hsum
      _ ≤ ENNReal.ofReal (K : ℝ) * (∑ _l : Fin K, ∑ i, volume (Z k i)) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun l hl => hkmax l hl)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast K, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 2
        ring
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    have hak : a (pattern p) = k := hi.2.2
    have he : {j | p ∈ Z k j} = {j | p ∈ U j} := by
      ext j
      simp [Z, U, hak]
      tauto
    simpa only [bodyCount, he] using hpoint p

end WangZahlLot.Obl.wz_broad_grains_initialization
