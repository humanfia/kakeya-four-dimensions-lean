-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.CountedSlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabExtraction

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

/-- Counted slab extraction for a subfamily whose body volumes are uniformly
comparable. The family need not exhaust the ambient index type. -/
lemma counted_slab_extraction {ι : Type*} (I : Finset ι) (U Y : ι → Set E)
    (hUc : ∀ i ∈ I, IsCompact (U i)) (hUconv : ∀ i ∈ I, Convex ℝ (U i))
    {ρ w C d : ℝ} (hρ : 0 < ρ) (hw : 0 < w) (hC : 0 < C) (hd : 0 ≤ d)
    (hballs : ∀ i ∈ I, ∃ x, Metric.ball x ρ ⊆ U i)
    (hbounded : ∀ i ∈ I, U i ⊆ Metric.closedBall (0 : E) 1)
    (hweights : ∀ i ∈ I, w ≤ (volume (U i)).toReal ∧ (volume (U i)).toReal ≤ C * w)
    (K : ℕ) (hbottom : (1 / 2 : ℝ) ^ K * (C * (I.card : ℝ)) ≤ 1)
    (hYm : ∀ i ∈ I, MeasurableSet (Y i)) (hYU : ∀ i ∈ I, Y i ⊆ U i)
    (hdense : ∀ i ∈ I, ENNReal.ofReal d * volume (U i) ≤ volume (Y i)) :
    ∃ (m : ℕ) (A : Fin m → ShadedCell ι),
      (∀ j, (A j).Valid I U Y (ENNReal.ofReal (d / 2)) (SlabFamilyGood U)) ∧
      Pairwise (fun j k => Disjoint (A j).support (A k).support) ∧
      d * (I.card : ℝ) ≤ 2 * (1 + 320 * K : ℝ) * C * ∑ j, ((A j).indices.card : ℝ) := by
  classical
  have hUpos : ∀ i ∈ I, volume (U i) ≠ 0 := by
    intro i hi hz
    have hw' := (hweights i hi).1
    rw [hz, ENNReal.toReal_zero] at hw'
    linarith
  have htotal : ∀ F ⊆ I, (∑ i ∈ F, (volume (U i)).toReal) ≤ (F.card : ℝ) * (C * w) := by
    intro F hFI
    calc (∑ i ∈ F, (volume (U i)).toReal) ≤ ∑ _i ∈ F, C * w :=
        Finset.sum_le_sum fun i hi => (hweights i (hFI hi)).2
      _ = _ := by simp
  have hbase : (1 / 2 : ℝ) ^ K * (∑ i ∈ I, (volume (U i)).toReal) ≤ w := by
    calc (1 / 2 : ℝ) ^ K * (∑ i ∈ I, (volume (U i)).toReal)
        ≤ (1 / 2 : ℝ) ^ K * ((I.card : ℝ) * (C * w)) := by gcongr; exact htotal I Subset.rfl
      _ = ((1 / 2 : ℝ) ^ K * (C * (I.card : ℝ))) * w := by ring
      _ ≤ 1 * w := by gcongr
      _ = w := one_mul _
  have htwice : 2 * ENNReal.ofReal (d / 2) = ENNReal.ofReal d := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  -- Restrict the abstract selector to the subtype, so it is available on every finite set.
  let e : I → ι := Subtype.val
  have hselect' : ∀ (F : Finset I), F.Nonempty →
      ∃ (J : Finset I) (W : Set E), J.Nonempty ∧ J ⊆ F ∧ MeasurableSet W ∧
        (∃ S : SlabSpec, W = S.carrier ∧ S.width ≤ 2 ∧
          ∀ T : SlabSpec, T.weight J (U ∘ e) (fun i => (volume (U (e i))).toReal) / T.width ≤
            2 * (∑ i ∈ J, (volume (U (e i))).toReal) / S.width) ∧
        (∀ i ∈ J, U (e i) ⊆ W) ∧
        ∑ i ∈ F, volume (U (e i) ∩ W) ≤ ENNReal.ofReal (1 + 320 * K : ℝ) * ∑ i ∈ J, volume (U (e i)) := by
    intro F hF
    apply select_slab_container F hF (U ∘ e) (fun i _ => hUc i i.property)
      (fun i _ => hUconv i i.property) (fun i _ => hUpos i i.property) hρ
      (fun i _ => hballs i i.property) (fun i _ => hbounded i i.property) K w
      (fun i _ => (hweights i i.property).1)
    apply le_trans _ hbase
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (∑ i ∈ F, (volume (U (e i))).toReal) ≤ ∑ i : I, (volume (U (e i))).toReal :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => ENNReal.toReal_nonneg)
      _ = _ := by simpa only [e] using Finset.sum_coe_sort I (fun i => (volume (U i)).toReal)
  obtain ⟨m, A, hA, hdisj, hmass⟩ := greedy_container_retained_weight (U ∘ e)
    (SlabFamilyGood (U ∘ e)) (ENNReal.ofReal (1 + 320 * K : ℝ)) (ENNReal.ofReal (d / 2))
    ENNReal.ofReal_ne_top hselect' Finset.univ (Y ∘ e)
    (fun i _ => hYm i i.property) (fun i _ => hYU i i.property)
    (fun i _ => (hUc i i.property).measure_ne_top)
    (fun i _ => by simpa only [htwice, Function.comp_apply] using hdense i i.property)
  let lift (B : ShadedCell I) : ShadedCell ι := {
    indices := B.indices.image e, region := B.region,
    shading := fun i => if hi : i ∈ I then B.shading ⟨i, hi⟩ else ∅ }
  have hinj : Function.Injective e := Subtype.val_injective
  have hlift : ∀ j, (lift (A j)).Valid I U Y (ENNReal.ofReal (d / 2)) (SlabFamilyGood U) := by
    intro j
    obtain ⟨hne, hsub, ⟨S, hS, hSw, hmax⟩, hwhole, hm, hsh, hd⟩ := hA j
    refine ⟨hne.image e, ?_, ⟨S, hS, hSw, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      exact k.property
    · intro T
      simpa only [SlabSpec.weight, lift, Finset.sum_image hinj.injOn, Function.comp_apply] using hmax T
    all_goals
      intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      simp only [lift, e, dite_true, k.property]
    · exact hwhole k hk
    · exact hm k hk
    · exact hsh k hk
    · exact hd k hk
  have hsupport : ∀ j, (lift (A j)).support = (A j).support := by
    intro j
    ext p
    simp only [ShadedCell.support, lift, mem_iUnion, Finset.mem_image]
    constructor
    · rintro ⟨i, ⟨k, hk, rfl⟩, hp⟩
      exact ⟨k, hk, by simpa only [lift, e, dite_true, k.property] using hp⟩
    · rintro ⟨k, hk, hp⟩
      exact ⟨e k, ⟨k, hk, rfl⟩, by simpa only [lift, e, dite_true, k.property] using hp⟩
  refine ⟨m, fun j => lift (A j), hlift, ?_, ?_⟩
  · intro j k hjk
    simpa only [hsupport] using hdisj hjk
  have hAfin : ∀ j, (∑ i ∈ (A j).indices, volume (U (e i))) ≠ ∞ :=
    fun j => ENNReal.sum_ne_top.mpr (fun i _ => (hUc i i.property).measure_ne_top)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr (fun j _ => hAfin j))) hmass
  dsimp only [Function.comp_apply] at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_sum (fun (i : I) _ => (hUc i i.property).measure_ne_top),
    ENNReal.toReal_sum (fun j _ => hAfin j)] at hreal
  have hinner (j : Fin m) : (∑ i ∈ (A j).indices, volume (U (e i))).toReal =
      ∑ i ∈ (A j).indices, (volume (U (e i))).toReal :=
    ENNReal.toReal_sum (fun i _ => (hUc i i.property).measure_ne_top)
  simp_rw [hinner] at hreal
  have hlo : (I.card : ℝ) * w ≤ ∑ i : I, (volume (U (e i))).toReal := by
    calc (I.card : ℝ) * w = ∑ _i : I, w := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => (hweights i i.property).1
  have hhi : (∑ j, ∑ i ∈ (A j).indices, (volume (U (e i))).toReal) ≤
      C * w * ∑ j, ((A j).indices.card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc (∑ i ∈ (A j).indices, (volume (U (e i))).toReal) ≤ ∑ _i ∈ (A j).indices, C * w :=
        Finset.sum_le_sum fun i _ => (hweights i i.property).2
      _ = _ := by simp; ring
  have hbound : d / 2 * ((I.card : ℝ) * w) ≤
      (1 + 320 * K : ℝ) * (C * w * ∑ j, ((A j).indices.card : ℝ)) := by
    exact (mul_le_mul_of_nonneg_left hlo (by positivity)).trans
      (hreal.trans (mul_le_mul_of_nonneg_left hhi (by positivity)))
  simp only [lift, Finset.card_image_of_injective _ hinj]
  apply (mul_le_mul_iff_right₀ hw).mp
  nlinarith [hbound]

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
