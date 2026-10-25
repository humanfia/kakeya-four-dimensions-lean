-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.PointwiseRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.MeasurablePackets

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped Classical
open wz_clustered_cover_volume_gain (bodyCount lintegral_bodyCount)
open wz_measurable_angular_selection (pd)

lemma measurable_body_count {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) : Measurable (bodyCount Y) := by
  classical
  have he : bodyCount Y = fun p => ∑ i, (Y i).indicator (fun _ => (1 : ℝ)) p := by
    funext p
    simp [bodyCount, Set.ncard_eq_toFinset_card', Set.indicator, Finset.sum_boole]
  rw [he]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hY i))

lemma body_count_cut {n : ℕ} (Y : Fin n → Set Space) (G : Set Space) (p : Space) :
    bodyCount (fun i => Y i ∩ G) p = if p ∈ G then bodyCount Y p else 0 := by
  classical
  by_cases hp : p ∈ G <;> simp [bodyCount, hp]

lemma body_count_difference {n : ℕ} {Y U : Fin n → Set Space} (hU : ∀ i, U i ⊆ Y i)
    (p : Space) : bodyCount U p + bodyCount (fun i => Y i \ U i) p = bodyCount Y p := by
  classical
  let S := Finset.univ.filter (fun i => p ∈ Y i)
  let T := Finset.univ.filter (fun i => p ∈ U i)
  have hTS : T ⊆ S := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU i (Finset.mem_filter.mp hi).2⟩
  have hd : Finset.univ.filter (fun i => p ∈ Y i \ U i) = S \ T := by
    ext i
    simp [S, T]
  have he := Finset.card_sdiff_add_card_eq_card hTS
  have hY : {i | p ∈ Y i}.toFinset = S := by ext i; simp [S]
  have hU' : {i | p ∈ U i}.toFinset = T := by ext i; simp [T]
  have hB : {i | p ∈ Y i \ U i}.toFinset = S \ T := by ext i; simp [S, T]
  simp only [bodyCount, Set.ncard_eq_toFinset_card', hY, hU', hB]
  exact_mod_cast (by omega : T.card + (S \ T).card = S.card)

/-- An incidence-dependent deletion can be followed by a common point cut so
that every surviving point keeps at least half its original incidences. The
extra mass loss is at most the original deletion loss. -/
theorem pointwise_half_refinement {n : ℕ} (Y U : Fin n → Set Space)
    (hY : ∀ i, MeasurableSet (Y i)) (hU : ∀ i, MeasurableSet (U i))
    (hUY : ∀ i, U i ⊆ Y i) :
    ∃ G : Set Space, MeasurableSet G ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (U i ∩ G)) +
        2 * ∑ i, volume (Y i \ U i) ∧
      ∀ p ∈ ⋃ i, U i ∩ G,
        bodyCount Y p ≤ 2 * bodyCount (fun i => U i ∩ G) p := by
  classical
  let G : Set Space := {p | bodyCount Y p ≤ 2 * bodyCount U p}
  have hG : MeasurableSet G :=
    measurableSet_le (measurable_body_count hY) ((measurable_body_count hU).const_mul 2)
  have hZ : ∀ i, MeasurableSet (U i ∩ G) := fun i => (hU i).inter hG
  have hB : ∀ i, MeasurableSet (Y i \ U i) := fun i => (hY i).diff (hU i)
  have hc (p : Space) : bodyCount Y p ≤ bodyCount (fun i => U i ∩ G) p +
      2 * bodyCount (fun i => Y i \ U i) p := by
    rw [body_count_cut]
    have hd := body_count_difference hUY p
    have hBpos : 0 ≤ bodyCount (fun i => Y i \ U i) p := Nat.cast_nonneg _
    by_cases hp : p ∈ G
    · rw [if_pos hp]
      linarith
    · rw [if_neg hp]
      have hfail : ¬ bodyCount Y p ≤ 2 * bodyCount U p := hp
      linarith
  refine ⟨G, hG, ?_, ?_⟩
  · calc
      _ = ∫⁻ p, ENNReal.ofReal (bodyCount Y p) := (lintegral_bodyCount hY).symm
      _ ≤ ∫⁻ p, (ENNReal.ofReal (bodyCount (fun i => U i ∩ G) p) +
          2 * ENNReal.ofReal (bodyCount (fun i => Y i \ U i) p)) := by
        apply lintegral_mono
        intro p
        have hh := ENNReal.ofReal_le_ofReal (hc p)
        have hzpos : 0 ≤ bodyCount (fun i => U i ∩ G) p := Nat.cast_nonneg _
        have hbpos : 0 ≤ bodyCount (fun i => Y i \ U i) p := Nat.cast_nonneg _
        rw [ENNReal.ofReal_add hzpos (mul_nonneg (by norm_num) hbpos),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at hh
        exact hh
      _ = _ := by
        rw [lintegral_add_left ((measurable_body_count hZ).ennreal_ofReal),
          lintegral_const_mul _ ((measurable_body_count hB).ennreal_ofReal),
          lintegral_bodyCount hZ, lintegral_bodyCount hB]
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    rw [body_count_cut, if_pos hi.2]
    exact hi.2

/-- A pointwise incidence fraction preserves broadness with the inverse
fraction as its only additional constant. -/
theorem broadness_of_pointwise_fraction_at {n : ℕ} {Y Z : Fin n → Set Space}
    {v : Fin n → Space} {C B r β : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hZY : ∀ i, Z i ⊆ Y i)
    (hcount : ∀ p ∈ ⋃ i, Z i, bodyCount Y p ≤ C * bodyCount Z p)
    (p u : Space)
    (hbroad : ({i | p ∈ Y i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
      B * r ^ β * bodyCount Y p) :
    ({i | p ∈ Z i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
      (C * B) * r ^ β * bodyCount Z p := by
  by_cases hp : p ∈ ⋃ i, Z i
  · have hsub : {i | p ∈ Z i ∧ pd (v i) u ≤ r} ⊆ {i | p ∈ Y i ∧ pd (v i) u ≤ r} :=
      fun i hi => ⟨hZY i hi.1, hi.2⟩
    calc
      _ ≤ ({i | p ∈ Y i ∧ pd (v i) u ≤ r}.ncard : ℝ) :=
        Nat.cast_le.mpr (Set.ncard_mono hsub)
      _ ≤ B * r ^ β * bodyCount Y p := hbroad
      _ ≤ B * r ^ β * (C * bodyCount Z p) :=
        mul_le_mul_of_nonneg_left (hcount p hp) (mul_nonneg hB (Real.rpow_nonneg hr _))
      _ = _ := by ring
  · have he : {i | p ∈ Z i ∧ pd (v i) u ≤ r} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hi _ => hp (Set.mem_iUnion.mpr ⟨i, hi⟩)
    rw [he, Set.ncard_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hB) (Real.rpow_nonneg hr _)) (Nat.cast_nonneg _)

/-- Uniform broadness follows from the pointwise transfer. -/
theorem broadness_of_pointwise_fraction {n : ℕ} {Y Z : Fin n → Set Space}
    {v : Fin n → Space} {C B r β : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hr : 0 ≤ r) (hZY : ∀ i, Z i ⊆ Y i)
    (hcount : ∀ p ∈ ⋃ i, Z i, bodyCount Y p ≤ C * bodyCount Z p)
    (hbroad : ∀ p u, ({i | p ∈ Y i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
      B * r ^ β * bodyCount Y p) (p u : Space) :
    ({i | p ∈ Z i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
      (C * B) * r ^ β * bodyCount Z p :=
  broadness_of_pointwise_fraction_at hC hB hr hZY hcount p u (hbroad p u)

end WangZahlLot.Obl.wz_broad_grains_initialization
