-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.NDCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.ShearFubini
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Projection

/-!
# Nondegeneracy, step 1: a rich prism

Transversal tubes with fair shading mass in a horizontal slab of height `L` concentrate, after
choosing a popular height and an AD window of the twisted slice there, in a prism
`{|twist f q - c| ≤ 4L/θ}` that contains `≳ L^(1-σ) n` dense tubes.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

private lemma ndc_coord_le (p : Space) (k : Fin 3) : |p k| ≤ ‖p‖ :=
  PiLp.norm_apply_le p k

private lemma ndc_tube_coord {δ t : ℝ} {x v q : Space} (h : ‖q - (x + t • v)‖ < δ) (k : Fin 3) :
    |q k - (x k + t * v k)| < δ := by
  have := (ndc_coord_le (q - (x + t • v)) k).trans_lt h
  simpa using this

/-- A point of a transversal tube is within `2δ/θ` (in the first two coordinates) of the
axis point at the same height. -/
private lemma ndc_tube_slice {δ θ : ℝ} {x v p : Space} (hδ : 0 < δ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hv : ‖v‖ = 1) (hθv : θ ≤ |v 2|) (hp : p ∈ Tube δ x v) :
    |p 0 - (x 0 + (p 2 - x 2) / v 2 * v 0)| ≤ 2 * δ / θ ∧
    |p 1 - (x 1 + (p 2 - x 2) / v 2 * v 1)| ≤ 2 * δ / θ := by
  obtain ⟨t, -, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  have he := ndc_tube_coord hpt
  have hv2 : 0 < |v 2| := hθ.trans_le hθv
  have hv2' : v 2 ≠ 0 := abs_pos.mp hv2
  have hvk : ∀ k, |v k| ≤ 1 := fun k => (ndc_coord_le v k).trans hv.le
  set s := (p 2 - x 2) / v 2 with hs_def
  have hsv : s * v 2 = p 2 - x 2 := by rw [hs_def]; field_simp
  have hts : |t - s| ≤ δ / θ := by
    have h1 : |t - s| * |v 2| < δ := by
      rw [← abs_mul]
      have : (t - s) * v 2 = -(p 2 - (x 2 + t * v 2)) := by rw [sub_mul, hsv]; ring
      rw [this, abs_neg]
      exact he 2
    rw [le_div_iff₀ hθ]
    calc |t - s| * θ ≤ |t - s| * |v 2| := mul_le_mul_of_nonneg_left hθv (abs_nonneg _)
      _ ≤ δ := h1.le
  have hδθ : δ ≤ δ / θ := by rw [le_div_iff₀ hθ]; nlinarith
  have hcoord : ∀ k, |p k - (x k + s * v k)| ≤ 2 * δ / θ := by
    intro k
    have : p k - (x k + s * v k) = (p k - (x k + t * v k)) + (t - s) * v k := by ring
    rw [this]
    calc |(p k - (x k + t * v k)) + (t - s) * v k|
        ≤ |p k - (x k + t * v k)| + |(t - s) * v k| := abs_add_le _ _
      _ = |p k - (x k + t * v k)| + |t - s| * |v k| := by rw [abs_mul]
      _ ≤ δ + δ / θ * 1 := by
          gcongr
          · exact (he k).le
          · exact hvk k
      _ ≤ 2 * δ / θ := by rw [mul_one, mul_div_assoc]; linarith
  exact ⟨hcoord 0, hcoord 1⟩

/-- The grain-coordinate area of a horizontal slice of a transversal tube is `≲ δ²/θ²`. -/
private lemma ndc_slice_area {δ θ : ℝ} {f : ℝ → ℝ} {x v : Space} {S : Set Space}
    (hδ : 0 < δ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hv : ‖v‖ = 1) (hθv : θ ≤ |v 2|)
    (hS : S ⊆ Tube δ x v) (hSf : ∀ q ∈ S, |f (q 2)| ≤ 1) (z : ℝ) :
    ∫⁻ u, volume (grainFib f S u z) ≤ ENNReal.ofReal (32 * δ ^ 2 / θ ^ 2) := by
  set s := (z - x 2) / v 2 with hs_def
  set y0 := x 1 + s * v 1 with hy0
  set u0 := x 0 + s * v 0 + f z * y0 with hu0
  have key : ∀ u y, ofTwist f u y z ∈ S → |y - y0| ≤ 2 * δ / θ ∧ |u - u0| ≤ 4 * δ / θ := by
    intro u y hmem
    have h := ndc_tube_slice hδ hθ hθ1 hv hθv (hS hmem)
    have hf := hSf _ hmem
    simp only [ofTwist_zero, ofTwist_one, ofTwist_two] at h hf
    obtain ⟨h0, h1⟩ := h
    refine ⟨h1, ?_⟩
    have heq : u - u0 = (u - f z * y - (x 0 + s * v 0)) + f z * (y - y0) := by
      rw [hu0]; ring
    rw [heq]
    calc |(u - f z * y - (x 0 + s * v 0)) + f z * (y - y0)|
        ≤ |u - f z * y - (x 0 + s * v 0)| + |f z * (y - y0)| := abs_add_le _ _
      _ = |u - f z * y - (x 0 + s * v 0)| + |f z| * |y - y0| := by rw [abs_mul]
      _ ≤ 2 * δ / θ + 1 * (2 * δ / θ) := by
          gcongr
      _ = 4 * δ / θ := by ring
  calc ∫⁻ u, volume (grainFib f S u z)
      ≤ ∫⁻ u, (Icc (u0 - 4 * δ / θ) (u0 + 4 * δ / θ)).indicator
          (fun _ => ENNReal.ofReal (4 * δ / θ)) u := by
        apply lintegral_mono
        intro u
        by_cases hu : u ∈ Icc (u0 - 4 * δ / θ) (u0 + 4 * δ / θ)
        · rw [indicator_of_mem hu]
          calc volume (grainFib f S u z)
              ≤ volume (Icc (y0 - 2 * δ / θ) (y0 + 2 * δ / θ)) := by
                apply measure_mono
                intro y hy
                have := (key u y hy).1
                rw [abs_le] at this
                constructor <;> linarith [this.1, this.2]
            _ = ENNReal.ofReal (4 * δ / θ) := by
                rw [Real.volume_Icc]; congr 1; ring
        · rw [indicator_of_notMem hu]
          have hempty : grainFib f S u z = ∅ := by
            apply eq_empty_of_forall_notMem
            intro y hy
            apply hu
            have := (key u y hy).2
            rw [abs_le] at this
            constructor <;> linarith [this.1, this.2]
          simp only [hempty, measure_empty, le_refl]
    _ = ENNReal.ofReal (4 * δ / θ) * volume (Icc (u0 - 4 * δ / θ) (u0 + 4 * δ / θ)) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (32 * δ ^ 2 / θ ^ 2) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- Within the slab, the twisted coordinate of a transversal tube drifts by at most `3L/θ`. -/
private lemma ndc_drift {δ θ L z1 : ℝ} {f : ℝ → ℝ} {x v q q' : Space}
    (hδ : 0 < δ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hδL : 100 * δ ≤ L) (hLθ : 10 * L ≤ θ)
    (hv : ‖v‖ = 1) (hθv : θ ≤ |v 2|)
    (hq : q ∈ Tube δ x v) (hq' : q' ∈ Tube δ x v)
    (hqJ : q 2 ∈ Icc z1 (z1 + L)) (hq'J : q' 2 ∈ Icc z1 (z1 + L))
    (hq1 : |q 1| ≤ 1) (hf' : |f (q' 2)| ≤ 1)
    (hlip : |f (q 2) - f (q' 2)| ≤ 2 * L * |q 2 - q' 2|) :
    |twist f q - twist f q'| ≤ 3 * L / θ := by
  obtain ⟨t, -, hqt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hq
  obtain ⟨t', -, hqt'⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hq'
  have he := ndc_tube_coord hqt
  have he' := ndc_tube_coord hqt'
  have hvk : ∀ k, |v k| ≤ 1 := fun k => (ndc_coord_le v k).trans hv.le
  have hqq : |q 2 - q' 2| ≤ L := by
    rw [abs_le]; constructor <;> linarith [hqJ.1, hqJ.2, hq'J.1, hq'J.2]
  have hD : |t - t'| * θ ≤ L + 2 * δ := by
    have h2 : (t - t') * v 2 =
        (q 2 - q' 2) - (q 2 - (x 2 + t * v 2)) + (q' 2 - (x 2 + t' * v 2)) := by ring
    calc |t - t'| * θ ≤ |t - t'| * |v 2| := mul_le_mul_of_nonneg_left hθv (abs_nonneg _)
      _ = |(t - t') * v 2| := (abs_mul _ _).symm
      _ ≤ |q 2 - q' 2| + |q 2 - (x 2 + t * v 2)| + |q' 2 - (x 2 + t' * v 2)| := by
          rw [h2]
          exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ L + δ + δ := by linarith [he 2, he' 2]
      _ = L + 2 * δ := by ring
  have hk : ∀ k, |q k - q' k| ≤ |t - t'| + 2 * δ := by
    intro k
    have h3 : q k - q' k =
        (t - t') * v k + (q k - (x k + t * v k)) - (q' k - (x k + t' * v k)) := by ring
    rw [h3]
    calc |(t - t') * v k + (q k - (x k + t * v k)) - (q' k - (x k + t' * v k))|
        ≤ |(t - t') * v k| + |q k - (x k + t * v k)| + |q' k - (x k + t' * v k)| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |t - t'| * |v k| + |q k - (x k + t * v k)| + |q' k - (x k + t' * v k)| := by
          rw [abs_mul]
      _ ≤ |t - t'| * 1 + δ + δ := by
          gcongr
          · exact hvk k
          · exact (he k).le
          · exact (he' k).le
      _ = |t - t'| + 2 * δ := by ring
  have htw : twist f q - twist f q' =
      (q 0 - q' 0) + f (q' 2) * (q 1 - q' 1) + (f (q 2) - f (q' 2)) * q 1 := by
    simp only [twist]; ring
  have hlipL : |f (q 2) - f (q' 2)| ≤ 2 * L * L :=
    hlip.trans (mul_le_mul_of_nonneg_left hqq (by linarith))
  rw [htw]
  have hL : 0 < L := by linarith
  calc |(q 0 - q' 0) + f (q' 2) * (q 1 - q' 1) + (f (q 2) - f (q' 2)) * q 1|
      ≤ |q 0 - q' 0| + |f (q' 2)| * |q 1 - q' 1| + |f (q 2) - f (q' 2)| * |q 1| := by
        rw [← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (|t - t'| + 2 * δ) + 1 * (|t - t'| + 2 * δ) + (2 * L * L) * 1 := by
        gcongr
        · exact hk 0
        · exact hk 1
    _ ≤ 3 * L / θ := by
        rw [le_div_iff₀ hθ]
        have hD' := hD
        have hab : 0 ≤ |t - t'| := abs_nonneg _
        nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hθ1), mul_nonneg (mul_nonneg hL.le hL.le)
          (sub_nonneg.mpr hθ1), mul_nonneg hL.le (show 0 ≤ 1 / 10 - L by linarith)]

/-- A transversal tube meets the slab `{q 2 ∈ [z1, z1 + L]}` in volume `≲ L δ² / θ`. -/
private lemma ndc_vol_le {δ θ L z1 : ℝ} {x v : Space} {S : Set Space}
    (hδ : 0 < δ) (hθ : 0 < θ) (hδL : 100 * δ ≤ L) (hv : ‖v‖ = 1) (hθv : θ ≤ |v 2|)
    (hS : S ⊆ Tube δ x v) (hSJ : S ⊆ {q | q 2 ∈ Icc z1 (z1 + L)}) :
    volume S ≤ ENNReal.ofReal (576 * L * δ ^ 2 / θ) := by
  let e2 : Space := EuclideanSpace.single 2 1
  have hinner : ∀ p : Space, inner ℝ e2 p = p 2 := by
    intro p; simp [e2, EuclideanSpace.inner_single_left]
  have he2 : ‖e2‖ ≤ 1 := by simp [e2]
  have hv2 : 0 < |v 2| := hθ.trans_le hθv
  have hsub : S ⊆ Tube δ x v ∩ {p | |inner ℝ e2 p - (z1 + L / 2)| ≤ L / 2} := by
    intro q hq
    refine ⟨hS hq, ?_⟩
    have hJ := hSJ hq
    simp only [mem_ofPred_eq] at hJ ⊢
    rw [hinner, abs_le]
    constructor <;> linarith [hJ.1, hJ.2]
  have h := tube_slab_volume_le hδ (show δ ≤ L / 2 by linarith) x v e2 hv he2
    (by rwa [hinner]) (z1 + L / 2)
  rw [hinner] at h
  refine (measure_mono hsub).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  have hL : 0 < L := by linarith
  have heq : 1152 * (L / 2 / |v 2|) * δ ^ 2 = 576 * L * δ ^ 2 / |v 2| := by ring
  rw [heq]
  exact div_le_div_of_nonneg_left (by positivity) hθ hθv

theorem nd_count : ∃ K : ℝ, 1 ≤ K ∧ ∀ (σ η δ θ L mu z1 : ℝ), 0 < σ → σ < 1 → 0 < η →
    0 < δ → δ ≤ 1 / 100 → 0 < θ → θ ≤ 1 → 0 < mu → 100 * δ ≤ L → 10 * L ≤ θ →
    -1 ≤ z1 → z1 + L ≤ 1 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), Family δ n x v Y →
    ∀ f : ℝ → ℝ, Continuous f → (∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1) →
    (∀ z ∈ Icc z1 (z1 + L), ∀ z' ∈ Icc z1 (z1 + L), |f z - f z'| ≤ 2 * L * |z - z'|) →
    GlobalGrains σ η δ f (⋃ i, Y i) →
    ∀ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) → (∀ i, Z i ⊆ Y i) →
    (∀ i, (Z i).Nonempty → θ ≤ |v i 2|) → (∀ i, Z i ⊆ {q | q 2 ∈ Icc z1 (z1 + L)}) →
    ENNReal.ofReal (mu * n * L * δ ^ 2) ≤ ∑ i, volume (Z i) →
    ∃ (c : ℝ) (G : Finset (Fin n)),
      (∀ i ∈ G, Z i ⊆ {q | |twist f q - c| ≤ 4 * L / θ}) ∧
      (∀ i ∈ G, ENNReal.ofReal (mu * L * δ ^ 2 / 2) ≤ volume (Z i)) ∧
      mu ^ 2 * θ ^ 3 * n * L ^ (1 - σ) * δ ^ η ≤ K * G.card := by
  classical
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro σ η δ θ L mu z1 hσ hσ1 hη hδ hδ1 hθ hθ1 hmu hδL hLθ hz1 hz1L n x v Y hFam f hf hfb
    hflip hGG Z hZm hZY hZθ hZJ hmass
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, ∅, by simp, by simp, by simp⟩
  have hL : 0 < L := by linarith
  have hJ : Icc z1 (z1 + L) ⊆ Icc (-1) 1 := Icc_subset_Icc hz1 hz1L
  have hEb : (⋃ i, Y i) ⊆ ball 0 1 := iUnion_subset fun i => (hFam.sub i).trans (hFam.ball i)
  have hZT : ∀ i, Z i ⊆ Tube δ (x i) (v i) := fun i => (hZY i).trans (hFam.sub i)
  have hZf : ∀ i, ∀ q ∈ Z i, |f (q 2)| ≤ 1 := fun i q hq => hfb _ (hJ (hZJ i hq))
  -- The tubes with a fair share of the mass.
  set G1 : Finset (Fin n) :=
    Finset.univ.filter (fun i => ENNReal.ofReal (mu * L * δ ^ 2 / 2) ≤ volume (Z i)) with hG1_def
  have hG1ne : ∀ i ∈ G1, (Z i).Nonempty := by
    intro i hi
    apply nonempty_of_measure_ne_zero
    have h := (Finset.mem_filter.mp hi).2
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (mu * L * δ ^ 2 / 2) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact (hpos.trans_le h).ne'
  have hG1θ : ∀ i ∈ G1, θ ≤ |v i 2| := fun i hi => hZθ i (hG1ne i hi)
  have hG1card : mu * n * θ ≤ 1152 * G1.card := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => ENNReal.ofReal (mu * L * δ ^ 2 / 2) ≤ volume (Z i)) (fun i => volume (Z i))
    have h1 : ∑ i ∈ G1, volume (Z i) ≤ G1.card • ENNReal.ofReal (576 * L * δ ^ 2 / θ) :=
      Finset.sum_le_card_nsmul _ _ _ (fun i hi =>
        ndc_vol_le hδ hθ hδL (hFam.unit i) (hG1θ i hi) (hZT i) (hZJ i))
    set G1c := Finset.univ.filter
      (fun i => ¬ ENNReal.ofReal (mu * L * δ ^ 2 / 2) ≤ volume (Z i)) with hG1c_def
    have h2 : ∑ i ∈ G1c, volume (Z i) ≤ G1c.card • ENNReal.ofReal (mu * L * δ ^ 2 / 2) :=
      Finset.sum_le_card_nsmul _ _ _ (fun i hi => (not_le.mp (Finset.mem_filter.mp hi).2).le)
    have hc2 : G1c.card ≤ n := (Finset.card_filter_le _ _).trans (by simp)
    have htot : ENNReal.ofReal (mu * n * L * δ ^ 2) ≤
        ENNReal.ofReal (G1.card * (576 * L * δ ^ 2 / θ) + n * (mu * L * δ ^ 2 / 2)) := by
      calc ENNReal.ofReal (mu * n * L * δ ^ 2) ≤ ∑ i, volume (Z i) := hmass
        _ = ∑ i ∈ G1, volume (Z i) + ∑ i ∈ G1c, volume (Z i) := hsplit.symm
        _ ≤ G1.card • ENNReal.ofReal (576 * L * δ ^ 2 / θ) +
              G1c.card • ENNReal.ofReal (mu * L * δ ^ 2 / 2) := add_le_add h1 h2
        _ ≤ G1.card • ENNReal.ofReal (576 * L * δ ^ 2 / θ) +
              n • ENNReal.ofReal (mu * L * δ ^ 2 / 2) := by
            gcongr
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), nsmul_eq_mul, nsmul_eq_mul,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot
    have hLd : 0 < L * δ ^ 2 := by positivity
    have h3 : mu * n * L * δ ^ 2 / 2 ≤ G1.card * (576 * L * δ ^ 2 / θ) := by linarith
    have h4 := mul_le_mul_of_nonneg_right h3 (show 0 ≤ 2 * θ by positivity)
    have e1 : mu * n * L * δ ^ 2 / 2 * (2 * θ) = (mu * n * θ) * (L * δ ^ 2) := by ring
    have e2 : (G1.card : ℝ) * (576 * L * δ ^ 2 / θ) * (2 * θ) =
        (1152 * G1.card) * (L * δ ^ 2) := by field_simp; ring
    rw [e1, e2] at h4
    exact le_of_mul_le_mul_right h4 hLd
  -- Slice areas.
  set g : Fin n → ℝ → ℝ≥0∞ := fun i z => ∫⁻ u, volume (grainFib f (Z i) u z) with hg_def
  have hgm : ∀ i, Measurable (g i) := fun i =>
    (measurable_grainFib_volume hf (hZm i)).lintegral_prod_left'
  have hgZ : ∀ i, volume (Z i) = ∫⁻ z, g i z := fun i => volume_eq_lintegral_grainFib hf (hZm i)
  have hgle : ∀ i ∈ G1, ∀ z, g i z ≤ ENNReal.ofReal (32 * δ ^ 2 / θ ^ 2) := fun i hi z =>
    ndc_slice_area hδ hθ hθ1 (hFam.unit i) (hG1θ i hi) (hZT i) (hZf i) z
  have hg0 : ∀ i z, z ∉ Icc z1 (z1 + L) → g i z = 0 := by
    intro i z hz
    have hempty : ∀ u, grainFib f (Z i) u z = ∅ := by
      intro u
      apply eq_empty_of_forall_notMem
      intro y hy
      have := hZJ i (mem_grainFib.mp hy)
      simp only [mem_ofPred_eq, ofTwist_two] at this
      exact hz this
    simp [hg_def, hempty]
  -- A popular height.
  set cnt : ℝ → ℕ := fun z => (G1.filter (fun i => 0 < g i z)).card with hcnt_def
  obtain ⟨zs, hzsJ, hzsmax⟩ :
      ∃ zs ∈ Icc z1 (z1 + L), ∀ z ∈ Icc z1 (z1 + L), cnt z ≤ cnt zs := by
    have hne : (cnt '' Icc z1 (z1 + L)).Nonempty := (nonempty_Icc.mpr (by linarith)).image _
    have hbdd : BddAbove (cnt '' Icc z1 (z1 + L)) :=
      ⟨G1.card, by rintro _ ⟨z, -, rfl⟩; exact Finset.card_filter_le _ _⟩
    obtain ⟨zs, hzs, hzseq⟩ := Nat.sSup_mem hne hbdd
    exact ⟨zs, hzs, fun z hz => hzseq ▸ le_csSup hbdd ⟨z, hz, rfl⟩⟩
  set G2 := G1.filter (fun i => 0 < g i zs) with hG2_def
  have hG2card : (G1.card : ℝ) * mu * θ ^ 2 ≤ 64 * G2.card := by
    have hFle : ∀ z, ∑ i ∈ G1, g i z ≤ (Icc z1 (z1 + L)).indicator
        (fun _ => (G2.card : ℝ≥0∞) * ENNReal.ofReal (32 * δ ^ 2 / θ ^ 2)) z := by
      intro z
      by_cases hz : z ∈ Icc z1 (z1 + L)
      · rw [indicator_of_mem hz]
        calc ∑ i ∈ G1, g i z = ∑ i ∈ G1.filter (fun i => 0 < g i z), g i z :=
              (Finset.sum_filter_of_ne (fun i _ h => pos_iff_ne_zero.mpr h)).symm
          _ ≤ (G1.filter (fun i => 0 < g i z)).card • ENNReal.ofReal (32 * δ ^ 2 / θ ^ 2) :=
              Finset.sum_le_card_nsmul _ _ _ (fun i hi => hgle i (Finset.mem_filter.mp hi).1 z)
          _ ≤ _ := by
              rw [nsmul_eq_mul]
              exact mul_le_mul' (by exact_mod_cast hzsmax z hz) le_rfl
      · rw [indicator_of_notMem hz]
        rw [Finset.sum_eq_zero (fun i _ => hg0 i z hz)]
    have hup : ∑ i ∈ G1, volume (Z i) ≤
        ENNReal.ofReal (G2.card * (32 * δ ^ 2 / θ ^ 2) * L) := by
      calc ∑ i ∈ G1, volume (Z i) = ∑ i ∈ G1, ∫⁻ z, g i z :=
            Finset.sum_congr rfl (fun i _ => hgZ i)
        _ = ∫⁻ z, ∑ i ∈ G1, g i z := (lintegral_finsetSum _ (fun i _ => hgm i)).symm
        _ ≤ ∫⁻ z, (Icc z1 (z1 + L)).indicator
              (fun _ => (G2.card : ℝ≥0∞) * ENNReal.ofReal (32 * δ ^ 2 / θ ^ 2)) z :=
            lintegral_mono hFle
        _ = (G2.card : ℝ≥0∞) * ENNReal.ofReal (32 * δ ^ 2 / θ ^ 2) *
              volume (Icc z1 (z1 + L)) := lintegral_indicator_const measurableSet_Icc _
        _ = _ := by
            rw [Real.volume_Icc, show z1 + L - z1 = L by ring, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have hlow : ENNReal.ofReal (G1.card * (mu * L * δ ^ 2 / 2)) ≤ ∑ i ∈ G1, volume (Z i) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ (fun i hi => (Finset.mem_filter.mp hi).2)
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlow.trans hup)
    have hpos : 0 < L * δ ^ 2 / (2 * θ ^ 2) := by positivity
    have e1 : (G1.card : ℝ) * (mu * L * δ ^ 2 / 2) =
        (G1.card * mu * θ ^ 2) * (L * δ ^ 2 / (2 * θ ^ 2)) := by field_simp
    have e2 : (G2.card : ℝ) * (32 * δ ^ 2 / θ ^ 2) * L =
        (64 * G2.card) * (L * δ ^ 2 / (2 * θ ^ 2)) := by field_simp; ring
    rw [e1, e2] at hreal
    exact le_of_mul_le_mul_right hreal hpos
  -- A point of each popular tube at the popular height.
  have hpt : ∀ i ∈ G2, ∃ q ∈ Z i, q 2 = zs := by
    intro i hi
    have hpos : 0 < g i zs := (Finset.mem_filter.mp hi).2
    by_contra hcon
    have h0 : ∀ u, volume (grainFib f (Z i) u zs) = 0 := by
      intro u
      by_contra hne
      obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero hne
      exact hcon ⟨ofTwist f u y zs, mem_grainFib.mp hy, ofTwist_two f u y zs⟩
    have : g i zs = 0 := by simp [hg_def, h0]
    exact hpos.ne' this
  have hpt' : ∀ i, ∃ q : Space, i ∈ G2 → q ∈ Z i ∧ q 2 = zs := by
    intro i
    by_cases hi : i ∈ G2
    · obtain ⟨q, hq, hq2⟩ := hpt i hi
      exact ⟨q, fun _ => ⟨hq, hq2⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose qq hqq using hpt'
  -- The AD covering of the twisted slice at the popular height.
  have hzs1 : zs ∈ Icc (-1 : ℝ) 1 := hJ hzsJ
  have hr : δ ≤ L / θ := by rw [le_div_iff₀ hθ]; nlinarith
  have hr4 : L / θ ≤ 4 := by rw [div_le_iff₀ hθ]; nlinarith
  obtain ⟨m, c, hcov, hm⟩ := hGG zs hzs1 (L / θ) 4 (-2) hr hr4
  have hPS : ∀ i ∈ G2, twist f (qq i) ∈ PS f (⋃ i, Y i) zs ∩ Icc (-2) (-2 + 4) := by
    intro i hi
    obtain ⟨hqZ, hq2⟩ := hqq i hi
    have hmem : twist f (qq i) ∈ PS f (⋃ i, Y i) zs :=
      ⟨qq i, mem_iUnion.mpr ⟨i, hZY i hqZ⟩, by simp [twist, hq2]⟩
    refine ⟨hmem, ?_⟩
    have := ps_subset_interval hEb (hfb zs hzs1) hmem
    norm_num
    exact this
  have hj : ∀ i ∈ G2, ∃ j, twist f (qq i) ∈ closedBall (c j) (L / θ) :=
    fun i hi => mem_iUnion.mp (hcov (hPS i hi))
  have hG2pos : 0 < G2.card := by
    have h1 : (0 : ℝ) < mu * n * θ := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have h2 : (0 : ℝ) < G1.card := by linarith
    have h3 : (0 : ℝ) < G1.card * mu * θ ^ 2 := by positivity
    have h4 : (0 : ℝ) < G2.card := by linarith
    exact_mod_cast h4
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hG2pos
  obtain ⟨j0', -⟩ := hj i0 hi0
  have hm0 : 0 < m := Fin.pos j0'
  have hj' : ∀ i, ∃ j : Fin m, i ∈ G2 → twist f (qq i) ∈ closedBall (c j) (L / θ) := by
    intro i
    by_cases hi : i ∈ G2
    · obtain ⟨j, hj⟩ := hj i hi
      exact ⟨j, fun _ => hj⟩
    · exact ⟨j0', fun h => absurd h hi⟩
  choose jj hjj using hj'
  -- Pigeonhole over the covering intervals.
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨j0, -, hj0⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := G2) (t := Finset.univ) (f := jj) (b := (G2.card : ℝ) / m)
    (fun i _ => Finset.mem_univ _) ⟨j0', Finset.mem_univ _⟩ (by
      rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hm0'.ne'])
  set G := G2.filter (fun i => jj i = j0) with hG_def
  refine ⟨c j0, G, ?_, ?_, ?_⟩
  · intro i hi q hq
    have hiG2 : i ∈ G2 := (Finset.mem_filter.mp hi).1
    have hji : jj i = j0 := (Finset.mem_filter.mp hi).2
    obtain ⟨hqZ, hq2⟩ := hqq i hiG2
    have hball := hjj i hiG2
    rw [hji, mem_closedBall, Real.dist_eq] at hball
    have hiG1 : i ∈ G1 := (Finset.mem_filter.mp hiG2).1
    have hq1 : |q 1| ≤ 1 :=
      (ndc_coord_le q 1).trans (mem_ball_zero_iff.mp (hEb (mem_iUnion.mpr ⟨i, hZY i hq⟩))).le
    have hdrift := ndc_drift (z1 := z1) (f := f) hδ hθ hθ1 hδL hLθ (hFam.unit i)
      (hG1θ i hiG1) (hZT i hq) (hZT i hqZ) (hZJ i hq) (hZJ i hqZ) hq1 (hZf i _ hqZ)
      (hflip _ (hZJ i hq) _ (hZJ i hqZ))
    simp only [mem_ofPred_eq]
    calc |twist f q - c j0| ≤ |twist f q - twist f (qq i)| + |twist f (qq i) - c j0| :=
          abs_sub_le _ _ _
      _ ≤ 3 * L / θ + L / θ := add_le_add hdrift hball
      _ = 4 * L / θ := by ring
  · intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1).2
  · have hGcard : (G2.card : ℝ) ≤ m * G.card := by
      rw [div_le_iff₀ hm0'] at hj0
      linarith
    have hmP : (m : ℝ) * (L ^ (1 - σ) * δ ^ η) ≤ 4 := by
      have hm' : (m : ℝ) ≤ δ ^ (-η) * (4 / (L / θ)) ^ (1 - σ) := hm
      have e1 : (4 / (L / θ)) ^ (1 - σ) * L ^ (1 - σ) = (4 * θ) ^ (1 - σ) := by
        rw [← Real.mul_rpow (by positivity) hL.le]
        congr 1
        field_simp
      have e2 : δ ^ (-η) * δ ^ η = 1 := by
        rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
      have h4 : (4 * θ) ^ (1 - σ) ≤ 4 := by
        calc (4 * θ) ^ (1 - σ) ≤ (4 : ℝ) ^ (1 - σ) :=
              Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
          _ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := Real.rpow_one 4
      calc (m : ℝ) * (L ^ (1 - σ) * δ ^ η)
          ≤ δ ^ (-η) * (4 / (L / θ)) ^ (1 - σ) * (L ^ (1 - σ) * δ ^ η) :=
            mul_le_mul_of_nonneg_right hm' (by positivity)
        _ = (δ ^ (-η) * δ ^ η) * ((4 / (L / θ)) ^ (1 - σ) * L ^ (1 - σ)) := by ring
        _ = (4 * θ) ^ (1 - σ) := by rw [e1, e2, one_mul]
        _ ≤ 4 := h4
    have hP : 0 < L ^ (1 - σ) * δ ^ η := by positivity
    have hchain : mu ^ 2 * θ ^ 3 * n ≤ 73728 * (m * G.card) := by
      calc mu ^ 2 * θ ^ 3 * n = (mu * θ ^ 2) * (mu * n * θ) := by ring
        _ ≤ (mu * θ ^ 2) * (1152 * G1.card) :=
            mul_le_mul_of_nonneg_left hG1card (by positivity)
        _ = 1152 * (G1.card * mu * θ ^ 2) := by ring
        _ ≤ 1152 * (64 * G2.card) := mul_le_mul_of_nonneg_left hG2card (by norm_num)
        _ ≤ 1152 * (64 * (m * G.card)) := by gcongr
        _ = 73728 * (m * G.card) := by ring
    have hG0 : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
    calc mu ^ 2 * θ ^ 3 * n * L ^ (1 - σ) * δ ^ η
        = (mu ^ 2 * θ ^ 3 * n) * (L ^ (1 - σ) * δ ^ η) := by ring
      _ ≤ (73728 * (m * G.card)) * (L ^ (1 - σ) * δ ^ η) :=
          mul_le_mul_of_nonneg_right hchain hP.le
      _ = 73728 * G.card * (m * (L ^ (1 - σ) * δ ^ η)) := by ring
      _ ≤ 73728 * G.card * 4 := mul_le_mul_of_nonneg_left hmP (by positivity)
      _ ≤ 10 ^ 6 * G.card := by linarith

end WangZahlLot.Obl.wz_grains_nonsingular_slices
