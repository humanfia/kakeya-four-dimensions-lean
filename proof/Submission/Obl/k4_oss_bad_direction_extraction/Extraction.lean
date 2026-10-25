import Submission.Obl.k4_oss_bad_direction_extraction.Grid
import Submission.Obl.k4_oss_bad_direction_extraction.Sampling

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Submission.Obl.k4_oss_bad_direction_extraction

/-- Probability controls the interval bound above radius one. -/
theorem interval_cap_large (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ C b : ℝ} (hδ : 0 < δ) (hC : 1 ≤ C) (hb : 0 ≤ b)
    (hcap : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ b)) :
    ∀ x u : ℝ, δ ≤ u → μ.real (Icc (x - u) (x + u)) ≤ C * u ^ b := by
  intro x u hu
  by_cases hu1 : u ≤ 1
  · have hn : 0 ≤ C * u ^ b := mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap x u hu hu1)).trans_eq
      (ENNReal.toReal_ofReal hn)
  · exact measureReal_le_one.trans
      (one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow (le_of_not_ge hu1) hb))

/-- A positive-mass part of a Frostman probability law contains a finite Frostman set.
The numerical hypotheses record the losses in sampling the occupied cells. -/
theorem finite_frostman_extraction {δ b C D m L : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hC : 1 ≤ C) (hD : 0 ≤ D) (hm : 0 < m) (hL : 0 ≤ L)
    (hsmall : 16 * (C * δ ^ b) ≤ m)
    (habsorb : (32 + 2 * L) * C ≤ D * m)
    (hcount : 16 * (δ⁻¹) ^ 2 ≤ Real.exp (L / 2))
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcap : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ b))
    (E : Set ℝ) (hE : MeasurableSet E) (hsupp : E ⊆ Icc (0 : ℝ) 1)
    (hmass : m ≤ μ.real E) :
    ∃ S : Finset ℝ, S.Nonempty ∧ (∀ t ∈ S, t ∈ E) ∧
      ∀ x u : ℝ, δ ≤ u →
        ((S.filter (fun t => dist t x ≤ u)).card : ℝ) ≤ D * u ^ b * (S.card : ℝ) := by
  classical
  let w : Fin (gridSize δ) → ℝ := fun i => μ.real (E ∩ gridCell δ i)
  let I := {i : Fin (gridSize δ) // 0 < w i}
  let k := C * δ ^ b
  have hk : 0 < k := mul_pos (by linarith) (Real.rpow_pos_of_pos hδ _)
  have hw0 (i : Fin (gridSize δ)) : 0 ≤ w i := measureReal_nonneg
  have hsum : ∑ i : I, w i.val = μ.real E := by
    calc
      ∑ i : I, w i.val = ∑ i ∈ Finset.univ.filter (fun i => 0 < w i), w i :=
        (Finset.sum_subtype _ (by simp) w).symm
      _ = ∑ i : Fin (gridSize δ), w i := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        have : ¬ 0 < w i := by simpa using hi
        exact le_antisymm (le_of_not_gt this) (hw0 i)
      _ = μ.real E := sum_grid_mass μ hδ hE hsupp
  obtain ⟨y, hy⟩ : ∃ y : I → ℝ, ∀ i, y i ∈ E ∩ gridCell δ i.val := by
    choose y hy using (fun i : I => nonempty_of_measureReal_ne_zero (ne_of_gt i.property))
    exact ⟨y, hy⟩
  have hyinj : Function.Injective y := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (gridCell_disjoint δ hne) (hy i).2 (hij.symm ▸ (hy j).2)
  have hcapreal := interval_cap_large μ hδ hC hb hcap
  have hwk (i : I) : w i.val ≤ k := by
    calc
      w i.val ≤ μ.real (Icc (y i - δ) (y i + δ)) := by
        refine measureReal_mono ?_
        intro z hz
        have hd := gridCell_dist_le hδ hz.2 (hy i).2
        rw [Real.dist_eq, abs_le] at hd
        exact ⟨by linarith [hd.1], by linarith [hd.2]⟩
      _ ≤ k := hcapreal _ _ le_rfl
  let p : I → ℝ := fun i => w i.val / k
  have hp0 (i : I) : 0 ≤ p i := div_nonneg (hw0 _) hk.le
  have hp1 (i : I) : p i ≤ 1 := (div_le_one hk).mpr (hwk i)
  have hsumP : ∑ i, p i = μ.real E / k := by
    simp only [p, ← Finset.sum_div, hsum]
  have hP : 16 ≤ ∑ i, p i := by
    rw [hsumP]
    exact (le_div_iff₀ hk).mpr (hsmall.trans hmass)
  have hcard : (Fintype.card I : ℝ) ≤ 2 * δ⁻¹ := by
    have hn : Fintype.card I ≤ gridSize δ := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective (fun i : I => i.val) Subtype.val_injective
    exact (Nat.cast_le.mpr hn).trans (gridSize_le hδ hδ1)
  have htests : 4 * (Fintype.card I : ℝ) ^ 2 ≤ Real.exp (L / 2) := by
    calc
      4 * (Fintype.card I : ℝ) ^ 2 ≤ 4 * (2 * δ⁻¹) ^ 2 := by gcongr
      _ = 16 * (δ⁻¹) ^ 2 := by ring
      _ ≤ Real.exp (L / 2) := hcount
  obtain ⟨T, hT, hinterval⟩ := exists_interval_sample y p hp0 hp1 hP hL htests
  have hTne : T.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (show (0 : ℝ) < T.card by linarith)
  have hM : m ≤ 2 * k * (T.card : ℝ) := by
    rw [hsumP] at hT
    have := (div_le_iff₀ hk).mp hT
    nlinarith [hmass]
  refine ⟨T.image y, hTne.image y, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    exact (hy i).1
  · intro x u hu
    have hu0 : 0 < u := hδ.trans_le hu
    have hq : δ ^ b ≤ u ^ b := Real.rpow_le_rpow hδ.le hu hb
    have hq0 : 0 ≤ u ^ b := Real.rpow_nonneg hu0.le _
    have hab (i : I) : (x - u ≤ y i ∧ y i ≤ x + u) ↔ dist (y i) x ≤ u := by
      rw [Real.dist_eq, abs_le]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    have hsel : ((T.filter (fun i => dist (y i) x ≤ u)).card : ℝ) ≤
        4 * ∑ i ∈ Finset.univ.filter (fun i => dist (y i) x ≤ u), p i + L := by
      simpa only [hab] using hinterval (x - u) (x + u)
    let U : Finset I := Finset.univ.filter (fun i => dist (y i) x ≤ u)
    have hwU : ∑ i ∈ U, w i.val ≤ 2 * C * u ^ b := by
      have hd : PairwiseDisjoint (U : Set I) (fun i => E ∩ gridCell δ i.val) := by
        intro i _ j _ hij
        exact (gridCell_disjoint δ (fun he => hij (Subtype.ext he))).mono
          inter_subset_right inter_subset_right
      calc
        ∑ i ∈ U, w i.val = μ.real (⋃ i ∈ U, E ∩ gridCell δ i.val) :=
          (measureReal_biUnion_finset hd
            (fun i _ => hE.inter (measurableSet_gridCell i.val))).symm
        _ ≤ μ.real (Icc (x - 2 * u) (x + 2 * u)) := by
          refine measureReal_mono ?_
          rintro z hz
          obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp hz
          have hiu : dist (y i) x ≤ u := (Finset.mem_filter.mp hi).2
          have hdz : dist z x ≤ 2 * u :=
            (dist_triangle z (y i) x).trans (by linarith [gridCell_dist_le hδ hz.2 (hy i).2])
          rw [Real.dist_eq, abs_le] at hdz
          exact ⟨by linarith [hdz.1], by linarith [hdz.2]⟩
        _ ≤ C * (2 * u) ^ b := hcapreal _ _ (by linarith)
        _ ≤ 2 * C * u ^ b := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu0.le]
          have h2b : (2 : ℝ) ^ b ≤ 2 := by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1
          nlinarith [mul_le_mul_of_nonneg_right h2b (mul_nonneg (by linarith : 0 ≤ C) hq0)]
    have hsumUk : k * (∑ i ∈ U, p i) = ∑ i ∈ U, w i.val := by
      simp only [p, ← Finset.sum_div]
      field_simp
    have hkc : k * ((T.filter (fun i => dist (y i) x ≤ u)).card : ℝ) ≤
        8 * C * u ^ b + L * k := by
      have hh := mul_le_mul_of_nonneg_left hsel hk.le
      change k * ((T.filter (fun i => dist (y i) x ≤ u)).card : ℝ) ≤
        k * (4 * (∑ i ∈ U, p i) + L) at hh
      nlinarith [hwU, hsumUk]
    have hDM := mul_le_mul_of_nonneg_left hM hD
    have hcoeff : (16 + L) * C ≤ D * k * (T.card : ℝ) := by nlinarith [habsorb]
    have hcoeffq := mul_le_mul_of_nonneg_right hcoeff hq0
    have hLq : L * k ≤ L * C * u ^ b := by
      change L * (C * δ ^ b) ≤ _
      nlinarith [mul_le_mul_of_nonneg_left hq (mul_nonneg hL (by linarith : 0 ≤ C))]
    have hfinal : ((T.filter (fun i => dist (y i) x ≤ u)).card : ℝ) ≤
        D * u ^ b * (T.card : ℝ) := by
      apply (mul_le_mul_iff_left₀ hk).mp
      nlinarith [mul_nonneg (by linarith : 0 ≤ C) hq0]
    simpa only [Finset.filter_image, Finset.card_image_of_injective _ hyinj] using hfinal

end Submission.Obl.k4_oss_bad_direction_extraction
