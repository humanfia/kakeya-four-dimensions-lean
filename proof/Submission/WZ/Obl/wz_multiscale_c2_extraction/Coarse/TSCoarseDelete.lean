-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSCoarseDelete.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSCubes
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSDelete

/-!
# Coarse multiplicity deletion

Grid cubes reached by the contracted shadings of too many coarse fibres carry little
fine mass: otherwise the coarse family, shaded by those cubes, would be a frozen family
at the coarse scale with too small a union.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate enumerate enumerate_mem
  enumerate_injective enumerate_surjective)

/-- Union of the shadings of one fibre. -/
def fibreUnion {n k : ℕ} (fc : Fin n → Fin k) (Y : Fin n → Set Space) (j : Fin k) :
    Set Space :=
  ⋃ i, fibreShading fc Y j i

theorem mem_fibreUnion {n k : ℕ} {fc : Fin n → Fin k} {Y : Fin n → Set Space} {j : Fin k}
    {p : Space} : p ∈ fibreUnion fc Y j ↔ ∃ i, fc i = j ∧ p ∈ Y i := by
  simp only [fibreUnion, mem_iUnion, fibreShading]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h
    · exact ⟨i, h, hi⟩
    · exact absurd hi (Set.notMem_empty p)
  · rintro ⟨i, h, hi⟩
    exact ⟨i, by simp [h, hi]⟩

/-- Cubes reached by the contracted shading of a fibre. -/
noncomputable def coarseCubes {n k : ℕ} (ρ : ℝ) (K : ℕ) (fc : Fin n → Fin k)
    (Y : Fin n → Set Space) (j : Fin k) : Finset (Fin 3 → ℤ) :=
  reachedF ρ K ((1 - 2 * (16 * ρ)) • fibreUnion fc Y j)

/-- Number of selected coarse tubes reaching a cube. -/
noncomputable def cubeMult {n k : ℕ} (ρ : ℝ) (K : ℕ) (fc : Fin n → Fin k)
    (Y : Fin n → Set Space) (Q : Finset (Fin k)) (m : Fin 3 → ℤ) : ℕ :=
  (Q.filter (fun j => m ∈ coarseCubes ρ K fc Y j)).card

/-- Cubes reached by too many selected coarse tubes. -/
noncomputable def highCubes {n k : ℕ} (ρ : ℝ) (K : ℕ) (fc : Fin n → Fin k)
    (Y : Fin n → Set Space) (Q : Finset (Fin k)) (θc : ℝ) : Finset (Fin 3 → ℤ) :=
  (Q.biUnion (coarseCubes ρ K fc Y)).filter (fun m => θc * Q.card < cubeMult ρ K fc Y Q m)

/-- Double counting of cubes and coarse tubes. -/
theorem sum_card_inter_eq {n k : ℕ} (ρ : ℝ) (K : ℕ) (fc : Fin n → Fin k)
    (Y : Fin n → Set Space) (Q : Finset (Fin k)) (S : Finset (Fin 3 → ℤ)) :
    ∑ j ∈ Q, (S.filter (fun m => m ∈ coarseCubes ρ K fc Y j)).card =
      ∑ m ∈ S, cubeMult ρ K fc Y Q m := by
  simp only [cubeMult, Finset.card_filter]
  exact Finset.sum_comm

/-- Fine mass inside one contracted cube is small for each fine tube. -/
theorem volume_Tube_inter_cube_le {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1 / 100)
    (x v : Space) (hv : ‖v‖ = 1) (m : Fin 3 → ℤ) :
    volume (Tube δ x v ∩ (1 - 2 * (16 * ρ))⁻¹ • gridCube ρ m) ≤
      ENNReal.ofReal (2688 * ρ * δ ^ 2) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hl : 1 / 2 ≤ 1 - 2 * (16 * ρ) := by linarith
  have hl0 : 0 < 1 - 2 * (16 * ρ) := by linarith
  set c : Space := (1 - 2 * (16 * ρ))⁻¹ • (WithLp.toLp 2 (fun j => ρ * (m j : ℝ)) : Space)
  have hcorner : (WithLp.toLp 2 (fun j => ρ * (m j : ℝ)) : Space) ∈ gridCube ρ m := by
    intro j
    simp only [PiLp.toLp_apply]
    constructor
    · exact le_rfl
    · nlinarith
  have hsub : (1 - 2 * (16 * ρ))⁻¹ • gridCube ρ m ⊆ ball c (4 * ρ) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_ball, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hl0)]
    have hd := diam_le_of_mem_gridCube hρ0 hq hcorner
    rw [dist_eq_norm] at hd
    have hinv : (1 - 2 * (16 * ρ))⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hl0 (by norm_num)]; linarith
    calc (1 - 2 * (16 * ρ))⁻¹ * ‖q - _‖ ≤ 2 * ‖q - _‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ < 2 * (2 * ρ) := by linarith
      _ = 4 * ρ := by ring
  refine (measure_mono (inter_subset_inter_right _ hsub)).trans
    ((volume_Tube_inter_ball_le hδ (by positivity) x v c hv).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have : 0 ≤ δ ^ 2 := sq_nonneg δ
  nlinarith

/-- The fine mass in cubes of high coarse multiplicity is small. -/
theorem coarse_high_small {δ ρ ηs t θc Fmax : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρ : ρ ≤ 1 / 1000)
    {n k : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space} (hv : ∀ i, ‖v i‖ = 1)
    (hY : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hYball : ∀ i, Y i ⊆ ball 0 1)
    {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) (fc : Fin n → Fin k)
    (hfc : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (z (fc i)) (w (fc i)))
    (Q : Finset (Fin k)) (hYQ : ∀ i, fc i ∉ Q → Y i = ∅)
    (hFmax : ∀ j, ((Finset.univ.filter (fun i => fc i = j)).card : ℝ) ≤ Fmax)
    (hQball : ∀ j, ntube (8 * ρ) (16 * ρ) (z j) (w j) ⊆ ball 0 1)
    (hQhalf : ∀ j ∈ Q, ∀ j' ∈ Q, j ≠ j' →
      volume (ntube (8 * ρ) (16 * ρ) (z j) (w j) ∩ ntube (8 * ρ) (16 * ρ) (z j') (w j')) ≤
        (1 / 2 : ℝ≥0∞) * volume (ntube (8 * ρ) (16 * ρ) (z j) (w j)))
    (hQsep : Q.Nonempty → Separated ηs (8 * ρ) Q.card
      (fun a => (1 - 2 * (16 * ρ)) • z (enumerate Q a) - (16 * ρ) • w (enumerate Q a))
      (fun a => w (enumerate Q a)))
    (hlowc : ∀ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family ηs (8 * ρ) m x' v' Y' → Separated ηs (8 * ρ) m x' v' →
        ENNReal.ofReal ((8 * ρ) ^ t) < volume (⋃ q, Y' q))
    (hθc : 0 < θc) (hunion : 24576 * ρ ^ 2 / θc ≤ (8 * ρ) ^ t) (hFmax0 : 0 ≤ Fmax)
    (K : ℕ) (hK : 2 / ρ + 1 ≤ K) :
    ∑ i, (volume (Y i ∩ (1 - 2 * (16 * ρ))⁻¹ •
      ⋃ m ∈ highCubes ρ K fc Y Q θc, gridCube ρ m)).toReal ≤
      172032 * (8 * ρ) ^ ηs * Fmax * Q.card * δ ^ 2 := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  set lam : ℝ := 1 - 2 * (16 * ρ) with hlam_def
  have hl0 : 0 < lam := by rw [hlam_def]; linarith
  set H := highCubes ρ K fc Y Q θc with hH_def
  set U := ⋃ m ∈ H, gridCube ρ m with hU_def
  set cubes := coarseCubes ρ K fc Y with hcubes_def
  -- contracted fibre unions lie in the contracted coarse tubes and in the ball of radius 2
  have hfu_tube : ∀ j, fibreUnion fc Y j ⊆ Tube ρ (z j) (w j) := by
    intro j p hp
    obtain ⟨i, hij, hpi⟩ := mem_fibreUnion.mp hp
    rw [← hij]; exact hfc i (hYT i hpi)
  have hfu_ball : ∀ j, lam • fibreUnion fc Y j ⊆ ball 0 2 := by
    rintro j _ ⟨p, hp, rfl⟩
    obtain ⟨i, -, hpi⟩ := mem_fibreUnion.mp hp
    have h1 := hYball i hpi
    rw [mem_ball_zero_iff] at h1 ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
    have : lam ≤ 1 := by rw [hlam_def]; linarith
    nlinarith [norm_nonneg p]
  -- per-tube bound
  have hper : ∀ i, (volume (Y i ∩ lam⁻¹ • U)).toReal ≤
      (H.filter (fun m => m ∈ cubes (fc i))).card * (2688 * ρ * δ ^ 2) := by
    intro i
    have hsub : Y i ∩ lam⁻¹ • U ⊆ ⋃ m ∈ H.filter (fun m => m ∈ cubes (fc i)),
        (Tube δ (x i) (v i) ∩ lam⁻¹ • gridCube ρ m) := by
      rintro p ⟨hpY, hpU⟩
      obtain ⟨q, hqU, hqp⟩ := Set.mem_smul_set.mp hpU
      obtain ⟨m, hmH, hqm⟩ := mem_iUnion₂.mp hqU
      have hq : q = lam • p := by
        rw [← hqp, smul_smul, mul_inv_cancel₀ hl0.ne', one_smul]
      have hm : m ∈ cubes (fc i) := by
        apply mem_reachedF hρ0 hK (hfu_ball (fc i))
        refine ⟨q, hqm, ?_⟩
        rw [hq]
        exact Set.smul_mem_smul_set (mem_fibreUnion.mpr ⟨i, rfl, hpY⟩)
      refine mem_iUnion₂.mpr ⟨m, Finset.mem_filter.mpr ⟨hmH, hm⟩, hYT i hpY, ?_⟩
      rw [← hqp]
      exact Set.smul_mem_smul_set hqm
    have hmeas := measure_mono (μ := volume) hsub
    have hsum := measure_biUnion_finset_le (μ := volume)
      (H.filter (fun m => m ∈ cubes (fc i)))
      (fun m => Tube δ (x i) (v i) ∩ lam⁻¹ • gridCube ρ m)
    have hb : ∀ m ∈ H.filter (fun m => m ∈ cubes (fc i)),
        volume (Tube δ (x i) (v i) ∩ lam⁻¹ • gridCube ρ m) ≤
          ENNReal.ofReal (2688 * ρ * δ ^ 2) :=
      fun m _ => volume_Tube_inter_cube_le hδ hδρ (by linarith) (x i) (v i) (hv i) m
    have htot := hmeas.trans (hsum.trans (Finset.sum_le_sum hb))
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at htot
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) htot
  -- cubes of fibres outside the selection are empty
  have hcubesQ : ∀ j, j ∉ Q → cubes j = ∅ := by
    intro j hj
    apply Finset.eq_empty_of_forall_notMem
    intro m hm
    obtain ⟨-, q, -, hq⟩ := Finset.mem_filter.mp hm
    obtain ⟨p, hp, -⟩ := Set.mem_smul_set.mp hq
    obtain ⟨i, hij, hpi⟩ := mem_fibreUnion.mp hp
    rw [hYQ i (hij ▸ hj)] at hpi
    exact hpi
  -- the sum of per-tube counts is a sum over cubes
  set S : ℝ := ∑ m ∈ H, (cubeMult ρ K fc Y Q m : ℝ) with hS_def
  have hcount : ∑ i, ((H.filter (fun m => m ∈ cubes (fc i))).card : ℝ) ≤ Fmax * S := by
    have h1 : ∑ i, ((H.filter (fun m => m ∈ cubes (fc i))).card : ℝ) =
        ∑ j, ((Finset.univ.filter (fun i => fc i = j)).card : ℝ) *
          (H.filter (fun m => m ∈ cubes j)).card := by
      rw [← Finset.sum_fiberwise Finset.univ fc
        (fun i => ((H.filter (fun m => m ∈ cubes (fc i))).card : ℝ))]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
        Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ j, ((Finset.univ.filter (fun i => fc i = j)).card : ℝ) *
          (H.filter (fun m => m ∈ cubes j)).card ≤
        ∑ j ∈ Q, Fmax * (H.filter (fun m => m ∈ cubes j)).card := by
      rw [← Finset.sum_subset (Finset.subset_univ Q) (fun j _ hj => by
        rw [hcubesQ j hj]; simp)]
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hFmax j) (Nat.cast_nonneg _)
    have h3 : ∑ j ∈ Q, Fmax * ((H.filter (fun m => m ∈ cubes j)).card : ℝ) = Fmax * S := by
      rw [← Finset.mul_sum, hS_def]
      congr 1
      exact_mod_cast sum_card_inter_eq ρ K fc Y Q H
    linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  -- the key bound on the high cubes, by the coarse volume lower bound
  have hkey : S * ρ ^ 3 ≤ (8 * ρ) ^ ηs * Q.card * (8 * ρ) ^ 2 := by
    by_contra hbig
    push Not at hbig
    have h8 : 0 < 8 * ρ := by positivity
    have hQne : Q.Nonempty := by
      rcases Q.eq_empty_or_nonempty with hQ | hQ
      · exfalso
        have hS : S = 0 := by
          rw [hS_def]
          apply Finset.sum_eq_zero
          intro m _
          simp [cubeMult, hQ]
        rw [hS, hQ] at hbig
        simp at hbig
      · exact hQ
    have hQpos : 0 < Q.card := Finset.card_pos.mpr hQne
    -- the coarse family shaded by high cubes
    set Y' : Fin Q.card → Set Space := fun a =>
      ⋃ m ∈ H.filter (fun m => m ∈ cubes (enumerate Q a)), gridCube ρ m with hY'_def
    have hY'sub : ∀ a, Y' a ⊆ ntube (8 * ρ) (16 * ρ) (z (enumerate Q a)) (w (enumerate Q a)) := by
      intro a q hq
      obtain ⟨m, hm, hqm⟩ := mem_iUnion₂.mp hq
      have hm' := (Finset.mem_filter.mp hm).2
      obtain ⟨-, p, hpm, hpA⟩ := Finset.mem_filter.mp hm'
      have hreach : m ∈ reached ρ ((1 - 2 * (16 * ρ)) •
          Tube ρ (z (enumerate Q a)) (w (enumerate Q a))) :=
        ⟨p, hpm, Set.smul_set_mono (hfu_tube _) hpA⟩
      exact gridCube_subset_ntube hρ0 (by linarith) hreach hqm
    have hY'vol : ∀ a, volume (Y' a) =
        ((H.filter (fun m => m ∈ cubes (enumerate Q a))).card : ℝ≥0∞) * ENNReal.ofReal ρ ^ 3 := by
      intro a
      rw [hY'_def]
      simp only
      rw [measure_biUnion_finset (fun m _ m' _ hmm => gridCube_disjoint hρ0 hmm)
        (fun m _ => measurableSet_gridCube ρ m)]
      simp only [volume_gridCube hρ0, Finset.sum_const, nsmul_eq_mul]
    have hsumY' : ∑ a, volume (Y' a) = ENNReal.ofReal (S * ρ ^ 3) := by
      simp only [hY'vol]
      rw [← Finset.sum_mul]
      have h1 : ∑ a : Fin Q.card, ((H.filter (fun m => m ∈ cubes (enumerate Q a))).card : ℝ≥0∞) =
          ENNReal.ofReal S := by
        have hN : ∑ a : Fin Q.card, (H.filter (fun m => m ∈ cubes (enumerate Q a))).card =
            ∑ m ∈ H, cubeMult ρ K fc Y Q m := by
          rw [WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_sum Q
            (fun j => (H.filter (fun m => m ∈ cubes j)).card)]
          exact sum_card_inter_eq ρ K fc Y Q H
        have hSN : S = ((∑ m ∈ H, cubeMult ρ K fc Y Q m : ℕ) : ℝ) := by
          rw [hS_def, Nat.cast_sum]
        rw [← Nat.cast_sum, hN, hSN, ENNReal.ofReal_natCast]
      rw [h1, ← ENNReal.ofReal_pow hρ0.le, ← ENNReal.ofReal_mul hS0]
    have hFam : Family ηs (8 * ρ) Q.card
        (fun a => (1 - 2 * (16 * ρ)) • z (enumerate Q a) - (16 * ρ) • w (enumerate Q a))
        (fun a => w (enumerate Q a)) Y' := by
      refine ⟨hQpos, fun a => hw _, fun a => hQball _, ?_, ?_, hY'sub, ?_⟩
      · intro a b hab
        exact hQhalf _ (enumerate_mem Q a) _ (enumerate_mem Q b) ((enumerate_injective Q).ne hab)
      · intro a
        exact Finset.measurableSet_biUnion _ (fun m _ => measurableSet_gridCube ρ m)
      · rw [hsumY']
        apply ENNReal.ofReal_le_ofReal
        linarith
    have hlt := hlowc _ _ _ Y' hFam (hQsep hQne)
    -- the union is small
    have hUsub : (⋃ a, Y' a) ⊆ U := by
      intro q hq
      obtain ⟨a, ha⟩ := mem_iUnion.mp hq
      obtain ⟨m, hm, hqm⟩ := mem_iUnion₂.mp ha
      exact mem_iUnion₂.mpr ⟨m, (Finset.mem_filter.mp hm).1, hqm⟩
    have hUvol : volume U = (H.card : ℝ≥0∞) * ENNReal.ofReal ρ ^ 3 := by
      rw [hU_def, measure_biUnion_finset (fun m _ m' _ hmm => gridCube_disjoint hρ0 hmm)
        (fun m _ => measurableSet_gridCube ρ m)]
      simp only [volume_gridCube hρ0, Finset.sum_const, nsmul_eq_mul]
    have hHcard : (H.card : ℝ) * (θc * Q.card) ≤ Q.card * (24576 / ρ) := by
      have h1 : (H.card : ℝ) * (θc * Q.card) ≤ S := by
        rw [hS_def, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro m hm
        rw [Nat.cast_one, one_mul]
        exact (Finset.mem_filter.mp hm).2.le
      have h2 : S ≤ ∑ m ∈ Q.biUnion cubes, (cubeMult ρ K fc Y Q m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.cast_nonneg _)
      have h3 : ∑ m ∈ Q.biUnion cubes, (cubeMult ρ K fc Y Q m : ℝ) =
          ∑ j ∈ Q, ((cubes j).card : ℝ) := by
        have hN : ∑ m ∈ Q.biUnion cubes, cubeMult ρ K fc Y Q m = ∑ j ∈ Q, (cubes j).card := by
          rw [← sum_card_inter_eq ρ K fc Y Q (Q.biUnion cubes)]
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          ext m
          simp only [Finset.mem_filter, Finset.mem_biUnion]
          exact ⟨fun h => h.2, fun h => ⟨⟨j, hj, h⟩, h⟩⟩
        exact_mod_cast hN
      have h4 : ∑ j ∈ Q, ((cubes j).card : ℝ) ≤ ∑ j ∈ Q, 24576 / ρ :=
        Finset.sum_le_sum (fun j _ => card_reachedF_le hρ0 (by linarith) (z j) (w j) (hw j)
          (Set.smul_set_mono (hfu_tube j)))
      rw [Finset.sum_const, nsmul_eq_mul] at h4
      linarith
    have hUle : volume U ≤ ENNReal.ofReal ((8 * ρ) ^ t) := by
      rw [hUvol, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hρ0.le,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hQc : (0 : ℝ) < Q.card := by exact_mod_cast hQpos
      have h5 : (H.card : ℝ) ≤ 24576 / (ρ * θc) := by
        rw [le_div_iff₀ (by positivity)]
        have h6 : (Q.card : ℝ) * ((H.card : ℝ) * θc) ≤ (Q.card : ℝ) * (24576 / ρ) := by
          have := hHcard; nlinarith
        have h7 := le_of_mul_le_mul_left h6 hQc
        have h8 : (H.card : ℝ) * θc * ρ ≤ 24576 / ρ * ρ := mul_le_mul_of_nonneg_right h7 hρ0.le
        rw [div_mul_cancel₀ _ hρ0.ne'] at h8
        nlinarith
      calc (H.card : ℝ) * ρ ^ 3 ≤ 24576 / (ρ * θc) * ρ ^ 3 :=
            mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = 24576 * ρ ^ 2 / θc := by field_simp
        _ ≤ (8 * ρ) ^ t := hunion
    exact absurd hlt (not_lt.mpr ((measure_mono hUsub).trans hUle))
  -- conclusion
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)
  rw [← Finset.sum_mul] at hsum
  have hS' : S ≤ 64 * (8 * ρ) ^ ηs * Q.card / ρ := by
    rw [le_div_iff₀ hρ0]
    have hρ2 : 0 < ρ ^ 2 := by positivity
    nlinarith
  calc ∑ i, (volume (Y i ∩ lam⁻¹ • U)).toReal
      ≤ (∑ i, ((H.filter (fun m => m ∈ cubes (fc i))).card : ℝ)) * (2688 * ρ * δ ^ 2) := hsum
    _ ≤ (Fmax * S) * (2688 * ρ * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ (Fmax * (64 * (8 * ρ) ^ ηs * Q.card / ρ)) * (2688 * ρ * δ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hS' hFmax0
    _ = 172032 * (8 * ρ) ^ ηs * Fmax * Q.card * δ ^ 2 := by
        field_simp
        ring

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
