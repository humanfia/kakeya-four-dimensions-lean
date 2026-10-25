import Submission.Obl.k4_plank_projected_multiplicity.TimeCells
import Submission.Obl.k4_plank_projected_multiplicity.PlankTail

namespace Submission.Obl.k4_plank_projected_multiplicity

open Set Finset MeasureTheory Filter
open Submission.Lib.K4PlankGeometry (binTime cellCode)
open Submission.Obl.k4_scalar_coefficient_clustering (timeCell)

noncomputable section

def nearTraces {ι : Type*} [Fintype ι] (D : ℕ) (b u : ι → E2) (i : ι) (t : ℝ) :
    Finset ι := by
  classical
  exact univ.filter (fun l => ‖(b l + t • u l) - (b i + t • u i)‖ ≤ 2 / (D : ℝ))

theorem card_nearTraces_codes {ι : Type*} [Fintype ι] {D : ℕ} (hD : 1 ≤ D)
    (b u : ι → E2) (hu : ∀ i, ‖u i‖ ≤ 1) (i : ι) (j : Fin D) {t : ℝ}
    (ht : t ∈ timeCell D j) :
    (((nearTraces D b u i t).image (fun l => cellCode D (b l) (u l) j)).card : ℝ) ≤ 121 := by
  classical
  have hsub : (nearTraces D b u i t).image (fun l => cellCode D (b l) (u l) j) ⊆
      expandProjectedCells {cellCode D (b i) (u i) j} localCellOffsets := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
    exact cellCode_near_of_timeCell hD j ht (b l) (u l) (b i) (u i) (hu l) (hu i)
      (Finset.mem_filter.mp hl).2
  have hcount := (Finset.card_le_card hsub).trans
    (card_expandProjectedCells {cellCode D (b i) (u i) j} localCellOffsets)
  have hcount' : ((nearTraces D b u i t).image (fun l => cellCode D (b l) (u l) j)).card ≤ 121 := by
    simpa only [Finset.card_singleton, one_mul, card_localCellOffsets] using hcount
  exact_mod_cast hcount'

/-- A large actual-time multiplicity forces a neighboring heavy midpoint cell. -/
theorem crowd_implies_neighboring_heavy_cell {ι : Type*} [Fintype ι]
    {D : ℕ} (hD : 1 ≤ D) (b u : ι → E2) (hu : ∀ i, ‖u i‖ ≤ 1)
    (i : ι) (j : Fin D) {t M : ℝ} (ht : t ∈ timeCell D j) (hM : 0 ≤ M)
    (hcrowd : 121 * M < ((nearTraces D b u i t).card : ℝ)) :
    cellCode D (b i) (u i) j ∈ expandProjectedCells
      (heavyLabels ((univ : Finset ι).sigma (fun _ => (univ : Finset (Fin D))))
        (fun p : (Σ _ : ι, Fin D) => cellCode D (b p.1) (u p.1) p.2) M) localCellOffsets := by
  classical
  let S := nearTraces D b u i t
  let f : ι → ℕ × (Fin 2 → ℤ) := fun l => cellCode D (b l) (u l) j
  let T : Finset (Σ _ : ι, Fin D) := univ.sigma (fun _ => univ)
  let g : (Σ _ : ι, Fin D) → ℕ × (Fin 2 → ℤ) :=
    fun p => cellCode D (b p.1) (u p.1) p.2
  have hcard : ((S.image f).card : ℝ) ≤ 121 := card_nearTraces_codes hD b u hu i j ht
  have hsum : (S.image f).card • M < ∑ _l ∈ S, (1 : ℝ) := by
    simp only [nsmul_eq_mul, Finset.sum_const, mul_one]
    exact (mul_le_mul_of_nonneg_right hcard hM).trans_lt hcrowd
  obtain ⟨q, hq, hqM⟩ := Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum
    (fun l hl => Finset.mem_image.mpr ⟨l, hl, rfl⟩) hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hqM
  have hfiber : (((S.filter (fun l => f l = q)).card : ℝ)) ≤
      ((T.filter (fun p => g p = q)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun l : ι => (⟨l, j⟩ : Σ _ : ι, Fin D))
      (by intro l hl; exact Finset.mem_filter.mpr ⟨by simp [T], (Finset.mem_filter.mp hl).2⟩)
      (by intro l hl l' hl' heq; exact congrArg Sigma.fst heq)
  obtain ⟨l, hl, hfl⟩ := Finset.mem_image.mp hq
  have hheavy : q ∈ heavyLabels T g M := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨⟨l, j⟩, by simp [T], hfl⟩,
      hqM.le.trans hfiber⟩
  have hnear : ‖(b i + t • u i) - (b l + t • u l)‖ ≤ 2 / (D : ℝ) := by
    simpa only [norm_sub_rev] using (Finset.mem_filter.mp hl).2
  have hcode := cellCode_near_of_timeCell hD j ht (b i) (u i) (b l) (u l) (hu i) (hu l) hnear
  change cellCode D (b i) (u i) j ∈ expandProjectedCells {f l} localCellOffsets at hcode
  rw [hfl] at hcode
  obtain ⟨⟨q', r⟩, hqr, heq⟩ := Finset.mem_image.mp hcode
  obtain ⟨hq', hr⟩ := Finset.mem_product.mp hqr
  have hq'eq : q' = q := Finset.mem_singleton.mp hq'
  subst q'
  exact Finset.mem_image.mpr ⟨(q, r), Finset.mem_product.mpr ⟨hheavy, hr⟩, heq⟩

def expandedHeavyMarks {ι : Type*} [Fintype ι] (D : ℕ) (b u : ι → E2) (M : ℝ)
    (i : ι) : Finset (Fin D) := by
  classical
  exact univ.filter (fun j => cellCode D (b i) (u i) j ∈ expandProjectedCells
    (heavyLabels ((univ : Finset ι).sigma (fun _ => (univ : Finset (Fin D))))
      (fun p : (Σ _ : ι, Fin D) => cellCode D (b p.1) (u p.1) p.2) M) localCellOffsets)

theorem volume_crowded_times_le_marks {ι : Type*} [Fintype ι] {D : ℕ} (hD : 1 ≤ D)
    (b u : ι → E2) (hu : ∀ i, ‖u i‖ ≤ 1) (i : ι) {M : ℝ} (hM : 0 ≤ M) :
    volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ 121 * M < ((nearTraces D b u i t).card : ℝ)} ≤
      ENNReal.ofReal (((expandedHeavyMarks D b u M i).card : ℝ) / (D : ℝ)) := by
  apply volume_le_selected_time_cells hD
  intro t ht
  obtain ⟨j, hj⟩ := Submission.Obl.k4_scalar_coefficient_clustering.exists_timeCell hD ht.1
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
  exact crowd_implies_neighboring_heavy_cell hD b u hu i j hj hM ht.2

theorem card_expandedHeavyMarks_le {ι : Type*} [Fintype ι]
    (D : ℕ) (b u : ι → E2) {M : ℝ} (hM : 0 ≤ M) :
    (∑ i : ι, ((expandedHeavyMarks D b u M i).card : ℝ)) ≤
      122 * ∑ i : ι, ((highCellMarks
        (fun p : (Σ _ : ι, Fin D) => cellCode D (b p.1) (u p.1) p.2) M i).card : ℝ) := by
  classical
  have heq : (univ.sigma (expandedHeavyMarks D b u M)) =
      (((univ : Finset ι).sigma (fun _ => (univ : Finset (Fin D)))).filter
        (fun p : (Σ _ : ι, Fin D) => cellCode D (b p.1) (u p.1) p.2 ∈ expandProjectedCells
          (heavyLabels (univ.sigma (fun _ => univ))
            (fun p : (Σ _ : ι, Fin D) => cellCode D (b p.1) (u p.1) p.2) M) localCellOffsets)) := by
    ext p
    constructor
    · intro hp
      exact Finset.mem_filter.mpr ⟨by simp, (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2⟩
    · intro hp
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩⟩
  have hh := card_pairs_in_expanded_heavy_cells
    (fun p : (Σ _ : ι, Fin D) => cellCode D (b p.1) (u p.1) p.2) hM localCellOffsets
  rw [← heq, Finset.card_sigma, Nat.cast_sum, card_localCellOffsets] at hh
  norm_num at hh ⊢
  exact hh

theorem sum_volume_crowded_times_le_marks {ι : Type*} [Fintype ι] {D : ℕ}
    (hD : 1 ≤ D) (b u : ι → E2) (hu : ∀ i, ‖u i‖ ≤ 1) {M : ℝ} (hM : 0 ≤ M) :
    (∑ i : ι, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      121 * M < ((nearTraces D b u i t).card : ℝ)}) ≤
      ENNReal.ofReal (122 * (∑ i : ι, ((highCellMarks
        (fun p : (Σ _ : ι, Fin D) => cellCode D (b p.1) (u p.1) p.2) M i).card : ℝ)) /
          (D : ℝ)) := by
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  calc
    _ ≤ ∑ i : ι, ENNReal.ofReal (((expandedHeavyMarks D b u M i).card : ℝ) / (D : ℝ)) :=
      Finset.sum_le_sum (fun i _ => volume_crowded_times_le_marks hD b u hu i hM)
    _ = ENNReal.ofReal ((∑ i : ι, ((expandedHeavyMarks D b u M i).card : ℝ)) / (D : ℝ)) := by
      rw [Finset.sum_div]
      exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (card_expandedHeavyMarks_le D b u hM) hDp.le)

/-- The continuous-time multiplicity tail for a normalized projected family. -/
theorem continuous_projected_multiplicity_tail (hplank : PlankEstimate) {a R : ℝ}
    (ha : 0 < a) (hR : 1 ≤ R) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      ∀ {ι : Type*} [Fintype ι] (b : ι → E2) (s : ι → E3),
      (∀ i, ‖b i‖ ≤ 1 ∧ ‖planarPart (s i)‖ ≤ 1) →
      (∀ i, |s i 2| ≤ R) →
      (∀ i j, i ≠ j → (D : ℝ)⁻¹ ≤ ‖s i - s j‖) →
      (∑ i : ι, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        (D : ℝ) ^ (1 + a) ≤ ((nearTraces D b (fun l => planarPart (s l)) i t).card : ℝ)}) ≤
          ENNReal.ofReal ((Fintype.card ι : ℝ) * (D : ℝ) ^ (-τ)) := by
  obtain ⟨τ, hτ, D₁, htail⟩ := high_projected_cell_tail hplank (a := a / 2) (by positivity) hR
  have hlarge : ∀ᶠ D : ℕ in atTop, 122 ≤ (D : ℝ) ^ (a / 2) :=
    ((tendsto_rpow_atTop (show 0 < a / 2 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hfactor : ∀ᶠ D : ℕ in atTop, 122 ≤ (D : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (show 0 < τ / 2 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp
    (hlarge.and (hfactor.and ((eventually_ge_atTop D₁).and (eventually_ge_atTop 1))))
  refine ⟨τ / 2, by positivity, D₀, ?_⟩
  intro D hD ι _ b s hbu hs hsep
  obtain ⟨hlargeD, hfactorD, hDD₁, hD₁⟩ := hD₀ D hD
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD₁)
  have hM : 0 < (D : ℝ) ^ (1 + a / 2) := Real.rpow_pos_of_pos hDp _
  have hthreshold : 121 * (D : ℝ) ^ (1 + a / 2) < (D : ℝ) ^ (1 + a) := by
    calc
      121 * (D : ℝ) ^ (1 + a / 2) < 122 * (D : ℝ) ^ (1 + a / 2) := by linarith
      _ ≤ (D : ℝ) ^ (a / 2) * (D : ℝ) ^ (1 + a / 2) :=
        mul_le_mul_of_nonneg_right hlargeD hM.le
      _ = (D : ℝ) ^ (1 + a) := by rw [← Real.rpow_add hDp]; congr 1; ring
  have hcount := htail D hDD₁ b s hbu hs hsep
  have hpower : (D : ℝ) ^ (1 - τ) = (D : ℝ) * (D : ℝ) ^ (-τ) := by
    rw [show 1 - τ = 1 + (-τ) by ring, Real.rpow_add hDp, Real.rpow_one]
  calc
    _ ≤ ∑ i : ι, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        121 * (D : ℝ) ^ (1 + a / 2) <
          ((nearTraces D b (fun l => planarPart (s l)) i t).card : ℝ)} := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_mono (fun t ht => ⟨ht.1, hthreshold.trans_le ht.2⟩)
    _ ≤ ENNReal.ofReal (122 * (∑ i : ι, ((highCellMarks
        (fun p : (Σ _ : ι, Fin D) => cellCode D (b p.1) (planarPart (s p.1)) p.2)
          ((D : ℝ) ^ (1 + a / 2)) i).card : ℝ)) / (D : ℝ)) :=
      sum_volume_crowded_times_le_marks hD₁ b _ (fun i => (hbu i).2) hM.le
    _ ≤ ENNReal.ofReal (122 * ((Fintype.card ι : ℝ) * (D : ℝ) ^ (1 - τ)) / (D : ℝ)) := by
      gcongr
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (122 * (D : ℝ) ^ (-τ))) := by
      rw [hpower]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * ((D : ℝ) ^ (τ / 2) * (D : ℝ) ^ (-τ))) := by
      gcongr
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * (D : ℝ) ^ (-(τ / 2))) := by
      rw [← Real.rpow_add hDp]
      congr 2
      ring

end

end Submission.Obl.k4_plank_projected_multiplicity
