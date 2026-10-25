import Mathlib
import Submission.WZ.Seed.Kakeya

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace Submission.Lib.KakeyaCovering

/-- A null set has countable open ball covers of any mesh and arbitrarily small
sum of powers of the radii. Compactness and measurability of the set are unnecessary. -/
theorem exists_countable_ball_cover_of_hausdorffMeasure_eq_zero
    {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} (hs : 0 < s) {E : Set X} (hE : μH[s] E = 0)
    {r η : ℝ} (hr : 0 < r) (hη : 0 < η) :
    ∃ (c : ℕ → X) (ρ : ℕ → ℝ),
      (∀ i, 0 < ρ i ∧ ρ i ≤ r) ∧ E ⊆ ⋃ i, ball (c i) (ρ i) ∧
      ∑' i, ENNReal.ofReal (ρ i ^ s) ≤ ENNReal.ofReal η := by
  classical
  let q : ℝ := η / (4 * (2 : ℝ) ^ s)
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨U, hEU, hdiam, hsum⟩ :=
    WangZahlLot.Seed.Kakeya.exists_cover_of_hausdorffMeasure_eq_zero' hs hE
      (r := ENNReal.ofReal (r / 2)) (η := ENNReal.ofReal q)
      (ENNReal.ofReal_pos.mpr (by positivity)) (ENNReal.ofReal_pos.mpr hq)
  let d : ℕ → ℝ := fun i => (ediam (U i)).toReal
  have hd0 (i : ℕ) : 0 ≤ d i := ENNReal.toReal_nonneg
  have hd (i : ℕ) : d i ≤ r / 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hdiam i)
  have hediam (i : ℕ) : ediam (U i) = ENNReal.ofReal (d i) :=
    (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam i))).symm
  let b : ℕ → ℝ := fun i => η / 4 * (1 / 2 : ℝ) ^ (i + 1)
  have hb (i : ℕ) : 0 < b i := by dsimp [b]; positivity
  let ε : ℕ → ℝ := fun i => min r ((b i) ^ s⁻¹)
  have hε (i : ℕ) : 0 < ε i := lt_min hr (Real.rpow_pos_of_pos (hb i) _)
  have hεs (i : ℕ) : ε i ^ s ≤ b i := by
    calc
      ε i ^ s ≤ ((b i) ^ s⁻¹) ^ s :=
        Real.rpow_le_rpow (hε i).le (min_le_right _ _) hs.le
      _ = b i := Real.rpow_inv_rpow (hb i).le hs.ne'
  let c : ℕ → X := fun i => if h : (U i).Nonempty then h.some else Classical.arbitrary X
  let ρ : ℕ → ℝ := fun i => max (2 * d i) (ε i)
  have hρ (i : ℕ) : 0 < ρ i ∧ ρ i ≤ r := by
    constructor
    · exact (hε i).trans_le (le_max_right _ _)
    · exact max_le (by linarith [hd i]) (min_le_left _ _)
  refine ⟨c, ρ, hρ, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hEU hx)
    have hUi : (U i).Nonempty := ⟨x, hxi⟩
    have hci : c i ∈ U i := by simp only [c, dite_eq_left hUi]; exact hUi.some_mem
    have hdist : dist x (c i) ≤ d i := by
      have h := edist_le_ediam_of_mem hxi hci
      rw [hediam, edist_dist] at h
      exact (ENNReal.ofReal_le_ofReal_iff (hd0 i)).mp h
    have hlt : d i < ρ i := by
      by_cases hdi : d i = 0
      · simpa only [hdi] using (hρ i).1
      · exact (by linarith [lt_of_le_of_ne (hd0 i) (Ne.symm hdi)] : d i < 2 * d i).trans_le
          (le_max_left _ _)
    exact mem_iUnion.mpr ⟨i, hdist.trans_lt hlt⟩
  · apply ENNReal.tsum_le_of_sum_range_le
    intro n
    have hsumd : ∑ i ∈ Finset.range n, d i ^ s < q := by
      have hbound := (ENNReal.sum_le_tsum (Finset.range n) (f := fun i => ediam (U i) ^ s)).trans_lt hsum
      have heq : (∑ i ∈ Finset.range n, ediam (U i) ^ s) =
          ENNReal.ofReal (∑ i ∈ Finset.range n, d i ^ s) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (hd0 i) s)]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hediam, ENNReal.ofReal_rpow_of_nonneg (hd0 i) hs.le]
      rw [heq] at hbound
      exact (ENNReal.ofReal_lt_ofReal_iff hq).mp hbound
    have hsumb : ∑ i ∈ Finset.range n, b i ≤ η / 4 := by
      have hgeo : ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1) ≤ 1 := by
        calc
          ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1) =
              (1 / 2 : ℝ) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
          _ ≤ (1 / 2 : ℝ) * ∑' i : ℕ, (1 / 2 : ℝ) ^ i := by
            gcongr
            exact summable_geometric_two.sum_le_tsum _ (fun _ _ => by positivity)
          _ = 1 := by rw [tsum_geometric_two]; norm_num
      dsimp [b]
      rw [← Finset.mul_sum]
      nlinarith
    have hsumρ : ∑ i ∈ Finset.range n, ρ i ^ s ≤ η := by
      calc
        ∑ i ∈ Finset.range n, ρ i ^ s ≤
            ∑ i ∈ Finset.range n, ((2 : ℝ) ^ s * d i ^ s + b i) := by
          apply Finset.sum_le_sum
          intro i hi
          dsimp [ρ]
          rw [Real.rpow_max (by positivity) (hε i).le hs.le, Real.mul_rpow (by norm_num) (hd0 i)]
          exact max_le (le_add_of_nonneg_right (hb i).le)
            ((hεs i).trans (le_add_of_nonneg_left (by positivity)))
        _ = (2 : ℝ) ^ s * (∑ i ∈ Finset.range n, d i ^ s) + ∑ i ∈ Finset.range n, b i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ (2 : ℝ) ^ s * q + η / 4 := by gcongr
        _ ≤ η := by
          dsimp [q]
          have hpow : (2 : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) s).ne'
          field_simp
          nlinarith
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (hρ i).1.le s)]
    exact ENNReal.ofReal_le_ofReal hsumρ

end Submission.Lib.KakeyaCovering
