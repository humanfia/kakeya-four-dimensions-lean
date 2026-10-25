-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_sticky_twisted_extraction.Extremal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_sticky_twisted_extraction.Monotonicity
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Counting

namespace WangZahlLot.Obl.wz_sticky_twisted_extraction

open Set Metric MeasureTheory
open scoped ENNReal

/-- The union of the shadings lies in the fixed bounded ambient ball. -/
theorem DenseFamily.union_subset_ball {η δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : DenseFamily η δ n x v Y) : (⋃ i, Y i) ⊆ ball 0 1 :=
  iUnion_subset (fun i => (h.2.2.2.2.2.1 i).trans (h.2.2.1 i))

/-- Averaging over the finite nonempty tube family. -/
theorem DenseFamily.union_volume_lower {η δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : DenseFamily η δ n x v Y) (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ (2 + η)) ≤ volume (⋃ i, Y i) := by
  have hfin : volume (⋃ i, Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono h.union_subset_ball)
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  have hlower := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.density_union_lower
    h.1 hfin (a := δ ^ η * δ ^ 2)
    (by simpa only [mul_right_comm] using h.2.2.2.2.2.2)
  rwa [Real.rpow_add hδ, Real.rpow_two, mul_comm] 

/-- A persistent volume deficit cannot have exponent larger than two. -/
theorem VolumeExamples.le_two {s : ℝ} (h : VolumeExamples s) : s ≤ 2 := by
  by_contra hs
  have hs' : 2 < s := lt_of_not_ge hs
  obtain ⟨δ, hδ, _, hδ100, n, x, v, Y, hfamily, _, hvol⟩ :=
    h ((s - 2) / 2) 1 (by linarith) zero_lt_one
  have hlower := hfamily.union_volume_lower hδ
  have hpow := (ENNReal.ofReal_le_ofReal_iff
    (Real.rpow_nonneg hδ.le s)).mp (hlower.trans hvol)
  have hexp := (Real.rpow_le_rpow_left_iff_of_base_lt_one hδ
    (show δ < 1 by linarith)).mp hpow
  linarith

/-- Decreasing a deficit exponent preserves the arbitrarily-small examples. -/
theorem VolumeExamples.mono {s t : ℝ} (h : VolumeExamples s) (hts : t ≤ s) :
    VolumeExamples t := by
  intro η d0 hη hd0
  obtain ⟨δ, hδ, hδ0, hδ100, n, x, v, Y, hfamily, hscale, hvol⟩ := h η d0 hη hd0
  refine ⟨δ, hδ, hδ0, hδ100, n, x, v, Y, hfamily, hscale, hvol.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) hts

/-- The exponents of arbitrarily-small all-scales counterexamples. -/
def deficitExponents : Set ℝ := {s | VolumeExamples s}

/-- The extremal deficit is defined from the exact frozen family, including its
weak unique-containment convention. -/
noncomputable def extremalDeficit : ℝ := sSup deficitExponents

theorem deficitExponents_bddAbove : BddAbove deficitExponents :=
  ⟨2, fun _ h => h.le_two⟩

theorem extremalDeficit_pos (h : ∃ s : ℝ, 0 < s ∧ VolumeExamples s) :
    0 < extremalDeficit := by
  obtain ⟨s, hs, h⟩ := h
  exact hs.trans_le (le_csSup deficitExponents_bddAbove h)

theorem extremalDeficit_le_two (h : ∃ s : ℝ, VolumeExamples s) :
    extremalDeficit ≤ 2 :=
  csSup_le h (fun _ hs => hs.le_two)

/-- Every exponent strictly below the extremal one has arbitrarily-small examples.
This avoids asserting attainment of the supremum. -/
theorem volumeExamples_of_lt_extremalDeficit
    (hne : ∃ s : ℝ, VolumeExamples s) {t : ℝ} (ht : t < extremalDeficit) :
    VolumeExamples t := by
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hne ht
  exact VolumeExamples.mono hs hts.le

/-- A uniform positive extremal exponent with all strictly subextremal examples. -/
theorem exists_extremalDeficit (h : ∃ s : ℝ, 0 < s ∧ VolumeExamples s) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 2 ∧
      (∀ t : ℝ, t < σ → VolumeExamples t) ∧
      (∀ t : ℝ, σ < t → ¬ VolumeExamples t) := by
  have hne : ∃ s : ℝ, VolumeExamples s :=
    let ⟨s, _, hs⟩ := h
    ⟨s, hs⟩
  refine ⟨extremalDeficit, extremalDeficit_pos h, extremalDeficit_le_two hne,
    fun _ ht => volumeExamples_of_lt_extremalDeficit hne ht, ?_⟩
  intro t ht htex
  exact (not_le_of_gt ht) (le_csSup deficitExponents_bddAbove htex)

/-- Failure of arbitrarily-small examples gives a uniform lower bound with fixed
positive error and scale cutoff. -/
theorem uniform_lower_of_not_volumeExamples {t : ℝ} (h : ¬ VolumeExamples t) :
    ∃ η d0 : ℝ, 0 < η ∧ 0 < d0 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        DenseFamily η δ n x v Y → AllScales η δ n x v →
          ENNReal.ofReal (δ ^ t) < volume (⋃ i, Y i) := by
  classical
  simp only [VolumeExamples, not_forall, not_exists, not_and, not_le] at h
  obtain ⟨η, d0, hη, hd0, h⟩ := h
  exact ⟨η, d0, hη, hd0, fun δ hδ hδ0 hδ100 n x v Y hfamily hscale =>
    h δ hδ hδ0 hδ100 n x v Y hfamily hscale⟩

/-- The upper extremal bound, with its error and cutoff chosen before the family. -/
theorem uniform_lower_above_extremalDeficit {t : ℝ} (ht : extremalDeficit < t) :
    ∃ η d0 : ℝ, 0 < η ∧ 0 < d0 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        DenseFamily η δ n x v Y → AllScales η δ n x v →
          ENNReal.ofReal (δ ^ t) < volume (⋃ i, Y i) := by
  apply uniform_lower_of_not_volumeExamples
  intro h
  exact (not_le_of_gt ht) (le_csSup deficitExponents_bddAbove h)

/-- Any smaller positive input error still satisfies a previously obtained uniform
bound. This permits choosing a single error for several scales. -/
theorem uniform_lower_with_smaller_error {t : ℝ} (ht : extremalDeficit < t) :
    ∃ η d0 : ℝ, 0 < η ∧ 0 < d0 ∧
      ∀ η' δ : ℝ, 0 < η' → η' ≤ η → 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        DenseFamily η' δ n x v Y → AllScales η' δ n x v →
          ENNReal.ofReal (δ ^ t) < volume (⋃ i, Y i) := by
  obtain ⟨η, d0, hη, hd0, h⟩ := uniform_lower_above_extremalDeficit ht
  refine ⟨η, d0, hη, hd0, ?_⟩
  intro η' δ _ hη' hδ hδ0 hδ100 n x v Y hf hs
  exact h δ hδ hδ0 hδ100 n x v Y
    (hf.mono_error hδ (by linarith) hη')
    (hs.mono_error hδ (by linarith) hη')

end WangZahlLot.Obl.wz_sticky_twisted_extraction
