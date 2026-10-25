-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.Measure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_close_pair_moment

open MeasureTheory

/-- The vertical strip used in the frozen statement. -/
def strip (δ : ℝ) (g : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Set.Icc (-1 : ℝ) 1 ∧ |p.1 - g p.2| ≤ δ}

/-- Multiplicity, retaining the indices even when functions coincide. -/
noncomputable def multiplicity {n : ℕ} (δ : ℝ) (g : Fin n → ℝ → ℝ)
    (p : ℝ × ℝ) : ENNReal :=
  ∑ i, (strip δ (g i)).indicator (fun _ => (1 : ENNReal)) p

theorem measurableSet_strip {δ : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    MeasurableSet (strip δ g) :=
  (measurableSet_Icc.preimage continuous_snd.measurable).inter
    (isClosed_le ((continuous_fst.sub (hg.comp continuous_snd)).abs)
      continuous_const).measurableSet

theorem measurable_multiplicity {n : ℕ} {δ : ℝ} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) : Measurable (multiplicity δ g) := by
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.indicator (measurableSet_strip (hg i))

theorem multiplicity_le_card {n : ℕ} (δ : ℝ) (g : Fin n → ℝ → ℝ)
    (p : ℝ × ℝ) : multiplicity δ g p ≤ n := by
  calc
    multiplicity δ g p ≤ ∑ _i : Fin n, (1 : ENNReal) :=
      Finset.sum_le_sum fun i _ => Set.indicator_le_self _ _ p
    _ = n := by simp

theorem rich_set_eq_empty_of_card_lt {n : ℕ} {δ lam : ℝ}
    {g : Fin n → ℝ → ℝ} (hlam : (n : ℝ) < lam) :
    {p | ENNReal.ofReal lam ≤ multiplicity δ g p} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hlt : (n : ENNReal) < ENNReal.ofReal lam := by
    simpa using (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (Nat.cast_nonneg n) hlam)).mpr hlam
  exact (not_le_of_gt hlt) (hp.trans (multiplicity_le_card δ g p))

theorem strip_fiber {δ : ℝ} {g : ℝ → ℝ} {z : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    (fun x : ℝ => (x, z)) ⁻¹' strip δ g = Set.Icc (g z - δ) (g z + δ) := by
  ext x
  change (z ∈ Set.Icc (-1 : ℝ) 1 ∧ |x - g z| ≤ δ) ↔ _
  rw [and_iff_right hz, abs_le]
  change (-δ ≤ x - g z ∧ x - g z ≤ δ) ↔ (g z - δ ≤ x ∧ x ≤ g z + δ)
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem strip_fiber_of_not_mem {δ : ℝ} {g : ℝ → ℝ} {z : ℝ}
    (hz : z ∉ Set.Icc (-1 : ℝ) 1) :
    (fun x : ℝ => (x, z)) ⁻¹' strip δ g = ∅ := by
  ext x
  change (z ∈ Set.Icc (-1 : ℝ) 1 ∧ |x - g z| ≤ δ) ↔ False
  exact iff_false_intro (fun h => hz h.1)

/-- A strip has area `4 δ`, independently of its height and slope. -/
theorem volume_strip {δ : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    volume (strip δ g) = ENNReal.ofReal (4 * δ) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_strip hg)]
  have hf : (fun z : ℝ => volume ((fun x : ℝ => (x, z)) ⁻¹' strip δ g)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (2 * δ)) := by
    funext z
    by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
    · rw [strip_fiber hz, Real.volume_Icc, Set.indicator_of_mem hz]
      congr 1
      ring
    · rw [strip_fiber_of_not_mem hz, measure_empty, Set.indicator_of_notMem hz]
  rw [hf, lintegral_indicator measurableSet_Icc, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num only [sub_neg_eq_add, one_add_one_eq_two]
  rw [mul_comm, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem lintegral_multiplicity {n : ℕ} {δ : ℝ} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) :
    ∫⁻ p, multiplicity δ g p = ENNReal.ofReal (4 * δ * n) := by
  unfold multiplicity
  rw [lintegral_finsetSum _ (fun i _ =>
    measurable_const.indicator (measurableSet_strip (hg i)))]
  simp_rw [lintegral_indicator (measurableSet_strip (hg _)), lintegral_const,
    Measure.restrict_apply_univ, one_mul, volume_strip (hg _)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul' (Nat.cast_nonneg n)]

/-- The elementary first-moment bound. The endpoint incidence theorem requires
an additional factor of `lam ^ (-1/2)` beyond this estimate. -/
theorem rich_volume_le_first_moment {n : ℕ} {δ lam : ℝ} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) (hlam : 0 < lam) :
    volume {p | ENNReal.ofReal lam ≤ multiplicity δ g p} ≤
      ENNReal.ofReal (4 * δ * n / lam) := by
  have h := meas_ge_le_lintegral_div (μ := volume) (measurable_multiplicity (δ := δ) hg).aemeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hlam) ENNReal.ofReal_ne_top
  rw [lintegral_multiplicity hg, ← ENNReal.ofReal_div_of_pos hlam] at h
  exact h

end WangZahlLot.Obl.wz_jet_close_pair_moment
