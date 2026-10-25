/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/CrossingLoss.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/CrossingLoss.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.CrossingLists
import Submission.Obl.k4_balanced_native_packet_transport.CPF.CrossingVolume
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SelectedBudget

/-! The quantitative original-law loss for making chart labels known. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set MeasureTheory
open scoped Classical ENNReal

noncomputable section

def crossingFactor (κ : ℝ) : ℝ := 8 * (1 + 4 * κ ^ 2) * Real.pi * κ ^ 2

theorem measurable_obs (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  fun_prop

theorem Atlas.crossingSets_eq_empty {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) {γ : Fin (p.W k)} {b : Fin a.C}
    (hγ : a.γ b ≠ γ) : a.crossingSets r bins m γ b = ∅ := by
  ext o
  simp [crossingSets, hγ]

theorem Atlas.measurableSet_crossingSets {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (γ : Fin (p.W k)) (b : Fin a.C) :
    MeasurableSet (a.crossingSets r bins m γ b) := by
  by_cases hγ : a.γ b = γ
  · have hbin : MeasurableSet {o : Observation | o.2 ∈ bins γ} :=
      (bins γ).finite_toSet.measurableSet.preimage measurable_snd
    simpa only [crossingSets, hγ, true_and, BoundedChartCrosses, ofPred_and] using
      hbin.inter (measurableSet_chartCrosses a.κ a.T (a.j b : ℝ) (δ (p.N k) r)
        (p.B k γ) (a.c b) (a.u b) (a.Q b) (a.R b) m)
  · rw [a.crossingSets_eq_empty r bins m hγ]
    exact MeasurableSet.empty

theorem Atlas.measurableSet_shortCrossingList {p : Data} {k : ℕ} (a : Atlas p k)
    (r : ℝ) (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (H : ℝ)
    (γ : Fin (p.W k)) (b : Fin a.C) :
    MeasurableSet {o | b ∈ a.shortCrossingList r bins m H γ o} := by
  have hcard : Measurable (fun o => ((a.crossingList r bins m γ o).card : ℝ)) := by
    have h := ENNReal.measurable_toReal.comp (measurable_finiteCrossingCount
      (a.crossingSets r bins m γ) (a.measurableSet_crossingSets r bins m γ))
    simpa only [Function.comp_def, finiteCrossingCount, Atlas.crossingList,
      ENNReal.toReal_natCast] using h
  have heq : {o | b ∈ a.shortCrossingList r bins m H γ o} =
      {o | ((a.crossingList r bins m γ o).card : ℝ) ≤ H} ∩
        a.crossingSets r bins m γ b := by
    ext o
    simp only [mem_inter_iff, mem_ofPred_eq]
    by_cases h : ((a.crossingList r bins m γ o).card : ℝ) ≤ H
    · simp only [Atlas.shortCrossingList, if_pos h, h, true_and]
      simp [Atlas.crossingList, finiteCrossingList]
    · simp [Atlas.shortCrossingList, h]
  rw [heq]
  exact (measurableSet_le hcard measurable_const).inter
    (a.measurableSet_crossingSets r bins m γ b)

def Atlas.crossingVolume {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) : ENNReal :=
  ∑ γ, ENNReal.ofReal (p.ω k γ) *
    ∑ b, (volume.prod Measure.count) (a.crossingSets r bins m γ b)

/-- The true floors bound total crossing volume by total selected mass.
No conditioning on successful incidences appears in the weights. -/
theorem Atlas.crossingVolume_le {p : Data} {k M D : ℕ} {r : ℝ} (a : Atlas p k)
    (ha : a.TrueAt M D r) (hN : 0 < p.N k) (hκ : 1 ≤ a.κ)
    (hB : ∀ γ, 0 < p.B k γ) (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) :
    a.crossingVolume r bins m ≤
      ENNReal.ofReal (crossingFactor a.κ * a.κ / (p.N k ^ (-p.f r))) * a.mass := by
  let n := p.N k ^ (-p.f r)
  have hn : 0 < n := Real.rpow_pos_of_pos hN _
  have hκ0 : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  have hfac : 0 ≤ crossingFactor a.κ * a.κ / n := by unfold crossingFactor; positivity
  let obsVolume : Measure Observation := volume.prod Measure.count
  have hsingle (b : Fin a.C) :
      (∑ γ, ENNReal.ofReal (p.ω k γ) * obsVolume (a.crossingSets r bins m γ b)) =
        ENNReal.ofReal (p.ω k (a.γ b)) * obsVolume (a.crossingSets r bins m (a.γ b) b) := by
    apply Finset.sum_eq_single (a.γ b)
    · intro γ _ hγ
      rw [a.crossingSets_eq_empty r bins m (Ne.symm hγ), measure_empty, mul_zero]
    · simp
  have hbound (b : Fin a.C) : obsVolume (a.crossingSets r bins m (a.γ b) b) ≤
      ENNReal.ofReal (crossingFactor a.κ * a.κ / n) *
        ((p.ν k (a.γ b)).prod volume) (a.F b) := by
    obtain ⟨hQ, _, _, _, hR, _, _, _, _, _, _, hfloor⟩ := ha.2.2.1 b
    calc
      _ ≤ obsVolume {o : Observation | ChartCrosses a.κ a.T (a.j b : ℝ) (δ (p.N k) r)
          (p.B k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) m o} :=
        measure_mono (fun _ ho => ho.2.2)
      _ ≤ ENNReal.ofReal (crossingFactor a.κ * |Matrix.det (a.Q b)| / (2 : ℝ) ^ a.T) :=
        volume_chartCrosses hR (by unfold δ; positivity) (hB _) hκ0 hQ
      _ = ENNReal.ofReal (crossingFactor a.κ * a.κ / n) *
          ENNReal.ofReal (n * |Matrix.det (a.Q b)| / ((2 : ℝ) ^ a.T * a.κ)) := by
        rw [← ENNReal.ofReal_mul hfac]
        congr 1
        field_simp
        <;> ring
      _ ≤ _ := mul_le_mul le_rfl hfloor zero_le zero_le
  calc
    a.crossingVolume r bins m = ∑ b, ∑ γ,
        ENNReal.ofReal (p.ω k γ) * obsVolume (a.crossingSets r bins m γ b) := by
      unfold crossingVolume
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * obsVolume (a.crossingSets r bins m (a.γ b) b) :=
      Finset.sum_congr rfl (fun b _ => hsingle b)
    _ ≤ ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) *
        (ENNReal.ofReal (crossingFactor a.κ * a.κ / n) *
          ((p.ν k (a.γ b)).prod volume) (a.F b)) := Finset.sum_le_sum fun b _ =>
      mul_le_mul le_rfl (hbound b) zero_le zero_le
    _ = _ := by
      unfold Atlas.mass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

def Atlas.crossingLostMass {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (H : ℝ) : ENNReal :=
  ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume)
    (a.F b \ a.crossingKeep r bins m H b)

/-- Only the analytic exceptional mass and a relative Markov cost are lost. -/
theorem Atlas.crossingLostMass_le {p : Data} {k M D : ℕ} {r : ℝ} (a : Atlas p k)
    (ha : a.TrueAt M D r) (hN : 0 < p.N k) (hκ : 1 ≤ a.κ)
    (hB : ∀ γ, 0 < p.B k γ) (bins : Fin (p.W k) → Finset ℤ) (m : ℕ)
    {H : ℝ} (hH : 0 < H) (θ : ENNReal)
    (hg : ∀ γ, Measurable (p.g k γ r))
    (hmap : ∀ γ, Measure.map (obs (p.B k γ) (δ (p.N k) r))
      (((p.ν k γ).prod volume).restrict (p.E k γ)) =
        (volume.prod Measure.count).withDensity (p.g k γ r)) :
    a.crossingLostMass r bins m H ≤
      (∑ γ, ENNReal.ofReal (p.ω k γ) *
        (((p.ν k γ).prod volume).restrict (p.E k γ))
          {q | θ < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}) +
      (θ / ENNReal.ofReal H * ENNReal.ofReal
        (crossingFactor a.κ * a.κ / (p.N k ^ (-p.f r)))) * a.mass := by
  let Z : Fin (p.W k) → Set Incidence := fun γ =>
    {q | ENNReal.ofReal H < finiteCrossingCount (a.crossingSets r bins m γ)
      (obs (p.B k γ) (δ (p.N k) r) q)}
  have hZ (γ : Fin (p.W k)) : MeasurableSet (Z γ) := measurableSet_lt measurable_const
    ((measurable_finiteCrossingCount _ (a.measurableSet_crossingSets r bins m γ)).comp
      (measurable_obs _ _))
  have hsets (b : Fin a.C) : a.F b \ a.crossingKeep r bins m H b = a.F b ∩ Z (a.γ b) := by
    ext q
    simp only [mem_sdiff, mem_inter_iff, Z, mem_ofPred_eq, crossingKeep,
      finiteCrossingCount_gt_iff _ _ hH.le, not_le, crossingList]
  let μ : Fin (p.W k) → Measure Incidence := fun γ =>
    ((p.ν k γ).prod volume).restrict (p.E k γ)
  have hworld (γ : Fin (p.W k)) : μ γ (Z γ) ≤
      μ γ {q | θ < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)} +
        θ * ((∑ b, (volume.prod Measure.count) (a.crossingSets r bins m γ b)) /
          ENNReal.ofReal H) :=
    observed_long_crossing_list_mass (μ γ) (volume.prod Measure.count)
      (obs (p.B k γ) (δ (p.N k) r)) (measurable_obs _ _) (hg γ) (hmap γ)
        (a.crossingSets r bins m γ) (a.measurableSet_crossingSets r bins m γ) θ
        (by positivity) ENNReal.ofReal_ne_top
  calc
    a.crossingLostMass r bins m H ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) * μ γ (Z γ) := by
      unfold crossingLostMass
      simp_rw [hsets]
      exact a.selected_weighted_budget ha.2.1 _ ha.2.2.1 Z hZ
    _ ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) *
        (μ γ {q | θ < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)} +
          θ * ((∑ b, (volume.prod Measure.count) (a.crossingSets r bins m γ b)) /
            ENNReal.ofReal H)) := Finset.sum_le_sum fun γ _ =>
      mul_le_mul le_rfl (hworld γ) zero_le zero_le
    _ = (∑ γ, ENNReal.ofReal (p.ω k γ) *
        μ γ {q | θ < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}) +
        (θ / ENNReal.ofReal H) * a.crossingVolume r bins m := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      unfold crossingVolume
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      rw [mul_assoc]
      exact mul_le_mul le_rfl (a.crossingVolume_le ha hN hκ hB bins m) zero_le zero_le

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
