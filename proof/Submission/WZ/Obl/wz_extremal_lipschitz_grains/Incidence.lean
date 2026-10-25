-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.Incidence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic
import Submission.WZ.Obl.wz_transverse_brush_selection.Energy
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable abbrev incidence {n : ℕ} (Y : Fin n → Set Space) (p : Space) : ℝ :=
  WangZahlLot.Obl.wz_transverse_brush_selection.multiplicity Y Finset.univ p

noncomputable def shadingMass {n : ℕ} (Y : Fin n → Set Space) : ℝ :=
  ∑ i, (volume (Y i)).toReal

theorem incidence_nonneg {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    0 ≤ incidence Y p :=
  WangZahlLot.Obl.wz_transverse_brush_selection.multiplicity_nonneg Y _ p

theorem incidence_eq_ncard {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    incidence Y p = ({i | p ∈ Y i}.ncard : ℝ) := by
  classical
  rw [incidence, WangZahlLot.Obl.wz_transverse_brush_selection.multiplicity_eq_card]
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

theorem measurable_incidence {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) : Measurable (incidence Y) := by
  classical
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hY i)

theorem integrable_incidence {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, volume (Y i) ≠ ∞) :
    Integrable (incidence Y) :=
  WangZahlLot.Obl.wz_transverse_brush_selection.integrable_multiplicity Y _
    (fun i _ => hY i) (fun i _ => hfin i)

theorem integral_incidence {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, volume (Y i) ≠ ∞) :
    (∫ p, incidence Y p) = shadingMass Y :=
  WangZahlLot.Obl.wz_transverse_brush_selection.integral_multiplicity Y _
    (fun i _ => hY i) (fun i _ => hfin i)

theorem incidence_restrict {n : ℕ} (Y : Fin n → Set Space) (A : Set Space)
    (p : Space) : incidence (fun i => Y i ∩ A) p = A.indicator (incidence Y) p := by
  classical
  by_cases hp : p ∈ A
  · simp only [Set.indicator_of_mem hp]
    apply Finset.sum_congr rfl
    intro i _
    simp [WangZahlLot.Obl.wz_transverse_brush_selection.oneOn, Set.indicator_apply, hp]
  · simp [incidence, WangZahlLot.Obl.wz_transverse_brush_selection.multiplicity,
      WangZahlLot.Obl.wz_transverse_brush_selection.oneOn, hp]

theorem incidence_eq_zero_of_notMem {n : ℕ} (Y : Fin n → Set Space)
    {p : Space} (hp : p ∉ ⋃ i, Y i) : incidence Y p = 0 := by
  classical
  have hi : ∀ i, p ∉ Y i := by simpa using hp
  simp [incidence, WangZahlLot.Obl.wz_transverse_brush_selection.multiplicity,
    WangZahlLot.Obl.wz_transverse_brush_selection.oneOn, hi]

theorem shadingMass_mono {n : ℕ} {Y Z : Fin n → Set Space}
    (hfin : ∀ i, volume (Y i) ≠ ∞) (hZY : ∀ i, Z i ⊆ Y i) :
    shadingMass Z ≤ shadingMass Y :=
  Finset.sum_le_sum fun i _ => ENNReal.toReal_mono (hfin i) (measure_mono (hZY i))

theorem shadingMass_restrict_add_compl {n : ℕ} {Y : Fin n → Set Space}
    (hfin : ∀ i, volume (Y i) ≠ ∞) {A : Set Space} (hA : MeasurableSet A) :
    shadingMass (fun i => Y i ∩ A) + shadingMass (fun i => Y i ∩ Aᶜ) =
      shadingMass Y := by
  rw [shadingMass, shadingMass, shadingMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← ENNReal.toReal_add
    (ne_top_of_le_ne_top (hfin i) (measure_mono inter_subset_left))
    (ne_top_of_le_ne_top (hfin i) (measure_mono inter_subset_left)),
    ← sdiff_eq, measure_inter_add_sdiff _ hA]

theorem Family.shading_finite {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hH : Family η δ n x v Y) :
    ∀ i, volume (Y i) ≠ ∞ := fun i =>
  ne_top_of_le_ne_top hH.volume_union_ne_top (measure_mono (subset_iUnion Y i))

theorem Family.mass_lower {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hH : Family η δ n x v Y) (hδ : 0 < δ) :
    δ ^ η * (n : ℝ) * δ ^ 2 ≤ shadingMass Y := by
  have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => hH.shading_finite i)
    hH.2.2.2.2.2.2
  rw [ENNReal.toReal_sum (fun i _ => hH.shading_finite i),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ δ ^ η * (n : ℝ) * δ ^ 2)] at h
  exact h

theorem Family.of_subsets_mass {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space} (hH : Family η δ n x v Y)
    (hZY : ∀ i, Z i ⊆ Y i) (hZ : ∀ i, MeasurableSet (Z i))
    (hmass : δ ^ ε * (n : ℝ) * δ ^ 2 ≤ shadingMass Z) : Family ε δ n x v Z := by
  refine ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1, hZ,
    fun i => (hZY i).trans (hH.2.2.2.2.2.1 i), ?_⟩
  apply (ENNReal.ofReal_le_ofReal hmass).trans_eq
  rw [shadingMass, ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  exact Finset.sum_congr rfl fun i _ =>
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top (hH.shading_finite i) (measure_mono (hZY i)))

theorem Family.mass_upper {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hH : Family η δ n x v Y)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : shadingMass Y ≤ 384 * (n : ℝ) * δ ^ 2 := by
  calc
    shadingMass Y ≤ ∑ _ : Fin n, (384 * δ ^ 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := (measure_mono (hH.2.2.2.2.2.1 i)).trans
        (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ hδ1 (x i) (v i) (hH.2.1 i))
      have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rwa [ENNReal.toReal_ofReal (by positivity : 0 ≤ 384 * δ ^ 2)] at hr
    _ = 384 * (n : ℝ) * δ ^ 2 := by simp; ring

theorem high_incidence_volume {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, volume (Y i) ≠ ∞) (M : ℝ) :
    M * (volume {p | M ≤ incidence Y p}).toReal ≤ shadingMass Y := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (incidence_nonneg Y)) (integrable_incidence hY hfin) M
  rwa [integral_incidence hY hfin] at h

theorem low_incidence_mass {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hUfin : volume (⋃ i, Y i) ≠ ∞)
    {M : ℝ} (hM : 0 ≤ M) :
    shadingMass (fun i => Y i ∩ {p | incidence Y p ≤ M}) ≤
      M * (volume (⋃ i, Y i)).toReal := by
  let A : Set Space := {p | incidence Y p ≤ M}
  have hA : MeasurableSet A := measurableSet_le (measurable_incidence hY) measurable_const
  have hfin : ∀ i, volume (Y i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top hUfin (measure_mono (subset_iUnion Y i))
  have hZ : ∀ i, MeasurableSet (Y i ∩ A) := fun i => (hY i).inter hA
  have hZfin : ∀ i, volume (Y i ∩ A) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top (hfin i) (measure_mono inter_subset_left)
  have hpoint : ∀ p, incidence (fun i => Y i ∩ A) p ≤
      M * WangZahlLot.Obl.wz_transverse_brush_selection.oneOn (⋃ i, Y i) p := by
    intro p
    rw [incidence_restrict]
    by_cases hp : p ∈ ⋃ i, Y i
    · rw [WangZahlLot.Obl.wz_transverse_brush_selection.oneOn_of_mem hp, mul_one]
      by_cases hpa : p ∈ A
      · exact (Set.indicator_of_mem hpa _).trans_le hpa
      · simpa [hpa] using hM
    · rw [WangZahlLot.Obl.wz_transverse_brush_selection.oneOn_of_notMem hp, mul_zero]
      by_cases hpa : p ∈ A <;> simp [hpa, incidence_eq_zero_of_notMem Y hp]
  have hu := WangZahlLot.Obl.wz_transverse_brush_selection.integrable_oneOn
    (MeasurableSet.iUnion hY) hUfin
  have hi := integral_mono (integrable_incidence hZ hZfin) (hu.const_mul M) hpoint
  rwa [integral_incidence hZ hZfin, integral_const_mul,
    WangZahlLot.Obl.wz_transverse_brush_selection.integral_oneOn (MeasurableSet.iUnion hY)] at hi

/-- Superextremal lower bounds force the high-multiplicity part to carry little mass. -/
theorem Family.trim_high_incidence {η θ δ s M : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hH : Family η δ n x v Y) (hM : 0 < M)
    (hcap : shadingMass Y ≤ M * δ ^ s)
    (hlower : ∀ Z : Fin n → Set Space, Family θ δ n x v Z →
      ENNReal.ofReal (δ ^ s) < volume (⋃ i, Z i)) :
    ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧
      (∀ i, MeasurableSet (Z i)) ∧
      shadingMass Y - δ ^ θ * (n : ℝ) * δ ^ 2 < shadingMass Z ∧
      ∀ p, incidence Z p ≤ M := by
  classical
  let A : Set Space := {p | M ≤ incidence Y p}
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const (measurable_incidence hH.2.2.2.2.1)
  have hAU : A ⊆ ⋃ i, Y i := by
    intro p hp
    by_contra hn
    have hz := incidence_eq_zero_of_notMem Y hn
    exact hM.not_ge (hz ▸ hp)
  have hAfin : volume A ≠ ∞ :=
    ne_top_of_le_ne_top hH.volume_union_ne_top (measure_mono hAU)
  have hVA : volume A ≤ ENNReal.ofReal (δ ^ s) := by
    have hmarkov := high_incidence_volume hH.2.2.2.2.1 hH.shading_finite M
    have hr : (volume A).toReal ≤ δ ^ s :=
      (mul_le_mul_iff_right₀ hM).mp (hmarkov.trans hcap)
    rw [← ENNReal.ofReal_toReal hAfin]
    exact ENNReal.ofReal_le_ofReal hr
  have hsmall : shadingMass (fun i => Y i ∩ A) < δ ^ θ * (n : ℝ) * δ ^ 2 := by
    by_contra hn
    have hZ := hH.of_subsets_mass (fun _ => inter_subset_left)
      (fun i => (hH.2.2.2.2.1 i).inter hA) (le_of_not_gt hn)
    have hV := hlower _ hZ
    exact hV.not_ge ((measure_mono (iUnion_subset fun _ => inter_subset_right)).trans hVA)
  refine ⟨fun i => Y i ∩ Aᶜ, fun _ => inter_subset_left,
    fun i => (hH.2.2.2.2.1 i).inter hA.compl, ?_, ?_⟩
  · have hsum := shadingMass_restrict_add_compl hH.shading_finite hA
    linarith
  · intro p
    rw [incidence_restrict]
    by_cases hp : p ∈ Aᶜ
    · rw [Set.indicator_of_mem hp]
      change ¬ M ≤ incidence Y p at hp
      exact (not_le.mp hp).le
    · simpa [hp] using hM.le

/-- Deleting points of low incidence preserves the incidence of every retained point. -/
theorem trim_low_incidence {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hUfin : volume (⋃ i, Y i) ≠ ∞)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hupper : ∀ p, incidence Y p ≤ M) :
    ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧
      (∀ i, MeasurableSet (Z i)) ∧
      shadingMass Y - L * (volume (⋃ i, Y i)).toReal ≤ shadingMass Z ∧
      (∀ p, incidence Z p ≤ M) ∧ (∀ p ∈ ⋃ i, Z i, L < incidence Z p) := by
  classical
  let A : Set Space := {p | incidence Y p ≤ L}
  have hA : MeasurableSet A := measurableSet_le (measurable_incidence hY) measurable_const
  have hfin : ∀ i, volume (Y i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top hUfin (measure_mono (subset_iUnion Y i))
  refine ⟨fun i => Y i ∩ Aᶜ, fun _ => inter_subset_left,
    fun i => (hY i).inter hA.compl, ?_, ?_, ?_⟩
  · have hlow := low_incidence_mass hY hUfin hL
    have heq := shadingMass_restrict_add_compl hfin hA
    linarith
  · intro p
    rw [incidence_restrict]
    by_cases hp : p ∈ Aᶜ
    · simpa only [Set.indicator_of_mem hp] using hupper p
    · simpa [hp] using hM
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    rw [incidence_restrict, Set.indicator_of_mem hi.2]
    exact not_le.mp hi.2

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
