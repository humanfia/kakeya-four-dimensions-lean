import Mathlib

/-!
# Pruning a finite tower of labels at all levels at once

A restriction `G` of a parent law is covered, at each of finitely many levels,
by the boxes `X x` of the labels `x` of that level; labels of different levels
meeting at a generic point are in ancestor relation, and the reference weights
of the descendants of a label at any deeper level sum to at most its own.

Delete every label that is light at its level, with thresholds `θ / 4^level`,
and remove its whole box. Then

* `tower_removed_le`: the removed mass is at most `2 θ W`;
* `tower_retained_floor`: every retained label (not light, no light ancestor)
  keeps at least half of its threshold `θ / 4^level · w`, since deeper deletions
  inside it cost at most a third of it and shallower ones do not meet it;
* `tower_retained_cover`: the remaining set is still covered at every level, by
  retained labels.

A sequential deletion would invalidate earlier floors; the geometric
thresholds make one simultaneous deletion work.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Threshold at a level. -/
def towerThreshold (θ : ℝ) (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal (θ * (1 / 4 : ℝ) ^ j)

/-- Light labels. -/
def towerLight (μ : Measure Ω) (G : Set Ω) (lv : ι → ℕ) (X : ι → Set Ω) (w : ι → ℝ≥0∞)
    (θ : ℝ) (x : ι) : Prop :=
  μ (G ∩ X x) < towerThreshold θ (lv x) * w x

/-- The removed set: boxes of light labels. -/
def towerRemoved (μ : Measure Ω) (G : Set Ω) (lv : ι → ℕ) (X : ι → Set Ω) (w : ι → ℝ≥0∞)
    (θ : ℝ) : Set Ω :=
  ⋃ x ∈ {x | towerLight μ G lv X w θ x}, X x

/-- The retained restriction. -/
def towerKeep (μ : Measure Ω) (G : Set Ω) (lv : ι → ℕ) (X : ι → Set Ω) (w : ι → ℝ≥0∞)
    (θ : ℝ) : Set Ω :=
  G \ towerRemoved μ G lv X w θ

/-- Retained labels: not light, and no light ancestor. -/
def towerRetained (μ : Measure Ω) (G : Set Ω) (lv : ι → ℕ) (X : ι → Set Ω) (w : ι → ℝ≥0∞)
    (θ : ℝ) (anc : ι → ι → Prop) (x : ι) : Prop :=
  ¬ towerLight μ G lv X w θ x ∧ ∀ y, anc y x → ¬ towerLight μ G lv X w θ y

theorem measurableSet_towerRemoved (μ : Measure Ω) (G : Set Ω) (lv : ι → ℕ) (X : ι → Set Ω)
    (w : ι → ℝ≥0∞) (θ : ℝ) (hX : ∀ x, MeasurableSet (X x)) :
    MeasurableSet (towerRemoved μ G lv X w θ) :=
  MeasurableSet.biUnion (Set.to_countable _) fun x _ => hX x

theorem measurableSet_towerKeep (μ : Measure Ω) {G : Set Ω} (hG : MeasurableSet G)
    (lv : ι → ℕ) (X : ι → Set Ω) (w : ι → ℝ≥0∞) (θ : ℝ) (hX : ∀ x, MeasurableSet (X x)) :
    MeasurableSet (towerKeep μ G lv X w θ) :=
  hG.diff (measurableSet_towerRemoved μ G lv X w θ hX)

/-- Geometric tail of the thresholds. -/
theorem sum_towerThreshold_tail_le {θ : ℝ} (hθ : 0 ≤ θ) (j M : ℕ) :
    ∑ i ∈ Finset.Ioo j M, towerThreshold θ i ≤ ENNReal.ofReal (θ * (1 / 4 : ℝ) ^ j / 3) := by
  unfold towerThreshold
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hθ
  have hI : Finset.Ioo j M = Finset.Ico (j + 1) M := by
    ext i; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
  rw [hI]
  calc ∑ i ∈ Finset.Ico (j + 1) M, (1 / 4 : ℝ) ^ i
      ≤ (1 / 4 : ℝ) ^ (j + 1) / (1 - 1 / 4) :=
        geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = (1 / 4 : ℝ) ^ j / 3 := by rw [pow_succ]; ring

theorem sum_towerThreshold_le {θ : ℝ} (hθ : 0 ≤ θ) (M : ℕ) :
    ∑ j ∈ Finset.range M, towerThreshold θ j ≤ ENNReal.ofReal (2 * θ) := by
  unfold towerThreshold
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum, mul_comm 2 θ]
  apply mul_le_mul_of_nonneg_left _ hθ
  rw [Finset.range_eq_Ico]
  calc ∑ i ∈ Finset.Ico 0 M, (1 / 4 : ℝ) ^ i
      ≤ (1 / 4 : ℝ) ^ 0 / (1 - 1 / 4) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ ≤ 2 := by norm_num

section Theorems


variable {μ : Measure Ω} {G : Set Ω} {lv : ι → ℕ} {X : ι → Set Ω} {w : ι → ℝ≥0∞} {θ : ℝ}
  {anc : ι → ι → Prop} {M : ℕ}

open Classical in
theorem towerRemoved_eq :
    towerRemoved μ G lv X w θ =
      ⋃ y ∈ (Finset.univ.filter fun y => towerLight μ G lv X w θ y), X y := by
  classical
  ext p
  simp [towerRemoved]

open Classical in
/-- The mass of `G` inside the light boxes is at most the sum of the light masses. -/
theorem measure_inter_removed_le (S : Set Ω) :
    μ (S ∩ towerRemoved μ G lv X w θ) ≤
      ∑ y ∈ (Finset.univ.filter fun y => towerLight μ G lv X w θ y), μ (S ∩ X y) := by
  classical
  rw [towerRemoved_eq, inter_iUnion₂]
  exact measure_biUnion_finset_le _ _

open Classical in
/-- **Removed mass.** -/
theorem tower_removed_le (hθ : 0 ≤ θ) (W : ℝ≥0∞) (hlv : ∀ x, lv x < M)
    (hroot : ∀ j, ∑ y ∈ Finset.univ.filter (fun y => lv y = j), w y ≤ W) :
    μ (G ∩ towerRemoved μ G lv X w θ) ≤ ENNReal.ofReal (2 * θ) * W := by
  classical
  calc μ (G ∩ towerRemoved μ G lv X w θ)
      ≤ ∑ y ∈ (Finset.univ.filter fun y => towerLight μ G lv X w θ y), μ (G ∩ X y) :=
        measure_inter_removed_le G
    _ ≤ ∑ y ∈ (Finset.univ.filter fun y => towerLight μ G lv X w θ y),
          towerThreshold θ (lv y) * w y := by
        apply Finset.sum_le_sum
        intro y hy
        exact (Finset.mem_filter.mp hy).2.le
    _ ≤ ∑ y : ι, towerThreshold θ (lv y) * w y :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ j ∈ Finset.range M, ∑ y ∈ Finset.univ.filter (fun y => lv y = j),
          towerThreshold θ (lv y) * w y := by
        rw [Finset.sum_fiberwise_of_maps_to]
        intro y _
        exact Finset.mem_range.mpr (hlv y)
    _ = ∑ j ∈ Finset.range M, towerThreshold θ j *
          ∑ y ∈ Finset.univ.filter (fun y => lv y = j), w y := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        rw [(Finset.mem_filter.mp hy).2]
    _ ≤ ∑ j ∈ Finset.range M, towerThreshold θ j * W := by
        gcongr with j _
        exact hroot j
    _ = (∑ j ∈ Finset.range M, towerThreshold θ j) * W := by rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal (2 * θ) * W := by gcongr; exact sum_towerThreshold_le hθ M

/-- A set that is generically empty is null. -/
theorem measure_eq_zero_of_ae {S : Set Ω} (h : ∀ᵐ p ∂μ, p ∈ S → False) : μ S = 0 := by
  rw [← compl_compl S, ← mem_ae_iff]
  filter_upwards [h] with p hp
  exact hp

open Classical in
/-- **Floors of retained labels.** -/
theorem tower_retained_floor (hθ : 0 ≤ θ) (hlv : ∀ x, lv x < M)
    (hdesc : ∀ x j, lv x < j →
      ∑ y ∈ Finset.univ.filter (fun y => lv y = j ∧ anc x y), w y ≤ w x)
    (hgen : ∀ᵐ p ∂μ, p ∈ G → ∀ x y, p ∈ X x → p ∈ X y →
      (lv x < lv y → anc x y) ∧ (lv x = lv y → x = y))
    {x : ι} (hx : towerRetained μ G lv X w θ anc x) (hwx : w x ≠ ⊤) :
    ENNReal.ofReal (θ * (1 / 4 : ℝ) ^ lv x / 2) * w x ≤
      μ (towerKeep μ G lv X w θ ∩ X x) := by
  classical
  obtain ⟨hxl, hxa⟩ := hx
  set thr := θ * (1 / 4 : ℝ) ^ lv x with hthr
  have hthr0 : 0 ≤ thr := by positivity
  -- light boxes meeting `X x` generically are deeper descendants of `x`
  have hnull : ∀ y, towerLight μ G lv X w θ y → ¬ (lv x < lv y ∧ anc x y) →
      μ (G ∩ X x ∩ X y) = 0 := by
    intro y hy hy'
    apply measure_eq_zero_of_ae
    filter_upwards [hgen] with p hp hpS
    obtain ⟨⟨hpG, hpx⟩, hpy⟩ := hpS
    obtain ⟨h1, h2⟩ := hp hpG x y hpx hpy
    obtain ⟨h3, h4⟩ := hp hpG y x hpy hpx
    rcases lt_trichotomy (lv x) (lv y) with h | h | h
    · exact hy' ⟨h, h1 h⟩
    · exact hxl (h2 h ▸ hy)
    · exact hxa y (h3 h) hy
  have hrem : μ (G ∩ X x ∩ towerRemoved μ G lv X w θ) ≤ ENNReal.ofReal (thr / 3) * w x := by
    calc μ (G ∩ X x ∩ towerRemoved μ G lv X w θ)
        ≤ ∑ y ∈ (Finset.univ.filter fun y => towerLight μ G lv X w θ y), μ (G ∩ X x ∩ X y) :=
          measure_inter_removed_le _
      _ ≤ ∑ y ∈ Finset.univ.filter (fun y => lv x < lv y ∧ anc x y),
            towerThreshold θ (lv y) * w y := by
          rw [← Finset.sum_filter_add_sum_filter_not _ (fun y => lv x < lv y ∧ anc x y)]
          have hzero : ∑ y ∈ (Finset.univ.filter fun y => towerLight μ G lv X w θ y).filter
              (fun y => ¬ (lv x < lv y ∧ anc x y)), μ (G ∩ X x ∩ X y) = 0 := by
            apply Finset.sum_eq_zero
            intro y hy
            rw [Finset.mem_filter, Finset.mem_filter] at hy
            exact hnull y hy.1.2 hy.2
          rw [hzero, add_zero]
          calc ∑ y ∈ (Finset.univ.filter fun y => towerLight μ G lv X w θ y).filter
                (fun y => lv x < lv y ∧ anc x y), μ (G ∩ X x ∩ X y)
              ≤ ∑ y ∈ (Finset.univ.filter fun y => towerLight μ G lv X w θ y).filter
                  (fun y => lv x < lv y ∧ anc x y), towerThreshold θ (lv y) * w y := by
                apply Finset.sum_le_sum
                intro y hy
                rw [Finset.mem_filter, Finset.mem_filter] at hy
                exact (measure_mono (by intro p hp; exact ⟨hp.1.1, hp.2⟩)).trans hy.1.2.le
            _ ≤ ∑ y ∈ Finset.univ.filter (fun y => lv x < lv y ∧ anc x y),
                  towerThreshold θ (lv y) * w y := by
                apply Finset.sum_le_sum_of_subset
                intro y hy
                rw [Finset.mem_filter] at hy ⊢
                exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy.1).2 |> fun _ => hy.2⟩
      _ = ∑ j ∈ Finset.Ioo (lv x) M, ∑ y ∈ Finset.univ.filter (fun y => lv y = j ∧ anc x y),
            towerThreshold θ (lv y) * w y := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := lv) (t := Finset.Ioo (lv x) M)]
          · apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr
            · ext y
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
              · rintro ⟨h3, h2⟩; exact ⟨⟨h3 ▸ by
                  have : j ∈ Finset.Ioo (lv x) M := by assumption
                  exact (Finset.mem_Ioo.mp this).1, h2⟩, h3⟩
            · intro y _; rfl
          · intro y hy
            rw [Finset.mem_filter] at hy
            exact Finset.mem_Ioo.mpr ⟨hy.2.1, hlv y⟩
      _ = ∑ j ∈ Finset.Ioo (lv x) M, towerThreshold θ j *
            ∑ y ∈ Finset.univ.filter (fun y => lv y = j ∧ anc x y), w y := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          rw [(Finset.mem_filter.mp hy).2.1]
      _ ≤ ∑ j ∈ Finset.Ioo (lv x) M, towerThreshold θ j * w x := by
          gcongr with j hj
          exact hdesc x j (Finset.mem_Ioo.mp hj).1
      _ = (∑ j ∈ Finset.Ioo (lv x) M, towerThreshold θ j) * w x := by rw [Finset.sum_mul]
      _ ≤ ENNReal.ofReal (thr / 3) * w x := by
          gcongr
          exact sum_towerThreshold_tail_le hθ (lv x) M
  -- combine
  have hlow : ENNReal.ofReal thr * w x ≤ μ (G ∩ X x) := not_lt.mp hxl
  have hsplit : μ (G ∩ X x) ≤ μ (towerKeep μ G lv X w θ ∩ X x) +
      μ (G ∩ X x ∩ towerRemoved μ G lv X w θ) := by
    calc μ (G ∩ X x) ≤ μ ((towerKeep μ G lv X w θ ∩ X x) ∪
          (G ∩ X x ∩ towerRemoved μ G lv X w θ)) := by
          apply measure_mono
          intro p ⟨hpG, hpx⟩
          by_cases hr : p ∈ towerRemoved μ G lv X w θ
          · exact Or.inr ⟨⟨hpG, hpx⟩, hr⟩
          · exact Or.inl ⟨⟨hpG, hr⟩, hpx⟩
      _ ≤ _ := measure_union_le _ _
  have key : ENNReal.ofReal thr * w x ≤ μ (towerKeep μ G lv X w θ ∩ X x) +
      ENNReal.ofReal (thr / 3) * w x := (hlow.trans hsplit).trans (by gcongr)
  -- `thr/2 + thr/3 ≤ thr`
  have hsum : ENNReal.ofReal (thr / 2) * w x + ENNReal.ofReal (thr / 3) * w x ≤
      ENNReal.ofReal thr * w x := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
    linarith
  have hfin : ENNReal.ofReal (thr / 3) * w x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwx
  calc ENNReal.ofReal (thr / 2) * w x
      = ENNReal.ofReal (thr / 2) * w x + ENNReal.ofReal (thr / 3) * w x -
          ENNReal.ofReal (thr / 3) * w x := (ENNReal.add_sub_cancel_right hfin).symm
    _ ≤ ENNReal.ofReal thr * w x - ENNReal.ofReal (thr / 3) * w x := tsub_le_tsub_right hsum _
    _ ≤ μ (towerKeep μ G lv X w θ ∩ X x) := by
        rw [tsub_le_iff_right]; exact key

/-- **Coverage by retained labels.** -/
theorem tower_retained_cover
    (hgen : ∀ᵐ p ∂μ, p ∈ G → ∀ x y, p ∈ X x → p ∈ X y →
      (lv x < lv y → anc x y) ∧ (lv x = lv y → x = y))
    (hcover : ∀ᵐ p ∂μ, p ∈ G → ∀ j < M, ∃ x, lv x = j ∧ p ∈ X x)
    (hanc : ∀ x y, anc y x → lv y < lv x)
    (huniq : ∀ x y y', anc y x → anc y' x → lv y = lv y' → (X x).Nonempty → y = y') :
    ∀ᵐ p ∂μ, p ∈ towerKeep μ G lv X w θ → ∀ j < M, ∃ x, lv x = j ∧
      towerRetained μ G lv X w θ anc x ∧ p ∈ X x := by
  classical
  filter_upwards [hgen, hcover] with p hp hc hpk j hj
  obtain ⟨hpG, hpr⟩ := hpk
  obtain ⟨x, hxj, hpx⟩ := hc hpG j hj
  have hnotlight : ∀ z, p ∈ X z → ¬ towerLight μ G lv X w θ z := by
    intro z hz hzl
    apply hpr
    rw [towerRemoved_eq]
    simp only [mem_iUnion]
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzl⟩, hz⟩
  refine ⟨x, hxj, ⟨hnotlight x hpx, ?_⟩, hpx⟩
  intro y hy
  -- the label of `p` at the level of `y` is an ancestor of `x`, hence equals `y`
  have hyM : lv y < M := (hanc x y hy).trans (hxj ▸ hj)
  obtain ⟨y', hy'j, hpy'⟩ := hc hpG (lv y) hyM
  have hy'x : anc y' x := (hp hpG y' x hpy' hpx).1 (hy'j ▸ hanc x y hy)
  have : y = y' := huniq x y y' hy hy'x hy'j.symm ⟨p, hpx⟩
  rw [this]
  exact hnotlight y' hpy'

end Theorems

end

end Submission.Lib.K4ContactTransfer
