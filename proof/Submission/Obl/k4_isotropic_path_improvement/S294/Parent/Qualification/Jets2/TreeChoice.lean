-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.TreeChoice, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/TreeChoice.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/TreeChoice.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/TreeChoice.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Tree

set_option autoImplicit false

/-!
# Choosing one good tree of times

Copied from this LOT tree: o229, session x0801, branch `x0801` at `ec0250f0`,
`Jets/TreeChoice.lean` (independent of `j`; only the namespace changed).

The paper samples an independent random time tree and uses Jensen's inequality at every split.
Here a single deterministic tree is chosen.  For a label set `Lab ⊆ Λ × ℝ` and pair levels
`Tl k` (pairs of depth `k` lie in a common dyadic interval of length `2^{-Tl k}`), the success
function `treeP k Y l n j` of the uniform random tree of depth `k` in the dyadic interval
`dI n j` (root restricted to `Y`) satisfies

  `treeP (k+1) Y l = avg over the subintervals I' of (treeP k Y l I') * (treeP k univ l I')`.

`tree_exists`: in the success regime, there is a tree with pairs at distance in
`[H k / Kg, H k]`, all its times in the interval and its root in `Y`, whose labelled prior mass
is at least `∫ treeP k Y · dμ - L_k μ(univ)` with `L_{k+1} = 2 L_k + 2/Kg`: choose the
subinterval of largest average, the right subtree for the measure `treeP k Y · μ`, then the left
subtree for `μ` restricted to the trajectories labelled on the right subtree, with its root
outside a gap of length `2 H/Kg` around the right root.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The success function of the uniform random tree. -/
def treeP (Lab : Set (Λ × ℝ)) (Tl : ℕ → ℕ) : ℕ → Set ℝ → Λ → ℕ → ℤ → ℝ≥0∞
  | 0, Y, l, n, j => volume (dI n j ∩ Y ∩ {t | (l, t) ∈ Lab}) * 2 ^ n
  | k + 1, Y, l, n, j =>
    (∑ i ∈ Finset.range (2 ^ (Tl (k + 1) - n)),
      treeP Lab Tl k Y l (Tl (k + 1)) (subIdx n (Tl (k + 1)) j i) *
        treeP Lab Tl k univ l (Tl (k + 1)) (subIdx n (Tl (k + 1)) j i)) /
      2 ^ (Tl (k + 1) - n)

theorem treeP_le_one (Lab : Set (Λ × ℝ)) (Tl : ℕ → ℕ) :
    ∀ k Y l n j, treeP Lab Tl k Y l n j ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro Y l n j
    simp only [treeP]
    calc volume (dI n j ∩ Y ∩ {t | (l, t) ∈ Lab}) * 2 ^ n ≤ volume (dI n j) * 2 ^ n := by
          gcongr; exact inter_subset_left.trans inter_subset_left
      _ = 1 := by
          rw [volume_dI, ENNReal.ofReal_inv_of_pos (by positivity)]
          rw [show ENNReal.ofReal ((2 : ℝ) ^ n) = (2 : ℝ≥0∞) ^ n by
            rw [ENNReal.ofReal_pow (by norm_num)]; simp]
          exact ENNReal.inv_mul_cancel (by positivity) (by simp)
  | succ k ih =>
    intro Y l n j
    simp only [treeP]
    rw [ENNReal.div_le_iff (by positivity) (by simp), one_mul]
    calc ∑ i ∈ Finset.range (2 ^ (Tl (k + 1) - n)),
          treeP Lab Tl k Y l (Tl (k + 1)) (subIdx n (Tl (k + 1)) j i) *
            treeP Lab Tl k univ l (Tl (k + 1)) (subIdx n (Tl (k + 1)) j i)
        ≤ ∑ _i ∈ Finset.range (2 ^ (Tl (k + 1) - n)), (1 : ℝ≥0∞) := by
          gcongr with i
          calc _ ≤ (1 : ℝ≥0∞) * 1 := mul_le_mul' (ih _ _ _ _) (ih _ _ _ _)
            _ = 1 := one_mul 1
      _ = 2 ^ (Tl (k + 1) - n) := by simp

theorem measurable_treeP {Lab : Set (Λ × ℝ)} (hLab : MeasurableSet Lab) (Tl : ℕ → ℕ) :
    ∀ k {Y : Set ℝ}, MeasurableSet Y → ∀ n j, Measurable (fun l => treeP Lab Tl k Y l n j) := by
  intro k
  induction k with
  | zero =>
    intro Y hY n j
    simp only [treeP]
    refine Measurable.mul_const ?_ _
    have hS : MeasurableSet {p : Λ × ℝ | p.2 ∈ dI n j ∩ Y ∧ p ∈ Lab} :=
      (measurable_snd ((measurableSet_dI n j).inter hY)).inter hLab
    have := measurable_measure_prodMk_left (ν := volume) hS
    have heq : (fun l => volume (dI n j ∩ Y ∩ {t | (l, t) ∈ Lab})) =
        (fun l => volume (Prod.mk l ⁻¹' {p : Λ × ℝ | p.2 ∈ dI n j ∩ Y ∧ p ∈ Lab})) := by
      funext l; congr 1
    rw [heq]; exact this
  | succ k ih =>
    intro Y hY n j
    simp only [treeP]
    refine Measurable.div_const ?_ _
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (ih hY _ _).mul (ih MeasurableSet.univ _ _)

/-- The set of trajectories labelled at every time of a tree. -/
def TTree.labSet (Lab : Set (Λ × ℝ)) {k : ℕ} (T : TTree k) : Set Λ :=
  {l | ∀ s, T.Mem s → (l, s) ∈ Lab}

theorem TTree.labSet_node (Lab : Set (Λ × ℝ)) {k : ℕ} (L R : TTree k) :
    (TTree.node L R).labSet Lab = L.labSet Lab ∩ R.labSet Lab := by
  ext l
  simp only [TTree.labSet, TTree.Mem, mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro h; exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
  · rintro ⟨h1, h2⟩ s (hs | hs)
    · exact h1 s hs
    · exact h2 s hs

theorem TTree.measurableSet_labSet {Lab : Set (Λ × ℝ)} (hLab : MeasurableSet Lab) :
    ∀ {k : ℕ} (T : TTree k), MeasurableSet (T.labSet Lab)
  | _, .leaf t => by
    have : (TTree.leaf t).labSet Lab = {l | (l, t) ∈ Lab} := by
      ext l; simp only [TTree.labSet, TTree.Mem, mem_ofPred_eq, forall_eq]
    rw [this]; exact measurable_prodMk_right hLab
  | _, .node L R => by
    rw [TTree.labSet_node]
    exact (TTree.measurableSet_labSet hLab L).inter (TTree.measurableSet_labSet hLab R)

/-- Removing `Z` from the allowed root set costs at most its relative length. -/
theorem treeP_le_diff (Lab : Set (Λ × ℝ)) (Tl : ℕ → ℕ) (hTl : ∀ k, Tl (k + 2) ≤ Tl (k + 1)) :
    ∀ k (Y Z : Set ℝ) (hZ : MeasurableSet Z) (l : Λ) (n : ℕ) (j : ℤ), (1 ≤ k → n ≤ Tl k) →
      treeP Lab Tl k Y l n j ≤ treeP Lab Tl k (Y \ Z) l n j + volume (Z ∩ dI n j) * 2 ^ n := by
  intro k
  induction k with
  | zero =>
    intro Y Z _ l n j _
    simp only [treeP]
    rw [← add_mul]
    gcongr
    calc volume (dI n j ∩ Y ∩ {t | (l, t) ∈ Lab})
        ≤ volume ((dI n j ∩ (Y \ Z) ∩ {t | (l, t) ∈ Lab}) ∪ (Z ∩ dI n j)) := by
          apply measure_mono
          intro t ⟨⟨h1, h2⟩, h3⟩
          by_cases hz : t ∈ Z
          · exact Or.inr ⟨hz, h1⟩
          · exact Or.inl ⟨⟨h1, h2, hz⟩, h3⟩
      _ ≤ _ := measure_union_le _ _
  | succ k ih =>
    intro Y Z hZ l n j hn
    have hnm : n ≤ Tl (k + 1) := hn (by omega)
    set m := Tl (k + 1)
    have hrec : ∀ i, treeP Lab Tl k Y l m (subIdx n m j i) ≤
        treeP Lab Tl k (Y \ Z) l m (subIdx n m j i) + volume (Z ∩ dI m (subIdx n m j i)) * 2 ^ m := by
      intro i
      refine ih Y Z hZ l m _ fun hk => ?_
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact hTl k'
    simp only [treeP]
    have hdivpos : (2 : ℝ≥0∞) ^ (m - n) ≠ 0 := by positivity
    have hdivtop : (2 : ℝ≥0∞) ^ (m - n) ≠ ⊤ := by simp
    rw [ENNReal.div_le_iff hdivpos hdivtop, add_mul, ENNReal.div_mul_cancel hdivpos hdivtop]
    calc ∑ i ∈ Finset.range (2 ^ (m - n)),
          treeP Lab Tl k Y l m (subIdx n m j i) * treeP Lab Tl k univ l m (subIdx n m j i)
        ≤ ∑ i ∈ Finset.range (2 ^ (m - n)),
          (treeP Lab Tl k (Y \ Z) l m (subIdx n m j i) * treeP Lab Tl k univ l m (subIdx n m j i) +
            volume (Z ∩ dI m (subIdx n m j i)) * 2 ^ m) := by
          gcongr with i
          calc treeP Lab Tl k Y l m (subIdx n m j i) * treeP Lab Tl k univ l m (subIdx n m j i)
              ≤ (treeP Lab Tl k (Y \ Z) l m (subIdx n m j i) +
                  volume (Z ∩ dI m (subIdx n m j i)) * 2 ^ m) *
                    treeP Lab Tl k univ l m (subIdx n m j i) := by gcongr; exact hrec i
            _ ≤ treeP Lab Tl k (Y \ Z) l m (subIdx n m j i) * treeP Lab Tl k univ l m (subIdx n m j i) +
                  volume (Z ∩ dI m (subIdx n m j i)) * 2 ^ m * 1 := by
                rw [add_mul]; gcongr; exact treeP_le_one Lab Tl _ _ _ _ _
            _ = _ := by rw [mul_one]
      _ = ∑ i ∈ Finset.range (2 ^ (m - n)),
            treeP Lab Tl k (Y \ Z) l m (subIdx n m j i) * treeP Lab Tl k univ l m (subIdx n m j i) +
          (∑ i ∈ Finset.range (2 ^ (m - n)), volume (Z ∩ dI m (subIdx n m j i))) * 2 ^ m := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = _ := by
          congr 1
          rw [← measure_biUnion_finset]
          · rw [← inter_iUnion₂, ← dI_cover hnm j]
            rw [show (2 : ℝ≥0∞) ^ m = 2 ^ n * 2 ^ (m - n) by
              rw [← pow_add, Nat.add_sub_cancel' hnm]]
            ring
          · intro i _ i' _ hii
            exact (dI_disjoint m ((subIdx_injective n m j).ne hii)).mono inter_subset_right
              inter_subset_right
          · intro i _; exact hZ.inter (measurableSet_dI _ _)

/-- Accumulated gap losses. -/
def gapLoss (Kg : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => 2 * gapLoss Kg k + 2 / Kg

theorem gapLoss_nonneg {Kg : ℝ} (hKg : 0 < Kg) : ∀ k, 0 ≤ gapLoss Kg k
  | 0 => le_rfl
  | k + 1 => by
    simp only [gapLoss]
    have := gapLoss_nonneg hKg k
    positivity

/-- The pair scales of the dyadic levels. -/
def levelScale (Tl : ℕ → ℕ) (k : ℕ) : ℝ := ((2 : ℝ) ^ Tl k)⁻¹

/-- Base case of the tree choice: one good time. -/
theorem leaf_exists {Lab : Set (Λ × ℝ)} (hLab : MeasurableSet Lab) (Tl : ℕ → ℕ) (n : ℕ) (j : ℤ)
    {Y : Set ℝ} (hY : MeasurableSet Y) (μ : Measure Λ) [IsFiniteMeasure μ]
    (hpos : 0 < ∫⁻ l, treeP Lab Tl 0 Y l n j ∂μ) :
    ∃ t ∈ dI n j ∩ Y, ∫⁻ l, treeP Lab Tl 0 Y l n j ∂μ ≤ μ {l | (l, t) ∈ Lab} := by
  classical
  set I := dI n j
  have hI : MeasurableSet I := measurableSet_dI n j
  set S : Set (Λ × ℝ) := {p | p.2 ∈ I ∩ Y ∧ p ∈ Lab}
  have hS : MeasurableSet S := (measurable_snd (hI.inter hY)).inter hLab
  set g : ℝ → ℝ≥0∞ := fun t => μ {l | (l, t) ∈ Lab}
  have hg : Measurable g := measurable_measure_prodMk_right hLab
  -- Tonelli
  have hton : ∫⁻ l, treeP Lab Tl 0 Y l n j ∂μ = (∫⁻ t in I ∩ Y, g t) * 2 ^ n := by
    simp only [treeP]
    have hmv : Measurable (fun l => volume (I ∩ Y ∩ {t | (l, t) ∈ Lab})) := by
      have := measurable_measure_prodMk_left (ν := volume) hS
      have heq : (fun l => volume (I ∩ Y ∩ {t | (l, t) ∈ Lab})) =
          (fun l => volume (Prod.mk l ⁻¹' S)) := by funext l; congr 1
      rw [heq]; exact this
    rw [lintegral_mul_const _ hmv]
    congr 1
    have h1 : ∫⁻ l, volume (I ∩ Y ∩ {t | (l, t) ∈ Lab}) ∂μ = (μ.prod volume) S := by
      rw [Measure.prod_apply hS]; rfl
    rw [h1, Measure.prod_apply_symm hS, ← lintegral_indicator (hI.inter hY)]
    congr 1
    ext t
    by_cases ht : t ∈ I ∩ Y
    · simp only [indicator_of_mem ht]; congr 1; ext l
      exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
    · simp only [ht, not_false_eq_true, indicator_of_notMem]
      have : (fun x => (x, t)) ⁻¹' S = ∅ := by
        ext l; simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact fun h => ht h.1
      rw [this, measure_empty]
  -- positive restricted volume
  have hvol : volume (I ∩ Y) ≠ 0 := by
    intro h0
    rw [hton, Measure.restrict_eq_zero.mpr h0, lintegral_zero_measure, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have hfin : volume (I ∩ Y) ≠ ⊤ := ne_top_of_le_ne_top (by rw [volume_dI]; simp)
    (measure_mono inter_subset_left)
  have hint : ∫⁻ t in I ∩ Y, g t ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (measure_ne_top μ univ) hfin) ?_
    calc ∫⁻ t in I ∩ Y, g t ≤ ∫⁻ _t in I ∩ Y, μ univ := lintegral_mono fun t => measure_mono (subset_univ _)
      _ = μ univ * volume (I ∩ Y) := by rw [setLIntegral_const]
  have : IsFiniteMeasure (volume.restrict (I ∩ Y)) := ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hfin⟩
  have hne : volume.restrict (I ∩ Y) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact hvol
  have := measure_laverage_le_pos hne hint
  rw [Measure.restrict_apply' (hI.inter hY)] at this
  obtain ⟨t, ht1, ht2⟩ := nonempty_of_measure_ne_zero this.ne'
  refine ⟨t, ht2, ?_⟩
  rw [hton]
  have hle : ⨍⁻ x, g x ∂volume.restrict (I ∩ Y) ≤ g t := ht1
  rw [laverage_eq, Measure.restrict_apply_univ] at hle
  have hle' : ∫⁻ t in I ∩ Y, g t ≤ g t * volume (I ∩ Y) :=
    (ENNReal.div_le_iff hvol hfin).mp hle
  calc (∫⁻ t in I ∩ Y, g t) * 2 ^ n ≤ g t * volume (I ∩ Y) * 2 ^ n := by gcongr
    _ = g t * (volume (I ∩ Y) * 2 ^ n) := by ring
    _ ≤ g t * (volume I * 2 ^ n) := by
        gcongr
        exact inter_subset_left
    _ = g t := by
        rw [volume_dI, ENNReal.ofReal_inv_of_pos (by positivity)]
        rw [show ENNReal.ofReal ((2 : ℝ) ^ n) = (2 : ℝ≥0∞) ^ n by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp]
        rw [ENNReal.inv_mul_cancel (by positivity) (by simp), mul_one]

/-- **The tree choice.** -/
theorem tree_exists {Lab : Set (Λ × ℝ)} (hLab : MeasurableSet Lab) (Tl : ℕ → ℕ)
    (hTl : ∀ k, Tl (k + 2) ≤ Tl (k + 1)) {Kg : ℝ} (hKg : 0 < Kg) :
    ∀ k (n : ℕ) (j : ℤ), (1 ≤ k → n ≤ Tl k) → ∀ (Y : Set ℝ), MeasurableSet Y →
      ∀ (μ : Measure Λ) [IsFiniteMeasure μ],
      ENNReal.ofReal (gapLoss Kg k) * μ univ < ∫⁻ l, treeP Lab Tl k Y l n j ∂μ →
      ∃ T : TTree k, T.Pairs (levelScale Tl) Kg ∧ T.Cells Tl ∧ (∀ s, T.Mem s → s ∈ dI n j) ∧
        T.root ∈ Y ∧
        ∫⁻ l, treeP Lab Tl k Y l n j ∂μ ≤ μ (T.labSet Lab) + ENNReal.ofReal (gapLoss Kg k) * μ univ := by
  intro k
  induction k with
  | zero =>
    intro n j _ Y hY μ _ hpos
    have hpos' : 0 < ∫⁻ l, treeP Lab Tl 0 Y l n j ∂μ := lt_of_le_of_lt bot_le hpos
    obtain ⟨t, ⟨htI, htY⟩, ht⟩ := leaf_exists hLab Tl n j hY μ hpos'
    refine ⟨.leaf t, trivial, trivial, fun s hs => by rw [hs]; exact htI, htY, ?_⟩
    have : (TTree.leaf t).labSet Lab = {l | (l, t) ∈ Lab} := by
      ext l; simp only [TTree.labSet, TTree.Mem, mem_ofPred_eq, forall_eq]
    rw [this]
    exact ht.trans le_self_add
  | succ k ih =>
    intro n j hn Y hY μ _ hbig
    classical
    have hnm : n ≤ Tl (k + 1) := hn (by omega)
    set m := Tl (k + 1) with hm
    have hlev : 1 ≤ k → m ≤ Tl k := by
      intro hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact hTl k'
    set idx := subIdx n m j
    set P : ℕ → Λ → ℝ≥0∞ := fun i l => treeP Lab Tl k Y l m (idx i)
    set Q : ℕ → Λ → ℝ≥0∞ := fun i l => treeP Lab Tl k univ l m (idx i)
    have hPm : ∀ i, Measurable (P i) := fun i => measurable_treeP hLab Tl k hY _ _
    have hQm : ∀ i, Measurable (Q i) := fun i => measurable_treeP hLab Tl k MeasurableSet.univ _ _
    -- the average over subintervals is at most the best one
    have hrange : (Finset.range (2 ^ (m - n))).Nonempty := ⟨0, by simp⟩
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.range (2 ^ (m - n)))
      (fun i => ∫⁻ l, P i l * Q i l ∂μ) hrange
    have hA : ∫⁻ l, treeP Lab Tl (k + 1) Y l n j ∂μ ≤ ∫⁻ l, P i₀ l * Q i₀ l ∂μ := by
      have hdivpos : (2 : ℝ≥0∞) ^ (m - n) ≠ 0 := by positivity
      have hdivtop : (2 : ℝ≥0∞) ^ (m - n) ≠ ⊤ := by simp
      have hfun : ∀ l, treeP Lab Tl (k + 1) Y l n j =
          (∑ i ∈ Finset.range (2 ^ (m - n)), P i l * Q i l) * ((2 : ℝ≥0∞) ^ (m - n))⁻¹ := by
        intro l; simp only [treeP, div_eq_mul_inv]; rfl
      have hsm : Measurable (fun l => ∑ i ∈ Finset.range (2 ^ (m - n)), P i l * Q i l) :=
        Finset.measurable_sum _ (fun i _ => (hPm i).mul (hQm i))
      have hpm : ∀ i ∈ Finset.range (2 ^ (m - n)), Measurable (fun l => P i l * Q i l) :=
        fun i _ => (hPm i).mul (hQm i)
      rw [lintegral_congr fun l => hfun l, lintegral_mul_const _ hsm,
        lintegral_finsetSum _ hpm, ← div_eq_mul_inv,
        ENNReal.div_le_iff hdivpos hdivtop]
      calc ∑ i ∈ Finset.range (2 ^ (m - n)), ∫⁻ l, P i l * Q i l ∂μ
          ≤ ∑ _i ∈ Finset.range (2 ^ (m - n)), ∫⁻ l, P i₀ l * Q i₀ l ∂μ :=
            Finset.sum_le_sum fun i hi => hmax i hi
        _ = (∫⁻ l, P i₀ l * Q i₀ l ∂μ) * 2 ^ (m - n) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]; norm_cast
    set B := ∫⁻ l, P i₀ l * Q i₀ l ∂μ
    have hLk : gapLoss Kg k ≤ gapLoss Kg (k + 1) := by
      simp only [gapLoss]; have := gapLoss_nonneg hKg k; have : 0 < 2 / Kg := by positivity
      linarith
    -- the right subtree, for the weighted measure
    set μ₁ := μ.withDensity (P i₀)
    have hμ₁univ : μ₁ univ ≤ μ univ := by
      simp only [μ₁, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      calc ∫⁻ l, P i₀ l ∂μ ≤ ∫⁻ _l, (1 : ℝ≥0∞) ∂μ :=
            lintegral_mono fun l => treeP_le_one Lab Tl _ _ _ _ _
        _ = μ univ := by rw [lintegral_one]
    haveI : IsFiniteMeasure μ₁ := ⟨lt_of_le_of_lt hμ₁univ (measure_lt_top μ univ)⟩
    have hB₁ : ∫⁻ l, Q i₀ l ∂μ₁ = B := by
      simp only [μ₁, B]
      rw [lintegral_withDensity_eq_lintegral_mul _ (hPm i₀) (hQm i₀)]
      rfl
    have hRbig : ENNReal.ofReal (gapLoss Kg k) * μ₁ univ < ∫⁻ l, Q i₀ l ∂μ₁ := by
      rw [hB₁]
      calc ENNReal.ofReal (gapLoss Kg k) * μ₁ univ ≤ ENNReal.ofReal (gapLoss Kg (k + 1)) * μ univ :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal hLk) hμ₁univ
        _ < _ := hbig.trans_le hA
    obtain ⟨R, hRP, hRC, hRin, -, hRb⟩ := ih m (idx i₀) hlev univ MeasurableSet.univ μ₁ hRbig
    have hRset := TTree.measurableSet_labSet hLab R
    -- the left subtree, for the restriction to the right label set, avoiding a gap
    set H := levelScale Tl (k + 1)
    have hH : 0 < H := by simp only [H, levelScale]; positivity
    set Gap := Ioo (R.root - H / Kg) (R.root + H / Kg)
    have hGap : MeasurableSet Gap := measurableSet_Ioo
    set Y' := Y \ Gap
    have hY' : MeasurableSet Y' := hY.diff hGap
    set μ₂ := μ.restrict (R.labSet Lab)
    have hμ₂univ : μ₂ univ ≤ μ univ := by
      simp only [μ₂, Measure.restrict_apply_univ]; exact measure_mono (subset_univ _)
    -- cost of the gap
    have hgapcost : ∀ l, P i₀ l ≤ treeP Lab Tl k Y' l m (idx i₀) + ENNReal.ofReal (2 / Kg) := by
      intro l
      refine (treeP_le_diff Lab Tl hTl k Y Gap hGap l m (idx i₀) hlev).trans (add_le_add le_rfl ?_)
      calc volume (Gap ∩ dI m (idx i₀)) * 2 ^ m ≤ volume Gap * 2 ^ m := by
            gcongr; exact inter_subset_left
        _ = ENNReal.ofReal (2 / Kg) := by
            rw [Real.volume_Ioo]
            rw [show (2 : ℝ≥0∞) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) by
              rw [ENNReal.ofReal_pow (by norm_num)]; simp]
            rw [← ENNReal.ofReal_mul (by have := div_pos hH hKg; linarith)]
            congr 1
            simp only [H, levelScale]
            field_simp
            ring
    have hμ₁R : μ₁ (R.labSet Lab) = ∫⁻ l, P i₀ l ∂μ₂ := by
      simp only [μ₁, μ₂]; rw [withDensity_apply _ hRset]
    have hLbig : ENNReal.ofReal (gapLoss Kg k) * μ₂ univ <
        ∫⁻ l, treeP Lab Tl k Y' l m (idx i₀) ∂μ₂ := by
      by_contra hle
      push Not at hle
      have h1 : ∫⁻ l, P i₀ l ∂μ₂ ≤ ∫⁻ l, treeP Lab Tl k Y' l m (idx i₀) ∂μ₂ +
          ENNReal.ofReal (2 / Kg) * μ₂ univ := by
        calc ∫⁻ l, P i₀ l ∂μ₂ ≤ ∫⁻ l, (treeP Lab Tl k Y' l m (idx i₀) + ENNReal.ofReal (2 / Kg)) ∂μ₂ :=
              lintegral_mono hgapcost
          _ = _ := by
              rw [lintegral_add_right _ measurable_const, lintegral_const]
      have h2 : B ≤ ENNReal.ofReal (gapLoss Kg (k + 1)) * μ univ := by
        calc B = ∫⁻ l, Q i₀ l ∂μ₁ := hB₁.symm
          _ ≤ μ₁ (R.labSet Lab) + ENNReal.ofReal (gapLoss Kg k) * μ₁ univ := hRb
          _ ≤ (ENNReal.ofReal (gapLoss Kg k) * μ univ + ENNReal.ofReal (2 / Kg) * μ univ) +
                ENNReal.ofReal (gapLoss Kg k) * μ univ := by
              rw [hμ₁R]
              gcongr
              calc ∫⁻ l, P i₀ l ∂μ₂ ≤ _ := h1
                _ ≤ ENNReal.ofReal (gapLoss Kg k) * μ₂ univ + ENNReal.ofReal (2 / Kg) * μ₂ univ :=
                    add_le_add hle le_rfl
                _ ≤ _ := by gcongr
          _ = ENNReal.ofReal (gapLoss Kg (k + 1)) * μ univ := by
              simp only [gapLoss]
              have h0 := gapLoss_nonneg hKg k
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
              simp only [ENNReal.ofReal_ofNat]
              ring
      exact absurd (hbig.trans_le (hA.trans h2)) (lt_irrefl _)
    obtain ⟨L, hLP, hLC, hLin, hLroot, hLb⟩ := ih m (idx i₀) hlev Y' hY' μ₂ hLbig
    -- assemble
    have hIsub : dI m (idx i₀) ⊆ dI n j := dI_sub hnm j (Finset.mem_range.mp hi₀)
    have hLr := hLin L.root (TTree.mem_root L)
    have hRr := hRin R.root (TTree.mem_root R)
    have hgap : H / Kg ≤ |R.root - L.root| := by
      by_contra hlt
      push Not at hlt
      apply hLroot.2
      rw [abs_lt] at hlt
      constructor <;> linarith
    have hclose : |R.root - L.root| ≤ H := by
      have := abs_sub_lt_of_mem_dI hRr hLr
      simp only [H, levelScale]; exact this.le
    refine ⟨.node L R, ⟨hLP, hRP, hgap, hclose⟩, ⟨hLC, hRC, idx i₀, hLr, hRr⟩, ?_, hLroot.1, ?_⟩
    · rintro s (hs | hs)
      · exact hIsub (hLin s hs)
      · exact hIsub (hRin s hs)
    · rw [TTree.labSet_node]
      have hμ₂L : μ₂ (L.labSet Lab) = μ (L.labSet Lab ∩ R.labSet Lab) := by
        simp only [μ₂]; rw [Measure.restrict_apply (TTree.measurableSet_labSet hLab L)]
      calc ∫⁻ l, treeP Lab Tl (k + 1) Y l n j ∂μ ≤ B := hA
        _ = ∫⁻ l, Q i₀ l ∂μ₁ := hB₁.symm
        _ ≤ μ₁ (R.labSet Lab) + ENNReal.ofReal (gapLoss Kg k) * μ₁ univ := hRb
        _ ≤ (∫⁻ l, treeP Lab Tl k Y' l m (idx i₀) ∂μ₂ + ENNReal.ofReal (2 / Kg) * μ univ) +
              ENNReal.ofReal (gapLoss Kg k) * μ univ := by
            rw [hμ₁R]
            gcongr
            calc ∫⁻ l, P i₀ l ∂μ₂ ≤ ∫⁻ l, (treeP Lab Tl k Y' l m (idx i₀) + ENNReal.ofReal (2 / Kg)) ∂μ₂ :=
                  lintegral_mono hgapcost
              _ = ∫⁻ l, treeP Lab Tl k Y' l m (idx i₀) ∂μ₂ + ENNReal.ofReal (2 / Kg) * μ₂ univ := by
                  rw [lintegral_add_right _ measurable_const, lintegral_const]
              _ ≤ _ := by gcongr
        _ ≤ ((μ₂ (L.labSet Lab) + ENNReal.ofReal (gapLoss Kg k) * μ univ) +
              ENNReal.ofReal (2 / Kg) * μ univ) + ENNReal.ofReal (gapLoss Kg k) * μ univ := by
            gcongr
            exact hLb.trans (by gcongr)
        _ = μ (L.labSet Lab ∩ R.labSet Lab) + ENNReal.ofReal (gapLoss Kg (k + 1)) * μ univ := by
            rw [hμ₂L]
            simp only [gapLoss]
            have h0 := gapLoss_nonneg hKg k
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
            simp only [ENNReal.ofReal_ofNat]
            ring

/-- The label fraction at level `m` averages to the label fraction at level `n ≤ m`. -/
theorem treeP_zero_avg (Lab : Set (Λ × ℝ)) (hLab : MeasurableSet Lab) (Tl : ℕ → ℕ) (l : Λ)
    {n m : ℕ} (hnm : n ≤ m) (j : ℤ) :
    (∑ i ∈ Finset.range (2 ^ (m - n)), treeP Lab Tl 0 univ l m (subIdx n m j i)) / 2 ^ (m - n) =
      treeP Lab Tl 0 univ l n j := by
  simp only [treeP, inter_univ]
  have hdivpos : (2 : ℝ≥0∞) ^ (m - n) ≠ 0 := by positivity
  have hdivtop : (2 : ℝ≥0∞) ^ (m - n) ≠ ⊤ := by simp
  have hsec : MeasurableSet {t | (l, t) ∈ Lab} := measurable_prodMk_left hLab
  rw [← Finset.sum_mul, ← measure_biUnion_finset]
  · rw [← iUnion₂_inter, ← dI_cover hnm j]
    -- (v * 2^m) / 2^(m-n) = v * 2^n
    rw [show (2 : ℝ≥0∞) ^ m = 2 ^ n * 2 ^ (m - n) by rw [← pow_add, Nat.add_sub_cancel' hnm]]
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm _ (volume _), mul_assoc, ← mul_assoc _ (2 ^ n),
      mul_comm (2 ^ (m - n))⁻¹, mul_assoc, ENNReal.inv_mul_cancel hdivpos hdivtop, mul_one]
  · intro i _ i' _ hii
    exact ((dI_disjoint m ((subIdx_injective n m j).ne hii)).mono inter_subset_left
      inter_subset_left)
  · intro i _
    exact (measurableSet_dI _ _).inter hsec

/-- **Jensen along the tree**: the success of the uniform tree is at least the `2^k`-th power of the
label fraction. -/
theorem treeP_ge_pow (Lab : Set (Λ × ℝ)) (hLab : MeasurableSet Lab) (Tl : ℕ → ℕ)
    (hTl : ∀ k, Tl (k + 2) ≤ Tl (k + 1)) (l : Λ) :
    ∀ k (n : ℕ) (j : ℤ), (1 ≤ k → n ≤ Tl k) →
      treeP Lab Tl 0 univ l n j ^ (2 ^ k) ≤ treeP Lab Tl k univ l n j := by
  intro k
  induction k with
  | zero => intro n j _; simp
  | succ k ih =>
    intro n j hn
    have hnm : n ≤ Tl (k + 1) := hn (by omega)
    set m := Tl (k + 1)
    have hlev : 1 ≤ k → m ≤ Tl k := by
      intro hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact hTl k'
    set a : ℕ → ℝ≥0∞ := fun i => treeP Lab Tl 0 univ l m (subIdx n m j i)
    have hdivpos : (2 : ℝ≥0∞) ^ (m - n) ≠ 0 := by positivity
    have hdivtop : (2 : ℝ≥0∞) ^ (m - n) ≠ ⊤ := by simp
    -- Jensen for the power 2^(k+1)
    have hw : ∑ _i ∈ Finset.range (2 ^ (m - n)), ((2 : ℝ≥0∞) ^ (m - n))⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      exact ENNReal.mul_inv_cancel hdivpos hdivtop
    have hJ := ENNReal.rpow_arith_mean_le_arith_mean_rpow (Finset.range (2 ^ (m - n)))
      (fun _ => ((2 : ℝ≥0∞) ^ (m - n))⁻¹) a hw (p := ((2 ^ (k + 1) : ℕ) : ℝ))
      (by exact_mod_cast Nat.one_le_two_pow)
    simp only [ENNReal.rpow_natCast] at hJ
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← ENNReal.div_eq_inv_mul, ← ENNReal.div_eq_inv_mul,
      treeP_zero_avg Lab hLab Tl l hnm j] at hJ
    refine hJ.trans ?_
    simp only [treeP]
    gcongr with i hi
    rw [pow_succ, pow_mul, sq]
    have hrec := ih m (subIdx n m j i) hlev
    exact mul_le_mul' hrec hrec

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
