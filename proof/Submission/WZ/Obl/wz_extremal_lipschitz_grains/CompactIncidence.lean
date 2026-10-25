-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.CompactIncidence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Compact
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Regularize

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- The part of a shaded union with exactly the membership pattern `s`. -/
def shadingAtom {n : ℕ} (Y : Fin n → Set Space) (s : Finset (Fin n)) : Set Space :=
  (⋃ i, Y i) ∩ {p | ∀ i, p ∈ Y i ↔ i ∈ s}

theorem measurableSet_shadingAtom {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (s : Finset (Fin n)) :
    MeasurableSet (shadingAtom Y s) := by
  apply (MeasurableSet.iUnion hY).inter
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ s
  · convert hY i using 1
    ext p
    simp [hi]
  · convert (hY i).compl using 1
    ext p
    simp [hi]

theorem shadingAtom_disjoint {n : ℕ} (Y : Fin n → Set Space) :
    Pairwise (fun s t => Disjoint (shadingAtom Y s) (shadingAtom Y t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro p hps hpt
  apply hst
  ext i
  exact (hps.2 i).symm.trans (hpt.2 i)

theorem eq_union_shadingAtom {n : ℕ} (Y : Fin n → Set Space) (i : Fin n) :
    Y i = ⋃ s : Finset (Fin n), if i ∈ s then shadingAtom Y s else ∅ := by
  classical
  ext p
  constructor
  · intro hp
    let s : Finset (Fin n) := Finset.univ.filter fun j => p ∈ Y j
    have hi : i ∈ s := by simp [s, hp]
    apply mem_iUnion.mpr
    refine ⟨s, ?_⟩
    rw [ite_eq_left hi]
    exact ⟨mem_iUnion.mpr ⟨i, hp⟩, by simp [s]⟩
  · intro hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp hp
    split_ifs at hs with hi
    · exact (hs.2 i).mpr hi
    · exact hs.elim

private theorem measure_pattern_union {n : ℕ} {K : Finset (Fin n) → Set Space}
    (hK : ∀ s, MeasurableSet (K s)) (hdisj : Pairwise (fun s t => Disjoint (K s) (K t))) (i : Fin n) :
    volume (⋃ s : Finset (Fin n), if i ∈ s then K s else ∅) =
      ∑ s : Finset (Fin n), if i ∈ s then volume (K s) else 0 := by
  classical
  have hm : ∀ s : Finset (Fin n), MeasurableSet (if i ∈ s then K s else ∅) := by
    intro s
    split_ifs <;> simp_all
  have hd : Pairwise (fun s t : Finset (Fin n) =>
      Disjoint (if i ∈ s then K s else ∅) (if i ∈ t then K t else ∅)) := by
    intro s t hst
    split_ifs <;> simp_all [hdisj hst]
  rw [measure_iUnion hd hm, tsum_fintype]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

/-- Simultaneous compact approximation preserves every membership pattern at the retained
points. In particular it preserves the exact number of shadings through those points. -/
theorem compact_incidence_refinement {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hUfin : volume (⋃ i, Y i) ≠ ∞) :
    ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧ (∀ i, IsCompact (Z i)) ∧
      (∀ i, volume (Y i) / 2 ≤ volume (Z i)) ∧
      (∀ p ∈ ⋃ i, Z i, ∀ i, p ∈ Z i ↔ p ∈ Y i) ∧
      (∀ p ∈ ⋃ i, Z i, incidence Z p = incidence Y p) := by
  classical
  have hAfin : ∀ s, volume (shadingAtom Y s) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hUfin (measure_mono inter_subset_left)
  choose K hKA hK hmass using fun s =>
    compact_half_mass (measurableSet_shadingAtom hY s) (hAfin s)
  let Z : Fin n → Set Space :=
    fun i => ⋃ s : Finset (Fin n), if i ∈ s then K s else ∅
  have hZY : ∀ i, Z i ⊆ Y i := by
    intro i p hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp hp
    split_ifs at hs with hi
    · exact ((hKA s hs).2 i).mpr hi
    · exact hs.elim
  have hZcompact : ∀ i, IsCompact (Z i) := by
    intro i
    apply isCompact_iUnion
    intro s
    split_ifs <;> simp_all
  have hKdisj : Pairwise (fun s t => Disjoint (K s) (K t)) := by
    intro s t hst
    exact (shadingAtom_disjoint Y hst).mono (hKA s) (hKA t)
  have hZmass : ∀ i, volume (Y i) / 2 ≤ volume (Z i) := by
    intro i
    conv_lhs => rw [eq_union_shadingAtom Y i,
      measure_pattern_union (measurableSet_shadingAtom hY) (shadingAtom_disjoint Y) i]
    rw [div_eq_mul_inv, Finset.sum_mul]
    change _ ≤ volume (⋃ s : Finset (Fin n), if i ∈ s then K s else ∅)
    rw [measure_pattern_union (fun s => (hK s).measurableSet) hKdisj i]
    apply Finset.sum_le_sum
    intro s _
    split_ifs with hi
    · exact hmass s
    · simp
  have hpattern : ∀ p ∈ ⋃ i, Z i, ∀ i, p ∈ Z i ↔ p ∈ Y i := by
    intro p hp i
    refine ⟨fun hpi => hZY i hpi, ?_⟩
    intro hpi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp hj
    split_ifs at hs with hj'
    · have hi : i ∈ s := ((hKA s hs).2 i).mp hpi
      exact mem_iUnion.mpr ⟨s, by simpa [hi] using hs⟩
    · exact hs.elim
  refine ⟨Z, hZY, hZcompact, hZmass, hpattern, ?_⟩
  intro p hp
  rw [incidence_eq_ncard, incidence_eq_ncard]
  congr 2
  ext i
  exact hpattern p hp i

theorem Family.compact_incidence_refinement {η ε δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space} (hH : Family η δ n x v Y)
    (hδ : 0 < δ) (hpower : δ ^ ε ≤ δ ^ η / 2) :
    ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧ (∀ i, IsCompact (Z i)) ∧
      Family ε δ n x v Z ∧
      (∀ p ∈ ⋃ i, Z i, ∀ i, p ∈ Z i ↔ p ∈ Y i) ∧
      (∀ p ∈ ⋃ i, Z i, incidence Z p = incidence Y p) := by
  obtain ⟨Z, hZY, hZcompact, hZmass, hpattern, hinc⟩ :=
    WangZahlLot.Obl.wz_extremal_lipschitz_grains.compact_incidence_refinement
      hH.2.2.2.2.1 hH.volume_union_ne_top
  have hhalf : shadingMass Y / 2 ≤ shadingMass Z := by
    rw [shadingMass, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    have hfin := ne_top_of_le_ne_top (hH.shading_finite i) (measure_mono (hZY i))
    have h := ENNReal.toReal_mono hfin (hZmass i)
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using h
  refine ⟨Z, hZY, hZcompact, hH.of_subsets_mass hZY
    (fun i => (hZcompact i).measurableSet) ?_, hpattern, hinc⟩
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg n)) (sq_nonneg δ)
  have hlower := hH.mass_lower hδ
  linarith

/-- Compact extremal examples may simultaneously be chosen to have uniform pointwise
incidence, including a lower incidence bound at every shaded point. -/
theorem compact_incidence_extremal_examples {σ : ℝ}
    (hbelow : ∀ t : ℝ, t < σ → Examples t)
    (habove : ∀ t : ℝ, σ < t → ¬ Examples t)
    (ε d0 : ℝ) (hε : 0 < ε) (hd0 : 0 < d0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family ε δ n x v Y ∧ Separated ε δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) ∧
        (∀ p, incidence Y p ≤ (n : ℝ) * δ ^ (2 - σ - ε)) ∧
        (∀ p ∈ ⋃ i, Y i, (n : ℝ) * δ ^ (2 - σ + ε) < incidence Y p) := by
  obtain ⟨d, hd, hpower⟩ := exists_power_cutoff
    (by positivity : 0 < ε / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hδ0, hδmax, n, x, v, Y, hH, hS, hV, hupper, hlower⟩ :=
    incidence_extremal_examples hbelow habove (ε / 2) (min d0 d)
      (by positivity) (lt_min hd0 hd)
  have hδ1 : δ ≤ 1 := by linarith
  have hp : δ ^ ε ≤ δ ^ (ε / 2) / 2 := by
    calc
      δ ^ ε = δ ^ (ε / 2) * δ ^ (ε / 2) := by
        rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (ε / 2) * (1 / 2) := mul_le_mul_of_nonneg_left
        (hpower δ hδ (hδ0.trans (min_le_right _ _))) (by positivity)
      _ = _ := by ring
  obtain ⟨Z, hZY, hZcompact, hHZ, hpattern, hinc⟩ := hH.compact_incidence_refinement hδ hp
  have hZU : (⋃ i, Z i) ⊆ ⋃ i, Y i := iUnion_mono hZY
  refine ⟨δ, hδ, hδ0.trans (min_le_left _ _), hδmax, n, x, v, Z,
    hHZ, hS.mono_error hδ hδ1 (by linarith), hZcompact, ?_, ?_, ?_⟩
  · apply ((measure_mono hZU).trans hV).trans
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : σ - ε ≤ σ - ε / 2))
  · intro p
    by_cases hp : p ∈ ⋃ i, Z i
    · rw [hinc p hp]
      exact (hupper p).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (Nat.cast_nonneg n))
    · rw [incidence_eq_zero_of_notMem Z hp]
      positivity
  · intro p hp
    rw [hinc p hp]
    apply lt_of_le_of_lt _ (hlower p (hZU hp))
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (Nat.cast_nonneg n)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
