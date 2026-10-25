import Mathlib

/-!
# Incidence time witnesses and finite projection covers

Adapted from: here:o063

Long-time trajectory witnesses retain original incidence mass. Each such witness
visits many time cells, and finite double counting bounds a projection cover when
one source cell can witness only nearby projection cells.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Lib.K4IncidenceWitnesses

/-- Incidences on trajectories with a quantitatively long labeled time set. -/
def longTimeIncidences {α : Type*} [MeasurableSpace α] (E : Set (α × ℝ)) (r : ℝ) :
    Set (α × ℝ) :=
  {p | p ∈ E ∧ ENNReal.ofReal r ≤ volume (Prod.mk p.1 ⁻¹' E)}

def shortTimeIncidences {α : Type*} [MeasurableSpace α] (E : Set (α × ℝ)) (r : ℝ) :
    Set (α × ℝ) :=
  {p | p ∈ E ∧ volume (Prod.mk p.1 ⁻¹' E) < ENNReal.ofReal r}

theorem measurableSet_longTimeIncidences {α : Type*} [MeasurableSpace α]
    {E : Set (α × ℝ)} (hE : MeasurableSet E) (r : ℝ) :
    MeasurableSet (longTimeIncidences E r) :=
  hE.inter (measurableSet_le measurable_const
    ((measurable_measure_prodMk_left hE).comp measurable_fst))

theorem measurableSet_shortTimeIncidences {α : Type*} [MeasurableSpace α]
    {E : Set (α × ℝ)} (hE : MeasurableSet E) (r : ℝ) :
    MeasurableSet (shortTimeIncidences E r) :=
  hE.inter (measurableSet_lt
    ((measurable_measure_prodMk_left hE).comp measurable_fst) measurable_const)

/-- Time domination pays for discarding every trajectory with a short witness set. -/
theorem shortTimeIncidences_mass {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    {C : ℝ} (hC : 0 ≤ C) (hdom : μ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} (hE : MeasurableSet E) (r : ℝ) :
    μ (shortTimeIncidences E r) ≤ ENNReal.ofReal (C * r) := by
  have hprod : (ν.prod volume) (shortTimeIncidences E r) ≤ ENNReal.ofReal r := by
    rw [Measure.prod_apply (measurableSet_shortTimeIncidences hE r)]
    calc
      _ ≤ ∫⁻ _l : α, ENNReal.ofReal r ∂ν := by
        apply lintegral_mono
        intro l
        change volume (Prod.mk l ⁻¹' shortTimeIncidences E r) ≤ ENNReal.ofReal r
        by_cases hs : volume (Prod.mk l ⁻¹' E) < ENNReal.ofReal r
        · have hf : Prod.mk l ⁻¹' shortTimeIncidences E r = Prod.mk l ⁻¹' E := by
            ext t
            simp only [mem_preimage, shortTimeIncidences, mem_ofPred_eq, hs, and_true]
          rw [hf]
          exact hs.le
        · have hf : Prod.mk l ⁻¹' shortTimeIncidences E r = ∅ := by
            ext t
            simp only [mem_preimage, shortTimeIncidences, mem_ofPred_eq, hs, and_false,
              mem_empty_iff_false]
          rw [hf, measure_empty]
          exact zero_le
      _ = ENNReal.ofReal r := by simp
  calc
    _ ≤ (ENNReal.ofReal C • (ν.prod volume)) (shortTimeIncidences E r) := hdom _
    _ = ENNReal.ofReal C * (ν.prod volume) (shortTimeIncidences E r) := rfl
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal r :=
      mul_le_mul_of_nonneg_left hprod (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal C)
    _ = ENNReal.ofReal (C * r) := (ENNReal.ofReal_mul hC).symm

/-- Dense incidence mass has long-time trajectory witnesses on at least half its mass. -/
theorem longTimeIncidences_mass {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    {C m : ℝ} (hC : 0 < C) (hm : 0 < m)
    (hdom : μ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} (hE : MeasurableSet E) (hmass : ENNReal.ofReal m ≤ μ E) :
    ENNReal.ofReal (m / 2) ≤ μ (longTimeIncidences E (m / (2 * C))) := by
  let r := m / (2 * C)
  have hshort : μ (shortTimeIncidences E r) ≤ ENNReal.ofReal (m / 2) := by
    convert shortTimeIncidences_mass ν μ hC.le hdom hE r using 1
    congr 1
    dsimp [r]
    field_simp
  have hcover : E ⊆ longTimeIncidences E r ∪ shortTimeIncidences E r := by
    intro p hp
    rcases le_or_gt (ENNReal.ofReal r) (volume (Prod.mk p.1 ⁻¹' E)) with hl | hs
    · exact Or.inl ⟨hp, hl⟩
    · exact Or.inr ⟨hp, hs⟩
  have hbound : ENNReal.ofReal m ≤ μ (longTimeIncidences E r) + ENNReal.ofReal (m / 2) := by
    calc
      _ ≤ μ E := hmass
      _ ≤ μ (longTimeIncidences E r ∪ shortTimeIncidences E r) := measure_mono hcover
      _ ≤ μ (longTimeIncidences E r) + μ (shortTimeIncidences E r) := measure_union_le _ _
      _ ≤ μ (longTimeIncidences E r) + ENNReal.ofReal (m / 2) := add_le_add le_rfl hshort
  have hsplit : ENNReal.ofReal m = ENNReal.ofReal (m / 2) + ENNReal.ofReal (m / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hsplit] at hbound
  exact ENNReal.le_of_add_le_add_right (by finiteness) hbound


/-- A finite family of labeled time cells covers at most its cardinality times the mesh. -/
theorem volume_le_time_labels {X : Type*} (P : Finset X) (timeIndex : X → ℤ)
    (E : Set ℝ) {h : ℝ} (hh : 0 < h)
    (hcover : ∀ t ∈ E, ∃ p ∈ P, timeIndex p = ⌊t / h⌋) :
    volume E ≤ ENNReal.ofReal ((P.card : ℝ) * h) := by
  classical
  have hsub : E ⊆ ⋃ p ∈ P,
      Ico (h * (timeIndex p : ℝ)) (h * (timeIndex p : ℝ) + h) := by
    intro t ht
    obtain ⟨p, hp, hi⟩ := hcover t ht
    have hlo := (le_div_iff₀ hh).mp (Int.floor_le (t / h))
    have hhi := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (t / h))
    apply mem_biUnion hp
    rw [hi]
    exact ⟨by nlinarith, by nlinarith⟩
  have hvol (p : X) :
      volume (Ico (h * (timeIndex p : ℝ)) (h * (timeIndex p : ℝ) + h)) = ENNReal.ofReal h := by
    rw [Real.volume_Ico]
    congr 1
    ring
  calc
    _ ≤ volume (⋃ p ∈ P,
        Ico (h * (timeIndex p : ℝ)) (h * (timeIndex p : ℝ) + h)) := measure_mono hsub
    _ ≤ ∑ p ∈ P,
        volume (Ico (h * (timeIndex p : ℝ)) (h * (timeIndex p : ℝ) + h)) :=
      measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal ((P.card : ℝ) * h) := by
      simp only [hvol, Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- A long time set visits proportionately many labeled cells. -/
theorem time_labels_card_lower {X : Type*} (P : Finset X) (timeIndex : X → ℤ)
    (E : Set ℝ) {h r : ℝ} (hh : 0 < h)
    (hcover : ∀ t ∈ E, ∃ p ∈ P, timeIndex p = ⌊t / h⌋)
    (hmass : ENNReal.ofReal r ≤ volume E) :
    r / h ≤ (P.card : ℝ) := by
  have hbound := hmass.trans (volume_le_time_labels P timeIndex E hh hcover)
  have hreal : r ≤ (P.card : ℝ) * h :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound
  exact (div_le_iff₀ hh).mpr hreal


/-- A finite integer box of coordinate diameter at most R has a product cardinality bound. -/
theorem card_pi_grid_of_diameter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset (ι → ℤ)) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, ∀ j, |(p j : ℝ) - (q j : ℝ)| ≤ R) :
    (P.card : ℝ) ≤ (2 * R + 3) ^ Fintype.card ι := by
  classical
  by_cases hP : P.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hP
    let B : ι → Finset ℤ := fun j =>
      Finset.Icc (p₀ j - ⌈R⌉) (p₀ j + ⌈R⌉)
    have hceil : (0 : ℤ) ≤ ⌈R⌉ := by exact_mod_cast hR.trans (Int.le_ceil R)
    have hsub : P ⊆ Fintype.piFinset B := by
      intro p hp
      apply Fintype.mem_piFinset.mpr
      intro j
      have hd := abs_le.mp (hdiam p hp p₀ hp₀ j)
      have hle : R ≤ (⌈R⌉ : ℝ) := Int.le_ceil R
      have hlo : (p₀ j - ⌈R⌉ : ℤ) ≤ p j := by
        have : (p₀ j : ℝ) - (⌈R⌉ : ℝ) ≤ (p j : ℝ) := by linarith
        exact_mod_cast this
      have hhi : p j ≤ p₀ j + ⌈R⌉ := by
        have : (p j : ℝ) ≤ (p₀ j : ℝ) + (⌈R⌉ : ℝ) := by linarith
        exact_mod_cast this
      exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
    have hB : ∀ j, ((B j).card : ℝ) ≤ 2 * R + 3 := by
      intro j
      have hc : ((B j).card : ℝ) = 2 * (⌈R⌉ : ℝ) + 1 := by
        dsimp [B]
        have hcalc := Int.card_Icc_of_le (p₀ j - ⌈R⌉) (p₀ j + ⌈R⌉)
          (show p₀ j - ⌈R⌉ ≤ p₀ j + ⌈R⌉ + 1 by omega)
        exact_mod_cast (by omega :
          ((Finset.Icc (p₀ j - ⌈R⌉) (p₀ j + ⌈R⌉)).card : ℤ) = 2 * ⌈R⌉ + 1)
      rw [hc]
      linarith [Int.ceil_lt_add_one R]
    calc
      (P.card : ℝ) ≤ ((Fintype.piFinset B).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ = ∏ j, ((B j).card : ℝ) := by rw [Fintype.card_piFinset, Nat.cast_prod]
      _ ≤ ∏ _j : ι, (2 * R + 3) :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hB j)
      _ = (2 * R + 3) ^ Fintype.card ι := by simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hP, Finset.card_empty, Nat.cast_zero]
    positivity


/-- Many witnesses per projection cell, with bounded local overlap, bound the projection cover. -/
theorem projection_cover_of_witnesses {X ι : Type*} [DecidableEq X]
    [Fintype ι] [DecidableEq ι]
    (P : Finset X) (C : Finset (ι → ℤ)) (W : (ι → ℤ) → Finset X)
    (f : X → ι → ℝ) {R L : ℝ} (hR : 0 ≤ R)
    (hW : ∀ c ∈ C, W c ⊆ P)
    (hlarge : ∀ c ∈ C, L ≤ ((W c).card : ℝ))
    (hnear : ∀ c ∈ C, ∀ p ∈ W c, ∀ j, |f p j - (c j : ℝ)| ≤ R) :
    (C.card : ℝ) * L ≤ (P.card : ℝ) * (4 * R + 3) ^ Fintype.card ι := by
  classical
  have habove : ∀ c ∈ C, P.bipartiteAbove (fun c p => p ∈ W c) c = W c := by
    intro c hc
    ext p
    simp only [Finset.mem_bipartiteAbove]
    exact ⟨fun hp => hp.2, fun hp => ⟨hW c hc hp, hp⟩⟩
  have hbelow : ∀ p ∈ P,
      ((C.bipartiteBelow (fun c p => p ∈ W c) p).card : ℝ) ≤
        (4 * R + 3) ^ Fintype.card ι := by
    intro p hp
    have hd : ∀ c ∈ C.bipartiteBelow (fun c p => p ∈ W c) p,
        ∀ c' ∈ C.bipartiteBelow (fun c p => p ∈ W c) p,
        ∀ j, |(c j : ℝ) - (c' j : ℝ)| ≤ 2 * R := by
      intro c hc c' hc' j
      obtain ⟨hc, hwc⟩ := Finset.mem_filter.mp hc
      obtain ⟨hc', hwc'⟩ := Finset.mem_filter.mp hc'
      have h₁ := hnear c hc p hwc j
      have h₂ := hnear c' hc' p hwc' j
      calc
        _ ≤ |(c j : ℝ) - f p j| + |f p j - (c' j : ℝ)| := abs_sub_le _ _ _
        _ ≤ 2 * R := by rw [abs_sub_comm] at h₁; linarith
    simpa only [show 2 * (2 * R) + 3 = 4 * R + 3 by ring] using
      card_pi_grid_of_diameter _ (show 0 ≤ 2 * R by positivity) hd
  have hdouble := Finset.card_nsmul_le_card_nsmul (R := ℝ)
    (r := fun c p => p ∈ W c) (s := C) (t := P)
    (m := L) (n := (4 * R + 3) ^ Fintype.card ι)
    (fun c hc => by rw [habove c hc]; exact hlarge c hc) hbelow
  simpa only [nsmul_eq_mul] using hdouble

/-- Long trajectory time witnesses give the finite projection cover used in the graph reduction. -/
theorem projection_cover_of_time_witnesses {X ι : Type*} [DecidableEq X]
    [Fintype ι] [DecidableEq ι]
    (P : Finset X) (C : Finset (ι → ℤ)) (W : (ι → ℤ) → Finset X)
    (f : X → ι → ℝ) (timeIndex : X → ℤ) (times : (ι → ℤ) → Set ℝ)
    {h r R : ℝ} (hh : 0 < h) (hR : 0 ≤ R)
    (hW : ∀ c ∈ C, W c ⊆ P)
    (htime : ∀ c ∈ C, ∀ t ∈ times c, ∃ p ∈ W c, timeIndex p = ⌊t / h⌋)
    (hlength : ∀ c ∈ C, ENNReal.ofReal r ≤ MeasureTheory.volume (times c))
    (hnear : ∀ c ∈ C, ∀ p ∈ W c, ∀ j, |f p j - (c j : ℝ)| ≤ R) :
    (C.card : ℝ) * (r / h) ≤ (P.card : ℝ) * (4 * R + 3) ^ Fintype.card ι :=
  projection_cover_of_witnesses P C W f hR hW
    (fun c hc => time_labels_card_lower (W c) timeIndex (times c) hh (htime c hc) (hlength c hc))
    hnear


end Submission.Lib.K4IncidenceWitnesses
