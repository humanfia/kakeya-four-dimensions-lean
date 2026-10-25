import Submission.Lib.K4ContactNormalization.AffineTimeTransfer
import Submission.Obl.k4_quadratic_atlas_normalization.Endpoints
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory MvPolynomial Set
open Submission.Lib.K4ContactNormalization

/-- A palette entry is tested on the entire original assigned block. -/
def affineFitSet {α : Type*} (b : α → Fin 6 → ℝ) (L : Fin 4 → ℝ)
    (s e E : ℝ) : Set α :=
  {l | ∀ t ∈ Icc s e, |eval (point (b l) t) (affineBase L) - point (b l) t 3| ≤ E}

theorem mem_affineFitSet_iff_endpoints {α : Type*} (b : α → Fin 6 → ℝ)
    (L : Fin 4 → ℝ) {s e E : ℝ} (hse : s ≤ e) (l : α) :
    l ∈ affineFitSet b L s e E ↔
      |eval (point (b l) s) (affineBase L) - point (b l) s 3| ≤ E ∧
      |eval (point (b l) e) (affineBase L) - point (b l) e 3| ≤ E := by
  constructor
  · intro h
    exact ⟨h s ⟨le_rfl, hse⟩, h e ⟨hse, le_rfl⟩⟩
  · rintro ⟨hs, he⟩ t ht
    rw [affine_hidden_residual] at hs he ⊢
    exact (Submission.Obl.k4_quadratic_atlas_normalization.abs_affine_le_endpoint_max
      _ _ s e t ht).trans (max_le hs he)

theorem measurableSet_affineFitSet {α : Type*} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (L : Fin 4 → ℝ)
    {s e E : ℝ} (hse : s ≤ e) : MeasurableSet (affineFitSet b L s e E) := by
  have hres (t : ℝ) : Measurable (fun l =>
      eval (point (b l) t) (affineBase L) - point (b l) t 3) := by
    simp_rw [affine_hidden_residual]
    have hcoord (i : Fin 6) : Measurable (fun l => b l i) :=
      (measurable_pi_apply i).comp hb
    fun_prop
  have hset : affineFitSet b L s e E =
      {l | |eval (point (b l) s) (affineBase L) - point (b l) s 3| ≤ E} ∩
      {l | |eval (point (b l) e) (affineBase L) - point (b l) e 3| ≤ E} := by
    ext l
    exact mem_affineFitSet_iff_endpoints b L hse l
  rw [hset]
  exact (measurableSet_le (hres s).abs measurable_const).inter
    (measurableSet_le (hres e).abs measurable_const)

/-- Assign the first successful entry without changing the original true label. -/
def assignedAffineEntry {α : Type*} {m : ℕ} (b : α → Fin 6 → ℝ)
    (B : Set α) (L : Fin m → Fin 4 → ℝ) (s e E : ℝ) (u : Fin m) : Set α :=
  (B ∩ affineFitSet b (L u) s e E) \ ⋃ v ∈ Finset.Iio u, affineFitSet b (L v) s e E

theorem measurableSet_assignedAffineEntry {α : Type*} [MeasurableSpace α]
    {m : ℕ} (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (B : Set α) (hB : MeasurableSet B) (L : Fin m → Fin 4 → ℝ)
    {s e E : ℝ} (hse : s ≤ e) (u : Fin m) :
    MeasurableSet (assignedAffineEntry b B L s e E u) := by
  apply (hB.inter (measurableSet_affineFitSet b hb (L u) hse)).diff
  exact MeasurableSet.biUnion (Finset.Iio u).countable_toSet
    (fun v _ => measurableSet_affineFitSet b hb (L v) hse)

theorem assignedAffineEntry_subset {α : Type*} {m : ℕ}
    (b : α → Fin 6 → ℝ) (B : Set α) (L : Fin m → Fin 4 → ℝ)
    (s e E : ℝ) (u : Fin m) :
    assignedAffineEntry b B L s e E u ⊆ B ∩ affineFitSet b (L u) s e E :=
  sdiff_subset

theorem disjoint_assignedAffineEntry {α : Type*} {m : ℕ}
    (b : α → Fin 6 → ℝ) (B : Set α) (L : Fin m → Fin 4 → ℝ)
    (s e E : ℝ) : Pairwise (fun u v =>
      Disjoint (assignedAffineEntry b B L s e E u) (assignedAffineEntry b B L s e E v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro l hu hv
  rcases lt_or_gt_of_ne huv with huv | hvu
  · exact hv.2 (mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨Finset.mem_Iio.mpr huv, hu.1.2⟩⟩)
  · exact hu.2 (mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨Finset.mem_Iio.mpr hvu, hv.1.2⟩⟩)

theorem iUnion_assignedAffineEntry {α : Type*} {m : ℕ}
    (b : α → Fin 6 → ℝ) (B : Set α) (L : Fin m → Fin 4 → ℝ)
    (s e E : ℝ) :
    (⋃ u, assignedAffineEntry b B L s e E u) =
      B ∩ ⋃ u, affineFitSet b (L u) s e E := by
  classical
  ext l
  constructor
  · intro hl
    obtain ⟨u, hu⟩ := mem_iUnion.mp hl
    exact ⟨hu.1.1, mem_iUnion.mpr ⟨u, hu.1.2⟩⟩
  · rintro ⟨hlB, hl⟩
    obtain ⟨u, hu⟩ := mem_iUnion.mp hl
    let S := Finset.univ.filter (fun v : Fin m => l ∈ affineFitSet b (L v) s e E)
    have hS : S.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
    let v := S.min' hS
    have hv : l ∈ affineFitSet b (L v) s e E :=
      (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    apply mem_iUnion.mpr
    refine ⟨v, ⟨hlB, hv⟩, ?_⟩
    intro hlw
    obtain ⟨w, hw⟩ := mem_iUnion.mp hlw
    obtain ⟨hwv, hfit⟩ := mem_iUnion.mp hw
    have hwS : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfit⟩
    exact (not_lt_of_ge (Finset.min'_le S w hwS)) (Finset.mem_Iio.mp hwv)

/-- Full assignment references are summable before any successful affine
entry is selected. The dyadic number of blocks cancels their common length. -/
theorem full_assignment_reference_sum_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {n T : ℕ}
    (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set α)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) :
    (∑ i, ENNReal.ofReal ((2 : ℝ) ^ (-(T : ℤ))) * ν (A i)) ≤ 1 := by
  have hbudget := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget
    (fun _ : Unit => ν) (fun _ : Unit => (1 : ENNReal)) (fun _ : Fin n => ()) j A
    (fun _ => measure_univ) (by simp) hA (fun i i' hne _ heq => hdisj i i' hne heq)
  simp only [one_mul, Fintype.card_fin] at hbudget
  rw [← Finset.mul_sum]
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(T : ℤ))) * (2 ^ T : ℕ) := by gcongr
    _ = 1 := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      have hcast : ((2 ^ T : ℕ) : ℝ) = (2 : ℝ) ^ T := by norm_cast
      rw [hcast]
      simp [zpow_neg, zpow_natCast]

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
