import Submission.Obl.k4_scalar_marked_packet_recovery.Restoration
import Submission.Obl.k4_scalar_marked_packet_recovery.Pruning

namespace Submission.Obl.k4_scalar_marked_packet_recovery

open Set MeasureTheory
open scoped ENNReal

abbrev originalAssignment {α : Type*} {H : ℕ} (b₀ : Fin H → Coeff)
    (tag : α → Fin H) (u : Coeff) (A : Set Label) : Set α :=
  {l | embed b₀ (tag l) u ∈ A}

theorem measurableSet_originalAssignment {α : Type*} [MeasurableSpace α] {H : ℕ}
    (b₀ : Fin H → Coeff) {tag : α → Fin H} (htag : Measurable tag) (u : Coeff)
    {A : Set Label} (hA : MeasurableSet A) :
    MeasurableSet (originalAssignment b₀ tag u A) :=
  hA.preimage ((measurable_of_finite (fun j => embed b₀ j u)).comp htag)

theorem originalAssignment_disjoint {α : Type*} {H : ℕ} (b₀ : Fin H → Coeff)
    (tag : α → Fin H) (u : Coeff) {A B : Set Label} (hAB : Disjoint A B) :
    Disjoint (originalAssignment b₀ tag u A) (originalAssignment b₀ tag u B) := by
  exact Set.disjoint_left.mpr fun l hl hl' => Set.disjoint_left.mp hAB hl hl'

/-- Every common-jitter slice restores by the original marked-cell inequalities. -/
theorem restore_sliceMass {α : Type*} [MeasurableSpace α] {H J : ℕ} (hJ : 0 < J)
    (μ : Measure (α × ℝ)) (tag : α → Fin H) (htag : Measurable tag)
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (mark : Fin H → Fin J → Bool) {K : ℝ} (hK : 0 < K)
    (hfloor : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z}) (A : Set Label) (u : Coeff) :
    sliceMass b₀ w mark A u ≤ ENNReal.ofReal K *
      μ (originalAssignment b₀ tag u A ×ˢ Icc (0 : ℝ) 1) := by
  classical
  let S := Finset.univ.filter (fun j => embed b₀ j u ∈ A)
  have h := restore_tag_set hJ μ tag htag w hw mark hK hfloor S
  convert h using 1
  · simp only [S, Finset.sum_filter, sliceMass]
  · congr 1
    congr 1
    ext p
    simp [S, originalAssignment]

/-- Recover a common jitter and original assignments with floors, after pruning. -/
theorem recover_assignment_mass {α : Type*} [MeasurableSpace α]
    {σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K) {H J n : ℕ} (hJ : 0 < J)
    (μ : Measure (α × ℝ)) (tag : α → Fin H) (htag : Measurable tag)
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (mark : Fin H → Fin J → Bool)
    (hfloor : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z})
    (A : Fin n → Set Label) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    {a : ℝ} (ha : 0 < a)
    (hmass : ENNReal.ofReal a ≤ MarkedLaw σ H J b₀ w mark ((⋃ i, A i) ×ˢ (univ : Set ℝ)))
    {f : ℝ≥0∞} (hbudget : (n : ℝ≥0∞) * f ≤ ENNReal.ofReal (a / (4 * K))) :
    ∃ (u : Coeff), (∀ e, u e ∈ Icc (0 : ℝ) σ) ∧
      ∃ (n' : ℕ) (e : Fin n' → Fin n), Function.Injective e ∧
        (∀ i, f ≤ μ (originalAssignment b₀ tag u (A (e i)) ×ˢ Icc (0 : ℝ) 1)) ∧
        ENNReal.ofReal (a / (4 * K)) ≤
          μ {p | ∃ i, p.1 ∈ originalAssignment b₀ tag u (A (e i))} := by
  classical
  obtain ⟨u, hu, hslice⟩ := exists_common_jitter hσ b₀ w mark
    (MeasurableSet.iUnion hA) ha hmass
  let B : Fin n → Set α := fun i => originalAssignment b₀ tag u (A i)
  let C : Fin n → Set (α × ℝ) := fun i => B i ×ˢ Icc (0 : ℝ) 1
  have hB : ∀ i, MeasurableSet (B i) :=
    fun i => measurableSet_originalAssignment b₀ htag u (hA i)
  have hC : ∀ i, MeasurableSet (C i) := fun i => (hB i).prod measurableSet_Icc
  have hCdisj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact Set.disjoint_left.mp (originalAssignment_disjoint b₀ tag u (hdisj hij)) hp.1 hp'.1
  have hrestore := restore_sliceMass hJ μ tag htag b₀ w hw mark hK hfloor (⋃ i, A i) u
  have heq : originalAssignment b₀ tag u (⋃ i, A i) ×ˢ Icc (0 : ℝ) 1 = ⋃ i, C i := by
    ext p
    simp [originalAssignment, C, B]
  rw [heq] at hrestore
  have hhalf : ENNReal.ofReal ((a / 2) / K) ≤ μ (⋃ i, C i) := by
    rw [ENNReal.ofReal_div_of_pos hK]
    apply (ENNReal.div_le_iff (by positivity) ENNReal.ofReal_ne_top).mpr
    simpa only [mul_comm] using hslice.trans hrestore
  have htwo : ENNReal.ofReal (a / (4 * K)) + ENNReal.ofReal (a / (4 * K)) ≤
      μ (⋃ i, C i) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    convert hhalf using 1
    congr 1
    field_simp
    <;> ring
  obtain ⟨n', e, he, hf, hm⟩ := prune_finite_sets μ C hC hCdisj
    ENNReal.ofReal_ne_top htwo hbudget
  refine ⟨u, hu, n', e, he, hf, hm.trans (measure_mono ?_)⟩
  intro p hp
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  exact ⟨i, hi.1⟩

end Submission.Obl.k4_scalar_marked_packet_recovery
