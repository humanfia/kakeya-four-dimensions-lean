import Submission.Obl.k4_unbounded_geometric_packet_reduction.RecoveredCharts

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

abbrev CandidateIndex {N d s c : ℝ} {M D C : ℕ}
    (out : Fin C → ScalarCandidates N d s c M D) := Σ b, Fin (out b).count

def candidateEquiv {N d s c : ℝ} {M D C : ℕ}
    (out : Fin C → ScalarCandidates N d s c M D) :
    CandidateIndex out ≃ Fin (Fintype.card (CandidateIndex out)) := Fintype.equivFin _

/-- The assembled chart family has one index for each genuine scalar child
of a parent packet.  Its list is read from the original observation. -/
abbrev recoveredAtlas {p : Data} {k M D : ℕ} {d s c : ℝ}
    (a : Atlas p k) (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (out : Fin a.C → ScalarCandidates (p.N k) d s c M D) : Atlas p k where
  T := a.T
  C := Fintype.card (CandidateIndex out)
  γ := fun z => a.γ ((candidateEquiv out).symm z).1
  j := fun z => a.j ((candidateEquiv out).symm z).1
  c := fun z => a.c ((candidateEquiv out).symm z).1
  u := fun z => a.u ((candidateEquiv out).symm z).1
  Q := fun z => a.Q ((candidateEquiv out).symm z).1
  R := fun z => let bi := (candidateEquiv out).symm z
    recoveredTest a offset tangent bi.1 ((out bi.1).poly bi.2)
  A := fun z => let bi := (candidateEquiv out).symm z
    recoveredAssignment a offset tangent bi.1 ((out bi.1).assignment bi.2)
  F := fun z => let bi := (candidateEquiv out).symm z
    recoveredIncidence a offset tangent bi.1 ((out bi.1).assignment bi.2)
  lst := fun w o => ((a.lst w o).sigma (fun b => (out b).lists o)).map
    (candidateEquiv out).toEmbedding

theorem recoveredAtlas_list_mem {p : Data} {k M D : ℕ} {d s c : ℝ}
    (a : Atlas p k) (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (out : Fin a.C → ScalarCandidates (p.N k) d s c M D)
    (w : Fin (p.W k)) (o : EuclideanSpace ℝ (Fin 3) × ℤ)
    (z : Fin (recoveredAtlas a offset tangent out).C) :
    z ∈ (recoveredAtlas a offset tangent out).lst w o ↔
      ((candidateEquiv out).symm z).1 ∈ a.lst w o ∧
      ((candidateEquiv out).symm z).2 ∈ (out ((candidateEquiv out).symm z).1).lists o := by
  classical
  change z ∈ Finset.map _ _ ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨bi, hbi, heq⟩
    have he : bi = (candidateEquiv out).symm z := by
      exact (candidateEquiv out).injective (by simpa using heq)
    subst bi
    exact Finset.mem_sigma.mp hbi
  · intro hz
    exact ⟨(candidateEquiv out).symm z, Finset.mem_sigma.mpr hz, by simp⟩

theorem recoveredAtlas_list_measurable {p : Data} {k M D : ℕ} {d s c : ℝ}
    (a : Atlas p k) (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (out : Fin a.C → ScalarCandidates (p.N k) d s c M D)
    (hm : ∀ w b, MeasurableSet {o | b ∈ a.lst w o}) :
    ∀ w z, MeasurableSet {o | z ∈ (recoveredAtlas a offset tangent out).lst w o} := by
  intro w z
  have heq : {o | z ∈ (recoveredAtlas a offset tangent out).lst w o} =
      {o | ((candidateEquiv out).symm z).1 ∈ a.lst w o} ∩
        {o | ((candidateEquiv out).symm z).2 ∈
          (out ((candidateEquiv out).symm z).1).lists o} := by
    ext o
    exact recoveredAtlas_list_mem a offset tangent out w o z
  rw [heq]
  exact (hm _ _).inter ((out _).list_measurable _)

theorem recoveredAtlas_list_card {p : Data} {k M D : ℕ} {d s c : ℝ}
    (a : Atlas p k) (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (out : Fin a.C → ScalarCandidates (p.N k) d s c M D)
    (w : Fin (p.W k)) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((recoveredAtlas a offset tangent out).lst w o).card ≤ (a.lst w o).card * M := by
  classical
  change (Finset.map _ _).card ≤ _
  rw [Finset.card_map, Finset.card_sigma]
  calc
    _ ≤ ∑ _b ∈ a.lst w o, M := Finset.sum_le_sum (fun b _ => (out b).list_bound o)
    _ = (a.lst w o).card * M := by simp

theorem recoveredAtlas_count {p : Data} {k M D : ℕ} {d s c : ℝ}
    (a : Atlas p k) (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (out : Fin a.C → ScalarCandidates (p.N k) d s c M D) :
    ((recoveredAtlas a offset tangent out).C : ℝ) ≤ (a.C : ℝ) * p.N k ^ (d * s + 1) := by
  change (Fintype.card (CandidateIndex out) : ℝ) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Nat.cast_sum]
  calc
    _ ≤ ∑ _b : Fin a.C, p.N k ^ (d * s + 1) :=
      Finset.sum_le_sum (fun b _ => (out b).count_bound)
    _ = _ := by simp

theorem ProjectedPackets.recovered_disjoint
    {p : Data} {k Mp Dp Mq Dq : ℕ} {loss h η d s m S U c : ℝ}
    (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (out : Fin a.atlas.C → ScalarCandidates (p.N k) d s c Mq Dq) :
    ∀ z z', z ≠ z' →
      (recoveredAtlas a.atlas a.offset a.tangent out).γ z =
        (recoveredAtlas a.atlas a.offset a.tangent out).γ z' →
      (recoveredAtlas a.atlas a.offset a.tangent out).j z =
        (recoveredAtlas a.atlas a.offset a.tangent out).j z' →
      Disjoint ((recoveredAtlas a.atlas a.offset a.tangent out).A z)
        ((recoveredAtlas a.atlas a.offset a.tangent out).A z') := by
  have hdisj (x y : CandidateIndex out) (hne : x ≠ y)
      (hγ : a.atlas.γ x.1 = a.atlas.γ y.1) (hj : a.atlas.j x.1 = a.atlas.j y.1) :
      Disjoint (recoveredAssignment a.atlas a.offset a.tangent x.1 ((out x.1).assignment x.2))
        (recoveredAssignment a.atlas a.offset a.tangent y.1 ((out y.1).assignment y.2)) := by
    rcases x with ⟨b, i⟩
    rcases y with ⟨b', i'⟩
    by_cases hb : b = b'
    · subst b'
      have hi : i ≠ i' := fun hh => hne (by cases hh; rfl)
      apply Set.disjoint_left.mpr
      intro l hl hl'
      exact Set.disjoint_left.mp ((out b).disjoint i i' hi) hl.2 hl'.2
    · exact (a.known.1.2.1 b b' hb hγ hj).mono
        (fun _ hz => hz.1) (fun _ hz => hz.1)
  intro z z' hne hγ hj
  exact hdisj ((candidateEquiv out).symm z) ((candidateEquiv out).symm z')
    (fun hh => hne ((candidateEquiv out).symm.injective hh)) hγ hj

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
