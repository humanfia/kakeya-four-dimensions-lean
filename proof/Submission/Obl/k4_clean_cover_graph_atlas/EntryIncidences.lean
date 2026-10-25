-- Adapted from this LOT tree o194, session x0674 via x0672,
-- commit69d09a7b, Submission/Obl/k4_greedy_cover_graph_atlas/EntryIncidences.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.EntryPartition
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Submission.Lib.K4XInterface

/-- A finite cover indexed over candidates preserves total weighted mass. -/
theorem weighted_cover_mass_le {X α β : Type*} [MeasurableSpace X]
    [Fintype α] [Fintype β] (parent : β → α) (μ : α → Measure X)
    (weight : α → ENNReal) (V : α → Set X) (U : β → Set X)
    (hcover : ∀ a, ∀ p ∈ V a, ∃ e, parent e = a ∧ p ∈ U e) :
    (∑ a, weight a * μ a (V a)) ≤ ∑ e, weight (parent e) * μ (parent e) (U e) := by
  classical
  have hm (a : α) : μ a (V a) ≤ ∑ e : β, if parent e = a then μ a (U e) else 0 := by
    have hsub : V a ⊆ ⋃ e : β, if parent e = a then U e else ∅ := by
      intro p hp
      obtain ⟨e, he, hpe⟩ := hcover a p hp
      exact mem_iUnion.mpr ⟨e, by simpa only [ite_eq_left he] using hpe⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans_eq ?_)
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp_all
  calc
    _ ≤ ∑ a : α, weight a * ∑ e : β, if parent e = a then μ a (U e) else 0 :=
      Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (hm a)
    _ = ∑ e : β, ∑ a : α, if parent e = a then weight a * μ a (U e) else 0 := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      exact Finset.sum_comm
    _ = _ := by simp

/-- Disjoint members of a finite refinement stay within the original candidate mass. -/
theorem weighted_subpartition_mass_le {X α β : Type*} [MeasurableSpace X]
    [Fintype α] [Fintype β] (parent : β → α) (μ : α → Measure X)
    (weight : α → ENNReal) (V : α → Set X) (U : β → Set X)
    (hUm : ∀ e, MeasurableSet (U e))
    (hdisj : ∀ e e', e ≠ e' → parent e = parent e' → Disjoint (U e) (U e'))
    (hsub : ∀ e, U e ⊆ V (parent e)) :
    (∑ e, weight (parent e) * μ (parent e) (U e)) ≤ ∑ a, weight a * μ a (V a) := by
  classical
  have hmass := Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
    μ weight (fun _ : β => True) parent U (fun e _ => hUm e)
    (fun e e' _ _ hne he => hdisj e e' hne he)
  simp only [ite_true] at hmass
  rw [← hmass]
  refine Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (measure_mono ?_)
  rintro p ⟨e, _, he, hp⟩
  simpa only [he] using hsub e hp

section Incidences

variable {n C : ℕ} (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
  (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (j : Fin C → ℕ)
  (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
  (R : Fin C → MvPolynomial (Fin 4) ℝ) (Ti s₀ K : ℕ)
  (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))

/-- The original incidences of a candidate assigned to an entry. -/
def entryIncidences (e : Entry n s₀ K) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {p | p ∈ V e.1 ∧ p.1 ∈ memE old R' A' j c u Q R Ti s₀ K e ∧
    p.2 ∈ subBlock Ti s₀ (j (old e.1)) e.2.1}

/-- The entry incidence sets are measurable whenever their input assignments have format. -/
theorem measurableSet_entryIncidences {H : ℝ} {Dg : ℕ}
    (hA' : ∀ a q, Submission.Lib.K4XInterface.gfmt 6 H Dg {z | (q, z) ∈ A' a})
    (hR' : ∀ a, (R' a).totalDegree ≤ 2) (hR : ∀ b, (R b).totalDegree ≤ 2)
    (hV : ∀ a, MeasurableSet (V a)) (e : Entry n s₀ K) :
    MeasurableSet (entryIncidences old R' A' j c u Q R Ti s₀ K V e) := by
  have hm : MeasurableSet (memE old R' A' j c u Q R Ti s₀ K e) :=
    measurableSet_of_slices6 fun q =>
      measurableSet_of_gfmt (gfmt_memE hA' hR' hR e q)
  exact (hV e.1).inter ((hm.preimage measurable_fst).inter
    (measurableSet_Icc.preimage measurable_snd))

/-- Half-open entry incidences remove only a time endpoint. -/
def openEntryIncidences (e : Entry n s₀ K) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  entryIncidences old R' A' j c u Q R Ti s₀ K V e ∩
    {p | p.2 < ((subIdx s₀ (j (old e.1)) e.2.1 : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)}

theorem openEntryIncidences_mass (ν : Measure (ℕ × (Fin 6 → ℝ))) (e : Entry n s₀ K) :
    (ν.prod volume) (openEntryIncidences old R' A' j c u Q R Ti s₀ K V e) =
      (ν.prod volume) (entryIncidences old R' A' j c u Q R Ti s₀ K V e) := by
  exact Submission.Obl.k4_quadratic_finite_greedy_cover.measure_trim_right ν
    (entryIncidences old R' A' j c u Q R Ti s₀ K V e) _ (fun p hp => hp.2.2.2)

/-- At one candidate, the half-open entry incidences form a disjoint refinement. -/
theorem openEntryIncidences_disjoint {e e' : Entry n s₀ K} (hne : e ≠ e') (ha : e.1 = e'.1) :
    Disjoint (openEntryIncidences old R' A' j c u Q R Ti s₀ K V e)
      (openEntryIncidences old R' A' j c u Q R Ti s₀ K V e') := by
  let I := {f : Entry n s₀ K // f.1 = e.1}
  have hd := Submission.Obl.k4_quadratic_finite_greedy_cover.halfOpen_packets_disjoint
    (fun f : I => memE old R' A' j c u Q R Ti s₀ K f.val)
    (fun f : I => subIdx s₀ (j (old f.val.1)) f.val.2.1)
    ((2 : ℝ) ^ (Ti + s₀)) (by positivity) (fun f f' hff hblock => ?_)
  · have he : (⟨e, rfl⟩ : I) ≠ ⟨e', ha.symm⟩ := by
      intro h
      exact hne (congrArg Subtype.val h)
    refine (hd he).mono ?_ ?_
    · rintro p ⟨hp, hpright⟩
      exact ⟨hp.2.1, hp.2.2.1, hpright⟩
    · rintro p ⟨hp, hpright⟩
      exact ⟨hp.2.1, hp.2.2.1, hpright⟩
  · have hajj : f.val.1 = f'.val.1 := f.property.trans f'.property.symm
    obtain ⟨_, hjj⟩ := subIdx_inj f.val.2.1.isLt f'.val.2.1.isLt hblock
    exact memE_disjoint_of_ne old R' A' j c u Q R Ti s₀ K hajj (Fin.ext hjj)
      (fun h => hff (Subtype.ext h))

/-- Every original candidate incidence is covered by an entry at the same candidate. -/
theorem entryIncidences_cover
    (hV : ∀ a, ∀ p ∈ V a, p.1 ∈ A' a ∧
      p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ Ti)
        (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti))
    (hz : ∀ a, ∀ l ∈ A' a, ∀ jj : Fin (2 ^ s₀),
      ‖zc (Q (old a)) (c (old a)) (u (old a)) l (subMid Ti s₀ (j (old a)) jj)‖ ≤ K * side s₀)
    (a : Fin n) {p : (ℕ × (Fin 6 → ℝ)) × ℝ} (hp : p ∈ V a) :
    ∃ e : Entry n s₀ K, e.1 = a ∧
      p ∈ entryIncidences old R' A' j c u Q R Ti s₀ K V e := by
  obtain ⟨hpA, hpt⟩ := hV a p hp
  obtain ⟨jj, hjj⟩ := exists_subBlock (s₀ := s₀) hpt
  obtain ⟨e, he, hejj, hpe⟩ := exists_memE old R' A' j c u Q R Ti s₀ K hpA (hz a p.1 hpA jj)
  refine ⟨e, he, ?_, hpe, ?_⟩
  · simpa only [he] using hp
  · simpa only [he, hejj] using hjj

/-- Refining a greedy cover into entries retains at least its original weighted mass. -/
theorem weighted_entryIncidences_mass_le {W : ℕ} (γ : Fin C → Fin W)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (weight : Fin W → ENNReal)
    (hV : ∀ a, ∀ p ∈ V a, p.1 ∈ A' a ∧
      p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ Ti)
        (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti))
    (hz : ∀ a, ∀ l ∈ A' a, ∀ jj : Fin (2 ^ s₀),
      ‖zc (Q (old a)) (c (old a)) (u (old a)) l (subMid Ti s₀ (j (old a)) jj)‖ ≤ K * side s₀) :
    (∑ a, weight (γ (old a)) * ((ν (γ (old a))).prod volume) (V a)) ≤
      ∑ e : Entry n s₀ K, weight (γ (old e.1)) * ((ν (γ (old e.1))).prod volume)
        (entryIncidences old R' A' j c u Q R Ti s₀ K V e) := by
  exact weighted_cover_mass_le (fun e : Entry n s₀ K => e.1)
    (fun a => (ν (γ (old a))).prod volume) (fun a => weight (γ (old a))) V
    (entryIncidences old R' A' j c u Q R Ti s₀ K V)
    (fun a p hp => entryIncidences_cover old R' A' j c u Q R Ti s₀ K V hV hz a hp)

/-- Entry refinement preserves the full original weighted incidence mass, including
when the candidate masses are unequal. -/
theorem weighted_entryIncidences_mass {W : ℕ} (γ : Fin C → Fin W)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (weight : Fin W → ENNReal)
    {H : ℝ} {Dg : ℕ}
    (hA' : ∀ a q, gfmt 6 H Dg {z | (q, z) ∈ A' a})
    (hR' : ∀ a, (R' a).totalDegree ≤ 2) (hR : ∀ b, (R b).totalDegree ≤ 2)
    (hVm : ∀ a, MeasurableSet (V a))
    (hV : ∀ a, ∀ p ∈ V a, p.1 ∈ A' a ∧
      p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ Ti)
        (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ Ti))
    (hz : ∀ a, ∀ l ∈ A' a, ∀ jj : Fin (2 ^ s₀),
      ‖zc (Q (old a)) (c (old a)) (u (old a)) l (subMid Ti s₀ (j (old a)) jj)‖ ≤ K * side s₀) :
    (∑ e : Entry n s₀ K, weight (γ (old e.1)) * ((ν (γ (old e.1))).prod volume)
      (entryIncidences old R' A' j c u Q R Ti s₀ K V e)) =
        ∑ a, weight (γ (old a)) * ((ν (γ (old a))).prod volume) (V a) := by
  apply le_antisymm
  · have hu (e : Entry n s₀ K) :
        MeasurableSet (openEntryIncidences old R' A' j c u Q R Ti s₀ K V e) :=
      (measurableSet_entryIncidences old R' A' j c u Q R Ti s₀ K V hA' hR' hR hVm e).inter
        (measurableSet_lt measurable_snd measurable_const)
    have hmass := weighted_subpartition_mass_le (fun e : Entry n s₀ K => e.1)
      (fun a => (ν (γ (old a))).prod volume) (fun a => weight (γ (old a))) V
      (openEntryIncidences old R' A' j c u Q R Ti s₀ K V) hu
      (fun e e' hne ha => openEntryIncidences_disjoint old R' A' j c u Q R Ti s₀ K V hne ha)
      (fun e p hp => hp.1.1)
    simpa only [openEntryIncidences_mass] using hmass
  · exact weighted_entryIncidences_mass_le old R' A' j c u Q R Ti s₀ K V γ ν weight hV hz

end Incidences

end Submission.Obl.k4_clean_cover_graph_atlas
