import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.FrameCore
import Submission.Obl.k4_contact_shifted_quadratic_candidates.SourceGood
import Submission.Obl.k4_contact_shifted_quadratic_candidates.HistoryNumerics

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

noncomputable section

/-- A finite successful affine source yields a clean original-law core in
one parent, with every descendant floor retained after parent selection. -/
theorem frame_source_has_parent_core
    {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' E : ℝ}
    (f : Frame D k s₀ U') (hK : 0 < D.K k) (hM : 1 ≤ f.M)
    (hν : IsProbabilityMeasure (D.ν k)) (hb : Measurable (D.b k))
    (hdom : D.μ k ≤ ENNReal.ofReal (D.K k) • (D.ν k).prod volume)
    (hρ : D.ρ k ≤ D.μ k) (hcontact : ∀ᵐ p ∂D.μ k, |D.b k p.1 4 + D.b k p.1 0| ≤ E)
    (hmeas : ∀ h i, MeasurableSet (D.A k (f.depth h) i) ∧ MeasurableSet (D.B k (f.depth h) i))
    (hdisj : ∀ h i i', i ≠ i' → D.j k (f.depth h) i = D.j k (f.depth h) i' →
      Disjoint (D.A k (f.depth h) i) (D.A k (f.depth h) i'))
    (hnest : ∀ h i, D.A k (f.depth (h + 1)) i ⊆ D.A k (f.depth h) (f.anc h i) ∧
      f.block (h + 1) i ⊆ f.block h (f.anc h i))
    (S : Set (α × ℝ)) (hS : MeasurableSet S)
    (hsuccess : ∀ p ∈ S, ∀ h ≤ f.m, ∃ i u,
      p ∈ (D.A k (f.depth h) i ∩ f.entry h i u) ×ˢ f.block h i)
    (hmass : ENNReal.ofReal ((D.K k)⁻¹ / 2) ≤ D.ρ k S) :
    let θ := historyFloorFraction (D.K k) f.M f.m
    ∃ (i₀ : Fin (f.nl 0)) (u₀ : Fin f.M) (C : Set (α × ℝ)),
      MeasurableSet C ∧ C.Nonempty ∧ C ⊆ S ∧ C ⊆ f.event 0 i₀ u₀ ∧
      ENNReal.ofReal (θ * f.ql 0) * D.ν k (D.A k (f.depth 0) i₀) ≤ D.ρ k C ∧
      (∀ p ∈ C, |D.b k p.1 4 + D.b k p.1 0| ≤ E) ∧
      (∀ p ∈ C, ∀ h ≤ f.m, ∃ i u, p ∈ f.event h i u) ∧
      ∀ h ≤ f.m, ∀ i u, (f.event h i u ∩ C).Nonempty →
        f.block h i ⊆ f.block 0 i₀ ∧ f.hist h i u ⊆ f.hist 0 i₀ u₀ ∧
        ENNReal.ofReal (θ * f.ql h) * D.ν k (D.A k (f.depth h) i) ≤
          D.ρ k (f.event h i u ∩ C) := by
  classical
  letI : IsProbabilityMeasure (D.ν k) := hν
  obtain ⟨G, hGm, hGS, hGmass, hGend, hGcontact⟩ :=
    clean_source_mass (D.ν k) (D.μ k) (D.ρ k) (ENNReal.ofReal (D.K k)) hdom hρ
      (D.b k) hb E hcontact f.nl f.Tl (fun h => D.j k (f.depth h)) S hS
  have huniq (p : α × ℝ) (hp : p ∈ G) :=
    original_labels_unique_on_endpointGood f.nl f.Tl (fun h => D.j k (f.depth h))
      (fun h => D.A k (f.depth h)) hdisj p (hGend p hp)
  have hrootuniq : ∀ p ∈ G, ∀ (i i' : Fin (f.nl 0)) (u u' : Fin f.M),
      p ∈ f.event 0 i u → p ∈ f.event 0 i' u' → i = i' ∧ u = u' := by
    intro p hp i i' u u' hi hi'
    have hii : i = i' := huniq p hp 0 i i' ⟨hi.1.1, hi.2⟩ ⟨hi'.1.1, hi'.2⟩
    subst i'
    refine ⟨rfl, ?_⟩
    by_contra huu
    have hd := disjoint_assignedAffineEntry (D.b k) (D.B k (f.depth 0) i)
      (f.pal 0 i) (f.left 0 i) (f.right 0 i) (f.H * D.N k ^ (-f.depth 0)) huu
    exact Set.disjoint_left.mp hd hi.1.2 hi'.1.2
  have hcover : ∀ p ∈ G, ∀ h ≤ f.m, ∃ i u, p ∈ f.event h i u := by
    intro p hp h hh
    exact exists_historyIncidence f.nl (fun h => D.A k (f.depth h)) f.entry f.anc f.block
      hnest p h (fun r _ => huniq p hp r)
      (fun r hr => hsuccess p (hGS hp) r (hr.trans hh))
  have hentrymeas : ∀ h i u, MeasurableSet (f.entry h i u) := by
    intro h i u
    apply measurableSet_assignedAffineEntry (D.b k) hb _ (hmeas h i).2 (f.pal h i) _ u
    dsimp only [Frame.left, Frame.right]
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hhistmeas : ∀ h i u, MeasurableSet (f.hist h i u) :=
    measurableSet_historyAssignment f.nl (fun h => D.A k (f.depth h)) f.entry f.anc
      (fun h i => (hmeas h i).1) hentrymeas
  have heventmeas : ∀ h ≤ f.m, ∀ i u, MeasurableSet (f.event h i u) := by
    intro h _ i u
    exact (hhistmeas h i u).prod measurableSet_Icc
  have hbudget : ∀ h ≤ f.m,
      (∑ i, ENNReal.ofReal (f.ql h) * D.ν k (D.A k (f.depth h) i)) ≤ 1 := by
    intro h _
    exact full_assignment_reference_sum_le (D.ν k) (D.j k (f.depth h)) (D.A k (f.depth h))
      (fun i => (hmeas h i).1) (hdisj h)
  have hcost : ENNReal.ofReal (historyFloorFraction (D.K k) f.M f.m) *
      (((f.m + 1 : ℕ) : ℝ≥0∞) * (f.M : ℝ≥0∞) ^ (f.m + 1)) < D.ρ k G := by
    apply (historyFloorFraction_cost_lt_reserve hK hM).trans_le
    rw [hGmass]
    exact hmass
  obtain ⟨i₀, u₀, C, hCm, hCne, hCG, hCr, hCmasses, hCcover, hCfloor⟩ :=
    frame_exists_parent_core f hM G hGm heventmeas (fun h _ i => (hnest h i).2)
      hrootuniq hcover hbudget (historyFloorFraction_pos hK hM).le hcost
  exact ⟨i₀, u₀, C, hCm, hCne, hCG.trans hGS, hCr, hCmasses,
    (fun p hp => hGcontact p (hCG hp)), hCcover, hCfloor⟩

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
