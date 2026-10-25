import Submission.Obl.k4_pair_bin_atlas_assembly.PairTransfer
import Submission.Obl.k4_pair_bin_atlas_assembly.PairAnchor
import Submission.Obl.k4_pair_bin_atlas_assembly.FiniteChoices
import Submission.Obl.k4_pair_bin_atlas_assembly.TimeFreezing

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open scoped ENNReal

namespace PairData

variable {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε)
    {d : ℕ}

def neighbourCompatible (bins : Fin p.m → Finset (Fin d → ℤ))
    (s : Fin p.m) (β : Fin d → ℤ) (v : PairPoint) : Prop :=
  ∃ s' ∈ p.sourceList s v, p.frame s' = p.frame s ∧
    ∃ β' ∈ bins s', ∀ i, |β i - β' i| ≤ 1

theorem measurableSet_neighbourCompatible (bins : Fin p.m → Finset (Fin d → ℤ))
    (s : Fin p.m) (β : Fin d → ℤ) :
    MeasurableSet {v | p.neighbourCompatible bins s β v} := by
  have heq : {v | p.neighbourCompatible bins s β v} = ⋃ s',
      {v | s' ∈ p.sourceList s v} ∩
      {v : PairPoint | p.frame s' = p.frame s ∧ ∃ β' ∈ bins s', ∀ i, |β i - β' i| ≤ 1} := by
    ext v
    simp only [neighbourCompatible, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro s'
  apply (p.measurable_sourceList_membership s s').inter
  by_cases hc : p.frame s' = p.frame s ∧ ∃ β' ∈ bins s', ∀ i, |β i - β' i| ≤ 1
  · simpa [hc] using MeasurableSet.univ (α := PairPoint)
  · simpa [hc] using MeasurableSet.empty (α := PairPoint)

def sourcePairEvent (bins : Fin p.m → Finset (Fin d → ℤ))
    (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)
    (eligible : Fin p.J → (Fin d → ℤ) → Set Trajectory)
    (G : Fin p.m → Set PairPoint) (s : Fin p.m) (β : Fin d → ℤ) : Set PairPoint :=
  {v | v ∈ G s ∧ β ∈ bins s ∧
    (∃ r, p.representative bins α ρ (p.frame s) β = some r) ∧
    v.1 ∈ eligible (p.frame s) β ∧ p.neighbourCompatible bins s β v}

theorem measurableSet_sourcePairEvent (bins : Fin p.m → Finset (Fin d → ℤ))
    (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)
    (eligible : Fin p.J → (Fin d → ℤ) → Set Trajectory)
    (heligible : ∀ b β, MeasurableSet (eligible b β))
    (G : Fin p.m → Set PairPoint) (hG : ∀ s, MeasurableSet (G s))
    (s : Fin p.m) (β : Fin d → ℤ) :
    MeasurableSet (p.sourcePairEvent bins α ρ eligible G s β) := by
  classical
  by_cases hβ : β ∈ bins s
  · by_cases hr : ∃ r, p.representative bins α ρ (p.frame s) β = some r
    · have heq : p.sourcePairEvent bins α ρ eligible G s β =
          (G s ∩ (Prod.fst ⁻¹' eligible (p.frame s) β)) ∩
            {v | p.neighbourCompatible bins s β v} := by
        ext v
        simp only [sourcePairEvent, mem_ofPred_eq, hβ, hr, true_and, mem_inter_iff,
          mem_preimage, and_assoc]
      rw [heq]
      exact ((hG s).inter ((heligible _ _).preimage measurable_fst)).inter
        (p.measurableSet_neighbourCompatible bins s β)
    · have heq : p.sourcePairEvent bins α ρ eligible G s β = ∅ := by
        ext v
        simp only [sourcePairEvent, mem_ofPred_eq, hr, false_and, and_false,
          mem_empty_iff_false]
      rw [heq]
      exact MeasurableSet.empty
  · have heq : p.sourcePairEvent bins α ρ eligible G s β = ∅ := by
      ext v
      simp only [sourcePairEvent, mem_ofPred_eq, hβ, false_and, and_false,
        mem_empty_iff_false]
    rw [heq]
    exact MeasurableSet.empty

/-- Fix one source bin from its finite table, while source time is still
averaged. Every selected event remains a measurable original pair event. -/
theorem choose_source_bins (bins : Fin p.m → Finset (Fin d → ℤ))
    (hbins : ∀ s, (bins s).card ≤ 2)
    (α : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)
    (eligible : Fin p.J → (Fin d → ℤ) → Set Trajectory)
    (heligible : ∀ b β, MeasurableSet (eligible b β))
    (G : Fin p.m → Set PairPoint) (hG : ∀ s, MeasurableSet (G s))
    (hcover : ∀ s, G s ⊆ ⋃ β ∈ bins s, p.sourcePairEvent bins α ρ eligible G s β) :
    ∃ coin : Fin p.m → (Fin d → ℤ),
      (∀ s, (bins s).Nonempty → coin s ∈ bins s) ∧
      (∀ s, MeasurableSet (p.sourcePairEvent bins α ρ eligible G s (coin s))) ∧
      p.pairMass G ≤ 2 * p.pairMass (fun s => p.sourcePairEvent bins α ρ eligible G s (coin s)) := by
  obtain ⟨coin, hcoin, hm⟩ := exists_source_bin_table (fun _ => (0 : ℤ)) p.pairLaw G
    bins hbins (p.sourcePairEvent bins α ρ eligible G) hcover
    (fun s => ENNReal.ofReal (ωk (p.world s) * (2 : ℝ) ^ p.T))
  exact ⟨coin, hcoin,
    (fun s => p.measurableSet_sourcePairEvent bins α ρ eligible heligible G hG s (coin s)), hm⟩

/-- The per-pair kernel covers the explicit measurable source-bin events.
The geometric interpolation step is the `hlift` input. -/
theorem choose_transferred_bins {Cs : ℕ} (k : BinKernel Cs)
    (hNk : 0 < Nk)
    (hAt : k.At Nk a (Submission.Obl.k4_quadratic_atlas_normalization.δ Nk L)
      ((2 : ℝ) ^ p.T) M)
    (θ : AnchorParameter) (hθ : θ ∈ anchorDomain)
    (eligible : Fin p.J → (Fin k.d → ℤ) → Set Trajectory)
    (heligible : ∀ b β, MeasurableSet (eligible b β))
    (hlift : ∀ (s : Fin p.m) (v : PairPoint), v ∈ p.H s →
      ∀ (β : Fin k.d → ℤ) (r : Fin p.m),
      p.representative (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) (p.frame s) β = some r →
      p.shortBounds k s v (p.P r) → v.1 ∈ eligible (p.frame s) β)
    (G : Fin p.m → Set PairPoint) (hG : ∀ s, MeasurableSet (G s))
    (hGH : ∀ s, G s ⊆ p.H s)
    (hsafe : ∀ s, ∀ v ∈ G s, ∀ s' ∈ p.sourceList s v,
      Nk ^ (-a) ≤ |MvPolynomial.eval (fun i => p.sourceBase s v i) (disc (p.P s'))| →
      SafeFor ((Nk ^ a) ^ (-(Cs : ℝ))) (disc (p.P s)) (disc (p.P s'))
        (p.sourceBase s v) θ.1 θ.2) :
    ∃ coin : Fin p.m → (Fin k.d → ℤ),
      (∀ s, (p.bins k θ.1 s).Nonempty → coin s ∈ p.bins k θ.1 s) ∧
      (∀ s, MeasurableSet (p.sourcePairEvent (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ)))
        eligible G s (coin s))) ∧
      p.pairMass G ≤ 2 * p.pairMass (fun s => p.sourcePairEvent (p.bins k θ.1) θ.1
        ((Nk ^ a) ^ (-(Cs : ℝ))) eligible G s (coin s)) := by
  have hcover (s : Fin p.m) : G s ⊆ ⋃ β ∈ p.bins k θ.1 s,
      p.sourcePairEvent (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) eligible G s β := by
    intro v hv
    obtain ⟨β, hβ, r, hr, hnear, hshort⟩ :=
      p.exists_short_representative k hNk hAt θ hθ s v (hGH s hv) (hsafe s v hv)
    refine Set.mem_iUnion.mpr ⟨β, Set.mem_iUnion.mpr ⟨hβ, ?_⟩⟩
    exact ⟨hv, hβ, ⟨r, hr⟩, hlift s v (hGH s hv) β r hr hshort, hnear⟩
  exact p.choose_source_bins (p.bins k θ.1)
    (fun s => k.card_le Nk a _ (p.P s) θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ)))
    eligible heligible G hG hcover

/-- Normalize and freeze the dyadic source time of already selected pair events. -/
theorem freeze_pair_events
    (hν : ∀ w, IsProbabilityMeasure (νk w)) (hω : ∀ w, 0 ≤ ωk w)
    (G : Fin p.m → Set PairPoint) (hG : ∀ s, MeasurableSet (G s))
    (hGH : ∀ s, G s ⊆ p.H s) :
    ∃ t : Fin (2 ^ p.T) → ℝ,
      (∀ b : Fin (2 ^ p.T), t b ∈ Icc ((b : ℝ) / (2 : ℝ) ^ p.T)
        (((b : ℝ) + 1) / (2 : ℝ) ^ p.T)) ∧
      p.pairMass G ≤ ∑ s, ENNReal.ofReal (ωk (p.world s)) *
        p.incidenceLaw s (pairSection (G s) (t (p.timeIndex s))) := by
  letI : ∀ s, SFinite (νk (p.world s)) := fun s => by
    letI := hν (p.world s)
    infer_instance
  have hfin (s : Fin p.m) : p.pairLaw s (G s) ≠ ∞ :=
    ne_top_of_le_ne_top (p.pairLaw_finite hν s) (measure_mono (hGH s))
  obtain ⟨t, ht, hm⟩ := exists_frozen_dyadic_pair_times (fun s => νk (p.world s))
    G hG hfin (fun s => ωk (p.world s)) (fun s => hω (p.world s)) p.T p.timeIndex
    (fun s v hv => p.source_time s (hGH s hv))
  exact ⟨t, ht, hm⟩

/-- A common frozen source time preserves the original world/block disjointness. -/
theorem frozen_sections_disjoint (G : Fin p.m → Set PairPoint)
    (hGH : ∀ s, G s ⊆ p.H s) (t : Fin (2 ^ p.T) → ℝ)
    (s s' : Fin p.m) (hne : s ≠ s') (hworld : p.world s = p.world s')
    (htime : p.timeIndex s = p.timeIndex s') :
    Disjoint (pairSection (G s) (t (p.timeIndex s)))
      (pairSection (G s') (t (p.timeIndex s'))) := by
  apply Set.disjoint_left.mpr
  intro v hv hv'
  have hs : (v.1, t (p.timeIndex s)) ∈ p.S s := p.source_mem s (hGH s hv)
  have hs' : (v.1, t (p.timeIndex s')) ∈ p.S s' := p.source_mem s' (hGH s' hv')
  exact Set.disjoint_left.mp (p.source_disjoint s s' hne hworld htime) hs
    (by simpa only [htime] using hs')

end PairData
end Submission.Obl.k4_pair_bin_atlas_assembly
