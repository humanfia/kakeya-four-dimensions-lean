-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/ObservationSheets.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.PosteriorBase
import Submission.Obl.k4_clean_cover_graph_atlas.SheetBands

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Metric

/-- The sampled agreement event is measurable on the finite pair of sheet indices. -/
theorem measurableSet_sheet_pair_agreement {D n : ℕ} (f : Fin n → RealSheet D) (V : ℝ) :
    MeasurableSet {q : (Fin n × Fin n) × Real3 | ‖q.2‖ ≤ (1 : ℝ) / 2 ∧
      ‖(f q.1.1).f (emb q.2) - (f q.1.2).f (emb q.2)‖ ≤ V} := by
  have hU : MeasurableSet (⋃ a : Fin n, ⋃ b : Fin n,
      ({(a, b)} : Set (Fin n × Fin n)) ×ˢ
        {x : Real3 | ‖x‖ ≤ (1 : ℝ) / 2 ∧ ‖(f a).f (emb x) - (f b).f (emb x)‖ ≤ V}) :=
    MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      (measurableSet_singleton (a, b)).prod (measurableSet_sheet_agreement (f a) (f b) V)
  convert hU using 1
  ext q
  simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_singleton_iff]
  constructor
  · intro hq
    exact ⟨q.1.1, q.1.2, by simp, hq⟩
  · rintro ⟨a, b, hq, hfit⟩
    simpa only [hq] using hfit

/-- Same original hidden-bin support gives the pointwise pair fitting certificate.
The posterior law remains the unnormalized covered original law. -/
theorem posterior_base_support_of_sheet_bins {D n : ℕ} {X : Type*} [MeasurableSpace X]
    (f : Fin n → RealSheet D) (ρ : Measure X) (p : X → Fin n → ℝ)
    (hpmeas : ∀ a, Measurable (fun o => p o a)) (hp : ∀ o a, 0 ≤ p o a)
    (base : X → Real3) (hb : Measurable base) (bin : X → ℤ) (δ η V : ℝ)
    (hwidth : 2 * η + δ ≤ V)
    (hfit : ∀ a, ∀ᵐ o ∂ρ, 0 < p o a →
      ‖base o‖ ≤ (1 : ℝ) / 2 ∧
      δ * (bin o : ℝ) - η ≤ ((f a).f (emb (base o))).re ∧
      ((f a).f (emb (base o))).re ≤ δ * ((bin o : ℝ) + 1) + η) :
    posteriorBasePairLaw ρ p base {q | ‖q.2‖ ≤ (1 : ℝ) / 2 ∧
      ‖(f q.1.1).f (emb q.2) - (f q.1.2).f (emb q.2)‖ ≤ V}ᶜ = 0 := by
  have hae : ∀ᵐ q ∂posteriorBasePairLaw ρ p base,
      ‖q.2‖ ≤ (1 : ℝ) / 2 ∧ ‖(f q.1.1).f (emb q.2) - (f q.1.2).f (emb q.2)‖ ≤ V := by
    apply posteriorBasePairLaw_ae ρ p hpmeas hp base hb (measurableSet_sheet_pair_agreement f V)
    intro a b
    filter_upwards [hfit a, hfit b] with o ha hb'
    intro hpa hpb
    obtain ⟨hhalf, halo, hahi⟩ := ha hpa
    obtain ⟨_, hblo, hbhi⟩ := hb' hpb
    refine ⟨hhalf, ?_⟩
    have hgap : |((f a).f (emb (base o))).re - ((f b).f (emb (base o))).re| ≤ 2 * η + δ :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hh := sheet_gap_of_real_fits (f a) (f b) (base o) (by linarith)
      (((f a).f (emb (base o))).re) (ηf := 0) (by simp) hgap
    have hclose : ‖(f a).f (emb (base o)) - (f b).f (emb (base o))‖ ≤ 2 * η + δ := by
      simpa only [zero_add] using hh
    exact hclose.trans hwidth
  exact ae_iff.mp hae

end Submission.Obl.k4_clean_cover_graph_atlas
