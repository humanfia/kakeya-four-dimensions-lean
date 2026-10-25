/- Adapted within this LOT tree from o190/x0630, commit adb2f45f4ccde121d91c5954051b6c45263cd6de,
Submission/Obl/k4_pair_bin_atlas_assembly/RepresentativeDeletion.lean. Existing provenance comments are retained below. -/
import Submission.Obl.k4_matched_pair_representative_realization.Selection.PairRepresentatives
import Submission.Obl.k4_matched_pair_representative_realization.Selection.PairAnchor
import Submission.Obl.k4_matched_pair_representative_realization.Selection.DensityDeletion

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open Set MeasureTheory
open scoped ENNReal

namespace PairData

variable {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε)
    {Bin : Type*} [DecidableEq Bin]

theorem representativeBadSet_volume {Cs : ℕ} {CD : ℝ}
    (hsublevel : SublevelAt Cs CD Nk a)
    (bins : Fin p.m → Finset Bin) (α : EuclideanSpace ℝ (Fin 3))
    (hα : ‖α‖ ≤ 1 / 8) (s : Fin p.m) (β : Bin) :
    volume (p.representativeBadSet bins α ((Nk ^ a) ^ (-(Cs : ℝ))) CD s β) ≤
      ENNReal.ofReal (Nk ^ (-(3 * a))) := by
  cases hr : p.representative bins α ((Nk ^ a) ^ (-(Cs : ℝ))) (p.frame s) β with
  | none => simp only [representativeBadSet, hr, measure_empty]; exact bot_le
  | some r =>
    have hgood := (p.representative_spec bins α ((Nk ^ a) ^ (-(Cs : ℝ))) hr).2.2
    simpa only [representativeBadSet, hr] using
      hsublevel (disc (p.P r)) α (p.tests r).2.2.2.1 (p.tests r).2.2.2.2 hα hgood

/-- Delete the bad bases of both possible representatives before choosing a
source bin or freezing the source time. The loss is `2 N^(-2a)`. -/
theorem delete_representative_sublevels {Cs : ℕ} {CD : ℝ}
    (hNk : 0 < Nk) (hω : ∀ w, 0 ≤ ωk w) (hsublevel : SublevelAt Cs CD Nk a)
    (bins : Fin p.m → Finset Bin) (hbins : ∀ s, (bins s).card ≤ 2)
    (α : EuclideanSpace ℝ (Fin 3)) (hα : ‖α‖ ≤ 1 / 8)
    (G : Fin p.m → Set PairPoint) (hG : ∀ s, MeasurableSet (G s))
    (hGH : ∀ s, G s ⊆ p.H s) :
    ∃ G' : Fin p.m → Set PairPoint,
      (∀ s, MeasurableSet (G' s)) ∧ (∀ s, G' s ⊆ G s) ∧
      (∀ s, ∀ v ∈ G' s, ∀ β ∈ bins s, ∀ r,
        p.representative bins α ((Nk ^ a) ^ (-(Cs : ℝ))) (p.frame s) β = some r →
        Nk ^ (-(CD * a)) ≤
          |MvPolynomial.eval (fun i => p.sourceBase s v i) (disc (p.P r))|) ∧
      p.pairMass G ≤ p.pairMass G' + ENNReal.ofReal (2 * Nk ^ (-(2 * a))) := by
  classical
  let ρ : ℝ := (Nk ^ a) ^ (-(Cs : ℝ))
  let bad : Fin p.m → Set PairPoint := fun s =>
    p.sourceBase s ⁻¹' p.sourceBadSet bins α ρ CD s
  have hbad (s : Fin p.m) : MeasurableSet (bad s) :=
    (p.measurableSet_sourceBadSet bins α ρ CD s).preimage (p.measurable_sourceBase s)
  let G' : Fin p.m → Set PairPoint := fun s => G s \ bad s
  have hcharge : (∑ s, ENNReal.ofReal (ωk (p.world s) * (2 : ℝ) ^ p.T) *
      p.pairLaw s (p.H s ∩ bad s)) ≤ ENNReal.ofReal (2 * Nk ^ (-(2 * a))) := by
    have hq : 0 < (2 : ℝ) ^ p.T := by positivity
    have hb := weighted_finite_candidate_exception_real_le
      p.pairLaw volume p.H p.sourceBase (fun s => ωk (p.world s)) p.β
      (fun s => hω (p.world s)) (fun s => (p.base_density s).1) hq
      (fun s U hU => (p.base_density s).2 U hU) p.density_budget bins hbins
      (p.representativeBadSet bins α ρ CD) (p.measurableSet_representativeBadSet bins α ρ CD)
      (fun s β _ => p.representativeBadSet_volume hsublevel bins α hα s β)
    have hpowers : Nk ^ a * (2 * Nk ^ (-(3 * a))) = 2 * Nk ^ (-(2 * a)) := by
      rw [mul_left_comm, ← Real.rpow_add hNk]
      congr 1
      congr 1
      ring
    rw [hpowers] at hb
    exact hb
  refine ⟨G', (fun s => (hG s).diff (hbad s)), (fun s => sdiff_subset), ?_, ?_⟩
  · intro s v hv β hβ r hr
    by_contra hn
    have hsmall := lt_of_not_ge hn
    apply hv.2
    refine Set.mem_iUnion.mpr ⟨β, Set.mem_iUnion.mpr ⟨hβ, ?_⟩⟩
    change p.sourceBase s v ∈ p.representativeBadSet bins α ρ CD s β
    rw [representativeBadSet, hr]
    exact ⟨p.sourceBase_norm s (hGH s hv.1), hsmall⟩
  · have hsplit (s : Fin p.m) : p.pairLaw s (G s) ≤
        p.pairLaw s (G' s) + p.pairLaw s (p.H s ∩ bad s) := by
      calc
        _ = p.pairLaw s (G' s) + p.pairLaw s (G s ∩ bad s) :=
          (measure_sdiff_add_inter (μ := p.pairLaw s) (G s) (hbad s)).symm
        _ ≤ _ := by
          apply add_le_add le_rfl
          apply measure_mono
          intro v hv
          exact ⟨hGH s hv.1, hv.2⟩
    calc
      _ ≤ ∑ s, ENNReal.ofReal (ωk (p.world s) * (2 : ℝ) ^ p.T) *
          (p.pairLaw s (G' s) + p.pairLaw s (p.H s ∩ bad s)) := by
        apply Finset.sum_le_sum
        intro s _
        gcongr
        exact hsplit s
      _ = p.pairMass G' + ∑ s, ENNReal.ofReal (ωk (p.world s) * (2 : ℝ) ^ p.T) *
          p.pairLaw s (p.H s ∩ bad s) := by
        simp only [mul_add, Finset.sum_add_distrib, pairMass]
      _ ≤ _ := add_le_add le_rfl hcharge

end PairData
end Submission.Obl.k4_matched_pair_representative_realization.Selection
