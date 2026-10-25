-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OriginalCoefficients, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/OriginalCoefficients.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSignal
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.DensityPreparation

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open Set MeasureTheory

noncomputable section

namespace OriginalCoefficients

open ParentSignal
abbrev Problem := DensityPreparation.Problem

/-- All seven original-time coefficients are uniformly bounded under the
unchanged original prior. The accepted global signal bound is used directly. -/
theorem original_bounds {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (k : ℕ) (w : Fin (p.W k)) :
    ∀ᵐ l ∂p.ν k w, ∀ i, |globalCoefficients (p.P k w) l i| ≤ 8 * p.K k := by
  obtain ⟨M, D, hdata⟩ := hp.2.2.2.2.2.2.2.2.1
  rcases (hdata k).2.2.2.1 w with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hline, _⟩
  filter_upwards [hline] with l hl i
  exact globalCoefficients_bound (fun t ht => (hl t ht).2) (hl 0 (by norm_num)).1 i

/-- The original full-time planar bounds are retained on the actual line
index, independently of all later incidence choices. -/
def boxLines (K : ℝ) : Set Ln :=
  {l | ∀ t ∈ Icc (0 : ℝ) 1, ‖y l t‖ + ‖v l‖ ≤ K}

theorem measurableSet_boxLines (K : ℝ) : MeasurableSet (boxLines K) := by
  have hy (t : ℝ) : Continuous (fun l : Ln => y l t) := by
    unfold y x
    fun_prop
  have hv : Continuous (fun l : Ln => v l) := by
    unfold v
    fun_prop
  have heq : boxLines K=(⋂ t, ⋂ (_ : t∈Icc (0:ℝ) 1),
      {l : Ln | ‖y l t‖+‖v l‖≤K}) := by
    ext l
    simp only [boxLines,mem_iInter,mem_setOf_eq]
  rw [heq]
  exact (isClosed_iInter (fun t => isClosed_iInter
    (fun (_ : t∈Icc (0:ℝ) 1) =>
      isClosed_le ((hy t).norm.add hv.norm) continuous_const))).measurableSet

theorem original_boxLines {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (k : ℕ) (w : Fin (p.W k)) : ∀ᵐ l ∂p.ν k w, l∈boxLines (p.K k) := by
  obtain ⟨M, D, hdata⟩ := hp.2.2.2.2.2.2.2.2.1
  rcases (hdata k).2.2.2.1 w with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hline, _⟩
  exact hline.mono (fun l hl t ht => (hl t ht).1)

/-- Full parent jets, the counted derivative floor, and the bounded original
time table can be imposed pointwise after any later event selection, with
exactly zero loss in its original product law. -/
theorem prepare_events {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (k : ℕ) (w : Fin (p.W k)) (F : Set Ev) (hFm : MeasurableSet F) (hF : F ⊆ p.E k w) :
    ∃ F' : Set Ev, MeasurableSet F' ∧ F' ⊆ F ∧
      ((p.ν k w).prod volume).restrict F' = ((p.ν k w).prod volume).restrict F ∧
      ∀ z ∈ F', z.1 ∈ goodLines (p.P k w) (p.K k) (p.B k w) ∧
        z ∈ regularEvents (p.P k w) (p.K k) (p.B k w) ∧
        ∀ i, |globalCoefficients (p.P k w) z.1 i| ≤ 8 * p.K k := by
  have hprob := (DensityPreparation.valid_iff p S η).mp hp
  obtain ⟨F₀, hF₀m, hF₀F, hF₀eq, hF₀⟩ :=
    ParentSignal.prepare_original_events hprob k w F hFm hF
  let G : Set Ln := {l | ∀ i, |globalCoefficients (p.P k w) l i| ≤ 8 * p.K k}
  have hGm : MeasurableSet G := measurableSet_bounded_globalCoefficients (p.P k w) (p.K k)
  have hprod : ∀ᵐ z ∂(p.ν k w).prod (volume : Measure ℝ), z.1 ∈ G :=
    (Measure.quasiMeasurePreserving_fst (μ := p.ν k w) (ν := (volume : Measure ℝ))).ae
      (original_bounds hp k w)
  let F' := F₀ ∩ Prod.fst ⁻¹' G
  have heq : ((p.ν k w).prod volume).restrict F' = ((p.ν k w).prod volume).restrict F₀ := by
    apply Measure.restrict_congr_set
    filter_upwards [hprod] with z hz
    simp only [F', mem_inter_iff, mem_preimage, hz, and_true]
  refine ⟨F', hF₀m.inter (hGm.preimage measurable_fst),
    (fun z hz => hF₀F hz.1), heq.trans hF₀eq, ?_⟩
  intro z hz
  exact ⟨(hF₀ z hz.1).1, (hF₀ z hz.1).2, hz.2⟩

/-- All actual parent, coefficient and planar bounds may be pointwise
simultaneously, still with exact equality of the original selected law. -/
theorem prepare_events_with_box {p : Problem} {S η : ℝ} (hp : p.Valid S η)
    (k : ℕ) (w : Fin (p.W k)) (F : Set Ev) (hFm : MeasurableSet F) (hF : F⊆p.E k w) :
    ∃ F' : Set Ev, MeasurableSet F' ∧ F'⊆F ∧
      ((p.ν k w).prod volume).restrict F'=((p.ν k w).prod volume).restrict F ∧
      ∀ z∈F', z.1∈goodLines (p.P k w) (p.K k) (p.B k w) ∧
        z∈regularEvents (p.P k w) (p.K k) (p.B k w) ∧
        (∀ i, |globalCoefficients (p.P k w) z.1 i|≤8*p.K k) ∧ z.1∈boxLines (p.K k) := by
  obtain ⟨F0,hF0,hF0F,heq0,hpoint⟩ := prepare_events hp k w F hFm hF
  have hprod : ∀ᵐ z ∂(p.ν k w).prod (volume : Measure ℝ), z.1∈boxLines (p.K k) :=
    (Measure.quasiMeasurePreserving_fst (μ := p.ν k w) (ν := (volume : Measure ℝ))).ae
      (original_boxLines hp k w)
  let F' := F0∩Prod.fst ⁻¹' boxLines (p.K k)
  have heq : ((p.ν k w).prod volume).restrict F'=((p.ν k w).prod volume).restrict F0 := by
    apply Measure.restrict_congr_set
    filter_upwards [hprod] with z hz
    simp only [F',mem_inter_iff,mem_preimage,hz,and_true]
  refine ⟨F',hF0.inter ((measurableSet_boxLines _).preimage measurable_fst),
    fun z hz => hF0F hz.1,heq.trans heq0,?_⟩
  intro z hz
  exact ⟨(hpoint z hz.1).1,(hpoint z hz.1).2.1,(hpoint z hz.1).2.2,hz.2⟩

end OriginalCoefficients

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
