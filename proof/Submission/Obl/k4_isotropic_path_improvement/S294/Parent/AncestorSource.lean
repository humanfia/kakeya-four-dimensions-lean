-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.AncestorSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/AncestorSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SourceBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ClockParentCoefficients

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set Filter

noncomputable section

namespace AncestorSource

abbrev Packet := ParentSource.Broad.Source.FrozenPacket

/-- The inverse clock map keeps the original indexed trajectory. -/
theorem fromAncestor_timeChange (p : Packet) (z : Ev) :
    AncestorQualification.fromAncestor p.unitFrame.t₀ p.unitFrame.q (p.timeChange z)=z := by
  rw [p.timeChange_apply]
  apply Prod.ext
  · rfl
  change p.unitFrame.t₀+p.unitFrame.q*(p.unitFrame.q⁻¹*(z.2-p.unitFrame.t₀))=z.2
  rw [←mul_assoc,mul_inv_cancel₀ p.unitFrame_length_pos.ne',one_mul]
  ring

theorem timeChange_fromAncestor (p : Packet) (z : Ev) :
    p.timeChange (AncestorQualification.fromAncestor p.unitFrame.t₀ p.unitFrame.q z)=z := by
  simpa only [MeasurableEquiv.apply_symm_apply] using
    congrArg p.timeChange (fromAncestor_timeChange p (p.timeChange.symm z))

theorem selectedEvent_eq (p : Packet) (U : Set Ev) :
    p.selectedEvent U=AncestorQualification.event p.unitFrame.t₀ p.unitFrame.q U := by
  ext z
  constructor
  · rintro ⟨q,hq,rfl⟩
    change AncestorQualification.fromAncestor _ _ (p.timeChange q)∈U
    rw [fromAncestor_timeChange]
    exact hq
  · intro hz
    exact ⟨AncestorQualification.fromAncestor _ _ z,hz,timeChange_fromAncestor p z⟩

/-- An original mass floor becomes density in the full assigned ancestor
prior. This is an exact clock transport, with the original reference. -/
theorem selected_density (p : Packet) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν p.assigned≠0) (U : Set Ev) (hU : MeasurableSet U) (hUF : U⊆p.counted)
    {mass : ENNReal}
    (hmass : mass*(ENNReal.ofReal p.unitFrame.q*ν p.assigned)≤(ν.prod volume) U) :
    IsProbabilityMeasure (p.prior ν) ∧ MeasurableSet (p.selectedEvent U) ∧
      p.selectedEvent U⊆univ×ˢIcc (0:ℝ) 1 ∧
      mass≤((p.prior ν).prod volume) (p.selectedEvent U) := by
  refine ⟨p.prior_probability ν hA,p.measurable_selectedEvent hU,
    (p.selectedEvent_subset hUF).trans p.event_unit_time,?_⟩
  simpa only [ParentSource.Broad.Source.FrozenPacket.selectedLaw,Measure.restrict_apply_univ]
    using p.selectedLaw_mass_lower ν hA hU hUF hmass

/-- The source chosen in a level-zero ancestor, prior to qualification or
selection of the eventual old packet. All masses are still original. -/
structure Selection (p : DensityPreparation.Problem) (S : ℝ) (R A : Finset ℝ) (τ : ℝ)
    (k : ℕ) (pth : OriginalPath.Data (p.W k)) (H : Fin (p.W k) → Set Ev) where
  node : Fin pth.C
  level : pth.lev node=0
  weight_pos : 0<p.ω k (pth.world node)
  current : Set Ev
  measurable : MeasurableSet current
  subset : current⊆H (pth.world node)∩pth.counted node
  reference_pos : 0<ENNReal.ofReal (PotentialFits.clock (pth.T 0))*
    p.ν k (pth.world node) (pth.assigned node)
  mass : ENNReal.ofReal (pth.κ⁻¹/8)*
    (ENNReal.ofReal (PotentialFits.clock (pth.T 0))*
      p.ν k (pth.world node) (pth.assigned node))≤
        ((p.ν k (pth.world node)).prod volume) current
  pointwise : ∀ z∈current, OriginalPreparation.PreparedAt p S R A τ k (pth.world node) z

/-- Existence uses the actual supplied level-zero packets and the original
uniform density preparation; no chosen prior is an additional input. -/
theorem exists_selection {p : DensityPreparation.Problem} {S η : ℝ} (hp : p.Valid S η)
    (R A : Finset ℝ) (hR : ∀ r∈R,0≤r ∧ r≤p.L)
    (hA : ∀ u∈A,0<u ∧ u≤η*p.L) {τ : ℝ} (hτ : 0<τ)
    (κ₁ : ℝ) (m : ℕ) (hm : 0 < m) (s : ℕ→ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) :
    ∃ σ : ℝ, 0<σ ∧ ∀ᶠ k in atTop,
      ∀ pth : OriginalPath.Data (p.W k),
      pth.Valid 0 (p.N k) p.L (p.ω k) (p.ν k) (p.E k) (p.B k) p.f
        κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (p.W k) → Set Ev,
      (∀ w,MeasurableSet (H w) ∧
        H w⊆{z | ∃ b,pth.lev b=m-1 ∧ pth.world b=w ∧ z∈pth.counted b}) →
      ENNReal.ofReal (pth.κ⁻¹/2)≤
        ∑ w,ENNReal.ofReal (p.ω k w)*((p.ν k w).prod volume) (H w) →
      Nonempty (Selection p S R A τ k pth H) := by
  obtain ⟨σ,hσ,hprep⟩ := OriginalPreparation.exists_prepared_packet hp R A hR hA hτ
    κ₁ m s δ₀ Mp Dp
  refine ⟨σ,hσ,hprep.mono ?_⟩
  intro k hk pth hpth H hH hmass
  obtain ⟨b,U,hb,hweight,hU,hsub,href,hmassU,hpoint⟩ := hk pth hpth H hH hmass 0 hm
  exact ⟨⟨b,hb,hweight,U,hU,hsub,href,hmassU,hpoint⟩⟩

section Selected

variable {p : DensityPreparation.Problem} {S η : ℝ} (hp : p.Valid S η)
    {R A : Finset ℝ} {τ : ℝ} {k : ℕ} {pth : OriginalPath.Data (p.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ→ℝ}
    {H : Fin (p.W k)→Set Ev}
    (hpth : pth.Valid 0 (p.N k) p.L (p.ω k) (p.ν k) (p.E k) (p.B k) p.f
      κ₁ m s δ₀ Mp Dp σ)
    (a : Selection p S R A τ k pth H)

def Selection.packet : Packet :=
  ParentSource.Broad.Source.originalPathPacket hpth a.node

include hp in
theorem Selection.normalized_density :
    let b := a.node
    let f := a.packet hpth
    IsProbabilityMeasure (f.prior (p.ν k (pth.world b))) ∧
      MeasurableSet (f.selectedEvent a.current) ∧
      f.selectedEvent a.current⊆univ×ˢIcc (0:ℝ) 1 ∧
      ENNReal.ofReal (pth.κ⁻¹/8)≤
        ((f.prior (p.ν k (pth.world b))).prod volume) (f.selectedEvent a.current) := by
  let ν := p.ν k (pth.world a.node)
  haveI : IsProbabilityMeasure ν := (ParentSignal.original_parent_bounds
    ((DensityPreparation.valid_iff p S η).mp hp) k (pth.world a.node)).2.1
  have hA := ParentSource.Broad.Source.originalPathPacket_assignment_nonzero hpth
    (show 0<p.N k by linarith [hp.1 k]) a.node
  apply selected_density (a.packet hpth) ν hA a.current a.measurable
    (fun z hz => (a.subset hz).2)
  simpa only [Selection.packet,ParentSource.Broad.Source.originalPathPacket,
    ParentSource.Broad.Source.FrozenPacket.unitFrame,a.level,PotentialFits.clock] using a.mass

theorem Selection.normalized_prepared_at (z : Ev)
    (hz : z∈(a.packet hpth).selectedEvent a.current) :
    OriginalPreparation.PreparedAt p S R A τ k (pth.world a.node)
      (AncestorQualification.fromAncestor (a.packet hpth).unitFrame.t₀
        (a.packet hpth).unitFrame.q z) := by
  rw [selectedEvent_eq] at hz
  exact a.pointwise _ hz

end Selected

end AncestorSource

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
