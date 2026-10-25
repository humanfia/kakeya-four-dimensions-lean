-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.SaturatedDichotomy, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/SaturatedDichotomy.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SourceBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PowerBudgetedNarrow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeDichotomy

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SaturatedDichotomy

open MeasureTheory Set
open ParentSource ParentSource.Native

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (P : PaletteStripSaturation F r fraction)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

/-- Preserve the full mass margin after removing saturated predictions. -/
theorem remaining_mass_strong
    (hfull : ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))))
    (hcapture : Q.law (labelledSupport P.captureResidual) ≤ ENNReal.ofReal (9 / 22 : ℝ)) :
    ENNReal.ofReal (93 / 176 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active P.remainingU))) := by
  classical
  let Full := labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))
  let Remaining := labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active P.remainingU))
  let Captured := labelledSupport P.captureResidual
  have hcover : Full ⊆ Remaining ∪ Captured := by
    intro z hz
    obtain ⟨b,hbi,hbw,hzb⟩ := hz
    have hb : F.active b := by
      by_contra hn
      simp only [PreparedAngularPath.selectedCoarseFamily,ite_eq_right hn,notMem_empty] at hzb
    have hU : z ∈ F.U b := by
      have hh : (p.γ b,z.2) ∈ F.U b := by
        simpa only [PreparedAngularPath.selectedCoarseFamily,ite_eq_left hb,mem_preimage] using hzb
      simpa only [hbw] using hh
    by_cases hcap : z ∈ P.captured b
    · apply Or.inr
      refine ⟨b,hbi,hbw,?_⟩
      simpa only [PaletteStripSaturation.captureFamily,ite_eq_left hb,mem_preimage,hbw] using hcap
    · apply Or.inl
      refine ⟨b,hbi,hbw,?_⟩
      simpa only [PreparedAngularPath.selectedCoarseFamily,ite_eq_left hb,mem_preimage,
        PaletteStripSaturation.remainingU,hbw] using (show z ∈ F.U b \ P.captured b from ⟨hU,hcap⟩)
  have hbound : ENNReal.ofReal (93 / 176 : ℝ) + ENNReal.ofReal (9 / 22 : ℝ) ≤
      Q.law Remaining + ENNReal.ofReal (9 / 22 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (15 / 16 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      _ ≤ Q.law Full := hfull
      _ ≤ Q.law Remaining + Q.law Captured :=
        (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ _ := add_le_add le_rfl hcapture
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hbound

/-- Removing saturated predictions retains at least half of the prepared law. -/
theorem remaining_mass
    (hfull : ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))))
    (hcapture : Q.law (labelledSupport P.captureResidual) ≤ ENNReal.ofReal (9 / 22 : ℝ)) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active P.remainingU))) :=
  (ENNReal.ofReal_le_ofReal (by norm_num : (1 / 2 : ℝ) ≤ 93 / 176)).trans
    (remaining_mass_strong P hfull hcapture)

/-- The original palette and all original reference marginals are kept;
only its successful event is reduced by the captured strip union. -/
def remainingPalette
    (hmass : ENNReal.ofReal (1 / 2 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active P.remainingU)))) :
    PaletteFamily Q i stop a A θ where
  coding := F.coding
  active := F.active
  code := F.code
  U := P.remainingU
  level := F.level
  weight_positive := F.weight_positive
  current_positive := F.current_positive
  code_original := F.code_original
  packet := F.packet
  coarse_positive := F.coarse_positive
  posterior := F.posterior
  measurable_U := fun b hb => (F.measurable_U b hb).diff (P.captured_measurable hp b hb)
  subset_coarse := fun b hb => sdiff_subset.trans (F.subset_coarse b hb)
  reference_floor := F.reference_floor
  joint_cap := by
    intro b hb e q
    letI : IsFiniteMeasure (Q.coarseLaw (p.lev b) (F.code b)) := by
      change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
      infer_instance
    apply le_trans _ (F.joint_cap b hb e q)
    exact measureReal_mono (fun z hz => ⟨hz.1.1,hz.2⟩) (measure_ne_top _ _)
  mass := hmass

/-- The remaining original palette family has no narrow fine state,
so the original broad-residual factory applies to it. -/
theorem remaining_is_broad (hd : d.Valid)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i < m) (hstop : stop < m) (hfraction : 0 < fraction)
    (hmass : ENNReal.ofReal (1 / 2 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active P.remainingU)))) :
    Nonempty (BroadResidual (remainingPalette P hp hmass) r (2 * fraction)) := by
  obtain hn | hb := (remainingPalette P hp hmass).broad_or_narrow hd hp hHE hH hi hstop
    r (2 * fraction) (by positivity)
  · obtain ⟨N⟩ := hn
    have hempty (w : Fin (d.W k)) : N.residual w = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨b,_,_,_,f,_,_,_,he,hactive,_⟩ := N.witness w x hx
      exact P.remaining_not_narrow hfraction b hactive (F.coding.code f) he
    have hzero := N.mass
    simp only [hempty,measure_empty,mul_zero,Finset.sum_const_zero,
      nonpos_iff_eq_zero,ENNReal.ofReal_eq_zero] at hzero
    have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
    have hpos : 0 < (p.κ⁻¹ / 8) * ((2 * fraction) * (1 / 8)) := by positivity
    linarith
  · exact hb

include hp

/-- If capture does not have the original mass required by the frozen
narrow exit, its prepared-law mass is bounded by `9/22`. -/
theorem prepared_capture_le_of_small_original (hd : d.Valid)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hbuffer : ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w))
    (hsmall : ¬ ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w)) :
    Q.law (labelledSupport P.captureResidual) ≤ ENNReal.ofReal (9 / 22 : ℝ) := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hcapMeas : ∀ w, MeasurableSet (P.captureResidual w) :=
    Q.measurableSet_packetFamilyResidual i P.captureFamily (P.captureFamily_measurable hp)
  have hcapSub (w : Fin (d.W k)) : P.captureResidual w ⊆ Q.residual w :=
    Q.packetFamilyResidual_subset i P.captureFamily P.captureFamily_subset w
  have htop : (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤)
    simpa only [labelledResidual_univ] using Q.original_total_le_one hd hHE
  by_contra hnot
  have hfloor : ENNReal.ofReal (9 / 22 : ℝ) ≤ Q.law (labelledSupport P.captureResidual) :=
    (lt_of_not_ge hnot).le
  have h := prepared_cut_original_floor (fun w => (d.ν k w).prod volume) (d.ω k)
    Q.residual (labelledSupport P.captureResidual) (measurableSet_labelledSupport _ hcapMeas)
    (by positivity : 0 < 11 * p.κ⁻¹ / 32) htop hbuffer hfloor
  have heq (w : Fin (d.W k)) : Q.residual w ∩ {x | (w,x) ∈ labelledSupport P.captureResidual} =
      P.captureResidual w := inter_eq_right.mpr (hcapSub w)
  apply hsmall
  simpa only [heq,show (11 * p.κ⁻¹ / 32) * (9 / 22) = 9 * p.κ⁻¹ / 64 by ring] using h

/-- The saturation dichotomy at the ORIGINAL threshold consumed by the
narrow atlas: either capture already has that mass, or an actual broad
residual survives under the same original references. -/
theorem broad_or_capture (hd : d.Valid)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i < m) (hstop : stop < m) (hfraction : 0 < fraction)
    (hbuffer : ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w))
    (hfull : ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U)))) :
    ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w)) ∨
      ∃ F' : PaletteFamily Q i stop a A θ, Nonempty (BroadResidual F' r (2 * fraction)) := by
  by_cases hlarge : ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w))
  · exact Or.inl hlarge
  · have hcap := prepared_capture_le_of_small_original P hp hd hHE hbuffer hlarge
    have hmass := remaining_mass P hfull hcap
    exact Or.inr ⟨remainingPalette P hp hmass,
      remaining_is_broad P hp hd hHE hH hi hstop hfraction hmass⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SaturatedDichotomy
