-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.VaryingParentStateBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/VaryingParentStateBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/VaryingParentStateBreadth.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineOutputBreadth

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

set_option maxHeartbeats 1000000 in
/-- Renew breadth in one fixed physical target frame while each deep packet
uses its own actual active broad parent. Full deep references provide the
original deletion budget even when quarter histories merge. -/
theorem PaletteFamily.exists_broad_physical_state_source_varying_parent {ι I : Type*} [Fintype ι]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (world : Fin (d.W k)) (fine : Fin p.C) (b packet : ι → Fin p.C)
    (hb : ∀ j, F.active (b j)) (hbγ : ∀ j, p.γ (b j)=world)
    (hf : ∀ j, p.lev (packet j) = stop) (hfγ : ∀ j, p.γ (packet j) = p.γ (b j))
    {r fraction width : ℝ} (hfraction : 0 ≤ fraction) (hwidth : 0 ≤ width)
    (hscale : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ r)
    (he : ∀ j, F.coding.code (packet j) ∉
      Q.intrinsicNarrowStates F.code stop F.U r fraction (b j))
    (hretained : ∀ j, F.coding.code (packet j) ∉
      fineRetentionFailures (Q.coarseLaw (p.lev (b j)) (F.code (b j)))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U (b j)) (ENNReal.ofReal (1 / 8 : ℝ)))
    (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hρ : ρ ≤ (d.ν k world).prod volume)
    (state : ((ℕ × (Fin 6 → ℝ)) × ℝ) → I) (hstate : Measurable state)
    (menus : ι → Finset I) (D : ℕ) (hD : ∀ j, (menus j).card ≤ D)
    (hcover : ∀ᵐ x ∂ρ, ∃ j, x ∈ F.fineOriginalEvent (b j) (packet j) univ)
    (hmenu : ∀ᵐ x ∂ρ, ∀ j, x ∈ F.fineOriginalEvent (b j) (packet j) univ → state x ∈ menus j)
    (δ : ENNReal) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ∞) :
    ∃ keep : Set ((ℕ × (Fin 6 → ℝ)) × ℝ), MeasurableSet keep ∧
      ρ univ ≤ (ρ.restrict keep) univ + δ * ((D : ENNReal) *
        ∑ j, ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
          d.ν k (p.γ (packet j)) (p.A (packet j))) ∧
      ∀ label (n center : EuclideanSpace ℝ (Fin 2)), ‖n‖ = 1 →
        (ρ.restrict keep) {x | state x = label ∧
          |inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity fine x - center)| ≤ width} ≤
          (δ⁻¹ * ENNReal.ofReal (8 * fraction)) *
            (ρ.restrict keep) {x | state x = label} := by
  classical
  let w : ι → ENNReal := fun j => ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
    d.ν k (p.γ (packet j)) (p.A (packet j))
  let reference := Submission.Lib.K4OutputReferenceMenus.outputReferenceWeight menus w
  let keep := Submission.Lib.K4ReferencePruning.referenceKeep ρ state reference δ
  have hkeep : MeasurableSet keep :=
    Submission.Lib.K4ReferencePruning.measurableSet_referenceKeep ρ state hstate reference δ
  have hsub : ρ.restrict keep ≤ ρ := Measure.restrict_le_self
  refine ⟨keep, hkeep, ?_, ?_⟩
  · exact (Submission.Lib.K4ReferencePruning.reference_pruning_mass_budget
      ρ state hstate reference δ).trans (add_le_add le_rfl
        (mul_le_mul' le_rfl (Submission.Lib.K4OutputReferenceMenus.output_reference_total_budget
          menus w D hD)))
  · intro label n center hn
    have hmass := Submission.Lib.K4ReferencePruning.reference_kept_state_mass
      ρ state hstate reference δ label
    by_cases hfloor : δ * reference label ≤ ρ (state ⁻¹' {label})
    · rw [ite_eq_left hfloor] at hmass
      have heq : (ρ.restrict keep) {x | state x = label} = ρ (state ⁻¹' {label}) := by
        simpa only [keep, preimage, mem_singleton_iff] using hmass
      let Test := {x : ((ℕ × (Fin 6 → ℝ)) × ℝ) | |inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity fine x-center)| ≤ width}
      have hTest : MeasurableSet Test := by
        have hm : Measurable (fun x : ((ℕ × (Fin 6 → ℝ)) × ℝ) => (6*p.κ)⁻¹ • p.normalizedVelocity fine x-center) :=
          ((p.measurable_normalizedVelocity fine).const_smul ((6*p.κ)⁻¹)).sub_const center
        exact measurableSet_le ((measurable_const.inner hm).abs) measurable_const
      apply output_reference_relative_event_cap ((d.ν k world).prod volume) (ρ.restrict keep)
        (hsub.trans hρ) (fun j => F.fineOriginalEvent (b j) (packet j) univ) state menus w
        (ENNReal.ofReal (8*fraction)) δ hδ0 hδtop ((ae_mono hsub) hcover) ((ae_mono hsub) hmenu)
        Test hTest _ label (by rw [heq]; exact hfloor)
      intro j
      simpa only [hbγ j,w,Test,Set.inter_def,Set.mem_setOf_eq] using F.fine_native_cube_strip_numerator_cap hd hp hHE hH
        (b j) (packet j) fine (hb j) (hf j) (hfγ j) hfraction hwidth hscale
        (he j) (hretained j) n center hn
    · rw [ite_eq_right hfloor] at hmass
      have heq : (ρ.restrict keep) {x | state x = label} = 0 := by
        simpa only [keep, preimage, mem_singleton_iff] using hmass
      calc
        _ ≤ (ρ.restrict keep) {x | state x = label} := measure_mono (fun _ hx => hx.1)
        _ = 0 := heq
        _ ≤ _ := zero_le

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
