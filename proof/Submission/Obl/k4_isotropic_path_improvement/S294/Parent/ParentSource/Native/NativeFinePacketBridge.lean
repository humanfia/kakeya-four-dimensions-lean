-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeFinePacketBridge, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeFinePacketBridge.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeFinePacketBridge.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeFinePacketBridge.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeFinePacketBridge.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeSelectedResidual
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFineHistory

/-! Selected countable history predictions become a finite table on original
fine packets after one ORIGINAL null deletion. The output chart predicates
can therefore use only finite unions of the old polynomial packet sets. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

section Path

variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

def PacketCoding.cleanResidual (q : PacketCoding p ν)
    (J : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (w : Fin W) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  (J w ∩ q.core w) ∩ {z | packetUnique p.lev p.γ p.F w z}

theorem PacketCoding.cleanResidual_measurable (q : PacketCoding p ν)
    (hF : ∀ b, MeasurableSet (p.F b))
    (J : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hJ : ∀ w, MeasurableSet (J w)) (w : Fin W) :
    MeasurableSet (q.cleanResidual J w) :=
  ((hJ w).inter (q.measurableSet_core hF w)).inter
    (measurableSet_packetUnique p.lev p.γ p.F hF w)

theorem PacketCoding.cleanResidual_original_mass (q : PacketCoding p ν)
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (J : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (w : Fin W) :
    ((ν w).prod volume) (q.cleanResidual J w) = ((ν w).prod volume) (J w) := by
  calc
    _ = ((ν w).prod volume) (J w ∩ q.core w) := by
      apply measure_congr
      filter_upwards [hp.ae_packet_unique w] with z hz
      simp only [cleanResidual, mem_inter_iff, mem_ofPred_eq, hz, and_true]
    _ = _ := q.original_mass_core w (J w)

theorem PathData.Valid.pointwise_fine_packet_witness
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (q : PacketCoding p ν) (stop : ℕ) (hstop : stop < m) (w : Fin W)
    (x : (ℕ × (Fin 6 → ℝ)) × ℝ) (hunique : packetUnique p.lev p.γ p.F w x)
    (hcore : x ∈ q.core w) (hterminal : x ∈ p.terminalCoverage m w) :
    ∃ b, p.lev b = stop ∧ p.γ b = w ∧
      finitePacketHistory p.lev p.γ p.F stop (w, x) = q.code b ∧ x ∈ p.packetWitness m stop w b := by
  obtain ⟨t, ht, hxt⟩ := hterminal
  obtain ⟨b, hb, hbw, _, hsub⟩ :=
    ancestor_of_parent p.lev p.par p.γ p.A p.F hp.parent t stop (by omega)
  have hbw' : p.γ b = w := hbw.trans ht.2
  have hxb : x ∈ p.F b := hsub hxt
  have hcode := q.code_eq_of_mem_core w hcore b hbw' hxb
  rw [hb] at hcode
  refine ⟨b, hb, hbw', hcode, ?_⟩
  simpa only [PathData.packetWitness, ite_eq_left (show p.lev b = stop ∧ p.γ b = w from ⟨hb, hbw'⟩),
    mem_inter_iff, mem_ofPred_eq] using
      (show (x ∈ p.F b ∧ packetUnique p.lev p.γ p.F w x) ∧ x ∈ p.terminalCoverage m w from
        ⟨⟨hxb, hunique⟩, t, ht, hxt⟩)

end Path

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PreparedAngularPath.mem_narrowHistoryFamily
    (active : Fin p.C → Prop) (stop : ℕ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (n : Fin p.C → ℕ → StripSpace) (β : Fin p.C → ℕ → ℝ)
    (r : ℝ) (Bad : Fin p.C → Set ℕ) (b : Fin p.C)
    (x : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    x ∈ Q.narrowHistoryFamily active stop U n β r Bad b ↔ active b ∧ ∃ e ∈ Bad b,
      finitePacketHistory p.lev p.γ p.F stop (p.γ b, x) = e ∧
        (p.γ b, x) ∈ U b ∧ p.normalizedVelocity b x ∈ affineStrip (n b e) (β b e) r := by
  classical
  by_cases hb : active b
  · simp only [PreparedAngularPath.narrowHistoryFamily, hb, ite_true, true_and, mem_preimage]
    constructor
    · intro hx
      obtain ⟨e, he⟩ := mem_iUnion.mp hx
      exact ⟨e.val, e.property, he⟩
    · rintro ⟨e, he, hx⟩
      exact mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩
  · simp only [PreparedAngularPath.narrowHistoryFamily, hb, ite_false, mem_empty_iff_false, false_and]

variable {Q} {code : Fin p.C → ℕ} {stop : ℕ}
  {U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ))} {r fraction : ℝ}
  (P : NarrowPredictionFamily Q code stop U r fraction)

theorem NarrowPredictionFamily.cleaned_fine_packet_cover
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (q : PacketCoding p (d.ν k)) (hstop : stop < m) (active : Fin p.C → Prop) (i : ℕ)
    (hH : ∀ w, H w ⊆ p.terminalCoverage m w)
    (hJH : ∀ w, P.residual active i w ⊆ H w)
    (hUpacket : ∀ b, active b → ∀ z ∈ U b, z.2 ∈ p.F b)
    (w : Fin (d.W k)) (x : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hx : x ∈ q.cleanResidual (P.residual active i) w) :
    ∃ b, p.lev b = i ∧ p.γ b = w ∧ x ∈ p.F b ∧ ∃ f,
      p.lev f = stop ∧ p.γ f = w ∧ x ∈ p.packetWitness m stop w f ∧
      q.code f ∈ Q.intrinsicNarrowStates code stop U r fraction b ∧ active b ∧
      p.normalizedVelocity b x ∈ affineStrip (P.normal b (q.code f)) (P.offset b (q.code f)) r := by
  have hcore := hx.1.2
  have hunique := hx.2
  have hxJ := hx.1.1
  obtain ⟨f, hf, hfw, hfcode, hxf⟩ := hp.pointwise_fine_packet_witness q stop hstop w x
    hunique hcore (hH w (hJH w hxJ))
  obtain ⟨b, hbi, hbw, hxb⟩ := hxJ
  obtain ⟨hb, e, he, hhist, hxU, hxstrip⟩ :=
    (Q.mem_narrowHistoryFamily active stop U P.normal P.offset r
      (Q.intrinsicNarrowStates code stop U r fraction) b x).mp hxb
  have hFb : x ∈ p.F b := hUpacket b hb _ hxU
  rw [hbw] at hhist
  have heq : e = q.code f := hhist.symm.trans hfcode
  rw [heq] at he hxstrip
  exact ⟨b, hbi, hbw, hFb, f, hf, hfw, hxf, he, hb, hxstrip⟩

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
