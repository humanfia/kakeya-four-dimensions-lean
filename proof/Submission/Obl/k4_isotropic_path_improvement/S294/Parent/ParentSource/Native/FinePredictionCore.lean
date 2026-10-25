-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FinePredictionCore, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FinePredictionCore.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FinePredictionCore.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FinePredictionCore.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/FinePredictionCore.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.HistoryPackets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.TerminalLists
import Submission.Lib.K4RepresentativeAssembly.FiniteFormat

/-! Fine packet predictions give pointwise terminal knowledge without
encoding an arbitrary residual. The only discarded code discrepancies are
null under the original incidence law, before any residual is chosen. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4XInterface
open scoped BigOperators

structure PacketCoding {W : ℕ} (p : PathData W)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) where
  code : Fin p.C → ℕ
  ae_code : ∀ b, ∀ᵐ z ∂(ν (p.γ b)).prod volume,
    finitePacketHistory p.lev p.γ p.F (p.lev b) (p.γ b, z) = code b ↔ z ∈ p.F b

section Coding

variable {W : ℕ} {p : PathData W} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    (q : PacketCoding p ν)

def PacketCoding.core (w : Fin W) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {z | ∀ b, p.γ b = w →
    (finitePacketHistory p.lev p.γ p.F (p.lev b) (w, z) = q.code b ↔ z ∈ p.F b)}

theorem PacketCoding.measurableSet_core (hF : ∀ b, MeasurableSet (p.F b)) (w : Fin W) :
    MeasurableSet (q.core w) := by
  have heq : q.core w = ⋂ b, {z | p.γ b = w →
      (finitePacketHistory p.lev p.γ p.F (p.lev b) (w, z) = q.code b ↔ z ∈ p.F b)} := by
    ext z
    simp only [core, mem_ofPred_eq, mem_iInter]
  rw [heq]
  apply MeasurableSet.iInter
  intro b
  have hm : Measurable (fun z : (ℕ × (Fin 6 → ℝ)) × ℝ =>
      finitePacketHistory p.lev p.γ p.F (p.lev b) (w, z)) :=
    (measurable_finitePacketHistory p.lev p.γ p.F hF (p.lev b)).comp measurable_prodMk_left
  exact (MeasurableSet.const (p.γ b = w)).imp
    ((measurableSet_eq_fun hm measurable_const).iff (hF b))

theorem PacketCoding.ae_core (w : Fin W) : ∀ᵐ z ∂(ν w).prod volume, z ∈ q.core w := by
  apply ae_all_iff.mpr
  intro b
  by_cases hb : p.γ b = w
  · have h := q.ae_code b
    rw [hb] at h
    filter_upwards [h] with z hz
    exact fun _ => hz
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hb h))

theorem PacketCoding.original_mass_core (w : Fin W) (D : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) :
    ((ν w).prod volume) (D ∩ q.core w) = ((ν w).prod volume) D := by
  apply measure_congr
  filter_upwards [q.ae_core w] with z hz
  simp only [mem_inter_iff, hz, and_true]

theorem PacketCoding.code_eq_of_mem_core (w : Fin W) {z : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hz : z ∈ q.core w) (b : Fin p.C) (hbw : p.γ b = w) (hzb : z ∈ p.F b) :
    finitePacketHistory p.lev p.γ p.F (p.lev b) (w, z) = q.code b :=
  (hz b hbw).mpr hzb

end Coding

/-- The prediction is a finite table on OLD fine packets. Eligibility of a
packet for an output label is a constant, not a new source predicate. -/
def packetPredictionUnion {C : ℕ} {X : Type*} (F : Fin C → Set X)
    (eligible : Fin C → Prop) : Set X := {z | ∃ b, eligible b ∧ z ∈ F b}

theorem measurableSet_packetPredictionUnion {C : ℕ} {X : Type*} [MeasurableSpace X]
    (F : Fin C → Set X) (hF : ∀ b, MeasurableSet (F b)) (eligible : Fin C → Prop) :
    MeasurableSet (packetPredictionUnion F eligible) := by
  classical
  have heq : packetPredictionUnion F eligible = ⋃ b, if eligible b then F b else ∅ := by
    ext z
    simp only [packetPredictionUnion, mem_ofPred_eq, mem_iUnion]
    aesop
  rw [heq]
  apply MeasurableSet.iUnion
  intro b
  split
  · exact hF b
  · exact MeasurableSet.empty

theorem packetPredictionUnion_format {C n D : ℕ} {H : ℝ} (hH : 0 ≤ H)
    (F : Fin C → Set (Fin n → ℝ)) (hF : ∀ b, gfmt n H D (F b)) (eligible : Fin C → Prop) :
    gfmt n ((C : ℝ) * H) D (packetPredictionUnion F eligible) := by
  classical
  have hh := Submission.Lib.K4RepresentativeAssembly.fmt_selected_iUnion F
    (fun b => decide (eligible b)) true hH hF
  convert hh using 1
  ext z
  simp only [packetPredictionUnion, mem_ofPred_eq, mem_iUnion, decide_eq_true_eq]
  aesop

/-- Endpoint uniqueness is a finite Boolean condition on the OLD packets.
Removing it from later geometric success sets costs only polynomial format. -/
theorem packetUnique_format {W C n D : ℕ} {H : ℝ} (hH : 0 ≤ H)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (F : Fin C → Set (Fin n → ℝ))
    (hF : ∀ b, gfmt n H D (F b)) (w : Fin W) :
    gfmt n (2 * (C : ℝ) ^ 2 * H) D {z | packetUnique lev γ F w z} := by
  classical
  let B : Fin C → Set (Fin n → ℝ) := fun b => packetPredictionUnion
    (fun b' => F b ∩ F b')
    (fun b' => b ≠ b' ∧ lev b = lev b' ∧ γ b = w ∧ γ b' = w)
  have hB (b : Fin C) : gfmt n ((C : ℝ) * (H + H)) D (B b) := by
    apply packetPredictionUnion_format (by positivity)
    intro b'
    simpa only [max_self] using Submission.Lib.K4RepresentativeAssembly.fmt_inter (hF b) (hF b')
  have hAll := packetPredictionUnion_format (by positivity : 0 ≤ (C : ℝ) * (H + H))
    B hB (fun _ => True)
  have heq : {z | packetUnique lev γ F w z} = (packetPredictionUnion B (fun _ => True))ᶜ := by
    ext z
    constructor
    · intro hz hbad
      obtain ⟨b, _, b', helig, hzb, hzb'⟩ := hbad
      exact helig.1 (hz b b' helig.2.1 helig.2.2.1 helig.2.2.2 hzb hzb')
    · intro hz b b' hlev hγ hγ' hzb hzb'
      by_contra hne
      exact hz ⟨b, trivial, b', ⟨hne, hlev, hγ, hγ'⟩, hzb, hzb'⟩
  rw [heq]
  have hcost : (C : ℝ) * ((C : ℝ) * (H + H)) = 2 * (C : ℝ) ^ 2 * H := by ring
  simpa only [hcost] using Submission.Lib.K4RepresentativeAssembly.fmt_compl hAll

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.exists_packetCoding
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 0 < Nk) :
    Nonempty (PacketCoding p ν) := by
  classical
  choose code hcode using hp.history_code_of_packet hN
  exact ⟨⟨code, hcode⟩⟩

/-- Only the chosen fine depth must be above the terminal observation width.
The old lists themselves are allowed to be arbitrary functions. -/
theorem PathData.Valid.prediction_union_known
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (i : ℕ) (hr : p.r i ≤ L) (w : Fin W) (eligible : Fin p.C → Prop)
    (helig : ∀ b, eligible b → p.lev b = i ∧ p.γ b = w)
    {z : (ℕ × (Fin 6 → ℝ)) × ℝ} (hz : z ∈ packetPredictionUnion p.F eligible) :
    ∃ b ∈ p.lst i w (Submission.Lib.K4Homogenization.coarsenObservation Nk (p.r i) L
      (obs (B w) (δ Nk L) z)), eligible b ∧ z ∈ p.F b := by
  obtain ⟨b, hb, hzb⟩ := hz
  obtain ⟨hbi, hbw⟩ := helig b hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hknown, _⟩ :=
    hp.2.2.2.2.2.2.2 b
  have hpred := hknown z hzb
  rw [hbi, hbw, obs_coarsen hN hr] at hpred
  exact ⟨b, hpred, hb, hzb⟩

/-- A successful-incidence restriction uses only a finite union of old
source sections. Its format cost is polynomial in the OLD packet count. -/
theorem PathData.Valid.prediction_union_section_format
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 0 < Nk)
    (eligible : Fin p.C → Prop) (copy : ℕ) :
    gfmt 7 ((p.C : ℝ) * Nk ^ Mp) Dp
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ packetPredictionUnion p.F eligible} := by
  have hF (b : Fin p.C) : gfmt 7 (Nk ^ Mp) Dp
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ p.F b} := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hfmt, _⟩ := hp.2.2.2.2.2.2.2 b
    exact (hfmt copy).2
  exact packetPredictionUnion_format (by positivity) _ hF eligible

theorem PathData.Valid.packet_unique_section_format
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 0 < Nk)
    (w : Fin W) (copy : ℕ) :
    gfmt 7 (2 * (p.C : ℝ) ^ 2 * Nk ^ Mp) Dp
      {z : Fin 7 → ℝ | packetUnique p.lev p.γ p.F w
        ((copy, fun j : Fin 6 => z j.castSucc), z 6)} := by
  apply packetUnique_format (by positivity)
  intro b
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hfmt, _⟩ := hp.2.2.2.2.2.2.2 b
  exact (hfmt copy).2

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
