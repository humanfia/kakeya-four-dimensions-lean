-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativePredictionAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativePredictionAssembly.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativePredictionAssembly.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativePredictionAssembly.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativePredictionAssembly.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.TerminalAncestry
import Submission.Lib.K4RepresentativeAssembly.WitnessAssembly

/-! Native fine-packet witnesses for the accepted finite witness assembly.
Their terminal knowledge is pointwise and their polynomial format uses only
old packet predicates, endpoint uniqueness and terminal coverage. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4XInterface Submission.Lib.K4RepresentativeAssembly
open scoped BigOperators

def PathData.terminalCoverage {W : ℕ} (p : PathData W) (m : ℕ) (w : Fin W) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  packetPredictionUnion p.F (fun b => p.lev b = m - 1 ∧ p.γ b = w)

def PathData.packetWitness {W : ℕ} (p : PathData W) (m stop : ℕ) (w : Fin W) (b : Fin p.C) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  if p.lev b = stop ∧ p.γ b = w then
    (p.F b ∩ {z | packetUnique p.lev p.γ p.F w z}) ∩ p.terminalCoverage m w else ∅

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.measurableSet_packetWitness
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (stop : ℕ) (w : Fin W) (b : Fin p.C) :
    MeasurableSet (p.packetWitness m stop w b) := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  dsimp only [packetWitness]
  split
  · exact ((hF b).inter (measurableSet_packetUnique p.lev p.γ p.F hF w)).inter
      (measurableSet_packetPredictionUnion p.F hF _)
  · exact MeasurableSet.empty

theorem PathData.Valid.packetWitness_known
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (stop : ℕ) (w : Fin W)
    (b : Fin p.C) {z : (ℕ × (Fin 6 → ℝ)) × ℝ} (hz : z ∈ p.packetWitness m stop w b) :
    b ∈ terminalAncestorList p m w (obs (B w) (δ Nk L) z) := by
  classical
  by_cases hb : p.lev b = stop ∧ p.γ b = w
  · have hh : (z ∈ p.F b ∧ packetUnique p.lev p.γ p.F w z) ∧
        z ∈ p.terminalCoverage m w := by simpa only [packetWitness, ite_eq_left hb, mem_inter_iff, mem_ofPred_eq] using hz
    obtain ⟨t, ht, hzt⟩ := hh.2
    exact hp.terminalAncestorList_mem w z hh.1.2 ⟨t, ht.1, ht.2, hzt⟩ b hb.2 hh.1.1
  · simp only [packetWitness, ite_eq_right hb, mem_empty_iff_false] at hz

/-- The code/compatibility table is absent from the polynomial atom budget. -/
theorem PathData.Valid.packetWitness_section_format
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 0 < Nk)
    (stop : ℕ) (w : Fin W) (b : Fin p.C) (copy : ℕ) :
    gfmt 7 (Nk ^ Mp + 2 * (p.C : ℝ) ^ 2 * Nk ^ Mp + (p.C : ℝ) * Nk ^ Mp) Dp
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ p.packetWitness m stop w b} := by
  classical
  have hF (a : Fin p.C) : gfmt 7 (Nk ^ Mp) Dp
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ p.F a} := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hfmt, _⟩ := hp.2.2.2.2.2.2.2 a
    exact (hfmt copy).2
  by_cases hb : p.lev b = stop ∧ p.γ b = w
  · have hU := hp.packet_unique_section_format hN w copy
    have hT := hp.prediction_union_section_format hN
      (fun a => p.lev a = m - 1 ∧ p.γ a = w) copy
    have heq : {z : Fin 7 → ℝ |
        ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ p.packetWitness m stop w b} =
        ({z | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ p.F b} ∩
          {z | packetUnique p.lev p.γ p.F w ((copy, fun j : Fin 6 => z j.castSucc), z 6)}) ∩
          {z | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈
            packetPredictionUnion p.F (fun a => p.lev a = m - 1 ∧ p.γ a = w)} := by
      ext z
      simp only [packetWitness, ite_eq_left hb, terminalCoverage, mem_inter_iff, mem_ofPred_eq]
    rw [heq]
    simpa only [max_self] using fmt_inter (fmt_inter (hF b) hU) hT
  · simp only [packetWitness, ite_eq_right hb, mem_empty_iff_false, Set.ofPred_false]
    exact fmt_mono (fmt_empty 7 Dp) (by positivity) le_rfl

/-- Accepted finite witness assembly gives a short list for every retained
incidence; global bin/net count never appears in this bound. -/
theorem PathData.Valid.merged_packetWitness_known {β : Type*} [DecidableEq β]
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (stop : ℕ) (w : Fin W) (compat : Fin p.C → Finset β)
    (G : β → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    {a : β} {z : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hz : z ∈ mergedWitnessEvents (p.packetWitness m stop w) compat G a) :
    a ∈ composedList (terminalAncestorList p m w (obs (B w) (δ Nk L) z)) compat :=
  mergedWitnessEvents_list (p.packetWitness m stop w) compat G
    (obs (B w) (δ Nk L)) (terminalAncestorList p m w)
    (fun b _ hz => hp.packetWitness_known stop w b hz) hz

theorem PathData.Valid.merged_packetWitness_list_card {β : Type*} [DecidableEq β]
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ)
    (compat : Fin p.C → Finset β) (K : ℝ) (hK : 0 ≤ K)
    (hcompat : ∀ b, ((compat b).card : ℝ) ≤ K) :
    ((composedList (terminalAncestorList p m w o) compat).card : ℝ) ≤ m * p.κ * K :=
  (card_composedList_le _ compat (fun b _ => hcompat b)).trans
    (mul_le_mul_of_nonneg_right (terminalAncestorList_card p m hp.2.2.2.2.2.1 w o) hK)

/-- Any later residual is enlarged to old finite-format witness sets. Its
mass is measured under the ORIGINAL world law throughout. -/
theorem PathData.Valid.original_mass_into_packetWitness {β : Type*} [DecidableEq β] [Fintype β]
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (stop : ℕ) (w : Fin W) (compat : Fin p.C → Finset β)
    (G : β → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (J : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcover : ∀ z ∈ J, z ∈ p.terminalCoverage m w)
    (hsuccess : ∀ z ∈ J, ∃ b a, p.lev b = stop ∧ p.γ b = w ∧
      z ∈ p.F b ∧ a ∈ compat b ∧ z ∈ G a) :
    ((ν w).prod volume) J ≤
      ∑ a, ((ν w).prod volume) (mergedWitnessEvents (p.packetWitness m stop w) compat G a) := by
  have hcongr : ((ν w).prod volume) (J ∩ {z | packetUnique p.lev p.γ p.F w z}) =
      ((ν w).prod volume) J := by
    apply measure_congr
    filter_upwards [hp.ae_packet_unique w] with z hz
    simp only [mem_inter_iff, mem_ofPred_eq, hz, and_true]
  rw [← hcongr]
  apply successfulMass_le_mergedWitnessEvents
  rintro z ⟨hzJ, hzU⟩
  obtain ⟨b, a, hb, hbw, hzb, hcompat, hzG⟩ := hsuccess z hzJ
  refine ⟨b, a, ?_, hcompat, hzG⟩
  simpa only [packetWitness, ite_eq_left (show p.lev b = stop ∧ p.γ b = w from ⟨hb, hbw⟩),
    mem_inter_iff, mem_ofPred_eq]
    using (show (z ∈ p.F b ∧ packetUnique p.lev p.γ p.F w z) ∧
      z ∈ p.terminalCoverage m w from ⟨⟨hzb, hzU⟩, hcover z hzJ⟩)

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
