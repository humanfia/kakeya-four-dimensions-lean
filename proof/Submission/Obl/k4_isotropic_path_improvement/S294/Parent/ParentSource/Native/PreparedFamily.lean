-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PreparedFamily, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PreparedFamily.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PreparedFamily.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PreparedFamily.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/PreparedFamily.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Partitions
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.MassPruning

/-! Keeping a substantial family of packets with fixed full-prior references. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable def PathData.heavyPackets {W : ℕ} (p : PathData W)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (i : ℕ) (c : ℝ) : Finset (Fin p.C) := by
  classical
  exact Finset.univ.filter fun b => p.lev b = i ∧
    ENNReal.ofReal (c / (2 : ℝ) ^ p.T i) * ν (p.γ b) (p.A b) ≤
      ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b)

def PathData.heavyResidual {W : ℕ} (p : PathData W)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (i : ℕ) (c : ℝ) (w : Fin W) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {z | z ∈ H w ∧ ∃ b ∈ p.heavyPackets ν H i c, p.γ b = w ∧ z ∈ p.F b}

section ValidPath

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

/-- The heavy packet family retains a fixed original residual fraction, and
every member has the same bounded domination by its frozen full-prior law. -/
theorem PathData.Valid.prepare_heavy_family_of_mass
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hmeas : ∀ w, MeasurableSet (H w))
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {a : ℝ} (ha : 0 < a) (hmass : ENNReal.ofReal a ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w)) (i : ℕ) (hi : i < m) :
    (∀ w, MeasurableSet (p.heavyResidual ν H i (a / 2) w) ∧
      p.heavyResidual ν H i (a / 2) w ⊆ H w) ∧
    ENNReal.ofReal (a / 2) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (p.heavyResidual ν H i (a / 2) w) ∧
    ∀ b ∈ p.heavyPackets ν H i (a / 2), p.lev b = i ∧
      IsProbabilityMeasure (p.referencePrior ν b) ∧
      IsProbabilityMeasure (p.referenceTime b) ∧
      IsProbabilityMeasure (p.residualPacketLaw ν H b) ∧
      p.residualPacketLaw ν H b ≤
        ENNReal.ofReal ((a / 2)⁻¹) • (p.referencePrior ν b).prod (p.referenceTime b) := by
  classical
  let c := a / 2
  let weight : Fin p.C → ENNReal :=
    fun b => if p.lev b = i then ENNReal.ofReal (ω (p.γ b)) else 0
  let reference : Fin p.C → ENNReal :=
    fun b => ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b)
  let selected : Fin p.C → ENNReal :=
    fun b => ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b)
  have htotal : ENNReal.ofReal (a) ≤ ∑ b, weight b * selected b := by
    have hs := hmass.trans_eq (h.residual_mass_eq_sum H hmeas hH i hi)
    simpa only [weight, selected, ite_mul, zero_mul] using hs
  have hgood := heavy_packet_mass_ge_half weight reference selected
    (a := a) (by positivity) (h.full_reference_mass_le_one hν hω hsum i) htotal
  have htest (b : Fin p.C) : ENNReal.ofReal (a / 2) * reference b =
      ENNReal.ofReal (c / (2 : ℝ) ^ p.T i) * ν (p.γ b) (p.A b) := by
    dsimp [reference]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
  have hsumgood : (∑ b, if ENNReal.ofReal (a / 2) * reference b ≤ selected b
      then weight b * selected b else 0) =
      ∑ b ∈ p.heavyPackets ν H i c, ENNReal.ofReal (ω (p.γ b)) * selected b := by
    rw [heavyPackets, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    rw [htest b]
    by_cases hb : p.lev b = i <;> simp [weight, hb, selected]
  have hgoodmass : ENNReal.ofReal c ≤
      ∑ b ∈ p.heavyPackets ν H i c, ENNReal.ofReal (ω (p.γ b)) * selected b := by
    rw [← hsumgood]
    exact hgood
  have hFmeas (b : Fin p.C) : MeasurableSet (p.F b) := by
    rcases h.2.2.2.2.2.2.2 b with ⟨_, _, _, _, _, _, _, _, _, hF, _⟩
    exact hF
  have hlevel (b : Fin p.C) (hb : b ∈ p.heavyPackets ν H i c) : p.lev b = i :=
    (Finset.mem_filter.mp hb).2.1
  have hunion (w : Fin W) :
      {z | ∃ b ∈ p.heavyPackets ν H i c, p.γ b = w ∧ z ∈ H (p.γ b) ∩ p.F b} =
        p.heavyResidual ν H i c w := by
    ext z
    constructor
    · rintro ⟨b, hb, hbw, hHz, hFz⟩
      exact ⟨by simpa only [hbw] using hHz, b, hb, hbw, hFz⟩
    · rintro ⟨hHz, b, hb, hbw, hFz⟩
      exact ⟨b, hb, hbw, by simpa only [hbw] using hHz, hFz⟩
  have hmixture : (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (p.heavyResidual ν H i c w)) =
      ∑ b ∈ p.heavyPackets ν H i c, ENNReal.ofReal (ω (p.γ b)) * selected b := by
    have heq := weighted_packet_union_mass (fun w => (ν w).prod volume)
      (fun w => ENNReal.ofReal (ω w)) p.γ (fun b => H (p.γ b) ∩ p.F b)
      (p.heavyPackets ν H i c) (fun b _ => (hmeas _).inter (hFmeas b))
      (fun b hb b' hb' hne hγ =>
        (h.packet_aedisjoint b b' hne ((hlevel b hb).trans (hlevel b' hb').symm) hγ).mono
          inter_subset_right inter_subset_right)
    simpa only [hunion] using heq
  refine ⟨?_, hgoodmass.trans_eq hmixture.symm, ?_⟩
  · intro w
    have heq : p.heavyResidual ν H i c w = H w ∩
        ⋃ b : Fin p.C, if b ∈ p.heavyPackets ν H i c ∧ p.γ b = w then p.F b else ∅ := by
      ext z
      simp only [heavyResidual, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_ite_empty_right]
      aesop
    refine ⟨?_, fun z hz => hz.1⟩
    rw [heq]
    apply (hmeas w).inter
    apply MeasurableSet.iUnion
    intro b
    split_ifs
    · exact hFmeas b
    · exact MeasurableSet.empty
  · intro b hb
    have hb' := (Finset.mem_filter.mp hb).2
    have hfloor : ENNReal.ofReal (c / (2 : ℝ) ^ p.T (p.lev b)) * ν (p.γ b) (p.A b) ≤
        ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) := by
      simpa only [hb'.1] using hb'.2
    have hpacket := h.conditional_packet_laws hNk hν H b (c := c) (by dsimp [c]; positivity) hfloor
    refine ⟨hb'.1, hpacket.1, hpacket.2.1, hpacket.2.2.1, ?_⟩
    exact hpacket.2.2.2


theorem PathData.Valid.prepare_heavy_family
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hmeas : ∀ w, MeasurableSet (H w))
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hmass : ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w)) (i : ℕ) (hi : i < m) :
    (∀ w, MeasurableSet (p.heavyResidual ν H i (p.κ⁻¹ / 4) w) ∧
      p.heavyResidual ν H i (p.κ⁻¹ / 4) w ⊆ H w) ∧
    ENNReal.ofReal (p.κ⁻¹ / 4) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (p.heavyResidual ν H i (p.κ⁻¹ / 4) w) ∧
    ∀ b ∈ p.heavyPackets ν H i (p.κ⁻¹ / 4), p.lev b = i ∧
      IsProbabilityMeasure (p.referencePrior ν b) ∧
      IsProbabilityMeasure (p.referenceTime b) ∧
      IsProbabilityMeasure (p.residualPacketLaw ν H b) ∧
      p.residualPacketLaw ν H b ≤
        ENNReal.ofReal (4 * p.κ) • (p.referencePrior ν b).prod (p.referenceTime b) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one h.1
  have hprep := h.prepare_heavy_family_of_mass hNk hν hω hsum H hmeas hH
    (a := p.κ⁻¹ / 2) (by positivity) hmass i hi
  have hhalf : p.κ⁻¹ / 2 / 2 = p.κ⁻¹ / 4 := by ring
  have hinv : (p.κ⁻¹ / 4)⁻¹ = 4 * p.κ := by field_simp
  simpa only [hhalf, hinv] using hprep

end ValidPath

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
