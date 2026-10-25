-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Assembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit c3fccb87c, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/Assembly.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- From the virtual completion output to the original candidate (x1078, o204).
-- `restoration_exponent` is adapted from this LOT tree, o204, session x1079, branch x1079,
-- commit 875d9736, file Submission/Obl/k4_uniform_sampled_isotropic_branches/
-- PhysicalDirectRestoration.lean (`exists_direct_restoration_exponent`), restated here with the
-- frozen `direct` of `Split`; it uses only accepted o144 and o288.
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.VirtualReturn
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.ChartTransport
import Submission.Obl.k4_physical_parent_potential_candidates.Statement
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.Expanded
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.SampledCandidate
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.NormalizedCandidate
import Submission.Obl.k4_seven_direction_local_degree_restoration

/-!
# Assembly of the virtual route

* `restoration_exponent`: one local exponent `cc`, chosen before every degree, jet exponent and
  source, for which every candidate of o288 at `cc` is a direct quadratic candidate (accepted
  o144 local restoration and o288's sampled-to-normalized-to-candidate conversion).
* `cd_original_of_virtual_cd`: o288's candidate at the one-packet virtual instance below an
  ancestor (prior `tanPrior`, unit one, image assignment and residual sets, same `N`, schedule
  of `Tangent.Schedule`) is the frozen candidate `cd` of the original family at packet `b`.
* `virtual_instance_facts`: the side conditions of o288 at the virtual instance that do not
  depend on the source (probability, unit, block index, depth room).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- One restoration exponent turns every o288 candidate into a direct one. -/
theorem restoration_exponent :
    ∃ cc : ℕ, 1 ≤ cc ∧ ∀ (J D : ℕ),
      Submission.Obl.k4_physical_parent_potential_candidates.JointJetBound D J →
      ∀ (Nk L : ℝ) (W : ℕ) (ν : Fin W → Measure Ln) (B : Fin W → ℝ)
        (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
        (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
        (A : Fin C → Set Ln) (H : Fin W → Set Ev),
        2 ≤ Nk →
        Submission.Obl.k4_physical_parent_potential_candidates.cd cc J D Nk L W ν B Mc d₁ ρ gain ε
          r T C lev γ j A H →
        Split.direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  have hlocal : Submission.Obl.k4_physical_parent_potential_candidates.Analytic.LocalRestorationAssertion :=
    Submission.k4_seven_direction_local_degree_restoration
  obtain ⟨cc, hcc, hrestore⟩ :=
    Submission.Obl.k4_physical_parent_potential_candidates.Analytic.apply_local_restoration hlocal
  refine ⟨cc, hcc, ?_⟩
  intro J D hjet Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H hNk hc
  rcases hc with hdirect | hsampled
  · exact hdirect
  · have hraw : Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RawSampledCandidate
        cc J D Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := hsampled
    have hs := Submission.Obl.k4_physical_parent_potential_candidates.Analytic.rawSampledCandidate_implies_sampled
      Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H hraw
    have hn := Submission.Obl.k4_physical_parent_potential_candidates.Analytic.sampledCandidate_implies_normalized
      hjet Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H hs
    exact Submission.Obl.k4_physical_parent_potential_candidates.Analytic.normalizedCandidate_implies_candidate
      cc hrestore Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H hNk hn

/-- The virtual completion output, at the restoration exponent, returns to the original
packet `b` of the original family, as the frozen candidate `cd` (direct alternative). -/
theorem cd_original_of_virtual_cd
    (cc : ℕ)
    (hrestore : ∀ (J D : ℕ),
      Submission.Obl.k4_physical_parent_potential_candidates.JointJetBound D J →
      ∀ (Nk L : ℝ) (W : ℕ) (ν : Fin W → Measure Ln) (B : Fin W → ℝ)
        (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
        (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
        (A : Fin C → Set Ln) (H : Fin W → Set Ev),
        2 ≤ Nk →
        Submission.Obl.k4_physical_parent_potential_candidates.cd cc J D Nk L W ν B Mc d₁ ρ gain ε
          r T C lev γ j A H →
        Split.direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H)
    (cc' J D : ℕ)
    (hjet : Submission.Obl.k4_physical_parent_potential_candidates.JointJetBound D J)
    -- the original family and its packet `b`
    (W : ℕ) (ν : Fin W → Measure Ln) [∀ w, SFinite (ν w)] (Bw : Fin W → ℝ) (r : ℕ → ℝ)
    (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Ln) (H : Fin W → Set Ev) (b : Fin C)
    -- the ancestor and the residual source
    (A_A : Set Ln) (H₀ : Set Ev) (hAb : MeasurableSet (A b)) (hAbA : A b ⊆ A_A)
    (h0 : ν (γ b) A_A ≠ 0) (hT : ν (γ b) A_A ≠ ⊤) (hH₀ : MeasurableSet H₀)
    (hH₀H : H₀ ⊆ H (γ b))
    (cA : P2) (a : Fin 4 → ℝ) (jA TA : ℕ) (hTT : TA ≤ T (lev b))
    (hj : jA * 2 ^ (T (lev b) - TA) ≤ j b)
    (N L d₁ ρ gain ε εt rA : ℝ) (Mc Mct : ℕ) (hB : 0 < Bw (γ b)) (hN : 2 ≤ N)
    (hgain : 0 ≤ gain) (hrA : 0 ≤ rA) (hrAL : rA < L) (hεt : εt ≤ ε)
    (htwo : 2 ≤ N ^ (ε - εt))
    (hcoeff : 81 * |Split.δ N rA| * N^Mct * residualBudget a 1 ^ 2 *
      (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA (Bw (γ b) / Split.δ N rA)).substBudget ^ 2
        ≤ N^Mc)
    (hvirt : Submission.Obl.k4_physical_parent_potential_candidates.cd cc J D N (L - rA) 1
      (fun _ => tanPrior (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
        (Bw (γ b) / Split.δ N rA)) a (ν (γ b)) A_A)
      (fun _ => 1) Mct d₁ ρ (gain * L / (L - rA)) εt (fun _ => r (lev b) - rA)
      (fun _ => T (lev b) - TA) 1 (fun _ => 0) (fun _ => 0)
      (fun _ => j b - jA * 2 ^ (T (lev b) - TA))
      (fun _ => tanLine (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
        (Bw (γ b) / Split.δ N rA)) a '' A b)
      (fun _ => tanEvent (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
        (Bw (γ b) / Split.δ N rA)) a '' H₀)) :
    Split.cd cc' J D N L W ν Bw Mc d₁ ρ gain ε r T C lev γ j A H := by
  have hdir := hrestore J D hjet N (L - rA) 1 _ _ Mct d₁ ρ (gain * L / (L - rA)) εt _ _ 1 _ _ _ _ _
    hN hvirt
  have hat := directAt_of_direct_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdir
  have hret := virtual_direct_return (ν (γ b)) A_A (A b) H₀ (H (γ b)) hAb hAbA h0 hT hH₀ hH₀H
    cA a jA TA (j b) (T (lev b)) hTT hj (Bw (γ b)) N L d₁ ρ gain ε εt rA (r (lev b)) Mc Mct hB
    (by linarith) hgain hrA hrAL hεt htwo hcoeff hat
  exact Or.inl ((direct_iff_exists_directAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨b, hret⟩)

/-- The source-independent side conditions of o288 at the virtual instance. -/
theorem virtual_instance_facts (ν : Measure Ln) (A_A : Set Ln) (h0 : ν A_A ≠ 0)
    (hT : ν A_A ≠ ⊤) (Φ : PFrame) (a : Fin 4 → ℝ) (L gain rA rb : ℝ) (Tb TA jA jb : ℕ)
    (hj : jA * 2 ^ (Tb - TA) ≤ jb) (hjup : jb < (jA + 1) * 2 ^ (Tb - TA))
    (hrAL : rA < L)
    (hrArb : rA ≤ rb) (hroom : rb + 2 * gain * L ≤ L) :
    IsProbabilityMeasure (tanPrior Φ a ν A_A) ∧
      jb - jA * 2 ^ (Tb - TA) < 2 ^ (Tb - TA) ∧ 0 ≤ rb - rA ∧
      (rb - rA) + 2 * (gain * L / (L - rA)) * (L - rA) ≤ L - rA := by
  refine ⟨isProbability_tanPrior Φ a ν A_A h0 hT, ?_, by linarith, ?_⟩
  · -- the packet's block lies inside the ancestor's block
    rw [Nat.add_mul, one_mul] at hjup
    omega
  · have hLt : 0 < L - rA := sub_pos.mpr hrAL
    have : 2 * (gain * L / (L - rA)) * (L - rA) = 2 * gain * L := by field_simp
    rw [this]; linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
