/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFiniteFirstJet.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFiniteFirstJet.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformFirstJet
import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity

/-! Finite first-jet thresholds from a certificate uniform over all original worlds. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

universe u

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts

def ScalarFirstJetUniformAt (a b d : ℝ) (m : ℕ) (ε α N : ℝ) : Prop :=
  ∀ (Λ : Type u) [MeasurableSpace Λ],
    ∀ (D : ScalarMotion Λ) (ν : Measure Λ) [IsProbabilityMeasure ν]
      (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ) (K ζ : ℝ)
      (start : Fin m → ℕ) (read : Fin m),
      1 ≤ K → K ≤ N ^ α → ScalarNormalHyp D ν E F S K ζ d → 0 < ζ →
      K⁻¹ ≤ (ν.prod volume).real E → ζ ≤ N ^ (-(4 * b)) →
      (∀ i, N ^ (-b) ≤ scalarDyadicLength (start i)) →
      (∀ i, scalarDyadicLength (start i) ≤ N ^ (-a)) →
      ScalarFirstJetOutput D ν E F start read d (N ^ ε)

/-- The input exponent and threshold precede every label space and
world. A unit model suffices because the sequence estimate already
holds eventually for ALL such worlds at once. -/
theorem finite_original_scalar_first_jet_between_powers_all_labels
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ScalarFirstJetUniformAt.{u} a b d m ε α N := by
  obtain ⟨α, hα, N₀, hN₀, hfinite⟩ :=
    Submission.Obl.k4_scalar_mesh_block_reduction.uniformity_of_sequence
      (Model := fun _ _ => Unit) (fun _ _ _ => True)
      (fun α N _ => ScalarFirstJetUniformAt.{u} a b d m ε α N) (by
        intro η Ns hη hηlim hNtwo hNt model hadmissible
        have hN : ∀ k, 1 ≤ Ns k := fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hNtwo k)
        let Ks : ℕ → ℝ := fun k => Ns k ^ η k
        obtain ⟨hKs, hKssub⟩ :=
          Submission.Obl.k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
            Ns η hN (fun k => (hη k).le) hηlim
        obtain ⟨H, hH, hHsub, hgood⟩ :=
          uniform_original_scalar_first_jet_between_powers_all_labels Ns Ks hN hNt hKs hKssub
            ha hab hd0 hd m
        obtain ⟨k, hk, hsmall⟩ := (hgood.and (hHsub ε hε)).exists
        refine ⟨k, ?_⟩
        intro Λ _ D ν _ E F S K ζ start read hK hKN hnormal hζ hmass hζN hlow hhigh
        have hnormalk : ScalarNormalHyp D ν E F S (Ks k) ζ d :=
          hnormal.increase_constant hζ hKN
        have hmassk : (Ks k)⁻¹ ≤ (ν.prod volume).real E :=
          (inv_anti₀ (zero_lt_one.trans_le hK) hKN).trans hmass
        have houtput := hk Λ D ν E F S ζ start read hnormalk hζ hmassk hζN hlow hhigh
        exact houtput.mono (zero_lt_one.trans_le (hH k)) hsmall)
  exact ⟨α, hα, N₀, hN₀, fun N hN => hfinite N hN () trivial⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
