-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativePacketCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativePacketCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativePacketCap.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativePacketCap.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PathFacts
import Submission.Obl.k4_uncapped_native_capping.UWE.NativeSignalCap

/-!
# Continuous pure caps on actual original path packets

The accepted quadratic native-band cap applies to each actual path test.
The original source observation law and its density ceiling are retained.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal

section Path

variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {κ : ℝ} {C : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Event}
    {lst : ℕ → Fin W → BaseObservation → Finset (Fin C)}
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ
      C lev par γ j c u Q R A F lst)

include hp

/-- The assigned dyadic block of an actual packet lies in unit time. -/
theorem path_packet_time_unit (b : Fin C) {p : Event} (hF : p ∈ F b) :
    p.2 ∈ Icc (0 : ℝ) 1 := by
  have hs := (path_packet_support hp b hF).2.2.1
  have hj : (j b : ℝ) + 1 ≤ (2 : ℝ) ^ T (lev b) := by
    exact_mod_cast Nat.succ_le_of_lt (hp.2.2.2.2.2.2.2 b).2.1
  exact ⟨(by positivity : 0 ≤ (j b : ℝ) / (2 : ℝ) ^ T (lev b)).trans hs.1,
    hs.2.trans ((div_le_one (by positivity)).2 hj)⟩

/-- The actual old native test caps every finer signal band under the
ORIGINAL source observation law, with arbitrary signal center. -/
theorem path_packet_native_signal_cap (b : Fin C) {K a : ℝ} (hκK : κ ≤ K)
    (hB : 0 < B (γ b)) (ha : 0 < a) (haδ : a ≤ δ Nk (r (lev b)))
    (ρ : Measure Event)
    (hρ : ρ ≤ ((ν (γ b)).prod volume).restrict (E (γ b)))
    (g : BaseObservation → ENNReal) (hg : Measurable g)
    (hlaw : (((ν (γ b)).prod volume).restrict (E (γ b))).map
      (obs (B (γ b)) a) = (volume.prod Measure.count).withDensity g)
    (M : ENNReal) (z : ℝ)
    (hF : ∀ᵐ p ∂ρ, p ∈ F b)
    (hy : ∀ᵐ p ∂ρ, ‖y p.1 p.2‖ ≤ K)
    (hband : ∀ᵐ p ∂ρ, |MvPolynomial.eval (x p.1 p.2) (R b) - z| ≤ K * a)
    (htypical : ∀ᵐ p ∂ρ, g (obs (B (γ b)) a p) ≤ M) :
    ρ.map (fun p => (obs (B (γ b)) a p).1) ≤
      (M * ENNReal.ofReal (64 * K ^ 2)) • volume := by
  have hκ : 0 < κ := lt_of_lt_of_le zero_lt_one hp.1
  have hK : 1 ≤ K := hp.1.trans hκK
  rcases (hp.2.2.2.2.2.2.2 b).2.2 with
    ⟨_, _, _, _, hdeg, _, _, _, _, hwhole, _, _⟩
  apply k4_uncapped_native_capping.UWE.native_signal_band_base_cap
    (((ν (γ b)).prod volume).restrict (E (γ b))) ρ hρ hK hB ha
    (R b) hdeg z g hg hlaw M
  filter_upwards [hF, hy, hband, htypical] with p hpF hpy hpb hpg
  have hs := path_packet_support hp b hpF
  have htst := (hwhole p.1 hs.2.1).2.2 p.2 hs.2.2.1
  have htime := path_packet_time_unit hp b hpF
  refine ⟨htime, hpy, hpb, ?_, ?_, ?_, hpg⟩
  · exact htst.2.2.1.trans (mul_le_mul_of_nonneg_right hκK hB.le)
  · exact htst.2.2.2.trans (by gcongr)
  · exact (show B (γ b) / K ≤ B (γ b) / κ by gcongr).trans hs.2.2.2

/-- Every submeasure on an actual native packet has the continuous pure
cap inherited from its ORIGINAL source observation law. The cap parameter
may enlarge the path tolerance to include the original spatial bound. -/
theorem path_packet_native_base_cap (b : Fin C) {K : ℝ} (hκK : κ ≤ K)
    (hB : 0 < B (γ b)) (ρ : Measure Event)
    (hρ : ρ ≤ ((ν (γ b)).prod volume).restrict (E (γ b)))
    (g : BaseObservation → ENNReal) (hg : Measurable g)
    (hlaw : (((ν (γ b)).prod volume).restrict (E (γ b))).map
      (obs (B (γ b)) (δ Nk (r (lev b)))) = (volume.prod Measure.count).withDensity g)
    (M : ENNReal)
    (hF : ∀ᵐ p ∂ρ, p ∈ F b)
    (hy : ∀ᵐ p ∂ρ, ‖y p.1 p.2‖ ≤ K)
    (htypical : ∀ᵐ p ∂ρ, g (obs (B (γ b)) (δ Nk (r (lev b))) p) ≤ M) :
    ρ.map (fun p => (obs (B (γ b)) (δ Nk (r (lev b))) p).1) ≤
      (M * ENNReal.ofReal (64 * K ^ 2)) • volume := by
  have ha : 0 < δ Nk (r (lev b)) := by unfold δ; positivity
  apply path_packet_native_signal_cap hp b hκK hB ha le_rfl ρ hρ g hg hlaw M 0 hF hy
    _ htypical
  filter_upwards [hF] with p hpF
  rcases (hp.2.2.2.2.2.2.2 b).2.2 with
    ⟨_, _, _, _, _, _, _, _, _, hwhole, _, _⟩
  have hs := path_packet_support hp b hpF
  have hv := ((hwhole p.1 hs.2.1).2.2 p.2 hs.2.2.1).2.1
  simpa only [sub_zero] using hv.trans (mul_le_mul_of_nonneg_right hκK ha.le)

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
