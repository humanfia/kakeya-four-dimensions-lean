-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Relative, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit 29e0a82c5, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/Relative.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- The unscaled virtual return: same N, L and gain, any ancestor depth (x1078, o204).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Orchestration

/-!
# Virtual packets with unscaled `L` and `gain`

The variant of `Tangent.Schedule`/`Tangent.Assembly` in which the virtual instance below an
ancestor keeps the same `N`, `L` and `gain`; only the depth `rb - rA`, the clock `Tb - TA` and the
block `jb - jA 2^(Tb - TA)` are relative. The ancestor depth `rA` is any real in `[0, rb]` (an
actual path depth, not a grid depth), so o288's exponent `Mc` is chosen once, for `(L, gain)`.
The price is the room `rb + L/4 ≤ L` of the packet: a returned `ag ≤ 1/8` then keeps
`rb + 2 ag L ≤ L`.

* `hpar_rel`, `virtual_direct_return_rel`: the return of a direct candidate.
* `cd_original_of_virtual_cd_rel`: o288's candidate at the virtual instance, at the restoration
  exponent, is the frozen `cd` of the original family.
* `virtual_instance_facts_rel`: o288's source-independent side conditions.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The exponent and thickness bookkeeping of `directAt_return`, unscaled schedule. -/
theorem hpar_rel (N L d₁ ρ gain ε εt rA rb : ℝ) (Tb TA : ℕ)
    (hN : 1 ≤ N) (hL : 0 ≤ L) (hroom : rb + L/4 ≤ L) (hεt : εt ≤ ε)
    (htwo : 2 ≤ N ^ (ε - εt)) (hT : TA ≤ Tb) :
    ∀ agt : ℝ, gain ≤ agt → agt ≤ 1/8 → (rb - rA) + 2*agt*L ≤ L → ∃ ag : ℝ,
      gain ≤ ag ∧ ag ≤ 1/8 ∧ rb + 2*ag*L ≤ L ∧
      Split.δ N rA * (N^(ρ*gain*L+εt) * Split.δ N ((rb - rA) + agt*L)) ≤
        N^(ρ*gain*L+ε) * Split.δ N (rb + ag*L) ∧
      N^(ρ*gain*L+εt) ≤ N^(ρ*gain*L+ε) ∧
      N^(ρ*gain*L+εt) * Split.δ N (rb + ag*L) ≤
        N^(ρ*gain*L+ε) * Split.δ N rA * Split.δ N ((rb - rA) + agt*L) ∧
      ENNReal.ofReal (N^(-((d₁*ag+ρ*gain)*L) - ε)/(2:ℝ)^Tb) ≤
        ENNReal.ofReal ((2:ℝ)^TA)⁻¹ * ENNReal.ofReal
          (N^(-((d₁*agt+ρ*gain)*L) - εt)/(2:ℝ)^(Tb - TA)) := by
  intro agt hgt hgt8 hrt
  have hdepth : rb + agt * L = rA + ((rb - rA) + agt * L) := by ring
  refine ⟨agt, hgt, hgt8, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · rw [hdepth]
    have h2 := δ_le_two_mul N rA ((rb - rA) + agt * L)
    have hpow : 2 * N ^ (ρ*gain*L+εt) ≤ N ^ (ρ*gain*L+ε) := by
      calc 2 * N ^ (ρ*gain*L+εt) ≤ N ^ (ε - εt) * N ^ (ρ*gain*L+εt) := by
            gcongr
        _ = N ^ (ρ*gain*L+ε) := by
            rw [← Real.rpow_add (by linarith)]; ring_nf
    have hN0 : 0 ≤ N ^ (ρ*gain*L+εt) := by positivity
    calc Split.δ N rA * (N ^ (ρ*gain*L+εt) * Split.δ N ((rb - rA) + agt * L))
        = N ^ (ρ*gain*L+εt) * (Split.δ N rA * Split.δ N ((rb - rA) + agt * L)) := by ring
      _ ≤ N ^ (ρ*gain*L+εt) * (2 * Split.δ N (rA + ((rb - rA) + agt * L))) := by gcongr
      _ = (2 * N ^ (ρ*gain*L+εt)) * Split.δ N (rA + ((rb - rA) + agt * L)) := by ring
      _ ≤ N ^ (ρ*gain*L+ε) * Split.δ N (rA + ((rb - rA) + agt * L)) := by
          gcongr; exact (δ_pos _ _).le
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · rw [hdepth]
    have h1 := δ_add_le N rA ((rb - rA) + agt * L)
    have hle : N ^ (ρ*gain*L+εt) ≤ N ^ (ρ*gain*L+ε) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    calc N ^ (ρ*gain*L+εt) * Split.δ N (rA + ((rb - rA) + agt * L))
        ≤ N ^ (ρ*gain*L+ε) * (Split.δ N rA * Split.δ N ((rb - rA) + agt * L)) :=
          mul_le_mul hle h1 (δ_pos _ _).le (by positivity)
      _ = _ := by ring
  · rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h2 : (2:ℝ) ^ Tb = (2:ℝ) ^ TA * (2:ℝ) ^ (Tb - TA) := by
      rw [← pow_add, Nat.add_sub_cancel' hT]
    rw [h2]
    have hle : N ^ (-((d₁*agt+ρ*gain)*L) - ε) ≤ N ^ (-((d₁*agt+ρ*gain)*L) - εt) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    calc N ^ (-((d₁*agt+ρ*gain)*L) - ε) / ((2:ℝ)^TA * (2:ℝ)^(Tb - TA))
        ≤ N ^ (-((d₁*agt+ρ*gain)*L) - εt) / ((2:ℝ)^TA * (2:ℝ)^(Tb - TA)) := by gcongr
      _ = ((2:ℝ)^TA)⁻¹ * (N ^ (-((d₁*agt+ρ*gain)*L) - εt) / (2:ℝ)^(Tb - TA)) := by
          field_simp

/-- The return of a direct candidate from the unscaled virtual packet below an ancestor. -/
theorem virtual_direct_return_rel
    (ν : Measure Ln) [SFinite ν] (A_A Ab : Set Ln) (H₀ H : Set Ev)
    (hAb : MeasurableSet Ab) (hAbA : Ab ⊆ A_A) (h0 : ν A_A ≠ 0) (hT : ν A_A ≠ ⊤)
    (hH₀ : MeasurableSet H₀) (hH₀H : H₀ ⊆ H)
    (c : P2) (a : Fin 4 → ℝ) (jA TA jb Tb : ℕ) (hTT : TA ≤ Tb) (hj : jA * 2 ^ (Tb - TA) ≤ jb)
    (B N L d₁ ρ gain ε εt rA rb : ℝ) (Mc Mct : ℕ) (hB : 0 < B) (hN : 1 ≤ N)
    (hL : 0 ≤ L) (hroom : rb + L/4 ≤ L) (hεt : εt ≤ ε)
    (htwo : 2 ≤ N ^ (ε - εt))
    (hcoeff : 81 * |Split.δ N rA| * N^Mct * residualBudget a 1 ^ 2 *
      (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA)).substBudget ^ 2 ≤ N^Mc)
    (htan : DirectAt N L
      (tanPrior (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA)) a ν A_A)
      1 Mct d₁ ρ gain εt (rb - rA) (Tb - TA) (jb - jA * 2 ^ (Tb - TA))
      (tanLine (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA)) a '' Ab)
      (tanEvent (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA)) a '' H₀)) :
    DirectAt N L ν B Mc d₁ ρ gain ε rb Tb jb Ab H := by
  set Φ := virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ c (B / Split.δ N rA) with hΦ
  have hq : 0 < Φ.F.q := by simp [hΦ, virtualFrame]
  have hD : Φ.F.D.det ≠ 0 := virtualFrame_det _ _ _ _ (by positivity)
  exact directAt_return_image Φ a hq hD ν A_A Ab H₀ H hAb hAbA h0 hT hH₀ hH₀H
    B (Split.δ N rA) hB (δ_pos _ _) rfl N L d₁ ρ gain ε rb Mc Tb jb
    N L ρ gain εt (rb - rA) Mct (Tb - TA) (jb - jA * 2 ^ (Tb - TA))
    (by linarith) (block_iff_virtual TA Tb jA jb hTT hj) hcoeff
    (hpar_rel N L d₁ ρ gain ε εt rA rb Tb TA hN hL hroom hεt htwo hTT) htan

/-- The unscaled virtual completion output, at the restoration exponent, returns to the
original packet `b` as the frozen candidate `cd` (direct alternative). -/
theorem cd_original_of_virtual_cd_rel
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
    (W : ℕ) (ν : Fin W → Measure Ln) [∀ w, SFinite (ν w)] (Bw : Fin W → ℝ) (r : ℕ → ℝ)
    (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set Ln) (H : Fin W → Set Ev) (b : Fin C)
    (A_A : Set Ln) (H₀ : Set Ev) (hAb : MeasurableSet (A b)) (hAbA : A b ⊆ A_A)
    (h0 : ν (γ b) A_A ≠ 0) (hT : ν (γ b) A_A ≠ ⊤) (hH₀ : MeasurableSet H₀)
    (hH₀H : H₀ ⊆ H (γ b))
    (cA : P2) (a : Fin 4 → ℝ) (jA TA : ℕ) (hTT : TA ≤ T (lev b))
    (hj : jA * 2 ^ (T (lev b) - TA) ≤ j b)
    (N L d₁ ρ gain ε εt rA : ℝ) (Mc Mct : ℕ) (hB : 0 < Bw (γ b)) (hN : 2 ≤ N)
    (hL : 0 ≤ L) (hroom : r (lev b) + L/4 ≤ L) (hεt : εt ≤ ε)
    (htwo : 2 ≤ N ^ (ε - εt))
    (hcoeff : 81 * |Split.δ N rA| * N^Mct * residualBudget a 1 ^ 2 *
      (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA (Bw (γ b) / Split.δ N rA)).substBudget ^ 2
        ≤ N^Mc)
    (hvirt : Submission.Obl.k4_physical_parent_potential_candidates.cd cc J D N L 1
      (fun _ => tanPrior (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
        (Bw (γ b) / Split.δ N rA)) a (ν (γ b)) A_A)
      (fun _ => 1) Mct d₁ ρ gain εt (fun _ => r (lev b) - rA)
      (fun _ => T (lev b) - TA) 1 (fun _ => 0) (fun _ => 0)
      (fun _ => j b - jA * 2 ^ (T (lev b) - TA))
      (fun _ => tanLine (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
        (Bw (γ b) / Split.δ N rA)) a '' A b)
      (fun _ => tanEvent (virtualFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
        (Bw (γ b) / Split.δ N rA)) a '' H₀)) :
    Split.cd cc' J D N L W ν Bw Mc d₁ ρ gain ε r T C lev γ j A H := by
  have hdir := hrestore J D hjet N L 1 _ _ Mct d₁ ρ gain εt _ _ 1 _ _ _ _ _ hN hvirt
  have hat := directAt_of_direct_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdir
  have hret := virtual_direct_return_rel (ν (γ b)) A_A (A b) H₀ (H (γ b)) hAb hAbA h0 hT hH₀
    hH₀H cA a jA TA (j b) (T (lev b)) hTT hj (Bw (γ b)) N L d₁ ρ gain ε εt rA (r (lev b)) Mc Mct
    hB (by linarith) hL hroom hεt htwo hcoeff hat
  exact Or.inl ((direct_iff_exists_directAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨b, hret⟩)

/-- The source-independent side conditions of o288 at the unscaled virtual instance. -/
theorem virtual_instance_facts_rel (ν : Measure Ln) (A_A : Set Ln) (h0 : ν A_A ≠ 0)
    (hT : ν A_A ≠ ⊤) (Φ : PFrame) (a : Fin 4 → ℝ) (L gain rA rb : ℝ) (Tb TA jA jb : ℕ)
    (hj : jA * 2 ^ (Tb - TA) ≤ jb) (hjup : jb < (jA + 1) * 2 ^ (Tb - TA))
    (hrA : 0 ≤ rA) (hrArb : rA ≤ rb) (hroom : rb + 2 * gain * L ≤ L) :
    IsProbabilityMeasure (tanPrior Φ a ν A_A) ∧
      jb - jA * 2 ^ (Tb - TA) < 2 ^ (Tb - TA) ∧ 0 ≤ rb - rA ∧
      (rb - rA) + 2 * gain * L ≤ L := by
  refine ⟨isProbability_tanPrior Φ a ν A_A h0 hT, ?_, by linarith, by linarith⟩
  rw [Nat.add_mul, one_mul] at hjup
  omega

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
