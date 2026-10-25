-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.DirectReturn, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit c3fccb87c, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/DirectReturn.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- Return of a direct quadratic candidate from a tangent instance (x1078, o204).
-- Uses the accepted o280 return lemmas (`fitS_affine_return`, `affine_lower_return`,
-- `coeff_affineLift_quadratic_le`), imported, not copied.
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Frame

/-!
# The direct candidate returns through a tangent frame

`DirectAt` is the direct quadratic alternative of the frozen candidate `cd` at one packet.
`direct_iff_exists_directAt` identifies the frozen family form with a choice of packet, and
`directAt_of_direct_one` reads it off a one-packet tangent instance.

`directAt_return`: a direct candidate of the tangent instance (frozen coordinates, prior
`tanPrior Φ a ν A₀`, hidden unit one) gives the direct candidate of the original packet with
test `Φ.affineLift a δA R`. The exponent, thickness and mass bookkeeping between the tangent and
original parameters is an explicit hypothesis `hpar`, discharged separately for each schedule.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory MvPolynomial
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The frozen direct quadratic candidate at one packet. -/
def DirectAt (Nk L : ℝ) (ν : Measure Ln) (B : ℝ) (Mc : ℕ) (d₁ ρ gain ε r : ℝ) (T j : ℕ)
    (A : Set Ln) (H : Set Ev) : Prop :=
  ∃ ag : ℝ, gain ≤ ag ∧ ag ≤ 1/8 ∧ r + 2*ag*L ≤ L ∧ ∃ (R : Po) (A' : Set Ln),
    R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Nk^Mc) ∧ MeasurableSet A' ∧ A' ⊆ A ∧
    (∀ l ∈ A', ∀ t ∈ Set.Icc ((j:ℝ)/(2:ℝ)^T) (((j:ℝ)+1)/(2:ℝ)^T),
      |MvPolynomial.eval (xp l t) R| ≤ Nk^(ρ*gain*L+ε) * Split.δ Nk (r + ag*L) ∧
      |MvPolynomial.eval (xp l t) (MvPolynomial.pderiv 3 R)| ≤ Nk^(ρ*gain*L+ε) * B ∧
      |MvPolynomial.eval (xp l t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R))| ≤
        Nk^(ρ*gain*L+ε) * B^2 / Split.δ Nk (r + ag*L)) ∧
    ENNReal.ofReal (Nk^(-((d₁*ag+ρ*gain)*L) - ε)/(2:ℝ)^T) * ν A ≤
      (ν.prod volume) {p | p ∈ H ∧ p.1 ∈ A' ∧
        p.2 ∈ Set.Icc ((j:ℝ)/(2:ℝ)^T) (((j:ℝ)+1)/(2:ℝ)^T) ∧
        B/Nk^(ρ*gain*L+ε) ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 R)|}

/-- The frozen family form is a choice of one packet. -/
theorem direct_iff_exists_directAt (Nk L : ℝ) (W : ℕ) (ν : Fin W → Measure Ln) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ)
    (γ : Fin C → Fin W) (j : Fin C → ℕ) (A : Fin C → Set Ln) (H : Fin W → Set Ev) :
    direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H ↔
      ∃ b : Fin C, DirectAt Nk L (ν (γ b)) (B (γ b)) Mc d₁ ρ gain ε (r (lev b)) (T (lev b))
        (j b) (A b) (H (γ b)) := Iff.rfl

/-- A one-packet instance carries its candidate at that packet. -/
theorem directAt_of_direct_one (Nk L : ℝ) (ν : Measure Ln) (B : ℝ) (Mc : ℕ)
    (d₁ ρ gain ε r : ℝ) (T j : ℕ) (A : Set Ln) (H : Set Ev)
    (h : direct Nk L 1 (fun _ => ν) (fun _ => B) Mc d₁ ρ gain ε (fun _ => r) (fun _ => T) 1
      (fun _ => 0) (fun _ => 0) (fun _ => j) (fun _ => A) (fun _ => H)) :
    DirectAt Nk L ν B Mc d₁ ρ gain ε r T j A H := by
  obtain ⟨_, h⟩ := (direct_iff_exists_directAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp h
  exact h

lemma measurable_xp_eval (R : Po) : Measurable (fun p : Ev => MvPolynomial.eval (xp p.1 p.2) R) := by
  have hpt : Measurable (fun p : Ev => xp p.1 p.2) := by
    refine measurable_pi_iff.mpr (fun i => ?_)
    fin_cases i <;> simp [xp] <;> fun_prop
  exact (MvPolynomial.continuous_eval R).measurable.comp hpt

/-- The direct candidate of a tangent instance returns to the original packet. -/
theorem directAt_return
    (Φ : PFrame) (a : Fin 4 → ℝ) (hq : 0 < Φ.F.q)
    (ν : Measure Ln) [SFinite ν] (A₀ Ab At : Set Ln) (H Ht : Set Ev)
    (hAb : MeasurableSet Ab) (hAbA₀ : Ab ⊆ A₀) (h0 : ν A₀ ≠ 0) (hT : ν A₀ ≠ ⊤)
    (hAtm : MeasurableSet At) (hHt : MeasurableSet Ht)
    (hAt_in : ∀ l ∈ Ab, tanLine Φ a l ∈ At)
    (hAt_back : ∀ l ∈ A₀, tanLine Φ a l ∈ At → l ∈ Ab)
    (hH_back : ∀ p : Ev, p.1 ∈ A₀ → tanEvent Φ a p ∈ Ht → p ∈ H)
    (B δA : ℝ) (hB : 0 < B) (hδA : 0 < δA) (hsc : Φ.sc = B / δA)
    (N L d₁ ρ gain ε rb : ℝ) (Mc Tb jb : ℕ)
    (Nt Lt ρt gaint εt rt : ℝ) (Mct Tt jt : ℕ) (hNt : 0 < Nt)
    (hblock : ∀ t ∈ Set.Icc ((jb:ℝ)/(2:ℝ)^Tb) (((jb:ℝ)+1)/(2:ℝ)^Tb),
      (t - Φ.F.t₀)/Φ.F.q ∈ Set.Icc ((jt:ℝ)/(2:ℝ)^Tt) (((jt:ℝ)+1)/(2:ℝ)^Tt))
    (hblock_back : ∀ t, (t - Φ.F.t₀)/Φ.F.q ∈ Set.Icc ((jt:ℝ)/(2:ℝ)^Tt) (((jt:ℝ)+1)/(2:ℝ)^Tt) →
      t ∈ Set.Icc ((jb:ℝ)/(2:ℝ)^Tb) (((jb:ℝ)+1)/(2:ℝ)^Tb))
    (hcoeff : 81 * |δA| * Nt^Mct * residualBudget a 1 ^ 2 * Φ.substBudget ^ 2 ≤ N^Mc)
    (hpar : ∀ agt : ℝ, gaint ≤ agt → agt ≤ 1/8 → rt + 2*agt*Lt ≤ Lt → ∃ ag : ℝ,
      gain ≤ ag ∧ ag ≤ 1/8 ∧ rb + 2*ag*L ≤ L ∧
      δA * (Nt^(ρt*gaint*Lt+εt) * Split.δ Nt (rt + agt*Lt)) ≤ N^(ρ*gain*L+ε) * Split.δ N (rb + ag*L) ∧
      Nt^(ρt*gaint*Lt+εt) ≤ N^(ρ*gain*L+ε) ∧
      Nt^(ρt*gaint*Lt+εt) * Split.δ N (rb + ag*L) ≤ N^(ρ*gain*L+ε) * δA * Split.δ Nt (rt + agt*Lt) ∧
      ENNReal.ofReal (N^(-((d₁*ag+ρ*gain)*L) - ε)/(2:ℝ)^Tb) ≤
        ENNReal.ofReal Φ.F.q * ENNReal.ofReal (Nt^(-((d₁*agt+ρt*gaint)*Lt) - εt)/(2:ℝ)^Tt))
    (htan : DirectAt Nt Lt (tanPrior Φ a ν A₀) 1 Mct d₁ ρt gaint εt rt Tt jt At Ht) :
    DirectAt N L ν B Mc d₁ ρ gain ε rb Tb jb Ab H := by
  obtain ⟨agt, hgt, hgt8, hrt, Rt, A't, hRdeg, hRcoeff, hA'm, hA'At, hfit, hmass⟩ := htan
  obtain ⟨ag, hg, hg8, hrb, hvalue, hfirst, hsecond, hmasspar⟩ := hpar agt hgt hgt8 hrt
  set Ht' : ℝ := Nt^(ρt*gaint*Lt+εt) with hHt'
  set C' : ℝ := N^(ρ*gain*L+ε) with hC'
  have hHpos : 0 < Ht' := Real.rpow_pos_of_pos hNt _
  have hδpos : ∀ M x : ℝ, 0 < Split.δ M x := fun M x => by unfold Split.δ; positivity
  refine ⟨ag, hg, hg8, hrb, Φ.affineLift a δA Rt, Ab ∩ tanLine Φ a ⁻¹' A't,
    (Φ.totalDegree_affineLift_le a δA Rt).trans hRdeg, fun e => ?_,
    hAb.inter (measurable_tanLine Φ a hA'm), Set.inter_subset_left, ?_, ?_⟩
  · exact (Φ.coeff_affineLift_quadratic_le a δA Rt hRdeg (Nt^Mct) hRcoeff e).trans hcoeff
  · intro l hl t ht
    have hfitS : fitS (hiddenShear Φ.eb a) Ht' (Split.δ Nt (rt + agt*Lt)) Rt l
        (Set.Icc ((jt:ℝ)/(2:ℝ)^Tt) (((jt:ℝ)+1)/(2:ℝ)^Tt)) := by
      intro τ hτ
      obtain ⟨h0', h1', h2'⟩ := hfit (tanLine Φ a l) hl.2 τ hτ
      rw [xp_tanLine] at h0' h1' h2'
      refine ⟨h0', by simpa using h1', by simpa using h2'⟩
    have hF := Φ.fitS_affine_return hq.ne' a δA B (Split.δ Nt (rt + agt*Lt)) (Split.δ N (rb + ag*L))
      Ht' C' hδA hB.le (hδpos _ _) (hδpos _ _) hsc Rt l _ _ hblock hfitS hvalue hfirst hsecond
    exact hF t ht
  · -- the mass floor
    set Xt : Set Ev := {p | p ∈ Ht ∧ p.1 ∈ A't ∧
        p.2 ∈ Set.Icc ((jt:ℝ)/(2:ℝ)^Tt) (((jt:ℝ)+1)/(2:ℝ)^Tt) ∧
        (1:ℝ)/Ht' ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 Rt)|} with hXt
    have hXm : MeasurableSet Xt := by
      refine hHt.inter ((measurable_fst hA'm).inter ((measurable_snd measurableSet_Icc).inter ?_))
      exact measurableSet_le measurable_const (measurable_xp_eval _).abs
    have hAt_le : nuE ν A₀ Ab ≤ tanPrior Φ a ν A₀ At := by
      rw [tanPrior_apply Φ a ν A₀ hAtm]
      exact measure_mono (fun l hl => hAt_in l hl)
    have h1 : ENNReal.ofReal (Nt^(-((d₁*agt+ρt*gaint)*Lt) - εt)/(2:ℝ)^Tt) * nuE ν A₀ Ab ≤
        ((tanPrior Φ a ν A₀).prod volume) Xt := by
      refine le_trans ?_ hmass
      gcongr
    have h2 := tan_floor_return Φ a ν A₀ Ab hAb hAbA₀ h0 hT hq hXm _ h1
    have hsub : {p : Ev | p.1 ∈ A₀ ∧ tanEvent Φ a p ∈ Xt} ⊆
        {p | p ∈ H ∧ p.1 ∈ Ab ∩ tanLine Φ a ⁻¹' A't ∧
          p.2 ∈ Set.Icc ((jb:ℝ)/(2:ℝ)^Tb) (((jb:ℝ)+1)/(2:ℝ)^Tb) ∧
          B/C' ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 (Φ.affineLift a δA Rt))|} := by
      rintro p ⟨hp0, hpH, hpA, hpI, hpL⟩
      refine ⟨hH_back p hp0 hpH, ⟨hAt_back p.1 hp0 (hA'At hpA), hpA⟩, hblock_back p.2 hpI, ?_⟩
      have hl : Ht'⁻¹ ≤ |MvPolynomial.eval (exS (hiddenShear Φ.eb a) p.1 ((p.2 - Φ.F.t₀)/Φ.F.q))
          (MvPolynomial.pderiv 3 Rt)| := by
        simpa [one_div, tanEvent, xp_tanLine] using hpL
      exact Φ.affine_lower_return hq.ne' a δA B Ht' C' hδA.ne' hB.le hHpos hfirst hsc Rt p.1 p.2 hl
    calc ENNReal.ofReal (N^(-((d₁*ag+ρ*gain)*L) - ε)/(2:ℝ)^Tb) * ν Ab
        ≤ (ENNReal.ofReal Φ.F.q * ENNReal.ofReal (Nt^(-((d₁*agt+ρt*gaint)*Lt) - εt)/(2:ℝ)^Tt))
            * ν Ab := by gcongr
      _ ≤ (ν.prod volume) {p : Ev | p.1 ∈ A₀ ∧ tanEvent Φ a p ∈ Xt} := h2
      _ ≤ _ := measure_mono hsub

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
