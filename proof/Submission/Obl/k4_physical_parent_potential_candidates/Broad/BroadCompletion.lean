-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/BroadCompletion.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.DirectPackaging
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.GroupMass

/-!
# Broad completion: the direct exit from a filled intercept group

This file composes the pieces of the broad completion into the frozen direct exit.

* A *core group* `Λ` of retained trajectories, with intercepts in a window, is broad in every
  base cell and long in time; multilinear Kakeya in three base dimensions
  (`occupied_cells_lower_bound`) gives at least `β (w/p)^3 / (A^2 K^9)` occupied base cells.
* Each occupied base cell contains an observation cell of counted mass at least `mcell`, all
  of whose counted incidences lie on trajectories of the *enlarged group* `A'`
  (`intercept_close_of_same_base` gives this in applications), so the enlarged group carries at
  least `mcell` times the number of occupied cells (`mass_ge_card_mul_of_cells`).
* The group test `R_b - Q₂ - c*` is small along the enlarged group (own-intercept fits plus a
  quadratic replacement of the potential), and `direct_of_group_test` packages the direct exit.

All geometric inputs are explicit hypotheses; the numerical budgets are explicit too.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ContinuousKakeya
open scoped NNReal ENNReal

noncomputable section

/-- **Broad completion.** -/
theorem direct_of_filled_group {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Ln}
    {B : Fin W → ℝ} {Mp Dp Mc : ℕ} {d₁ ρ gain ε κ : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {A : Fin C → Set Ln}
    {H : Fin W → Set Ev}
    -- the old packet and its frozen chart
    (b : Fin C) {Evs : Set Ev} {c u : P2} {Qf : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po}
    {Fb : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) Evs c u Qf Rb (A b) Fb ex)
    (hN : 1 ≤ Nk) (hB : 0 < B (γ b)) (hκ1 : 1 ≤ κ) (hκ : κ ≤ Nk ^ (ρ * gain * L + ε))
    (ag : ℝ) (hag : gain ≤ ag) (hag8 : ag ≤ 1 / 8) (hdepth : r (lev b) + 2 * ag * L ≤ L)
    (hagL : 0 ≤ ag * L)
    -- the enlarged group and its test
    (Q₂ : MvPolynomial (Fin 3) ℝ) (hQ₂ : Q₂.totalDegree ≤ 2) (cstar : ℝ)
    (hcoeff : ∀ e, |(groupTest Rb Q₂ cstar).coeff e| ≤ Nk ^ Mc)
    (A' : Set Ln) (hA'm : MeasurableSet A') (hA' : A' ⊆ A b)
    (hval : ∀ l ∈ A', ∀ t ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)),
      |MvPolynomial.eval (xp l t) (groupTest Rb Q₂ cstar)| ≤
        Nk ^ (ρ * gain * L + ε) * δ Nk (r (lev b) + ag * L))
    -- base filling of the core group, for the counted incidence measure `inc`
    (inc : Measure Ev) [IsFiniteMeasure inc] [IsFiniteMeasure (ν (γ b))]
    (hinc : inc ≤ (((ν (γ b)).prod volume).restrict {p | p ∈ H (γ b) ∧ p ∈ Fb}))
    (Φ : Ev → EuclideanSpace ℝ (Fin 3)) (hΦ : Measurable Φ)
    (ea aa : Ln → EuclideanSpace ℝ (Fin 3)) (ha : Measurable aa) (he : Measurable ea)
    (he1 : ∀ l, ‖ea l‖ = 1) (anchorBound : ℝ) (hanchor : ∀ l, ‖aa l‖ ≤ anchorBound)
    (Λ : Set Ln) (hΛ : MeasurableSet Λ) {m : ℕ}
    (E : Fin m → Set (EuclideanSpace ℝ (Fin 3))) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Function.onFun Disjoint E)) (boxBound : ℝ)
    (hbox : ∀ i, E i ⊆ Metric.closedBall 0 boxBound)
    (p R Ck ρb cb K w : ℝ) (hp : 0 < p) (hR : 0 < R) (hCk : 0 ≤ Ck)
    (hMK : FiniteMK 3 Ck) (hρb : 0 < ρb) (hcb : 0 ≤ cb) (hK : 1 ≤ K) (hw : 0 < w)
    (hvol : ∀ i, volume (E i) = ENNReal.ofReal (p ^ 3))
    (hpush : ∀ i, (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E i}).map Prod.fst ≤
      (K * p).toNNReal • (ν (γ b)).restrict Λ)
    (htube : ∀ i, ∀ ω : Ev, ω.1 ∈ Λ → Φ ω ∈ E i → ∀ x ∈ E i,
      x ∈ tube (R * p) (aa ω.1) (ea ω.1))
    (hbroad : ∀ i, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      cb * inc.real {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E i} ≤
        (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E i}).real
          {ω | ρb ≤ Metric.infDist (ea ω.1) (V : Set _)})
    (Mg : ℝ) (hMg : 0 < Mg)
    (hcover : Mg ≤ ∑ i, inc.real {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E i})
    (hprior : (ν (γ b)).real Λ ≤ K * Mg / w)
    -- occupied observation cells inside the enlarged group
    (O : Fin m → Set Ev) (hOm : ∀ i, MeasurableSet (O i))
    (hOdisj : Pairwise (Function.onFun Disjoint O)) (mcell : ℝ≥0∞)
    (hOmass : ∀ i, mcell ≤ inc (O i))
    (hOgroup : ∀ i, ∀ q ∈ O i, q.1 ∈ A' ∧
      q.2 ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)))
    -- the mass budget
    (hmass : ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) / (2:ℝ) ^ T (lev b)) *
        ν (γ b) (A b) ≤
      ENNReal.ofReal (((ρb / 2) ^ 3 / 2 * cb ^ 3) * (w / p) ^ 3 /
        ((8 * Ck * R ^ 3) ^ 2 * K ^ 9)) * mcell) :
    direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  -- number of occupied base cells
  have hcells := occupied_cells_lower_bound (ν (γ b)) inc Φ hΦ aa ea ha he he1 anchorBound
    hanchor Λ hΛ E hE hdisj boxBound hbox p R Ck ρb cb K w hp hR hCk hMK hρb hcb hK hw hvol
    hpush htube hbroad Mg hMg hcover hprior
  -- mass of the enlarged group's counted incidences
  set G : Set Ev := {q | q ∈ H (γ b) ∧ q ∈ Fb ∧ q.1 ∈ A' ∧
    q.2 ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b))} with hG
  have hOsub : ∀ i ∈ (Finset.univ : Finset (Fin m)), O i ∩ {q | q ∈ H (γ b) ∧ q ∈ Fb} ⊆ G := by
    intro i _ q hq
    exact ⟨hq.2.1, hq.2.2, (hOgroup i q hq.1).1, (hOgroup i q hq.1).2⟩
  have hgroupmass : (m : ℝ≥0∞) * mcell ≤ ((ν (γ b)).prod volume) G := by
    have h1 := mass_ge_card_mul_of_cells inc (Finset.univ : Finset (Fin m)) O
      (⋃ i, O i) mcell (fun i _ => Set.subset_iUnion O i) (fun i _ => hOm i)
      (fun i _ i' _ hne => hOdisj hne) (fun i _ => hOmass i)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    refine h1.trans ?_
    calc inc (⋃ i, O i) ≤ (((ν (γ b)).prod volume).restrict {p | p ∈ H (γ b) ∧ p ∈ Fb})
          (⋃ i, O i) := hinc _
      _ = ((ν (γ b)).prod volume) ((⋃ i, O i) ∩ {p | p ∈ H (γ b) ∧ p ∈ Fb}) :=
          Measure.restrict_apply (MeasurableSet.iUnion hOm)
      _ ≤ ((ν (γ b)).prod volume) G := by
          apply measure_mono
          intro q hq
          obtain ⟨hqU, hqHF⟩ := hq
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hqU
          exact hOsub i (Finset.mem_univ _) ⟨hi, hqHF⟩
  -- the numeric lower bound on the number of cells
  have hm : ((ρb / 2) ^ 3 / 2 * cb ^ 3) * (w / p) ^ 3 / ((8 * Ck * R ^ 3) ^ 2 * K ^ 9) ≤ m := by
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ (8 * Ck * R ^ 3) ^ 2 * K ^ 9 by positivity) with h | h
    · rw [← h, div_zero]; positivity
    · rw [div_le_iff₀ h]
      linarith [hcells]
  refine direct_of_group_test b hch hN hB hκ1 hκ ag hag hag8 hdepth hagL Q₂ hQ₂ cstar hcoeff
    A' hA'm hA' hval ?_
  refine hmass.trans ?_
  calc ENNReal.ofReal (((ρb / 2) ^ 3 / 2 * cb ^ 3) * (w / p) ^ 3 /
        ((8 * Ck * R ^ 3) ^ 2 * K ^ 9)) * mcell
      ≤ (m : ℝ≥0∞) * mcell := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hm
    _ ≤ ((ν (γ b)).prod volume) G := hgroupmass

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
