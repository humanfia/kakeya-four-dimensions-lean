-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ConcreteCompletion.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.BroadCompletion
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.BaseLines
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ObservationCell

/-!
# Broad completion with the actual base geometry

`direct_of_filled_group` is instantiated with the actual base map of incidences, the unit base
directions and clamped anchors of trajectories.  Its tube and time-in-cell hypotheses are then
proved (`mem_tube_of_cell`, `push_le_of_time_extent`), and the group test's value bound follows
from the own-intercept fits, the window of the enlarged group and the quadratic replacement.

What remains as input is exactly the source data: the potential with its own intercepts,
the quadratic replacement along the enlarged group, per-cell breadth and the prior ceiling of
the core group, and the occupied observation cells of the enlarged group with their mass floor.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ContinuousKakeya
open scoped NNReal ENNReal

noncomputable section

/-- The value bound of the group test along the enlarged group, from the own-intercept fits,
the intercept window and the quadratic replacement. -/
lemma groupTest_value_le {Rb : Po} {P Q₂ : MvPolynomial (Fin 3) ℝ} {cpt : Ln → ℝ}
    {εfit Erep c₀ ω : ℝ} {l : Ln} {t : ℝ}
    (hfit : |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
      cpt l| ≤ εfit)
    (hrep : |MvPolynomial.eval (fun i => xp l t i.castSucc) P -
      MvPolynomial.eval (fun i => xp l t i.castSucc) Q₂| ≤ Erep)
    (hwin : |cpt l - c₀| ≤ ω) :
    |MvPolynomial.eval (xp l t) (groupTest Rb Q₂ c₀)| ≤ εfit + ω + Erep := by
  rw [eval_groupTest]
  calc |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) Q₂ - c₀|
      = |(MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
          cpt l) + (cpt l - c₀) + (MvPolynomial.eval (fun i => xp l t i.castSucc) P -
          MvPolynomial.eval (fun i => xp l t i.castSucc) Q₂)| := by ring_nf
    _ ≤ εfit + ω + Erep := by
        refine (abs_add_three _ _ _).trans ?_
        linarith

/-- **Broad completion with the actual base geometry.** -/
theorem direct_of_actual_filled_group {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Ln}
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
    -- the potential, its own intercepts and the quadratic replacement along `A'`
    (P Q₂ : MvPolynomial (Fin 3) ℝ) (hQ₂ : Q₂.totalDegree ≤ 2) (cpt : Ln → ℝ)
    (hcpt : Measurable cpt) (εfit Erep c₀ ω : ℝ)
    (Aret : Set Ln) (hAretm : MeasurableSet Aret) (hAret : Aret ⊆ A b)
    (hfit : ∀ l ∈ Aret, ∀ t ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)),
      |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
        cpt l| ≤ εfit)
    (hrep : ∀ l ∈ Aret, |cpt l - c₀| ≤ ω → ∀ t ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)),
      |MvPolynomial.eval (fun i => xp l t i.castSucc) P -
        MvPolynomial.eval (fun i => xp l t i.castSucc) Q₂| ≤ Erep)
    (hcoeff : ∀ e, |(groupTest Rb Q₂ c₀).coeff e| ≤ Nk ^ Mc)
    (hvalue : εfit + ω + Erep ≤ Nk ^ (ρ * gain * L + ε) * δ Nk (r (lev b) + ag * L))
    -- the counted measure
    (inc : Measure Ev) [IsFiniteMeasure inc] [IsFiniteMeasure (ν (γ b))]
    (hinc : inc ≤ (((ν (γ b)).prod volume).restrict {p | p ∈ H (γ b) ∧ p ∈ Fb}))
    -- the core group and its base filling data
    (Λ : Set Ln) (hΛ : MeasurableSet Λ) (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hΛanchor : ∀ l ∈ Λ, ‖baseAnchor0 l‖ ≤ Bd) {m : ℕ}
    (E : Fin m → Set (EuclideanSpace ℝ (Fin 3))) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Function.onFun Disjoint E)) (boxBound : ℝ)
    (hbox : ∀ i, E i ⊆ Metric.closedBall 0 boxBound)
    (p R Ck ρb cb K w : ℝ) (hp : 0 < p) (hR : 0 < R) (hCk : 0 ≤ Ck)
    (hMK : FiniteMK 3 Ck) (hρb : 0 < ρb) (hcb : 0 ≤ cb) (hK : 1 ≤ K) (hw : 0 < w)
    (hvol : ∀ i, volume (E i) = ENNReal.ofReal (p ^ 3))
    (hdiam : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist x y < R * p)
    (htime : ∀ i, ∃ t₀ : ℝ, ∀ x ∈ E i, x 0 ∈ Icc t₀ (t₀ + p))
    (hbroad : ∀ i, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      cb * inc.real {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E i} ≤
        (inc.restrict {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E i}).real
          {ω | ρb ≤ Metric.infDist (baseDir ω.1) (V : Set _)})
    (Mg : ℝ) (hMg : 0 < Mg)
    (hcover : Mg ≤ ∑ i, inc.real {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E i})
    (hprior : (ν (γ b)).real Λ ≤ K * Mg / w)
    -- occupied observation cells of the enlarged group
    (O : Fin m → Set Ev) (hOm : ∀ i, MeasurableSet (O i))
    (hOdisj : Pairwise (Function.onFun Disjoint O)) (mcell : ℝ≥0∞)
    (hOmass : ∀ i, mcell ≤ inc (O i))
    (hOgroup : ∀ i, ∀ q ∈ O i, q.1 ∈ Aret ∧ |cpt q.1 - c₀| ≤ ω ∧
      q.2 ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)))
    -- the mass budget
    (hmass : ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) / (2:ℝ) ^ T (lev b)) *
        ν (γ b) (A b) ≤
      ENNReal.ofReal (((ρb / 2) ^ 3 / 2 * cb ^ 3) * (w / p) ^ 3 /
        ((8 * Ck * R ^ 3) ^ 2 * K ^ 9)) * mcell) :
    direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  -- the enlarged group of trajectories
  set A' : Set Ln := {l | l ∈ Aret ∧ |cpt l - c₀| ≤ ω} with hA'
  have hA'm : MeasurableSet A' :=
    hAretm.inter (measurableSet_le ((hcpt.sub_const _).abs) measurable_const)
  have hA'sub : A' ⊆ A b := fun l hl => hAret hl.1
  have hval : ∀ l ∈ A', ∀ t ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b))
      (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)),
      |MvPolynomial.eval (xp l t) (groupTest Rb Q₂ c₀)| ≤
        Nk ^ (ρ * gain * L + ε) * δ Nk (r (lev b) + ag * L) := by
    intro l hl t ht
    exact (groupTest_value_le (hfit l hl.1 t ht) (hrep l hl.1 hl.2 t ht) hl.2).trans hvalue
  -- tubes about the base lines of the core group
  have htube : ∀ i, ∀ q : Ev, q.1 ∈ Λ → basePoint q ∈ E i → ∀ x ∈ E i,
      x ∈ tube (R * p) (baseAnchor Bd q.1) (baseDir q.1) := by
    intro i q hq hqE x hx
    obtain ⟨l, t⟩ := q
    exact mem_tube_of_cell (hΛanchor l hq) hqE (hdiam i) x hx
  -- time spent in a cell
  have hinc' : inc ≤ (ν (γ b)).prod volume := hinc.trans Measure.restrict_le_self
  have hpush : ∀ i, (inc.restrict {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E i}).map Prod.fst ≤
      (K * p).toNNReal • (ν (γ b)).restrict Λ := by
    intro i
    obtain ⟨t₀, ht₀⟩ := htime i
    refine (push_le_of_time_extent (ν (γ b)) inc hinc' Λ hΛ (E i) (hE i) p t₀ ht₀).trans ?_
    have hle : p.toNNReal ≤ (K * p).toNNReal :=
      Real.toNNReal_le_toNNReal (le_mul_of_one_le_left hp.le hK)
    intro s
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    gcongr
  exact direct_of_filled_group b hch hN hB hκ1 hκ ag hag hag8 hdepth hagL Q₂ hQ₂ c₀ hcoeff
    A' hA'm hA'sub hval inc hinc basePoint measurable_basePoint baseDir (baseAnchor Bd)
    (measurable_baseAnchor Bd) measurable_baseDir norm_baseDir Bd (norm_baseAnchor_le hBd)
    Λ hΛ E hE hdisj boxBound hbox p R Ck ρb cb K w hp hR hCk hMK hρb hcb hK hw hvol hpush
    htube hbroad Mg hMg hcover hprior O hOm hOdisj mcell hOmass
    (fun i q hq => ⟨⟨(hOgroup i q hq).1, (hOgroup i q hq).2.1⟩, (hOgroup i q hq).2.2⟩) hmass

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
