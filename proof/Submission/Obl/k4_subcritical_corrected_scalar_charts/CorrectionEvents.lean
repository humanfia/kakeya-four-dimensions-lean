/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/CorrectionEvents.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.PairedSignals
import Submission.Obl.k4_subcritical_corrected_scalar_charts.OriginalGoodLines
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NamedAncestry

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem measurableSet_namedNativeIncidence {k : ℕ} {s₀ s : ℝ}
    (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
    (choice : Fin (2 ^ cfg.T k s₀) → Option (Fin (cfg.n k s₀)))
    (z : Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k s)) :
    MeasurableSet {p | cfg.namedNativeIncidence k s₀ s choice p z} := by
  simp only [namedNativeIncidence, setOf_exists, setOf_and]
  apply MeasurableSet.iUnion
  intro ip
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (((parent.fitted_measurable ip).preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter
        (((child.fitted_measurable z.2).preimage measurable_fst).inter
          ((measurableSet_Icc.preimage measurable_snd).inter
            ((MeasurableSet.const _).inter (MeasurableSet.const _)))))))

namespace ChosenPairedSample

variable {k : ℕ} {M s₀ ε : ℝ} (sample : cfg.ChosenPairedSample k M s₀ ε)

def rowEqualEvent (parent : cfg.NativeLevel k s₀) (c : Fin sample.coarse.charts.n) :
    Set (α × ℝ) :=
  {p | ∀ j : Fin (2 ^ cfg.T k s₀), p.2 ∈ I (cfg.T k s₀) j →
    sample.signal parent c p.2 = sample.row parent c j p.2}

theorem measurableSet_rowEqualEvent (parent : cfg.NativeLevel k s₀)
    (c : Fin sample.coarse.charts.n) : MeasurableSet (sample.rowEqualEvent parent c) := by
  simp only [rowEqualEvent, setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_Icc.preimage measurable_snd).imp
    (measurableSet_eq_fun ((sample.measurable_signal parent c).comp measurable_snd)
      ((sample.measurable_row parent c j).comp measurable_snd))

/-- The full original coarse charts, cut only by an original-incidence-conull
static set of bounded horizontal trajectories. -/
def originalGoodChart (c : Fin sample.coarse.charts.n) : Set α :=
  sample.coarse.charts.G c ∩ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M))

theorem measurableSet_originalGoodChart (h : cfg.Prepared) (c : Fin sample.coarse.charts.n) :
    MeasurableSet (sample.originalGoodChart c) :=
  (sample.coarse.measurable c).inter (measurableSet_goodOriginalLines (h.basic k).1 _ _)

/-- A common event carries the chosen coarse row, one original fine endpoint
row, and genuine named ancestry at all three terminal native levels. -/
def correctionEvent (parent : cfg.NativeLevel k s₀) (depth : Fin 3 → ℝ)
    (c : Fin sample.coarse.charts.n) : Set (α × ℝ) :=
  {p | p.1 ∈ sample.originalGoodChart c ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
    p ∈ sample.rowEqualEvent parent c ∧
    (∃ (cb : Fin sample.fine.charts.n)
      (z : Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k (3 * s₀ / 2))),
      p.1 ∈ sample.fine.charts.G cb ∧ sample.fine.paired cb z.2 ∧
      cfg.namedNativeIncidence k s₀ (3 * s₀ / 2) (sample.choice c) p z) ∧
    ∀ r : Fin 3, ∃ z : Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k (depth r)),
      cfg.namedNativeIncidence k s₀ (depth r) (sample.choice c) p z}

theorem measurableSet_correctionEvent (h : cfg.Prepared) (parent : cfg.NativeLevel k s₀)
    (fine : cfg.NativeLevel k (3 * s₀ / 2)) (depth : Fin 3 → ℝ)
    (terminal : ∀ r, cfg.NativeLevel k (depth r)) (c : Fin sample.coarse.charts.n) :
    MeasurableSet (sample.correctionEvent parent depth c) := by
  have hfine : MeasurableSet {p : α × ℝ | ∃ (cb : Fin sample.fine.charts.n)
      (z : Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k (3 * s₀ / 2))),
      p.1 ∈ sample.fine.charts.G cb ∧ sample.fine.paired cb z.2 ∧
        cfg.namedNativeIncidence k s₀ (3 * s₀ / 2) (sample.choice c) p z} := by
    simp only [setOf_exists, setOf_and]
    exact MeasurableSet.iUnion fun cb => MeasurableSet.iUnion fun z =>
      ((sample.fine.measurable cb).preimage measurable_fst).inter
        ((MeasurableSet.const _).inter (measurableSet_namedNativeIncidence parent fine _ z))
  have hterm : MeasurableSet {p : α × ℝ | ∀ r : Fin 3,
      ∃ z : Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k (depth r)),
        cfg.namedNativeIncidence k s₀ (depth r) (sample.choice c) p z} := by
    simp only [setOf_forall, setOf_exists]
    exact MeasurableSet.iInter fun r => MeasurableSet.iUnion fun z =>
      measurableSet_namedNativeIncidence parent (terminal r) _ z
  exact ((sample.measurableSet_originalGoodChart h c).preimage measurable_fst).inter
    ((measurableSet_Icc.preimage measurable_snd).inter
      ((sample.measurableSet_rowEqualEvent parent c).inter (hfine.inter hterm)))

theorem correctionEvent_subset (parent : cfg.NativeLevel k s₀) (depth : Fin 3 → ℝ)
    (c : Fin sample.coarse.charts.n) :
    sample.correctionEvent parent depth c ⊆ sample.originalGoodChart c ×ˢ Icc (0 : ℝ) 1 :=
  fun _ hp => ⟨hp.1, hp.2.1⟩

theorem correctionEvent_signal_bound (h : cfg.Prepared) (parent : cfg.NativeLevel k s₀)
    (depth : Fin 3 → ℝ) (c : Fin sample.coarse.charts.n)
    {p : α × ℝ} (hp : p ∈ sample.correctionEvent parent depth c) :
    |sample.signal parent c p.2| ≤ 6 * cfg.N k ^ ε := by
  obtain ⟨cb, z, hcb, hpair, ip, hchoice, hjp, hp₀, ht₀, hpc, htc, hA, hI⟩ := hp.2.2.2.1
  rw [hp.2.2.1 z.1 (by simpa only [hjp] using ht₀)]
  exact sample.row_bound h parent hchoice hp.2.1 ht₀

end ChosenPairedSample

/-- The common correction event covers the chosen law almost everywhere.
Every named ancestor is obtained from the original atlas null sets. -/
theorem Prepared.eventually_correction_event_cover (h : cfg.Prepared)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hsb : 3 * s₀ / 2 ≤ cfg.U)
    (depth : Fin 3 → ℝ) (hdepth : ∀ r, s₀ < depth r ∧ depth r ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ {M ε : ℝ} (sample : cfg.ChosenPairedSample k M s₀ ε), M ≤ cfg.e₀ →
      ∀ (parent : cfg.NativeLevel k s₀) (fine : cfg.NativeLevel k (3 * s₀ / 2))
        (terminal : ∀ r, cfg.NativeLevel k (depth r)),
      ∀ᵐ p ∂sample.σ, ∃ c, p ∈ sample.correctionEvent parent depth c := by
  have hterms := (Set.finite_univ : (univ : Set (Fin 3)).Finite).eventually_all.mpr
    (fun r _ => h.eventually_named_ancestry hs₀ (hdepth r).1 (hdepth r).2)
  filter_upwards [h.eventually_named_ancestry hs₀ (show s₀ < 3 * s₀ / 2 by linarith) hsb,
    hterms] with k hfn htn
  intro M ε sample hM parent fine terminal
  have hσμ := sample.le_rho.trans (h.basic k).2.2.2.2.1
  have htcov : ∀ᵐ p ∂cfg.μ k, ∀ r, ∃ i,
      p.1 ∈ cfg.B k (depth r) i ∧ p.2 ∈ I (cfg.T k (depth r)) (cfg.j k (depth r) i) :=
    ae_all_iff.mpr fun r => (terminal r).assignments.covers
  have htanc := ae_all_iff.mpr fun r : Fin 3 => htn r (mem_univ _) parent (terminal r)
  have hunit : ∀ᵐ p ∂cfg.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
    have hh : ∀ᵐ p ∂cfg.μ k, p ∈ univ ×ˢ Icc (0 : ℝ) 1 :=
      ae_iff.mpr (h.basic k).2.2.2.2.2.1
    simpa only [mem_prod, mem_univ, true_and] using hh
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hχ : cfg.N k ^ (-cfg.e₀) ≤ cfg.N k ^ (-M) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hM)
  filter_upwards [sample.coarse_cover, sample.fine_cover, sample.signal_eq_row_ae h parent,
    ae_mono hσμ (parent.original_good_ae h), ae_mono hσμ (hfn parent fine),
    ae_mono hσμ htcov, ae_mono hσμ htanc, ae_mono hσμ hunit]
    with p hcoarse hfine hrow hgood hfanc htcover htanc htunit
  obtain ⟨c, ip, hpc, hpp, hpt, hchoice⟩ := hcoarse
  obtain ⟨cb, ib, hcb, hpb, htb, hpair⟩ := hfine
  refine ⟨c, ⟨⟨hpc, hgood.1, hgood.2.trans hχ⟩, htunit, hrow c, ?_, ?_⟩⟩
  · obtain ⟨hA, hI⟩ := hfanc ib ip hpb htb hpp hpt
    exact ⟨cb, (cfg.j k s₀ ip, ib), hcb, hpair, ip, hchoice, rfl, hpp, hpt, hpb, htb, hA, hI⟩
  · intro r
    obtain ⟨ic, hpc, htc⟩ := htcover r
    obtain ⟨hA, hI⟩ := htanc r ic ip hpc htc hpp hpt
    exact ⟨(cfg.j k s₀ ip, ic), ip, hchoice, rfl, hpp, hpt, hpc, htc, hA, hI⟩

theorem Prepared.eventually_correction_event_fit (h : cfg.Prepared) {s₀ ε : ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε)
    (hsmall : ε ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16) :
    ∀ᶠ k in atTop, ∀ {M : ℝ} (sample : cfg.ChosenPairedSample k M s₀ ε)
      (parent : cfg.NativeLevel k s₀) (fine : cfg.NativeLevel k (3 * s₀ / 2))
      (depth : Fin 3 → ℝ) (c : Fin sample.coarse.charts.n),
      ∀ p ∈ sample.correctionEvent parent depth c,
      |(cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.N k ^ (-s₀)) *
        fiberDerivative (sample.fine.charts.baselineSelector p.1 - sample.coarse.charts.g c) p.2 -
          sample.signal parent c p.2| ≤ cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4)) := by
  filter_upwards [h.eventually_chosen_fine_signal hs₀ hε hsmall] with k hk
  intro M sample parent fine depth c p hp
  obtain ⟨cb, z, hcb, hpair, hn⟩ := hp.2.2.2.1
  have hn' := hn
  obtain ⟨ip, hchoice, hjp, hp₀, ht₀, hrest⟩ := hn'
  exact hk sample parent fine c cb p z hp.2.1 hcb hpair hn
    (hp.2.2.1 z.1 (by simpa only [hjp] using ht₀))

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
