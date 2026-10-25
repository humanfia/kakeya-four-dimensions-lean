/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/PairedSignals.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.PairedChoice
import Submission.Obl.k4_subcritical_corrected_scalar_charts.BlockSignal
import Submission.Obl.k4_subcritical_corrected_scalar_charts.PairedDirectionalRow
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeCellLists

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace ChartFamily

variable {α : Type} [MeasurableSpace α]

def baselineSelector (C : ChartFamily α) (l : α) : Fin 6 → ℝ :=
  ∑ c, (C.G c).indicator (fun _ => C.g c) l

theorem measurable_baselineSelector (C : ChartFamily α)
    (hm : ∀ c, MeasurableSet (C.G c)) : Measurable C.baselineSelector := by
  unfold baselineSelector
  exact Finset.measurable_sum _ fun c _ => measurable_const.indicator (hm c)

theorem baselineSelector_eq (C : ChartFamily α)
    (hd : ∀ c c', c ≠ c' → Disjoint (C.G c) (C.G c'))
    {c : Fin C.n} {l : α} (hl : l ∈ C.G c) : C.baselineSelector l = C.g c := by
  classical
  unfold baselineSelector
  rw [Finset.sum_eq_single c]
  · exact indicator_of_mem hl _
  · intro c' _ hne
    apply indicator_of_notMem
    intro hl'
    exact disjoint_left.mp (hd c' c hne) hl' hl
  · simp

end ChartFamily

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

namespace ChosenPairedSample

variable {k : ℕ} {M s₀ ε : ℝ} (sample : cfg.ChosenPairedSample k M s₀ ε)

def row (parent : cfg.NativeLevel k s₀) (c : Fin sample.coarse.charts.n)
    (j : Fin (2 ^ cfg.T k s₀)) (t : ℝ) : ℝ :=
  match sample.choice c j with
  | none => 0
  | some i => nativeFiberSignal (sample.coarse.charts.g c) (parent.L i)
      (cfg.N k ^ (-(2 * cfg.κ * s₀))) (cfg.N k ^ (-s₀)) t

def signal (parent : cfg.NativeLevel k s₀) (c : Fin sample.coarse.charts.n) : ℝ → ℝ :=
  blockSignal (cfg.T k s₀) (sample.row parent c)

theorem row_of_choice (parent : cfg.NativeLevel k s₀) {c : Fin sample.coarse.charts.n}
    {j : Fin (2 ^ cfg.T k s₀)} {ip : Fin (cfg.n k s₀)}
    (hi : sample.choice c j = some ip) (t : ℝ) :
    sample.row parent c j t = nativeFiberSignal (sample.coarse.charts.g c) (parent.L ip)
      (cfg.N k ^ (-(2 * cfg.κ * s₀))) (cfg.N k ^ (-s₀)) t := by
  simp only [row, hi]

theorem measurable_row (parent : cfg.NativeLevel k s₀) (c : Fin sample.coarse.charts.n)
    (j : Fin (2 ^ cfg.T k s₀)) : Measurable (sample.row parent c j) := by
  unfold row
  cases sample.choice c j with
  | none => exact measurable_const
  | some i =>
    dsimp only
    unfold nativeFiberSignal fiberDerivative
    fun_prop

theorem measurable_signal (parent : cfg.NativeLevel k s₀) (c : Fin sample.coarse.charts.n) :
    Measurable (sample.signal parent c) :=
  measurable_blockSignal _ _ (sample.measurable_row parent c)

theorem signal_eq_row_ae (h : cfg.Prepared) (parent : cfg.NativeLevel k s₀) :
    ∀ᵐ p ∂sample.σ, ∀ c j, p.2 ∈ I (cfg.T k s₀) j →
      sample.signal parent c p.2 = sample.row parent c j p.2 := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hdom := sample.le_rho.trans ((h.basic k).2.2.2.2.1.trans (h.basic k).2.2.2.1)
  exact (ae_all_iff.mpr fun c => blockSignal_eq_row_ae (cfg.ν k) sample.σ
    (ENNReal.ofReal (cfg.K k)) hdom (cfg.T k s₀) (sample.row parent c))

/-- The selected coarse time row is bounded by the paired whole-square norm,
without a native constant-coefficient bound. -/
theorem row_bound (h : cfg.Prepared) (parent : cfg.NativeLevel k s₀)
    {c : Fin sample.coarse.charts.n} {j : Fin (2 ^ cfg.T k s₀)}
    {ip : Fin (cfg.n k s₀)} {t : ℝ}
    (hi : sample.choice c j = some ip) (ht : t ∈ Icc (0 : ℝ) 1)
    (htI : t ∈ I (cfg.T k s₀) (cfg.j k s₀ ip)) :
    |sample.row parent c j t| ≤ 6 * cfg.N k ^ ε := by
  rw [sample.row_of_choice parent hi]
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hD : 0 < cfg.N k ^ (-(2 * cfg.κ * s₀)) := Real.rpow_pos_of_pos hN _
  have hA : 0 < cfg.N k ^ (-s₀) := Real.rpow_pos_of_pos hN _
  have hc := sample.coarse.comparison c ip (sample.choice_good c j ip hi).1 t htI
  have hh := parent.coarse_signal_bound ip hD hA ht
    (p₀ := (sample.coarse.charts.q c 1 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀)))
    (q₀ := (sample.coarse.charts.q c 2 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * s₀)))
    (by simpa only [add_mul, one_mul] using hc)
  exact hh.trans_eq (by field_simp)

end ChosenPairedSample

/-- The fixed fine endpoint predictor attached to a line fits the measurable
chosen coarse time signal, using the original named ancestor. -/
theorem Prepared.eventually_chosen_fine_signal (h : cfg.Prepared) {s₀ ε : ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε)
    (hsmall : ε ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16) :
    ∀ᶠ k in atTop, ∀ {M : ℝ} (sample : cfg.ChosenPairedSample k M s₀ ε)
      (parent : cfg.NativeLevel k s₀) (fine : cfg.NativeLevel k (3 * s₀ / 2))
      (c : Fin sample.coarse.charts.n) (cb : Fin sample.fine.charts.n)
      (p : α × ℝ) (z : Fin (2 ^ cfg.T k s₀) × Fin (cfg.n k (3 * s₀ / 2))),
      p.2 ∈ Icc (0 : ℝ) 1 → p.1 ∈ sample.fine.charts.G cb →
      sample.fine.paired cb z.2 → cfg.namedNativeIncidence k s₀ (3 * s₀ / 2) (sample.choice c) p z →
      sample.signal parent c p.2 = sample.row parent c z.1 p.2 →
      |(cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.N k ^ (-s₀)) *
        fiberDerivative (sample.fine.charts.baselineSelector p.1 - sample.coarse.charts.g c) p.2 -
          sample.signal parent c p.2| ≤ cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4)) := by
  filter_upwards [h.eventually_paired_directional_row hs₀ hε hsmall] with k hk
  intro M sample parent fine c cb p z ht hcb hpair hn hrow
  obtain ⟨ip, hchoice, hjp, hp₀, ht₀, hpc, htc, hA, hI⟩ := hn
  rw [sample.fine.charts.baselineSelector_eq sample.fine.disjoint hcb, hrow,
    sample.row_of_choice parent hchoice]
  have hh := hk parent fine ip z.2 hA hI (sample.coarse.charts.g c)
    (sample.fine.charts.g cb) ((sample.fine.charts.q cb 0 : ℝ) * cfg.N k ^ (-M))
    ((sample.fine.charts.q cb 1 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2))))
    ((sample.fine.charts.q cb 2 : ℝ) * cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2)))) p.2 ht htc
    (by simpa only [add_mul, one_mul] using sample.fine.comparison cb z.2 hpair p.2 htc)
  simpa only [abs_sub_comm] using hh

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
