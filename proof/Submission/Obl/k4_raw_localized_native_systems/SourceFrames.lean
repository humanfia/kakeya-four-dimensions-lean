import Submission.Obl.k4_raw_localized_native_systems.SourceSequence
import Submission.Obl.k4_raw_localized_native_systems.SourceLayers

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_raw_critical_segment_forests

noncomputable section

/-- The original earlier layer, with its observation policy keyed at the
terminal depth. Its assignments, events and frames are unchanged. -/
abbrev sourceFrame {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r) (i : ℕ) : Atlas p k :=
  finerLists (sourceLayer a ha i) (r i)

theorem sourceFrame_wchart {p : Data} (hp : Valid p) {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (hprep : a.Prepared r (sourceLists a r)) {i : ℕ} (hi : i < m)
    (hr : r i ≤ p.L) (e : Fin (sourceFrame a ha i).C) :
    Window.WChart p k (sourceFrame a ha i) M D a.κ (r i) e := by
  exact ⟨_, (sourceLayer_known hp a ha hprep hi hr).1.2.2.1 e⟩

theorem sourceFrame_floor {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r) {i : ℕ} (hi : i < m)
    (e : Fin (sourceFrame a ha i).C) :
    ENNReal.ofReal (p.N k ^ (-p.f (r i)) * |((sourceFrame a ha i).Q e).det| /
      ((2 : ℝ) ^ (sourceFrame a ha i).T * a.κ)) ≤ Window.wmass (sourceFrame a ha i) e :=
  source_layer_floor a ha (sourceLists a r) hi e

theorem sourceFrame_disjoint {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r) {i : ℕ} (hi : i < m) :
    ∀ e e', e ≠ e' → (sourceFrame a ha i).γ e = (sourceFrame a ha i).γ e' →
      (sourceFrame a ha i).j e = (sourceFrame a ha i).j e' →
      Disjoint ((sourceFrame a ha i).A e) ((sourceFrame a ha i).A e') :=
  (a.layer_trueDepth ha hi (sourceLists a r)).2.1

theorem sourceFrame_coverage {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r) {i : ℕ} (hi : i < m) :
    ENNReal.ofReal a.κ⁻¹ ≤ ∑ e, ENNReal.ofReal (p.ω k ((sourceFrame a ha i).γ e)) *
      Window.wmass (sourceFrame a ha i) e :=
  (a.layer_trueDepth ha hi (sourceLists a r)).2.2.2

theorem sourceFrame_known {p : Data} (hp : Valid p) {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (hprep : a.Prepared r (sourceLists a r)) {i : ℕ} (hi : i < m)
    (hr : r i ≤ p.L) :
    ∀ e z, z ∈ (sourceFrame a ha i).F e →
      e ∈ (sourceFrame a ha i).lst ((sourceFrame a ha i).γ e)
        (obs (p.B k ((sourceFrame a ha i).γ e)) (δ (p.N k) p.L) z) := by
  intro e z hz
  exact k4_native_calibrated_homogeneous_remainder.chart_extra
    ((sourceLayer_known hp a ha hprep hi hr).1.2.2.1 e) z hz

theorem sourceFrame_card {p : Data} (hp : Valid p) {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (hprep : a.Prepared r (sourceLists a r)) {i : ℕ} (hi : i < m)
    (hr : r i ≤ p.L) (γ : Fin (p.W k)) (o : Observation) :
    (((sourceFrame a ha i).lst γ o).card : ℝ) ≤ a.κ :=
  (sourceLayer_known hp a ha hprep hi hr).2 γ o

theorem sourceFrame_measurable {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r) (i : ℕ)
    (γ : Fin (p.W k)) (e : Fin (sourceFrame a ha i).C) :
    MeasurableSet {o | e ∈ (sourceFrame a ha i).lst γ o} :=
  sourceLayer_terminal_lists_measurable a ha i γ e

theorem sourceFrame_own_known {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (hprep : a.Prepared r (sourceLists a r)) (i : ℕ) :
    ∀ e z, z ∈ (sourceFrame a ha i).F e →
      e ∈ (sourceLayer a ha i).lst ((sourceFrame a ha i).γ e)
        (obs (p.B k ((sourceFrame a ha i).γ e)) (δ (p.N k) (r i)) z) :=
  fun e => ((a.layer_prepared (sourceLists a r) hprep i (ha.j_lt · ·)).2 e).2

theorem sourceFrame_own_card {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : Forest p k) (ha : a.Core M D m r)
    (hprep : a.Prepared r (sourceLists a r)) (i : ℕ)
    (γ : Fin (p.W k)) (o : Observation) :
    (((sourceLayer a ha i).lst γ o).card : ℝ) ≤ a.κ :=
  (a.layer_prepared (sourceLists a r) hprep i (ha.j_lt · ·)).1 γ o

/-- Homogeneity is inherited by the full original earlier frames without
changing their logarithmic widths or the selected scale sequence. -/
theorem sourceFrame_width {p : Data} {kr w ε q band : ℝ} {m M D : ℕ}
    {sd r : ℕ → ℝ} (src : HomogeneousSourceSequence p kr w ε q band m M D sd r)
    (n i : ℕ) (e : Fin (sourceFrame (src.forest n) (src.core n) i).C) :
    p.N (src.index n) ^ (-src.width n ((src.forest n).layerEmb i e)) =
      |((sourceFrame (src.forest n) (src.core n) i).Q e).det| *
        (4 : ℝ) ^ (sourceFrame (src.forest n) (src.core n) i).T ∧
      |src.width n ((src.forest n).layerEmb i e) - src.levelWidth n i| ≤ band := by
  have he := (src.forest n).layerEmb_lev i e
  constructor
  · change p.N (src.index n) ^ (-src.width n ((src.forest n).layerEmb i e)) =
      |((src.forest n).Q ((src.forest n).layerEmb i e)).det| * (4 : ℝ) ^ (src.forest n).T i
    simpa only [he] using src.width_exact n ((src.forest n).layerEmb i e)
  · simpa only [he] using src.width_band n ((src.forest n).layerEmb i e)

end
end Submission.Obl.k4_raw_localized_native_systems
