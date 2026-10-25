import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CoreData
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.AniGrid

/-!
# Cells and the grids met by labels and slices

`xcell h H p = (⌊t/h⌋, ⌊x1/h⌋, ⌊x2/H⌋)`. A label's plank and a slice's moving strip meet only
the cells of explicit anisotropic grids.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Anisotropic cell of a point. -/
def xcell (b : α → Fin 6 → ℝ) (h Hc : ℝ) (p : α × ℝ) : ℤ × ℤ × ℤ :=
  (⌊p.2 / h⌋, ⌊x1 b p.1 p.2 / h⌋, ⌊x2 b p.1 p.2 / Hc⌋)

theorem measurable_x1 {b : α → Fin 6 → ℝ} (hb : Measurable b) :
    Measurable (fun p : α × ℝ => x1 b p.1 p.2) := by
  unfold x1
  exact ((measurable_pi_apply 0).comp (hb.comp measurable_fst)).add
    (measurable_snd.mul ((measurable_pi_apply 3).comp (hb.comp measurable_fst)))

theorem measurable_x2 {b : α → Fin 6 → ℝ} (hb : Measurable b) :
    Measurable (fun p : α × ℝ => x2 b p.1 p.2) := by
  unfold x2
  exact ((measurable_pi_apply 1).comp (hb.comp measurable_fst)).add
    (measurable_snd.mul ((measurable_pi_apply 4).comp (hb.comp measurable_fst)))

theorem measurable_x3 {b : α → Fin 6 → ℝ} (hb : Measurable b) :
    Measurable (fun p : α × ℝ => x3 b p.1 p.2) := by
  unfold x3
  exact ((measurable_pi_apply 2).comp (hb.comp measurable_fst)).add
    (measurable_snd.mul ((measurable_pi_apply 5).comp (hb.comp measurable_fst)))

theorem measurable_xcell {b : α → Fin 6 → ℝ} (hb : Measurable b) (h Hc : ℝ) :
    Measurable (xcell b h Hc) := by
  unfold xcell
  refine ((Int.measurable_floor).comp (measurable_snd.div_const h)).prodMk
    (((Int.measurable_floor).comp ((measurable_x1 hb).div_const h)).prodMk
      ((Int.measurable_floor).comp ((measurable_x2 hb).div_const Hc)))

theorem measurableSet_xcell_eq {b : α → Fin 6 → ℝ} (hb : Measurable b) (h Hc : ℝ)
    (ω : ℤ × ℤ × ℤ) : MeasurableSet {p : α × ℝ | xcell b h Hc p = ω} :=
  measurable_xcell hb h Hc (measurableSet_singleton ω)

/-- Cells met by a label's plank (block `I`, geometry centred by `c`). -/
def plankGrid (h Hc q K g tm : ℝ) (c : Fin 5 → ℝ) : Finset (ℤ × ℤ × ℤ) :=
  aniGrid h Hc (q / 2) (K * q) (K * q * g) tm (c 0) (c 2 + c 4 * c 0)
    (c 1) (-(c 3 + c 4 * c 1)) (c 4)

theorem mem_plankGrid {b : α → Fin 6 → ℝ} {h Hc q K g tm : ℝ} {c : Fin 5 → ℝ}
    (hh : 0 < h) (hHc : 0 < Hc) {p : α × ℝ} (ht : |p.2 - tm| ≤ q / 2)
    (hx1 : |x1 b p.1 p.2 - c 0 - p.2 * c 1| ≤ K * q)
    (hx2 : |x2 b p.1 p.2 - c 2 - p.2 * c 3 - c 4 * x1 b p.1 p.2| ≤ K * q * g) :
    xcell b h Hc p ∈ plankGrid h Hc q K g tm c := by
  unfold plankGrid xcell
  apply mem_aniGrid hh hHc ht
  · have : x1 b p.1 p.2 - (c 0 + p.2 * c 1) = x1 b p.1 p.2 - c 0 - p.2 * c 1 := by ring
    rw [this]; exact hx1
  · have : x2 b p.1 p.2 - (c 2 + c 4 * c 0 - p.2 * -(c 3 + c 4 * c 1)) -
        c 4 * (x1 b p.1 p.2 - (c 0 + p.2 * c 1)) =
        x2 b p.1 p.2 - c 2 - p.2 * c 3 - c 4 * x1 b p.1 p.2 := by ring
    rw [this]; exact hx2

theorem card_plankGrid {h Hc q K g tm : ℝ} {c : Fin 5 → ℝ} (hh : 0 < h) (hHc : 0 < Hc)
    (hq : 0 ≤ q) (hK : 0 ≤ K) (hg : 0 ≤ g) :
    ((plankGrid h Hc q K g tm c).card : ℝ) ≤
      (2 * (q / 2) / h + 5) * (2 * (K * q + |c 1| * h) / h + 5) *
        (2 * (K * q * g + (|-(c 3 + c 4 * c 1)| + |c 4| * (1 + |c 1|)) * h) / Hc + 5) :=
  card_aniGrid hh hHc (by positivity) (by positivity) (by positivity) _ _ _ _ _ _

/-- Cells met by a slice's strip `x1 ≈ p + t v`, `x2 ≈ r - t w`. -/
def stripGrid (h Hc B C p r v w : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  aniGrid h Hc (1 / 2) B C (1 / 2) p r v w 0

theorem mem_stripGrid {b : α → Fin 6 → ℝ} {h Hc B C p₀ r v w : ℝ}
    (hh : 0 < h) (hHc : 0 < Hc) {p : α × ℝ} (ht : p.2 ∈ Icc (0 : ℝ) 1)
    (hx1 : |x1 b p.1 p.2 - (p₀ + p.2 * v)| ≤ B)
    (hx2 : |x2 b p.1 p.2 - (r - p.2 * w)| ≤ C) :
    xcell b h Hc p ∈ stripGrid h Hc B C p₀ r v w := by
  unfold stripGrid xcell
  apply mem_aniGrid hh hHc
  · rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  · exact hx1
  · simpa using hx2

theorem card_stripGrid {h Hc B C p r v w : ℝ} (hh : 0 < h) (hHc : 0 < Hc)
    (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ((stripGrid h Hc B C p r v w).card : ℝ) ≤
      (2 * (1 / 2) / h + 5) * (2 * (B + |v| * h) / h + 5) *
        (2 * (C + (|w| + |0| * (1 + |v|)) * h) / Hc + 5) :=
  card_aniGrid hh hHc (by norm_num) hB hC _ _ _ _ _ _

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
