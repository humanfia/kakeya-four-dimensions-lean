import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripAtlas
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripListBudgets

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface Submission.Lib.K4VelocityStrips
open Submission.Obl.k4_finite_forest_width_selection
open scoped RealInnerProductSpace

noncomputable def CoverData.normalizedObservation {W : ℕ} {p : PathData W} (c : CoverData p)
    (old : Fin p.C) (o : Observation) : Plane :=
  Matrix.toEuclideanLin (p.frame old)⁻¹
    (WithLp.toLp 2 ![o.1 1, o.1 2] - p.center old - (o.1 0) • p.velocity old)

noncomputable def CoverData.shortStripCodes {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    (o : Observation) (d : Fin p.C) : Finset UnitStripCode :=
  let old := forestAncestor p.lev p.par d c.level
  let repr := c.stripRepresentative width old
  let t₀ := (p.bin old : ℝ) / (2 : ℝ) ^ p.T c.level
  let q := ((2 : ℝ) ^ p.T c.level)⁻¹
  unitStripCodeList 1 ⌈4 + 6 * p.κ⌉₊ width (normal d) (bias d) width
    (fun row => (repr row).1) (fun row => (repr row).2)
    ((o.1 0 - t₀) / q) (c.normalizedObservation old o)

noncomputable def CoverData.stripLists {W : ℕ} {p : PathData W} (c : CoverData p)
    (Nk L width : ℝ) (j : ℕ) (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    (w : Fin W) (o : Observation) : Finset (c.usedStripKeys width) :=
  recoveredCodeList (fun b : c.usedStripKeys width => b.val)
    (fun d => forestAncestor p.lev p.par d c.level)
    (p.terminalLists Nk L j w o) (c.shortStripCodes width normal bias o)

section
variable {W m Mp Dp Mg Dg : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε width gap : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (j : ℕ) (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)

include hp

lemma CoverData.Valid.stripLists_count (w : Fin W) (o : Observation) :
    ((c.stripLists Nk L width j normal bias w o).card : ℝ) ≤ 1242 * p.κ ^ 2 := by
  apply recovered_unitStripCodeList_path_card (fun b : c.usedStripKeys width => b.val)
    Subtype.val_injective (fun d => forestAncestor p.lev p.par d c.level)
    (p.terminalLists Nk L j w o) hp.one_le_slack (hp.terminal_list_bound j w o)
    (fun _ => width) (fun _ => width) normal bias
    (fun d row => (c.stripRepresentative width (forestAncestor p.lev p.par d c.level) row).1)
    (fun d row => (c.stripRepresentative width (forestAncestor p.lev p.par d c.level) row).2)
    (fun d => (o.1 0 - (p.bin (forestAncestor p.lev p.par d c.level) : ℝ) /
      (2 : ℝ) ^ p.T c.level) / ((2 : ℝ) ^ p.T c.level)⁻¹)
    (fun d => c.normalizedObservation (forestAncestor p.lev p.par d c.level) o)

include hc ht

lemma CoverData.Valid.stripPiece_known
    (hNk : 1 ≤ Nk) (hrj : 0 ≤ p.r j) (hrjL : p.r j ≤ L)
    (hwidth : 0 < width) (hgap : gap ≤ width)
    (hfit : Nk ^ (4 * ρ * c.gain * L + 4 * ε) * Nk ^ (-c.gain * L) ≤ width)
    (a : Fin c.n) (z : ℤ) (key : c.usedStripKeys width)
    (hkey : key.val = (c.old a, (c.stripRow width a, z)))
    {v : Incidence} (hv : v ∈ c.pieceIncidence width gap j normal bias a z) :
    key ∈ c.stripLists Nk L width j normal bias (p.world (c.old a))
      (gobs (B (p.world (c.old a))) (gδ Nk L) v) := by
  obtain ⟨d, ⟨hd, hdw, hparent, halign⟩, hvd⟩ := hv.2
  apply (mem_recoveredCodeList (fun b : c.usedStripKeys width => b.val)
    (fun d => forestAncestor p.lev p.par d c.level) _ _ key).mpr
  refine ⟨d, ?_, ?_, ?_⟩
  · have hk := hp.terminal_known hNk hd hrj hrjL hvd
    simpa only [hdw] using hk
  · rw [hkey]
    exact hparent.symm
  · have hline := hv.1.2.1
    have htime := (hp.counted_support (c.old a) v hv.1.1).2.2.1
    rw [hc.old_level a] at htime
    have htime' : v.2 ∈ Icc
        ((p.bin (c.old a) : ℝ) / (2 : ℝ) ^ p.T c.level)
        ((p.bin (c.old a) : ℝ) / (2 : ℝ) ^ p.T c.level + ((2 : ℝ) ^ p.T c.level)⁻¹) := by
      simpa only [add_div, one_div] using htime
    have hparams :
        ‖c.unitNormal a - normal d‖ + |c.bias a - bias d| ≤ (1 : ℝ) * width ∨
        ‖c.unitNormal a + normal d‖ + |c.bias a + bias d| ≤ (1 : ℝ) * width := by
      rcases halign with h | h
      · exact Or.inl (by simpa only [one_mul] using h.trans hgap)
      · exact Or.inr (by simpa only [one_mul] using h.trans hgap)
    have hvel := hc.representative_fit ht hp hwidth hfit a v.1 hline
    have hCp : (4 + 6 * p.κ) * width ≤ (⌈4 + 6 * p.κ⌉₊ : ℝ) * width :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) hwidth.le
    have hknown := original_unit_strip_code_mem_list v.1
      (fun row => (c.stripRepresentative width (c.old a) row).1)
      (fun row => (c.stripRepresentative width (c.old a) row).2)
      (t₀ := (p.bin (c.old a) : ℝ) / (2 : ℝ) ^ p.T c.level)
      (q := ((2 : ℝ) ^ p.T c.level)⁻¹)
      (c := p.center (c.old a)) (u := p.velocity (c.old a)) (Q := p.frame (c.old a))
      (h := width) (r := width) (t := v.2) (Cr := 1) (Cp := ⌈4 + 6 * p.κ⌉₊)
      (n := c.unitNormal a) (m := normal d) (β := c.bias a) (γ := bias d)
      (by positivity) hwidth hwidth htime' (by simpa using hparams) (hvel.trans hCp)
    have hz : ⌊inner ℝ (Matrix.toEuclideanLin (p.frame (c.old a))⁻¹
        (gy v.1 (c.oldMidpoint a) - p.center (c.old a) -
          c.oldMidpoint a • p.velocity (c.old a)))
        (c.stripRepresentative width (c.old a) (c.stripRow width a)).1 / width⌋ = z := hv.1.2.2
    dsimp only [CoverData.oldMidpoint, CoverData.stripRow] at hz
    rw [hz] at hknown
    rw [hkey]
    simpa [CoverData.shortStripCodes, CoverData.normalizedObservation,
      hparent, CoverData.stripRow, CoverData.oldMidpoint, gobs, gy, gx] using hknown

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
