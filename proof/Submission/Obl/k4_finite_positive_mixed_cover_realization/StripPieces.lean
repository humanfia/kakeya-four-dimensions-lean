import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripNormal
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripRepresentatives
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripPredicates
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripBudgets

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

abbrev CoverData.Active {W : ℕ} {p : PathData W} (c : CoverData p) :=
  {a : Fin c.n // (c.assigned a).Nonempty}

noncomputable def CoverData.stripRow {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) (a : Fin c.n) : Fin 3 → ℤ :=
  stripParameterCode width (c.unitNormal a) (c.bias a)

noncomputable def CoverData.stripRepresentative {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) (old : Fin p.C) (row : Fin 3 → ℤ) : Plane × ℝ :=
  representativeStrip (fun a : c.Active => c.old a.val)
    (fun a : c.Active => c.unitNormal a.val) (fun a : c.Active => c.bias a.val) width old row

noncomputable def CoverData.oldMidpoint {W : ℕ} {p : PathData W} (c : CoverData p)
    (a : Fin c.n) : ℝ :=
  (p.bin (c.old a) : ℝ) / (2 : ℝ) ^ p.T c.level + ((2 : ℝ) ^ p.T c.level)⁻¹ / 2

/-- Candidate identities are used only to supply disjoint pieces. Their
geometric output parameters depend on the parent, row code and midpoint bin. -/
noncomputable def CoverData.stripPiece {W : ℕ} {p : PathData W} (c : CoverData p)
    (width : ℝ) (a : Fin c.n) (z : ℤ) : Set Trajectory :=
  c.assigned a ∩ stripMidpointBin (c.oldMidpoint a) (p.frame (c.old a))
    (p.center (c.old a)) (p.velocity (c.old a))
    (c.stripRepresentative width (c.old a) (c.stripRow width a)).1 width z

section
variable {W m Mp Dp Mg Dg : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε width : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hc ht

lemma CoverData.Valid.representative_unit (old : Fin p.C) (row : Fin 3 → ℤ) :
    ‖(c.stripRepresentative width old row).1‖ = 1 :=
  representativeStrip_unit _ _ _ _ (fun a : c.Active => hc.normal_unit ht a.val) old row

include hp

lemma CoverData.Valid.representative_bias (hfit :
    Nk ^ (4 * ρ * c.gain * L + 4 * ε) * Nk ^ (-c.gain * L) ≤ 1)
    (old : Fin p.C) (row : Fin 3 → ℤ) :
    |(c.stripRepresentative width old row).2| ≤ 3 * p.κ := by
  apply representativeStrip_bias_le _ _ _ _ (by linarith [hp.one_le_slack]) ?_ old row
  intro a
  obtain ⟨l, hl⟩ := a.property
  have hbound := strip_bias_le (hc.normal_unit ht a.val)
    (hc.normalized_velocity_bound hp a.val l hl) (hc.normal_fit ht a.val l hl)
  linarith [hp.one_le_slack]

lemma CoverData.Valid.representative_fit (hwidth : 0 < width)
    (hfit : Nk ^ (4 * ρ * c.gain * L + 4 * ε) * Nk ^ (-c.gain * L) ≤ width)
    (a : Fin c.n) (l : Trajectory) (hl : l ∈ c.assigned a) :
    |inner ℝ (c.normalizedVelocity a l)
        (c.stripRepresentative width (c.old a) (c.stripRow width a)).1 -
      (c.stripRepresentative width (c.old a) (c.stripRow width a)).2| ≤
        (4 + 6 * p.κ) * width := by
  let a' : c.Active := ⟨a, ⟨l, hl⟩⟩
  have h := representativeStrip_fit
    (fun b : c.Active => c.old b.val) (fun b : c.Active => c.unitNormal b.val)
    (fun b : c.Active => c.bias b.val) hwidth (show 0 ≤ 2 * p.κ by linarith [hp.one_le_slack])
    a' (c.normalizedVelocity a l) (hc.normalized_velocity_bound hp a l hl) hfit
    (hc.normal_fit ht a l hl)
  rw [show (4 + 3 * (2 * p.κ)) * width = (4 + 6 * p.κ) * width by ring] at h
  simpa only [CoverData.stripRepresentative, CoverData.stripRow, a'] using h

lemma CoverData.Valid.stripPiece_center (hwidth : 0 < width) (a : Fin c.n) (z : ℤ)
    (hne : (c.stripPiece width a z).Nonempty) : |(z : ℝ) * width| ≤ p.κ + width := by
  obtain ⟨l, hl⟩ := hne
  have hline := (hp.chart (c.old a)).2.2.2.2.2.2.2.2.2.1 l (hc.assigned_subset a hl.1)
  have hmid : c.oldMidpoint a ∈ Icc
      ((p.bin (c.old a) : ℝ) / (2 : ℝ) ^ p.T c.level)
      (((p.bin (c.old a) : ℝ) + 1) / (2 : ℝ) ^ p.T c.level) := by
    have hq : 0 < ((2 : ℝ) ^ p.T c.level)⁻¹ := by positivity
    constructor <;> simp only [CoverData.oldMidpoint, div_eq_mul_inv] <;> nlinarith
  have hpos := hline.2.2 (c.oldMidpoint a)
  rw [hc.old_level a] at hpos
  exact stripMidpointBin_center_le hwidth (hc.representative_unit ht _ _) (hpos hmid).1 hl.2

omit ht hp in
lemma CoverData.Valid.stripPiece_format (a : Fin c.n) (z : ℤ) (q : ℕ) :
    gfmt 6 (Nk ^ Mg + 2) (max Dg 1) {x | (q, x) ∈ c.stripPiece width a z} :=
  gfmt_inter (hc.assigned_format a q)
    (stripMidpointBin_format _ _ _ _ _ _ _ q)

omit ht hp in
lemma CoverData.Valid.stripPiece_measurable (a : Fin c.n) (z : ℤ) :
    MeasurableSet (c.stripPiece width a z) := by
  let n := (c.stripRepresentative width (c.old a) (c.stripRow width a)).1
  have hy : Continuous (fun l : Trajectory => gy l (c.oldMidpoint a)) := by
    dsimp only [gy, gx]
    fun_prop
  have hlin : Continuous (Matrix.toEuclideanLin (p.frame (c.old a))⁻¹) :=
    LinearMap.continuous_of_finiteDimensional _
  have hfun : Measurable (fun l : Trajectory => inner ℝ
      (Matrix.toEuclideanLin (p.frame (c.old a))⁻¹
        (gy l (c.oldMidpoint a) - p.center (c.old a) - c.oldMidpoint a • p.velocity (c.old a))) n / width) :=
    (((hlin.comp ((hy.sub continuous_const).sub continuous_const)).inner continuous_const).div_const _).measurable
  exact (hc.assigned_measurable a).inter
    ((Int.measurable_floor.comp hfun) (measurableSet_singleton z))

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
