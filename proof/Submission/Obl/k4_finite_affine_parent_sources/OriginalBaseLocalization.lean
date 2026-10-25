-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.BaseLocalization
import Submission.Obl.k4_finite_affine_parent_sources.NoCandidateFrames

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface

noncomputable section

/-- The original no-candidate hypothesis localizes an end label in any
earlier invertible packet chart. The output keeps the exact ratio of old
time lengths required by the native oscillation partition. -/
theorem PFrame.original_end_label_base_diameter
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (Mc : ℕ) (d₁ ρ gain ε : ℝ) (Hres : Fin W → Set Incidence)
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned Hres)
    (child : Fin p.C) (h : ℝ) (hgain : gain ≤ h) (hupper : h ≤ 1 / 8)
    (hroom : p.r (p.lev child) + 2 * h * L ≤ L)
    (hprior : 0 < ν (p.world child) (p.assigned child))
    (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (V : Set Incidence) (hne : V.Nonempty)
    (hV : ∀ z ∈ V, z ∈ Hres (p.world child) ∧ z.1 ∈ p.assigned child ∧
      z.2 ∈ Icc ((p.bin child : ℝ) / (2 : ℝ) ^ p.T (p.lev child))
        (((p.bin child : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev child)))
    (hfloor : ENNReal.ofReal (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev child)) *
      ν (p.world child) (p.assigned child) ≤ (ν (p.world child)).prod volume V)
    (Φ : PFrame) (hq₀ : 0 < Φ.F.q) (hD : Φ.F.D.det ≠ 0)
    (Kparent H : ℝ) (hK : 0 ≤ Kparent) (hH : 1 ≤ H)
    (hκH : p.κ ≤ H) (hKH : Kparent ≤ H)
    (hvel : ∀ l ∈ p.assigned child, ‖gv (0, Φ.eb l)‖ ≤ Kparent)
    (hrowBudget : 2 * Kparent / (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) ≤ H)
    (l : Trajectory) (hl : l ∈ p.assigned child)
    (l' : Trajectory) (hl' : l' ∈ p.assigned child)
    (t t' : ℝ)
    (ht : t ∈ Icc ((p.bin child : ℝ) / (2 : ℝ) ^ p.T (p.lev child))
      (((p.bin child : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev child)))
    (ht' : t' ∈ Icc ((p.bin child : ℝ) / (2 : ℝ) ^ p.T (p.lev child))
      (((p.bin child : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev child))) :
    ‖pointBaseS Φ.eb (l, (t - Φ.F.t₀) / Φ.F.q) -
        pointBaseS Φ.eb (l', (t' - Φ.F.t₀) / Φ.F.q)‖ ≤
      16 * H ^ 4 * ((((2 : ℝ) ^ p.T (p.lev child))⁻¹) / Φ.F.q) := by
  have hparent : ∀ z ∈ V, ∀ e : Fin 2,
      |(WithLp.toLp 2 ![Φ.eb z.1 3, Φ.eb z.1 4]) e| ≤ Kparent := by
    intro z hz e
    have he := (PiLp.norm_apply_le (gv (0, Φ.eb z.1)) e).trans (hvel z.1 (hV z hz).2.1)
    simpa only [gv, Real.norm_eq_abs] using he
  have hrows := relative_rows_of_no_original_candidate hp hNk Mc d₁ ρ gain ε Hres hno
    child h hgain hupper hroom hprior hbias V hne hV hfloor Φ Kparent hK hparent
  have hrowsH : ∀ e : Fin 2, ‖frameRow (relativeVelocityFrame Φ.F.q
      (((2 : ℝ) ^ p.T (p.lev child))⁻¹) Φ.F.D (p.frame child)) e‖ ≤ H := by
    intro e
    simpa only [frameRow] using (hrows e).trans hrowBudget
  let a := (p.bin child : ℝ) / (2 : ℝ) ^ p.T (p.lev child)
  let q := ((2 : ℝ) ^ p.T (p.lev child))⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hend : a + q = ((p.bin child : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev child) := by
    dsimp only [a, q]
    ring
  have hfit : ∀ l ∈ p.assigned child, ∀ r ∈ Icc a (a + q),
      ‖Matrix.toEuclideanLin (p.frame child)⁻¹
        (gy l r - p.center child - r • p.velocity child)‖ ≤ p.κ := by
    intro l hl r hr
    rw [hend] at hr
    exact (((hp.chart child).2.2.2.2.2.2.2.2.2.1 l hl).2.2 r hr).1
  exact Φ.end_label_base_diameter hq₀ hD (p.frame child) (hp.chart child).1
    (p.center child) (p.velocity child) (p.assigned child) a q p.κ H Kparent hq
    (zero_le_one.trans hp.one_le_slack) hK hH hκH hKH hrowsH hfit hvel
    l hl l' hl' t t' (by simpa only [hend] using ht) (by simpa only [hend] using ht')

end

end Submission.Obl.k4_finite_affine_parent_sources
