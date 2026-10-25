-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.BoundedRelativeRows
import Submission.Obl.k4_finite_affine_parent_sources.Path
import Submission.Obl.k4_finite_affine_parent_sources.VelocityFrame

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface

noncomputable section

/-- Negating the exact old candidate excludes every unit strip containing
a full-prior substantial portion of one original label. -/
theorem no_full_mass_strip_of_no_candidate
    {W : ℕ} (p : PathData W) (Nk L : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (Mc : ℕ) (d₁ ρ gain ε : ℝ) (H : Fin W → Set Incidence)
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned H)
    (b : Fin p.C) (h : ℝ) (hgain : gain ≤ h) (hupper : h ≤ 1 / 8)
    (hroom : p.r (p.lev b) + 2 * h * L ≤ L)
    (hprior : 0 < ν (p.world b) (p.assigned b))
    (V : Set Incidence)
    (hV : ∀ z ∈ V, z ∈ H (p.world b) ∧ z.1 ∈ p.assigned b ∧
      z.2 ∈ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)))
    (hfloor : ENNReal.ofReal (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev b)) *
      ν (p.world b) (p.assigned b) ≤ (ν (p.world b)).prod volume V) :
    ∀ (a : Fin 2 → ℝ) (bias : ℝ), (∑ e, (a e) ^ 2) = 1 → |bias| ≤ Nk ^ Mc →
      ¬(∀ z ∈ V, InStrip (p.T (p.lev b)) (p.velocity b) (p.frame b) a bias
        (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) z.1) := by
  intro a bias ha hb hstrip
  apply hno
  refine ⟨b, h, hgain, hupper, hroom, hprior, Or.inr ⟨a, bias, ha, hb, ?_⟩⟩
  apply hfloor.trans
  apply measure_mono
  intro z hz
  exact ⟨(hV z hz).1, (hV z hz).2.1, (hV z hz).2.2, hstrip z hz⟩

/-- Actual full-prior label floors and absence of an original candidate
bound both rows of the true relative velocity frame. The bias budget is
only `2*pathSlack`, obtained from an actual child velocity. -/
theorem relative_rows_of_no_original_candidate
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sgrid : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sgrid δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (Mc : ℕ) (d₁ ρ gain ε : ℝ) (H : Fin W → Set Incidence)
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned H)
    (b : Fin p.C) (h : ℝ) (hgain : gain ≤ h) (hupper : h ≤ 1 / 8)
    (hroom : p.r (p.lev b) + 2 * h * L ≤ L)
    (hprior : 0 < ν (p.world b) (p.assigned b))
    (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (V : Set Incidence) (hne : V.Nonempty)
    (hV : ∀ z ∈ V, z ∈ H (p.world b) ∧ z.1 ∈ p.assigned b ∧
      z.2 ∈ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)))
    (hfloor : ENNReal.ofReal (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev b)) *
      ν (p.world b) (p.assigned b) ≤ (ν (p.world b)).prod volume V)
    (Φ : PFrame) (Kparent : ℝ) (hKparent : 0 ≤ Kparent)
    (hparent : ∀ z ∈ V, ∀ e : Fin 2,
      |(WithLp.toLp 2 ![Φ.eb z.1 3, Φ.eb z.1 4]) e| ≤ Kparent) :
    ∀ e : Fin 2,
      ‖WithLp.toLp 2 (fun f =>
        relativeVelocityFrame Φ.F.q (((2 : ℝ) ^ p.T (p.lev b))⁻¹) Φ.F.D (p.frame b) e f)‖ ≤
      2 * Kparent / (Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) := by
  let q := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  have hq : 0 < q := by dsimp only [q]; positivity
  let old : Incidence → EuclideanSpace ℝ (Fin 2) := fun z =>
    q • Matrix.toEuclideanLin (p.frame b)⁻¹ (gv z.1 - p.velocity b)
  let parent : Incidence → EuclideanSpace ℝ (Fin 2) := fun z =>
    WithLp.toLp 2 ![Φ.eb z.1 3, Φ.eb z.1 4]
  let M := relativeVelocityFrame Φ.F.q q Φ.F.D (p.frame b)
  let offset := Φ.F.q • Matrix.toEuclideanLin Φ.F.D⁻¹ (p.velocity b - Φ.F.u)
  have hold : ∀ z ∈ V, ‖old z‖ ≤ 2 * p.κ := by
    intro z hz
    have hv := gchart_velocity (hp.chart b) (hV z hz).2.1
    change ‖q • Matrix.toEuclideanLin (p.frame b)⁻¹ (gv z.1 - p.velocity b)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hq.le]
    apply (mul_le_mul_of_nonneg_left hv hq.le).trans_eq
    dsimp only [q]
    field_simp
  have hrel : ∀ z ∈ V, parent z = offset + Matrix.toEuclideanLin M (old z) := by
    intro z _
    have h := relativeVelocityFrame_identity (q₀ := Φ.F.q) (q₁ := q)
      (Q₀ := Φ.F.D) (Q₁ := p.frame b) hq.ne' (hp.chart b).1 Φ.F.u (p.velocity b) (gv z.1)
    rwa [← Φ.velocity_eq] at h
  apply relative_rows_le_of_no_strip V hne old parent M offset (2 * p.κ) Kparent
    _ hKparent (by positivity) hold hparent hrel
  intro a bias ha hb hstrip
  apply no_full_mass_strip_of_no_candidate p Nk L ν B Mc d₁ ρ gain ε H hno b h
    hgain hupper hroom hprior V hV hfloor a bias ha (hb.trans hbias)
  intro z hz
  have hh := hstrip z hz
  simpa only [old, q, InStrip, PiLp.smul_apply, smul_eq_mul, v,
    k4_quadratic_finite_greedy_cover.v, gv, mul_assoc] using hh

end

end Submission.Obl.k4_finite_affine_parent_sources
