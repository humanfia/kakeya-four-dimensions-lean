-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/CenteredStripReturn.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.Path
import Submission.Obl.k4_finite_affine_candidate_return.BoundedRelativeRows

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory Set Submission.Lib.K4XInterface

noncomputable section

/-- Center a counted unit strip at an actual old velocity. Its bias then
uses only the old velocity bound, independently of the raw native strip
intercept or the relative matrix's inverse budget. -/
theorem recenter_unit_strip
    {Y : Type*} (V : Set Y) (hne : V.Nonempty)
    (old : Y → EuclideanSpace ℝ (Fin 2)) (K : ℝ)
    (hold : ∀ y ∈ V, ‖old y‖ ≤ K)
    (a : Fin 2 → ℝ) (ha : (∑ e, (a e) ^ 2) = 1) (bias width : ℝ)
    (hstrip : ∀ y ∈ V, |(∑ e, a e * old y e) - bias| ≤ width) :
    ∃ center : ℝ, |center| ≤ K ∧
      ∀ y ∈ V, |(∑ e, a e * old y e) - center| ≤ 2 * width := by
  obtain ⟨y₀, hy₀⟩ := hne
  let avec : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 a
  have hnorm : ‖avec‖ = 1 := by
    have hs : ‖avec‖ ^ 2 = 1 := by
      rw [norm_sq_fin2]
      simpa only [Fin.sum_univ_two] using ha
    nlinarith [norm_nonneg avec]
  have hinner (y : Y) : (∑ e, a e * old y e) = inner ℝ avec (old y) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial, avec]
    ring
  refine ⟨∑ e, a e * old y₀ e, ?_, fun y hy => ?_⟩
  · rw [hinner]
    exact (abs_real_inner_le_norm _ _).trans
      (by simpa only [hnorm, one_mul] using hold y₀ hy₀)
  · have heq : (∑ e, a e * old y e) - (∑ e, a e * old y₀ e) =
        ((∑ e, a e * old y e) - bias) - ((∑ e, a e * old y₀ e) - bias) := by ring
    rw [heq]
    exact (abs_sub _ _).trans ((add_le_add (hstrip y hy) (hstrip y₀ hy₀)).trans_eq (by ring))

/-- A substantial actual old strip returns as an allowed original
candidate after recentering. Its bias budget is only twice path slack;
the raw native slope and intercept need no separate height estimate. -/
theorem original_candidate_of_narrow_strip
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (Mc : ℕ) (d₁ ρ gain ε : ℝ) (H : Fin W → Set Incidence)
    (b : Fin p.C) (h : ℝ) (hgain : gain ≤ h) (hupper : h ≤ 1 / 8)
    (hroom : p.r (p.lev b) + 2 * h * L ≤ L)
    (hprior : 0 < ν (p.world b) (p.assigned b))
    (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (V : Set Incidence)
    (hV : ∀ z ∈ V, z ∈ H (p.world b) ∧ z.1 ∈ p.assigned b ∧
      z.2 ∈ Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)))
    (hfloor : ENNReal.ofReal (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev b)) *
      ν (p.world b) (p.assigned b) ≤ (ν (p.world b)).prod volume V)
    (a : Fin 2 → ℝ) (ha : (∑ e, (a e) ^ 2) = 1) (bias width : ℝ)
    (hstrip : ∀ z ∈ V, InStrip (p.T (p.lev b)) (p.velocity b) (p.frame b) a bias width z.1)
    (hwidth : 2 * width ≤ Nk ^ (ρ * h * L + ε) * Nk ^ (-h * L)) :
    MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world
      p.bin p.velocity p.frame p.assigned H := by
  have hpos : 0 < ENNReal.ofReal (Nk ^ (-ρ * h * L - ε) / (2 : ℝ) ^ p.T (p.lev b)) *
      ν (p.world b) (p.assigned b) := by positivity
  have hne : V.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty] at hfloor
    exact (not_le_of_gt hpos) hfloor
  let q := ((2 : ℝ) ^ p.T (p.lev b))⁻¹
  have hq : 0 < q := by dsimp only [q]; positivity
  let old (z : Incidence) : EuclideanSpace ℝ (Fin 2) :=
    q • Matrix.toEuclideanLin (p.frame b)⁻¹ (gv z.1 - p.velocity b)
  have hold (z : Incidence) (hz : z ∈ V) : ‖old z‖ ≤ 2 * p.κ := by
    have hv := gchart_velocity (hp.chart b) (hV z hz).2.1
    dsimp only [old]
    rw [norm_smul, Real.norm_of_nonneg hq.le]
    apply (mul_le_mul_of_nonneg_left hv hq.le).trans_eq
    dsimp only [q]
    field_simp
  have hstrip' (z : Incidence) (hz : z ∈ V) :
      |(∑ e, a e * old z e) - bias| ≤ width := by
    simpa only [old, q, InStrip, PiLp.smul_apply, smul_eq_mul, v,
      k4_quadratic_finite_greedy_cover.v, gv, mul_assoc] using hstrip z hz
  obtain ⟨center, hc, hcenter⟩ := recenter_unit_strip V hne old (2 * p.κ) hold a ha bias width hstrip'
  refine ⟨b, h, hgain, hupper, hroom, hprior, Or.inr ⟨a, center, ha, hc.trans hbias, ?_⟩⟩
  apply hfloor.trans
  apply measure_mono
  intro z hz
  refine ⟨(hV z hz).1, (hV z hz).2.1, (hV z hz).2.2, ?_⟩
  have hh := (hcenter z hz).trans hwidth
  simpa only [old, q, InStrip, PiLp.smul_apply, smul_eq_mul, v,
    k4_quadratic_finite_greedy_cover.v, gv, mul_assoc] using hh

end

end Submission.Obl.k4_finite_affine_candidate_return
