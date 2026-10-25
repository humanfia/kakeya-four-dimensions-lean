/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactValid.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactCorrection

/-!
# Validity of the zoomed contact instance along a sequence

`ZoomSeq` bundles a sequence of zoom inputs with the base corrections `Gb` of
their native polynomials (`Pn = nPush (P - Gb(base))`), the row/skew bounds `M₁`, the dense-mass constants `MG`, a
diagonal atlas range `Rm`, the velocity scales `vs` of the witness pairs and the
zoomed constant `Kz`; `ZoomSeq.Good` lists the hypotheses (all checkable at one
index, or eventual where the diagonal argument needs it). From them:

* `params_valid`: the zoomed parameters are valid;
* `common`: the zoomed model satisfies `Common` at every index;
* `caps`: the zoomed model satisfies `Caps` (hidden, corrected native and joint
  caps from the original caps on a finer original mesh);
* `atlases`, `nested`: eventual atlases and nesting through the diagonal range
  `Rm → ∞` and the grid step `δ → 0`;
* `valid`, `contact`, `result`: the zoomed model is a valid contact instance, so
  `ContactModelPrinciple` gives its `Result`.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter Topology
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point)
open Submission.Lib.K4MovingMeshBoxes (baseMesh)

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The parent block count gives a lower bound for the block length. -/
theorem atlas_q_lower {p : Parameters} {a : PreparedModel α} {R : ℝ} {k : ℕ} {s : ℝ}
    (hp : p.Valid) (h : a.AtlasAt p R k s) :
    p.N k ^ (-(p.kappa * s)) / p.K k ≤ a.q k s := by
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hK0 : 0 < p.K k := by linarith [hp.2.2.1.1 k]
  have h2 := h.2.1
  have hT : (0 : ℝ) < (2 : ℝ) ^ a.T k s := by positivity
  have hq : a.q k s = ((2 : ℝ) ^ a.T k s)⁻¹ := by
    simp only [PreparedModel.q, zpow_neg, zpow_natCast]
  rw [hq, Real.rpow_neg hN0.le, div_eq_mul_inv, ← mul_inv]
  apply inv_anti₀ hT
  rw [mul_comm]; exact h2

/-- Data of the zoomed contact instance along a sequence of indices. -/
structure ZoomSeq (p : Parameters) (a : PreparedModel α) (r : ℝ) where
  /-- zoom inputs -/
  I : ℕ → ZoomInput p a r
  /-- nonempty grids -/
  hM : ∀ m, 0 < (I m).M
  /-- base corrections of the native polynomials (original base coordinates) -/
  Gb : ℕ → MvPolynomial (Fin 3) ℝ
  /-- row and skew bound -/
  M₁ : ℕ → ℝ
  /-- inverse dense-mass fraction -/
  MG : ℕ → ℝ
  /-- diagonal atlas range -/
  Rm : ℕ → ℝ
  /-- velocity scale of the witness pairs -/
  vs : ℕ → ℝ
  /-- constant of the zoomed instance -/
  Kz : ℕ → ℝ
  /-- relative depth range of the zoomed instance -/
  U' : ℝ
  /-- contact exponent -/
  e₀' : ℝ

namespace ZoomSeq

variable {p : Parameters} {a : PreparedModel α} {r : ℝ}

/-- The zoomed model. -/
abbrev model (Z : ZoomSeq p a r) : PreparedModel α := zoomModel Z.I Z.hM

/-- The zoomed parameters. -/
abbrev params (Z : ZoomSeq p a r) : Parameters := zoomParams p Z.I Z.Kz Z.U' Z.e₀'

/-- Hypotheses on the data of the zoomed contact instance. -/
structure Good (Z : ZoomSeq p a r) : Prop where
  r_pos : 0 < r
  k_tendsto : Tendsto (fun m => (Z.I m).k) atTop atTop
  Gb_deg : ∀ m, (Z.Gb m).totalDegree ≤ 2
  Pn_eq : ∀ m, (Z.I m).Pn = Zoom.nPush (Z.I m).Z (Z.I m).B (Z.I m).lam
    (Submission.Lib.K4ContactNormalization.baseCalibratedTest (a.P (Z.I m).k) (Z.Gb m))
  R_gt : ∀ m, 1 < Z.Rm m
  R_tendsto : Tendsto Z.Rm atTop atTop
  atlas_r : ∀ m, a.AtlasAt p (Z.Rm m) (Z.I m).k r
  atlas_depth : ∀ m j, a.AtlasAt p (Z.Rm m) (Z.I m).k ((Z.I m).depth j)
  G_meas : ∀ m, MeasurableSet (Z.I m).G
  G_sub : ∀ m, (Z.I m).G ⊆ a.B (Z.I m).k r (Z.I m).Q ×ˢ a.block (Z.I m).k r (Z.I m).Q
  MG_pos : ∀ m, 0 < Z.MG m
  θ_pos : ∀ m, 0 < (Z.I m).θ
  θ_le : ∀ m, 4 * (Z.I m).θ ≤ 1 / Z.MG m
  mass : ∀ m, ENNReal.ofReal (a.q (Z.I m).k r / Z.MG m) *
    a.nu (Z.I m).k (a.A (Z.I m).k r (Z.I m).Q) ≤ a.rho (Z.I m).k (Z.I m).G
  lam_ne : ∀ m, (Z.I m).lam ≠ 0
  M₁_ge : ∀ m, 1 ≤ Z.M₁ m
  lam_inv_le : ∀ m, |(Z.I m).lam⁻¹| ≤ Z.M₁ m
  lam_le : ∀ m, |(Z.I m).lam| ≤ Z.M₁ m
  B_le : ∀ m, |(Z.I m).B 0| + |(Z.I m).B 1| ≤ Z.M₁ m
  δ_pos : ∀ m, 0 < (Z.I m).δ
  δ_tendsto : Tendsto (fun m => (Z.I m).δ) atTop (𝓝 0)
  U'_le : ∀ m, Z.U' ≤ (((Z.I m).M : ℝ) + 1) * (Z.I m).δ
  depth_le : ∀ m, r + (((Z.I m).M : ℝ) + 1) * (Z.I m).δ ≤ p.U
  vs_ge : ∀ m, (Z.Rm m)⁻¹ ≤ Z.vs m
  vs_le : ∀ m, Z.vs m ≤ Z.Rm m
  pi_vs : ∀ m (m' : ℤ), a.pi (Z.I m).k {w | ⌊w / p.N (Z.I m).k ^ (-Z.vs m)⌋ = m'} ≤
    ENNReal.ofReal (p.K (Z.I m).k * p.N (Z.I m).k ^ (-p.S * Z.vs m))
  gaps : ∀ m (j : Fin (Z.I m).M), 3 * (p.K (Z.I m).k * (p.K (Z.I m).k *
    p.N (Z.I m).k ^ (-p.S * Z.vs m))) < (Z.I m).θ * (1 / 4 : ℝ) ^ (j : ℕ) / 2
  contact : ∀ m, ∀ z ∈ (Z.I m).G,
    |Zoom.nCoeff (Z.I m).Z (Z.I m).B (Z.I m).lam (a.b (Z.I m).k z.1) 4 +
      Zoom.nCoeff (Z.I m).Z (Z.I m).B (Z.I m).lam (a.b (Z.I m).k z.1) 0| ≤
      p.N (Z.I m).k ^ (-Z.e₀')
  signal : ∀ m, ∀ z ∈ (Z.I m).G, ∀ t ∈ a.block (Z.I m).k r (Z.I m).Q,
    |MvPolynomial.eval (point (a.b (Z.I m).k z.1) t)
      (Submission.Lib.K4ContactNormalization.baseCalibratedTest (a.P (Z.I m).k) (Z.Gb m))| ≤
      Z.Kz m * width p (Z.I m).k r
  Gb_coeff : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ m in atTop,
    (Submission.Lib.K4ChartLifting.coeffL1 (Z.Gb m) + 1) * (2 + p.K (Z.I m).k) ^ 2 *
      ((2 * p.K (Z.I m).k + Z.M₁ m + 1) * Z.M₁ m * p.K (Z.I m).k) ≤ p.N (Z.I m).k ^ c₀
  Kz_K : ∀ m, p.K (Z.I m).k ≤ Z.Kz m
  Kz_MG : ∀ m, 2 * Z.MG m ≤ Z.Kz m
  Kz_coeff : ∀ m, 2 * p.K (Z.I m).k + Z.M₁ m * (2 * p.K (Z.I m).k + Z.M₁ m +
    2 * Z.M₁ m * p.K (Z.I m).k) ≤ Z.Kz m
  Kz_caps : ∀ m, 108 * p.K (Z.I m).k ^ 2 * Z.M₁ m ≤ Z.Kz m
  Kz_grid : ∀ m, p.K (Z.I m).k ^ 2 *
    p.N (Z.I m).k ^ ((p.kappa + p.d + p.ell) * (Z.I m).δ) ≤ Z.Kz m
  Kz_prune : ∀ m, 2 * 4 ^ (Z.I m).M / (Z.I m).θ ≤ Z.Kz m
  Kz_box : ∀ m, 4 * p.K (Z.I m).k + Z.M₁ m * (4 * p.K (Z.I m).k +
    12 * p.K (Z.I m).k ^ 2 / p.N (Z.I m).k ^ (-Z.vs m) + Z.M₁ m) ≤ Z.Kz m
  Kz_row : ∀ m, p.K (Z.I m).k * Z.M₁ m *
    p.N (Z.I m).k ^ ((1 + p.ell) * (Z.I m).δ) ≤ Z.Kz m
  Kz_sub : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, Z.Kz m ≤ p.N (Z.I m).k ^ ε
  U'_pos : 0 < Z.U'
  e₀'_pos : 0 < Z.e₀'

variable {Z : ZoomSeq p a r}

/-- The zoomed parameters are valid. -/
theorem params_valid (hp : p.Valid) (hZ : Z.Good) : Z.params.Valid := by
  refine ⟨fun m => hp.1 _, hp.2.1.comp hZ.k_tendsto,
    ⟨fun m => (hp.2.2.1.1 _).trans (hZ.Kz_K m), hZ.Kz_sub⟩, hp.2.2.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.2.1, hZ.U'_pos, hZ.e₀'_pos⟩

/-- **Common conditions of the zoomed instance.** -/
theorem common (hp : p.Valid) (hcommon : a.Common p) (hZ : Z.Good) :
    Z.model.Common Z.params := by
  intro m
  set J := Z.I m with hJ
  have hatr := hZ.atlas_r m
  have hats := hZ.atlas_depth m
  have hb := (hcommon J.k).1
  haveI := hcommon.prob J.k
  have hK1 := hp.2.2.1.1 J.k
  have hKz1 : 1 ≤ Z.Kz m := hK1.trans (hZ.Kz_K m)
  have hkeep := J.measurable_keep hats (hZ.G_meas m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact J.continuous_nCoeff.measurable.comp hb
  · exact J.condPrior_prob hp hatr
  · exact (hcommon J.k).2.2.1
  · refine (J.zoom_dom hcommon hatr hats (hZ.G_meas m) (hZ.G_sub m)).trans ?_
    rw [Measure.le_iff']
    intro s
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hZ.Kz_K m)) le_rfl
  · exact zoomLaw_mono_measure (hcommon.rho_le J.k) _ _ _ _
  · exact J.zoom_support hats (hZ.G_meas m) (hZ.G_sub m) _
  · refine le_trans ?_ (J.zoom_rho_mass hp hcommon hatr hats (hZ.G_meas m) (hZ.MG_pos m)
      (hZ.mass m) (hZ.θ_pos m).le (hZ.θ_le m))
    apply ENNReal.ofReal_le_ofReal
    have := hZ.MG_pos m
    rw [one_div]
    exact inv_anti₀ (by positivity) (hZ.Kz_MG m)
  · show (Z.I m).Pn.totalDegree ≤ 2
    rw [hZ.Pn_eq m]
    exact (Zoom.nPush_degree _).trans
      (Submission.Lib.K4ContactNormalization.baseCalibratedTest_degree
        (hcommon J.k).2.2.2.2.2.2.2.1 (hZ.Gb_deg m))
  · filter_upwards [J.zoom_coeff_bound hp hcommon hatr (hZ.B_le m) (hZ.lam_inv_le m)] with l hl
    exact hl.trans (hZ.Kz_coeff m)
  · have hPn : Z.model.P m = Zoom.nPush J.Z J.B J.lam
        (Submission.Lib.K4ContactNormalization.baseCalibratedTest (a.P J.k) (Z.Gb m)) :=
      hZ.Pn_eq m
    have h := J.zoom_corr_common hp hcommon hats (hZ.G_meas m) hZ.r_pos.le (hZ.lam_ne m)
      (Z.Gb m) (hZ.Kz_K m) (hZ.signal m)
    simp only [PreparedModel.x, hPn]
    exact h

/-- **Caps of the zoomed instance.** -/
theorem caps (hp : p.Valid) (ha : a.Valid p) (hZ : Z.Good) : Z.model.Caps Z.params := by
  have hcommon := ha.1
  intro R' hR'
  obtain ⟨c₀, hc₀, hc₀ev⟩ := hZ.Gb_coeff
  have hr := hZ.r_pos
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hd : 0 ≤ p.d := hp.2.2.2.1
  have hκℓr : 0 ≤ (p.kappa + p.ell + 1) * r := by positivity
  set R := R' + (p.kappa + p.ell + 1) * r + c₀ + 1 with hRdef
  have hRR' : R' ≤ R := by linarith
  have hR : 1 < R := lt_of_lt_of_le hR' hRR'
  filter_upwards [hZ.k_tendsto.eventually (ha.2.1 R hR), hc₀ev] with m hcm hc0m
  intro r' s' v hr'1 hr'2 hs'1 hs'2 hv1 hv2
  set J := Z.I m with hJ
  have hN0 : 0 < p.N J.k := by linarith [hp.1 J.k]
  have hN1 : 1 ≤ p.N J.k := by linarith [hp.1 J.k]
  have hK1 := hp.2.2.1.1 J.k
  have hK0 : 0 < p.K J.k := by linarith
  have hM₁ := hZ.M₁_ge m
  have hatr := hZ.atlas_r m
  have hats := hZ.atlas_depth m
  have := (hcommon J.k).2.2.1
  have hR'pos : 0 < R' := by linarith
  set r'' := R' + (p.kappa + p.ell + 1) * r + c₀ with hr''
  have hRinv : R⁻¹ ≤ R'⁻¹ := inv_anti₀ hR'pos hRR'
  have hR'inv : R'⁻¹ ≤ R' := by
    rw [inv_le_iff_one_le_mul₀ hR'pos]; nlinarith
  have hrr : r ≤ (p.kappa + p.ell + 1) * r := by nlinarith
  obtain ⟨hpi, hcell, hjoint⟩ := hcm r'' (r + s') v
    (by linarith) (by linarith) (by linarith) (by linarith)
    (hRinv.trans hv1) (hv2.trans hRR')
  -- resolution of the zoomed chart and variation of the base correction on the fine mesh
  set Γ := (Submission.Lib.K4ChartLifting.coeffL1 (Z.Gb m) + 1) * (2 + p.K J.k) ^ 2 with hΓ
  have hG0 := Submission.Lib.K4ChartLifting.coeffL1_nonneg (Z.Gb m)
  have hΓ1 : 1 ≤ Γ := by
    have h2 : 1 ≤ (2 + p.K J.k) ^ 2 := one_le_pow₀ (by linarith)
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ Γ := mul_le_mul (by linarith) h2 zero_le_one (by linarith)
  have hKM1 : 1 ≤ (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.K J.k := by
    have h1 : 1 ≤ (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m := by nlinarith
    nlinarith
  have hq := atlas_q_lower hp hatr
  have hgn : narrow p J.k r = p.N J.k ^ (-p.ell * r) := rfl
  have hNr : p.N J.k ^ (-r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hbase : (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.N J.k ^ (-r'') * Γ ≤
      a.q J.k r * narrow p J.k r * p.N J.k ^ (-R') := by
    have e1 : (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.N J.k ^ (-r'') * Γ =
        (Γ * ((2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.K J.k)) * p.N J.k ^ (-r'') /
          p.K J.k := by
      field_simp
    have e2 : p.N J.k ^ c₀ * p.N J.k ^ (-r'') / p.K J.k =
        (p.N J.k ^ (-(p.kappa * r)) / p.K J.k) * p.N J.k ^ (-p.ell * r) * p.N J.k ^ (-R') *
          p.N J.k ^ (-r) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.rpow_add hN0,
        ← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 2
      simp only [hr'']
      ring
    rw [e1, hgn]
    have hpos : 0 ≤ (p.N J.k ^ (-(p.kappa * r)) / p.K J.k) * p.N J.k ^ (-p.ell * r) *
        p.N J.k ^ (-R') := by positivity
    calc (Γ * ((2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.K J.k)) * p.N J.k ^ (-r'') / p.K J.k
        ≤ p.N J.k ^ c₀ * p.N J.k ^ (-r'') / p.K J.k := by
          gcongr
      _ = (p.N J.k ^ (-(p.kappa * r)) / p.K J.k) * p.N J.k ^ (-p.ell * r) * p.N J.k ^ (-R') *
            p.N J.k ^ (-r) := e2
      _ ≤ (p.N J.k ^ (-(p.kappa * r)) / p.K J.k) * p.N J.k ^ (-p.ell * r) * p.N J.k ^ (-R') *
            1 := mul_le_mul_of_nonneg_left hNr hpos
      _ ≤ a.q J.k r * p.N J.k ^ (-p.ell * r) * p.N J.k ^ (-R') := by rw [mul_one]; gcongr
  have hgpos := narrow_pos p hp J.k r
  have hqpos := q_pos a J.k r
  have hNR' : ∀ x, x ≤ R' → p.N J.k ^ (-R') ≤ p.N J.k ^ (-x) := fun x hx =>
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hres : (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.N J.k ^ (-r'') ≤
      a.q J.k r * narrow p J.k r * p.N J.k ^ (-r') := by
    have h0 : 0 ≤ (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.N J.k ^ (-r'') := by positivity
    calc (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.N J.k ^ (-r'')
        ≤ (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.N J.k ^ (-r'') * Γ :=
          le_mul_of_one_le_right h0 hΓ1
      _ ≤ a.q J.k r * narrow p J.k r * p.N J.k ^ (-R') := hbase
      _ ≤ a.q J.k r * narrow p J.k r * p.N J.k ^ (-r') := by gcongr
  have hvar : Submission.Lib.K4ChartLifting.coeffL1 (Z.Gb m) * (2 + p.K J.k) ^ 2 *
      p.N J.k ^ (-r'') ≤ p.N J.k ^ (-(r + s')) := by
    have hΓc : Submission.Lib.K4ChartLifting.coeffL1 (Z.Gb m) * (2 + p.K J.k) ^ 2 ≤
        p.N J.k ^ c₀ := by
      have h1 : Submission.Lib.K4ChartLifting.coeffL1 (Z.Gb m) * (2 + p.K J.k) ^ 2 ≤ Γ := by
        have : 0 ≤ (2 + p.K J.k) ^ 2 := by positivity
        rw [hΓ]; nlinarith
      have h2 : Γ ≤ Γ * ((2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.K J.k) :=
        le_mul_of_one_le_right (by linarith) hKM1
      linarith
    calc Submission.Lib.K4ChartLifting.coeffL1 (Z.Gb m) * (2 + p.K J.k) ^ 2 * p.N J.k ^ (-r'')
        ≤ p.N J.k ^ c₀ * p.N J.k ^ (-r'') := by gcongr
      _ = p.N J.k ^ (c₀ + -r'') := (Real.rpow_add hN0 _ _).symm
      _ ≤ p.N J.k ^ (-(r + s')) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hδ1 : p.N J.k ^ (-r'') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have e : p.N J.k ^ (-(p.d * (r + s'))) * p.N J.k ^ (p.d * r) * p.N J.k ^ (-3 * r') =
      p.N J.k ^ (-3 * r' - p.d * s') := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
  have hfin : 27 * p.K J.k * Z.M₁ m * (4 * (p.K J.k * p.N J.k ^ (-(p.d * (r + s'))))) *
      p.N J.k ^ (p.d * r) * p.N J.k ^ (-3 * r') ≤ Z.Kz m * p.N J.k ^ (-3 * r' - p.d * s') := by
    calc 27 * p.K J.k * Z.M₁ m * (4 * (p.K J.k * p.N J.k ^ (-(p.d * (r + s'))))) *
          p.N J.k ^ (p.d * r) * p.N J.k ^ (-3 * r')
        = 108 * p.K J.k ^ 2 * Z.M₁ m * (p.N J.k ^ (-(p.d * (r + s'))) * p.N J.k ^ (p.d * r) *
            p.N J.k ^ (-3 * r')) := by ring
      _ = 108 * p.K J.k ^ 2 * Z.M₁ m * p.N J.k ^ (-3 * r' - p.d * s') := by rw [e]
      _ ≤ Z.Kz m * p.N J.k ^ (-3 * r' - p.d * s') :=
          mul_le_mul_of_nonneg_right (hZ.Kz_caps m) (by positivity)
  have hfin' : 27 * p.K J.k ^ 2 * Z.M₁ m * p.N J.k ^ (-3 * r' - p.d * s') ≤
      Z.Kz m * p.N J.k ^ (-3 * r' - p.d * s') := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have := hZ.Kz_caps m
    have : 0 ≤ p.K J.k ^ 2 * Z.M₁ m := by positivity
    linarith
  have hPn : Z.model.P m = Zoom.nPush J.Z J.B J.lam
      (Submission.Lib.K4ContactNormalization.baseCalibratedTest (a.P J.k) (Z.Gb m)) :=
    hZ.Pn_eq m
  have horig0 : ∀ (z : Fin 3 → ℤ) (j : ℤ), a.mu J.k {w | a.cell (p.N J.k) r'' J.k w = z ∧
      ⌊(a.x J.k w.1 w.2) 3 / p.N J.k ^ (-(r + s'))⌋ = j} ≤
        ENNReal.ofReal (p.K J.k * p.N J.k ^ (-3 * r'' - p.d * (r + s'))) := by
    intro z j
    have h0 := hcell false z j
    simpa only [Bool.false_eq_true, ↓reduceIte] using h0
  have horig1 : ∀ (z : Fin 3 → ℤ) (j : ℤ), a.mu J.k {w | a.cell (p.N J.k) r'' J.k w = z ∧
      ⌊MvPolynomial.eval (a.x J.k w.1 w.2) (a.P J.k) / p.N J.k ^ (-(r + s'))⌋ = j} ≤
        ENNReal.ofReal (p.K J.k * p.N J.k ^ (-3 * r'' - p.d * (r + s'))) := by
    intro z j
    have h0 := hcell true z j
    simpa only [↓reduceIte] using h0
  have horigj : ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ), a.mu J.k {w | a.cell (p.N J.k) r'' J.k w = z ∧
      ⌊(a.x J.k w.1 w.2) 3 / p.N J.k ^ (-(r + s'))⌋ = j ∧
        ⌊a.b J.k w.1 3 / p.N J.k ^ (-v)⌋ = v₀} ≤
        ENNReal.ofReal (p.K J.k * p.N J.k ^ (-3 * r'' - p.d * (r + s'))) *
          a.pi J.k {w | ⌊w / p.N J.k ^ (-v)⌋ = v₀} := by
    intro z j v₀
    have h0 := hjoint false z j v₀
    simpa only [Bool.false_eq_true, ↓reduceIte] using h0
  have horigj1 : ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ), a.mu J.k {w | a.cell (p.N J.k) r'' J.k w = z ∧
      ⌊MvPolynomial.eval (a.x J.k w.1 w.2) (a.P J.k) / p.N J.k ^ (-(r + s'))⌋ = j ∧
        ⌊a.b J.k w.1 3 / p.N J.k ^ (-v)⌋ = v₀} ≤
        ENNReal.ofReal (p.K J.k * p.N J.k ^ (-3 * r'' - p.d * (r + s'))) *
          a.pi J.k {w | ⌊w / p.N J.k ^ (-v)⌋ = v₀} := by
    intro z j v₀
    have h0 := hjoint true z j v₀
    simpa only [↓reduceIte] using h0
  have hsplit : ∀ x : ℝ, p.K J.k * p.N J.k ^ (-3 * x - p.d * (r + s')) =
      p.K J.k * p.N J.k ^ (-(p.d * (r + s'))) * p.N J.k ^ (-3 * x) := by
    intro x
    rw [mul_assoc, ← Real.rpow_add hN0]; ring_nf
  refine ⟨?_, ?_, ?_⟩
  · intro j
    refine (hpi j).trans (ENNReal.ofReal_le_ofReal ?_)
    show p.K J.k * p.N J.k ^ (-p.S * v) ≤ Z.Kz m * p.N J.k ^ (-p.S * v)
    exact mul_le_mul_of_nonneg_right (hZ.Kz_K m) (by positivity)
  · intro h z j
    cases h
    · have h1 := J.zoom_hidden_cap hp hcommon hatr hats (hZ.G_meas m) hr.le (hZ.lam_ne m) hM₁
        (hZ.lam_inv_le m) (hZ.lam_le m) (hZ.B_le m) hres horig0 z j
      simp only [cell_eq_baseMesh, Bool.false_eq_true, ↓reduceIte]
      exact h1.trans (ENNReal.ofReal_le_ofReal hfin')
    · have h1 := J.zoom_corr_cap hp hcommon hatr hats (hZ.G_meas m) hr.le (hZ.lam_ne m) hM₁
        (hZ.lam_inv_le m) (hZ.lam_le m) (hZ.B_le m) (Z.Gb m) (hZ.Gb_deg m)
        (C₀ := p.K J.k * p.N J.k ^ (-(p.d * (r + s')))) (by positivity) hres hvar hδ1
        (fun _ => True) (MeasurableSet.const True)
        (fun z j => by
          simp only [and_true]
          exact (horig1 z j).trans_eq (by rw [hsplit])) z j
      simp only [and_true] at h1
      simp only [cell_eq_baseMesh, ↓reduceIte, hPn]
      exact h1.trans (ENNReal.ofReal_le_ofReal hfin)
  · intro h z j v₀
    set πv := (a.pi J.k {w | ⌊w / p.N J.k ^ (-v)⌋ = v₀}).toReal with hπv
    have hπ0 : 0 ≤ πv := ENNReal.toReal_nonneg
    have hπe : a.pi J.k {w | ⌊w / p.N J.k ^ (-v)⌋ = v₀} = ENNReal.ofReal πv := by
      rw [hπv, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    cases h
    · have h1 := J.zoom_joint_cap hp hcommon hatr hats (hZ.G_meas m) hr.le (hZ.lam_ne m) hM₁
        (hZ.lam_inv_le m) (hZ.lam_le m) (hZ.B_le m) hres horigj z j v₀
      simp only [cell_eq_baseMesh, Bool.false_eq_true, ↓reduceIte]
      refine h1.trans ?_
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hfin') le_rfl
    · have hb := (hcommon J.k).1
      have hE : MeasurableSet {l : α | ⌊a.b J.k l 3 / p.N J.k ^ (-v)⌋ = v₀} :=
        (measurableSet_singleton v₀).preimage
          (Int.measurable_floor.comp (((measurable_pi_apply 3).comp hb).div_const _))
      have h1 := J.zoom_corr_cap hp hcommon hatr hats (hZ.G_meas m) hr.le (hZ.lam_ne m) hM₁
        (hZ.lam_inv_le m) (hZ.lam_le m) (hZ.B_le m) (Z.Gb m) (hZ.Gb_deg m)
        (C₀ := p.K J.k * p.N J.k ^ (-(p.d * (r + s'))) * πv) (by positivity) hres hvar hδ1
        (fun l => ⌊a.b J.k l 3 / p.N J.k ^ (-v)⌋ = v₀) hE
        (fun z j => (horigj1 z j v₀).trans_eq (by
          rw [hπe, ← ENNReal.ofReal_mul (by positivity), hsplit]
          congr 1
          ring)) z j
      simp only [cell_eq_baseMesh, ↓reduceIte, hPn]
      have hset : {w : α × ℝ | baseMesh (p.N J.k ^ (-r'))
            (Zoom.baseOf (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) w.2) = z ∧
          ⌊MvPolynomial.eval (point (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) w.2)
            (Zoom.nPush J.Z J.B J.lam (Submission.Lib.K4ContactNormalization.baseCalibratedTest
              (a.P J.k) (Z.Gb m))) / p.N J.k ^ (-s')⌋ = j ∧
          ⌊Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1) 3 / p.N J.k ^ (-v)⌋ = v₀} =
          {w : α × ℝ | baseMesh (p.N J.k ^ (-r'))
            (Zoom.baseOf (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) w.2) = z ∧
          ⌊MvPolynomial.eval (point (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) w.2)
            (Zoom.nPush J.Z J.B J.lam (Submission.Lib.K4ContactNormalization.baseCalibratedTest
              (a.P J.k) (Z.Gb m))) / p.N J.k ^ (-s')⌋ = j ∧
          ⌊a.b J.k w.1 3 / p.N J.k ^ (-v)⌋ = v₀} := by
        ext w; simp only [mem_ofPred_eq, Zoom.nCoeff_three]
      show zoomLaw (a.mu J.k) J.keep J.Z.t₀ J.Z.q J.W {w : α × ℝ | baseMesh (p.N J.k ^ (-r'))
            (Zoom.baseOf (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) w.2) = z ∧
          ⌊MvPolynomial.eval (point (Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1)) w.2)
            (Zoom.nPush J.Z J.B J.lam (Submission.Lib.K4ContactNormalization.baseCalibratedTest
              (a.P J.k) (Z.Gb m))) / p.N J.k ^ (-s')⌋ = j ∧
          ⌊Zoom.nCoeff J.Z J.B J.lam (a.b J.k w.1) 3 / p.N J.k ^ (-v)⌋ = v₀} ≤
        ENNReal.ofReal (Z.Kz m * p.N J.k ^ (-3 * r' - p.d * s')) *
          a.pi J.k {w | ⌊w / p.N J.k ^ (-v)⌋ = v₀}
      rw [hset]
      refine h1.trans ?_
      have hKz0 : 0 ≤ Z.Kz m := zero_le_one.trans (hK1.trans (hZ.Kz_K m))
      rw [hπe, ← ENNReal.ofReal_mul (mul_nonneg hKz0 (by positivity))]
      apply ENNReal.ofReal_le_ofReal
      calc 27 * p.K J.k * Z.M₁ m * (4 * (p.K J.k * p.N J.k ^ (-(p.d * (r + s'))) * πv)) *
            p.N J.k ^ (p.d * r) * p.N J.k ^ (-3 * r')
          = (27 * p.K J.k * Z.M₁ m * (4 * (p.K J.k * p.N J.k ^ (-(p.d * (r + s'))))) *
            p.N J.k ^ (p.d * r) * p.N J.k ^ (-3 * r')) * πv := by ring
        _ ≤ (Z.Kz m * p.N J.k ^ (-3 * r' - p.d * s')) * πv :=
            mul_le_mul_of_nonneg_right hfin hπ0

end ZoomSeq


/-- A model with nonzero incidence mass has labels at every atlas depth. -/
theorem n_pos_of_atlas {p : Parameters} {a : PreparedModel α} {R : ℝ} {k : ℕ} {s : ℝ}
    (h : a.AtlasAt p R k s) (hμ : a.mu k univ ≠ 0) : 0 < a.n k s := by
  by_contra h0
  have hn : a.n k s = 0 := by omega
  have hF : ∀ᵐ z ∂a.mu k, False := by
    filter_upwards [h.cover] with z hz
    obtain ⟨i, _⟩ := hz
    have hi := i.2
    omega
  rw [ae_iff] at hF
  apply hμ
  simpa using hF

/-- Every incidence law of a common model is nonzero. -/
theorem mu_univ_ne {p : Parameters} (hp : p.Valid) {a : PreparedModel α} (hcommon : a.Common p)
    (k : ℕ) : a.mu k univ ≠ 0 := by
  have h1 := (hcommon k).2.2.2.2.2.2.1
  have h2 : a.rho k univ ≤ a.mu k univ := hcommon.rho_le k univ
  have hK := hp.2.2.1.1 k
  have hpos : 0 < ENNReal.ofReal (p.K k)⁻¹ :=
    ENNReal.ofReal_pos.mpr (inv_pos.mpr (by linarith))
  exact (lt_of_lt_of_le hpos (h1.trans h2)).ne'

/-- Deeper nested atlases have at least as many dyadic block levels. -/
theorem T_le_of_nest {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {r s : ℝ} (hats : a.AtlasAt p R k s)
    (hnestr : ∀ i : Fin (a.n k s), ∃ h : Fin (a.n k r),
      a.A k s i ⊆ a.A k r h ∧ a.block k s i ⊆ a.block k r h) :
    a.T k r ≤ a.T k s := by
  have hn := n_pos_of_atlas hats (mu_univ_ne hp hcommon k)
  obtain ⟨h, -, hI⟩ := hnestr ⟨0, hn⟩
  have hq := q_le_of_block_subset hI
  unfold PreparedModel.q at hq
  have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hq
  omega

namespace ZoomSeq

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} {Z : ZoomSeq p a r}

/-- Eventual nesting of the original atlas along the grid depths. -/
theorem nest_eventually (ha : a.Valid p) (hZ : Z.Good) :
    ∀ᶠ m in atTop,
      (∀ j j' : Fin (Z.I m).M, j < j' → ∀ i : Fin (a.n (Z.I m).k ((Z.I m).depth j')),
        ∃ h : Fin (a.n (Z.I m).k ((Z.I m).depth j)),
          a.A (Z.I m).k ((Z.I m).depth j') i ⊆ a.A (Z.I m).k ((Z.I m).depth j) h ∧
            a.block (Z.I m).k ((Z.I m).depth j') i ⊆ a.block (Z.I m).k ((Z.I m).depth j) h) ∧
      (∀ j : Fin (Z.I m).M, ∀ i : Fin (a.n (Z.I m).k ((Z.I m).depth j)),
        ∃ h : Fin (a.n (Z.I m).k r), a.A (Z.I m).k ((Z.I m).depth j) i ⊆ a.A (Z.I m).k r h ∧
          a.block (Z.I m).k ((Z.I m).depth j) i ⊆ a.block (Z.I m).k r h) := by
  have hr := hZ.r_pos
  set R₁ := r⁻¹ + 1 with hR₁def
  have hri := inv_pos.mpr hr
  have hR₁ : 1 < R₁ := by linarith
  have hR₁r : R₁⁻¹ ≤ r := by
    rw [inv_le_comm₀ (by linarith) hr]; linarith
  filter_upwards [hZ.k_tendsto.eventually (ha.2.2.2 R₁ hR₁)] with m hm
  set J := Z.I m
  have hδ := hZ.δ_pos m
  have hdep : ∀ j : Fin J.M, J.depth j ≤ p.U := by
    intro j
    have hj : ((j : ℕ) : ℝ) + 1 ≤ (J.M : ℝ) := by
      have := j.2
      exact_mod_cast this
    have := hZ.depth_le m
    simp only [ZoomInput.depth]
    nlinarith
  have hdep_gt : ∀ j : Fin J.M, r < J.depth j := by
    intro j
    simp only [ZoomInput.depth]
    have : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
    nlinarith
  have hdep_lt : ∀ j j' : Fin J.M, j < j' → J.depth j < J.depth j' := by
    intro j j' hjj'
    simp only [ZoomInput.depth]
    have : ((j : ℕ) : ℝ) < ((j' : ℕ) : ℝ) := by exact_mod_cast hjj'
    nlinarith
  exact ⟨fun j j' hjj' i => hm _ _ (hR₁r.trans (hdep_gt j).le) (hdep_lt j j' hjj') (hdep j') i,
    fun j i => hm _ _ hR₁r (hdep_gt j) (hdep j) i⟩

/-- **Atlases of the zoomed instance.** -/
theorem atlases (hp : p.Valid) (ha : a.Valid p) (hZ : Z.Good) : Z.model.Atlases Z.params := by
  intro R' hR'
  have hR'pos : 0 < R' := by linarith
  filter_upwards [nest_eventually ha hZ, hZ.R_tendsto.eventually_ge_atTop R',
    hZ.δ_tendsto.eventually (gt_mem_nhds (inv_pos.mpr hR'pos))] with m hnm hRm hδm
  intro σ hσ1 hσ2
  obtain ⟨hnest, hnestr⟩ := hnm
  have hTle : ∀ j, a.T (Z.I m).k r ≤ a.T (Z.I m).k ((Z.I m).depth j) := fun j =>
    T_le_of_nest hp ha.1 (hZ.atlas_depth m j) (hnestr j)
  exact zoom_atlasAt hp ha.1 Z.I Z.hM Z.Kz Z.U' Z.e₀' m (R := Z.Rm m) (R' := R')
    (M₁ := Z.M₁ m) (vs := Z.vs m)
    (hZ.atlas_r m) (hZ.atlas_depth m) hnest hnestr (hZ.G_meas m) (hZ.G_sub m) (hZ.θ_pos m)
    (hZ.lam_ne m) (hZ.lam_inv_le m) (hZ.B_le m) (hZ.M₁_ge m) hTle (hZ.δ_pos m)
    (hδm.le.trans hσ1) (hσ2.trans (hZ.U'_le m)) (hZ.vs_ge m) (hZ.vs_le m) (hZ.pi_vs m)
    (hZ.gaps m) (inv_anti₀ hR'pos hRm) hRm (hZ.Kz_grid m) (hZ.Kz_prune m) (hZ.Kz_box m)
    (hZ.Kz_row m)

/-- **Nesting of the zoomed instance.** -/
theorem nested (hp : p.Valid) (ha : a.Valid p) (hZ : Z.Good) : Z.model.Nested Z.params := by
  intro R' hR'
  filter_upwards [nest_eventually ha hZ] with m hnm
  intro s t hs hst ht i
  exact zoom_nested_at hp Z.I Z.hM m (hZ.atlas_r m) (hZ.atlas_depth m) hnm.1 hnm.2
    (hZ.θ_pos m) (hZ.δ_pos m) hst.le i

/-- **The zoomed instance is valid.** -/
theorem valid (hp : p.Valid) (ha : a.Valid p) (hZ : Z.Good) : Z.model.Valid Z.params :=
  ⟨common hp ha.1 hZ, caps hp ha hZ, atlases hp ha hZ, nested hp ha hZ⟩

/-- **The zoomed instance is in contact form.** -/
theorem contact (hcommon : a.Common p) (hZ : Z.Good) : Z.model.Contact Z.params := by
  intro m
  exact (Z.I m).contact_zoom hcommon (hZ.atlas_depth m) (hZ.G_meas m) (hZ.contact m)

/-- **The contact principle applies to the zoomed instance.** -/
theorem result (hp : p.Valid) (ha : a.Valid p) (hZ : Z.Good)
    (hCMP : ContactModelPrinciple) : Z.model.Result Z.params :=
  hCMP Z.params (params_valid hp hZ) α Z.model (contact ha.1 hZ) (valid hp ha hZ)

end ZoomSeq

end

end Submission.Obl.k4_row_parent_contact_candidates
