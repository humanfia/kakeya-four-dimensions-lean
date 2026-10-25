/- Adapted from: here:o222, session x0774, commit 0d01aa57.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ParentRowGeometry.lean. -/
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.ContactRowChart
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedParentGeometry
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMeshPowers

/-! Original row-parent data in the accepted prepared-model coordinates.

The parent zoom and coefficient estimate are adapted from this LOT
obligation, session x0776, `RowParent.lean` and `ContactCommon.lean` on
origin/x0776 (17941c95). The record is kept separate from that session's
nominal model types, so no compatibility aliases are needed by its users.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set MvPolynomial Filter
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh (Zoom)
open Submission.Lib.K4ContactNormalization (point skewCoeff)

noncomputable section

def parentAffineZoom {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) : Zoom where
  t₀ := (a.j k r Q : ℝ) / (2 : ℝ) ^ a.T k r
  q := a.q k r
  z₀ := a.c k r Q 0 + ((a.j k r Q : ℝ) / (2 : ℝ) ^ a.T k r) * a.c k r Q 1
  c₂ := a.c k r Q 2
  c₃ := a.c k r Q 3
  c₄ := a.c k r Q 4
  w := a.q k r * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r
  h₀ := 0
  a := Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r

theorem parentAffineZoom_ok {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) : (parentAffineZoom p a k r Q).Ok := by
  have hN : 0 < p.N k := by linarith [hp.1 k]
  constructor <;> dsimp [parentAffineZoom, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width] <;> positivity

theorem parentAffineZoom_block {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) :
    a.block k r Q = Icc (parentAffineZoom p a k r Q).t₀
      ((parentAffineZoom p a k r Q).t₀ + (parentAffineZoom p a k r Q).q) := by
  unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.block Submission.Obl.k4_general_parent_projected_layers.PreparedModel.interval parentAffineZoom Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q
  congr 1
  rw [zpow_neg, zpow_natCast, add_div, one_div]

/-- The row output with its original current-law floor. -/
structure CoarseRowParent {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (k : ℕ) (r E M : ℝ) where
  Q : Fin (a.n k r)
  B : Fin 2 → ℝ
  lam : ℝ
  G : Set (α × ℝ)
  measurable_G : MeasurableSet G
  G_sub : G ⊆ a.B k r Q ×ˢ a.block k r Q
  mass : ENNReal.ofReal (a.q k r / M) * a.nu k (a.A k r Q) ≤ a.rho k G
  B_le : |B 0| + |B 1| ≤ M
  lam_le : |lam| ≤ M
  row : ∀ z ∈ G,
    |(parentAffineZoom p a k r Q).coeff (a.b k z.1) 4 - B 0 - B 1 * a.b k z.1 3 +
      lam * (parentAffineZoom p a k r Q).coeff (a.b k z.1) 0| ≤ E

namespace CoarseRowParent

variable {α : Type} [MeasurableSpace α]
variable {p : Submission.Obl.k4_general_parent_projected_layers.Parameters} {a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α} {k : ℕ} {r E M : ℝ}

def chart (RP : CoarseRowParent p a k r E M) : ContactRowChart where
  Z := parentAffineZoom p a k r RP.Q
  B := RP.B
  lam := RP.lam

def sample (RP : CoarseRowParent p a k r E M) (μ : Measure (α × ℝ)) :
    Submission.Lib.K4ContactAffine.NativeSample (α × ℝ) :=
  RP.chart.sample μ (a.pi k) (fun z => a.b k z.1) Prod.snd (a.F k r RP.Q)

theorem chart_ok (RP : CoarseRowParent p a k r E M) (hp : p.Valid) : RP.chart.Z.Ok :=
  parentAffineZoom_ok p hp a k r RP.Q

theorem chart_jacobian (RP : CoarseRowParent p a k r E M) (hp : p.Valid) :
    |RP.chart.baseMatrix.det|⁻¹ = |RP.lam| * a.q k r ^ 3 * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := by
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hq : 0 < a.q k r := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  have hg : 0 < Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := Real.rpow_pos_of_pos hN _
  rw [RP.chart.abs_det_inv hq (mul_pos hq hg)]
  dsimp [chart, parentAffineZoom]
  ring

/-- Full parent boxes bound the normalized horizontal coefficients. The
unbounded hidden intercept and hidden velocity are absent from this bound. -/
theorem coeff_bound (RP : CoarseRowParent p a k r E M) (hp : p.Valid)
    {R : ℝ} (hatr : a.AtlasAt p R k r) (hlam : |RP.lam⁻¹| ≤ M)
    {l : α} (hlA : l ∈ a.A k r RP.Q) (hb3 : |a.b k l 3| ≤ p.K k) :
    |RP.chart.coeff (a.b k l) 0| + |RP.chart.coeff (a.b k l) 1| +
      |RP.chart.coeff (a.b k l) 3| + |RP.chart.coeff (a.b k l) 4| ≤
        2 * p.K k + M * (2 * p.K k + M + 2 * M * p.K k) := by
  let Z := parentAffineZoom p a k r RP.Q
  let b := a.b k l
  have hK0 : 0 ≤ p.K k := zero_le_one.trans (hp.2.2.1.1 k)
  have hM : 0 ≤ M := (abs_nonneg _).trans hlam
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hq : 0 < a.q k r := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  have hg : 0 < Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := Real.rpow_pos_of_pos hN _
  have ht₀ : Z.t₀ ∈ a.block k r RP.Q := by
    rw [parentAffineZoom_block p a k r RP.Q]
    exact ⟨le_rfl, le_add_of_nonneg_right hq.le⟩
  have hbox := (hatr.2.2.2.2.1 RP.Q).2.2.2.2.2.1 l hlA Z.t₀ ht₀
  have h0 : |Z.coeff b 0| ≤ p.K k := by
    rw [Zoom.coeff_zero, abs_div, show Z.q = a.q k r from rfl,
      abs_of_pos hq, div_le_iff₀ hq]
    have h := hbox.1
    change |b 0 + Z.t₀ * b 3 - a.c k r RP.Q 0 - Z.t₀ * a.c k r RP.Q 1| ≤ _ at h
    convert h using 1 <;> dsimp [Z, parentAffineZoom] <;> congr 1 <;> ring
  have h1 : |Z.coeff b 1| ≤ p.K k := by
    rw [Zoom.coeff_one, abs_div,
      show Z.w = a.q k r * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r from rfl,
      abs_of_pos (mul_pos hq hg), div_le_iff₀ (mul_pos hq hg)]
    have h := hbox.2.1
    change |(b 1 + Z.t₀ * b 4) - a.c k r RP.Q 2 - Z.t₀ * a.c k r RP.Q 3 -
      a.c k r RP.Q 4 * (b 0 + Z.t₀ * b 3)| ≤ _ at h
    calc
      _ = |(b 1 + Z.t₀ * b 4) - a.c k r RP.Q 2 - Z.t₀ * a.c k r RP.Q 3 -
          a.c k r RP.Q 4 * (b 0 + Z.t₀ * b 3)| := by
        congr 1
        dsimp [Z, parentAffineZoom]
        ring
      _ ≤ p.K k * a.q k r * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := h
      _ = _ := by ring
  have h4 : |Z.coeff b 4| ≤ p.K k := by
    have h := hbox.2.2
    have he : Z.coeff b 4 =
        (b 4 - a.c k r RP.Q 3 - a.c k r RP.Q 4 * b 3) / Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := by
      dsimp [Z, parentAffineZoom, Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff]
      field_simp
    rw [he, abs_div, abs_of_pos hg, div_le_iff₀ hg]
    exact h
  change |skewCoeff RP.B RP.lam (Z.coeff b) 0| +
    |skewCoeff RP.B RP.lam (Z.coeff b) 1| + |skewCoeff RP.B RP.lam (Z.coeff b) 3| +
    |skewCoeff RP.B RP.lam (Z.coeff b) 4| ≤ _
  simp only [skewCoeff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, Zoom.coeff_three]
  have hB := RP.B_le
  have hB0 := abs_nonneg (RP.B 0)
  have hB1 := abs_nonneg (RP.B 1)
  have e1 : |(Z.coeff b 1 - RP.B 1 * Z.coeff b 0) / RP.lam| ≤
      M * (p.K k + M * p.K k) := by
    rw [div_eq_mul_inv, abs_mul, mul_comm]
    apply mul_le_mul hlam _ (abs_nonneg _) hM
    calc
      _ ≤ |Z.coeff b 1| + |RP.B 1 * Z.coeff b 0| := abs_sub _ _
      _ ≤ p.K k + M * p.K k := by
        rw [abs_mul]
        have : |RP.B 1| ≤ M := by linarith
        nlinarith [abs_nonneg (Z.coeff b 0)]
  have e4 : |(Z.coeff b 4 - RP.B 0 - RP.B 1 * b 3) / RP.lam| ≤
      M * (p.K k + M + M * p.K k) := by
    rw [div_eq_mul_inv, abs_mul, mul_comm]
    apply mul_le_mul hlam _ (abs_nonneg _) hM
    calc
      _ ≤ |Z.coeff b 4 - RP.B 0| + |RP.B 1 * b 3| := abs_sub _ _
      _ ≤ (|Z.coeff b 4| + |RP.B 0|) + |RP.B 1 * b 3| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ p.K k + M + M * p.K k := by
        rw [abs_mul]
        have h1' : |RP.B 1| ≤ M := by linarith
        have h0' : |RP.B 0| ≤ M := by linarith
        nlinarith [abs_nonneg (b 3)]
  change |Z.coeff b 0| + |(Z.coeff b 1 - RP.B 1 * Z.coeff b 0) / RP.lam| +
    |b 3| + |(Z.coeff b 4 - RP.B 0 - RP.B 1 * b 3) / RP.lam| ≤ _
  nlinarith

/-- Matrix sums retain the original `q*g` denominator. -/
theorem row_sum_le (RP : CoarseRowParent p a k r E M) (hp : p.Valid)
    {R : ℝ} (hatr : a.AtlasAt p R k r) (hr : 0 ≤ r) (hM : 1 ≤ M)
    (hlam : |RP.lam⁻¹| ≤ M) :
    ∀ e, (∑ j, |RP.chart.baseMatrix e j|) ≤
      (2 * p.K k + M + 1) * M / (a.q k r * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r) := by
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hq : 0 < a.q k r := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  have hg : 0 < Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := Real.rpow_pos_of_pos hN _
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hg1 : Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k])
      (by nlinarith [mul_nonneg hℓ.le hr])
  have hc := (hatr.2.2.2.2.1 RP.Q).2.2.2.1
  exact RP.chart.row_sum_le hq hg hg1 (hp.2.2.1.1 k) hM rfl rfl (hc 3) (hc 4)
    RP.B_le hlam

/-- Every original row incidence supplies the full-time native hypotheses
for the parent's own test, apart from an original null exception. -/
theorem ae_sample_good (RP : CoarseRowParent p a k r E M) (hp : p.Valid)
    (hcommon : a.Common p) {R : ℝ} (hatr : a.AtlasAt p R k r)
    (hlam : RP.lam ≠ 0) (hlamM : |RP.lam⁻¹| ≤ M) {H : ℝ}
    (hKH : p.K k ≤ H)
    (hcoeffH : 2 * p.K k + M * (2 * p.K k + M + 2 * M * p.K k) ≤ H)
    (μ : Measure (α × ℝ)) :
    ∀ᵐ z ∂a.mu k, z ∈ RP.G →
      (RP.sample μ).Good H (E * |RP.lam⁻¹|) z := by
  rcases hcommon k with ⟨_hbmeas, hnu, _hpi, hdom, _hrho, _hsupp, _hmass, _hPdeg, hb, _hP⟩
  letI : IsProbabilityMeasure (a.nu k) := hnu
  have hbprod : ∀ᵐ z : α × ℝ ∂(a.nu k).prod volume,
      |a.b k z.1 0| + |a.b k z.1 1| + |a.b k z.1 3| + |a.b k z.1 4| ≤ p.K k :=
    (Measure.quasiMeasurePreserving_fst (μ := a.nu k) (ν := (volume : Measure ℝ))).ae hb
  have hbmu := (Measure.absolutelyContinuous_of_le_smul hdom).ae_le hbprod
  have hlabel := hatr.2.2.2.2.1 RP.Q
  have hfit := hlabel.2.2.2.2.2.2.1
  have hreg := hlabel.2.2.2.2.2.2.2
  have hK : 0 < p.K k := zero_lt_one.trans_le (hp.2.2.1.1 k)
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k r := Real.rpow_pos_of_pos hN _
  have hq : 0 < a.q k r := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  filter_upwards [hbmu, hreg] with z hz hzreg hzG
  obtain ⟨hzB, hzI⟩ := RP.G_sub hzG
  have hzA := (hatr.2.2.1 RP.Q).2.2 hzB
  have hb3 : |a.b k z.1 3| ≤ p.K k := by
    linarith [abs_nonneg (a.b k z.1 0), abs_nonneg (a.b k z.1 1),
      abs_nonneg (a.b k z.1 4)]
  apply RP.chart.sample_good μ (a.pi k) (fun z => a.b k z.1) Prod.snd (a.F k r RP.Q)
    (RP.chart_ok hp) hlam hq ha hK hKH z
  · exact (parentAffineZoom_block p a k r RP.Q ▸ hzI)
  · exact (RP.coeff_bound hp hatr hlamM hzA hb3).trans hcoeffH
  · intro t ht
    have htI : t ∈ a.block k r RP.Q := by
      rwa [parentAffineZoom_block p a k r RP.Q]
    exact hfit z.1 hzB t htI
  · exact hzreg hzB hzI
  · exact RP.row z hzG

end CoarseRowParent

/-- All subpower row choices satisfy one fixed polynomial matrix bound. -/
theorem eventually_coarse_row_matrix_bound {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) {r : ℝ} (hr : 0 < r)
    (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k)
    (hMsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ (R : ℝ) (hatr : a.AtlasAt p R k r)
      (E : ℝ) (RP : CoarseRowParent p a k r E (M k)),
        |RP.lam⁻¹| ≤ M k → ∀ e, (∑ j, |RP.chart.baseMatrix e j|) ≤ p.N k ^ C := by
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  let G : ℝ := (p.kappa + p.ell) * r + 1
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨G + 3, by positivity, ?_⟩
  filter_upwards [hp.2.2.1.2 1 one_pos, hMsub 1 one_pos,
    a.eventually_q_narrow_lower p hp r (eps := 1) one_pos,
    hp.2.1.eventually (eventually_ge_atTop 4)] with k hkK hkM hkqg hN4
  simp only [Real.rpow_one] at hkK hkM
  intro R hatr E RP hlam e
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hq : 0 < a.q k r := by unfold Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q; positivity
  have hg : 0 < Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := Real.rpow_pos_of_pos hN _
  have hqg : p.N k ^ (-G) ≤ a.q k r * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r := by
    convert hkqg R r hatr le_rfl using 1
    congr 1
    dsimp [G]
    ring
  have hInv : (a.q k r * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r)⁻¹ ≤ p.N k ^ G := by
    simpa only [Real.rpow_neg hN.le, inv_inv] using
      inv_anti₀ (Real.rpow_pos_of_pos hN (-G)) hqg
  have hcoef : (2 * p.K k + M k + 1) * M k ≤ 4 * p.N k ^ 2 := by
    have hfirst : 2 * p.K k + M k + 1 ≤ 4 * p.N k := by linarith [hp.1 k]
    calc
      _ ≤ (4 * p.N k) * p.N k :=
        mul_le_mul hfirst hkM (zero_le_one.trans (hM k)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (2 * p.K k + M k + 1) * M k / (a.q k r * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow p k r) :=
      RP.row_sum_le hp hatr hr.le (hM k) hlam e
    _ ≤ 4 * p.N k ^ 2 * p.N k ^ G := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hcoef hInv (by positivity) (by positivity)
    _ ≤ p.N k * p.N k ^ 2 * p.N k ^ G := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hN4 (sq_nonneg _)) (by positivity)
    _ = p.N k ^ (G + 3) := by
      rw [Real.rpow_add hN G 3, Real.rpow_ofNat]
      ring

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
