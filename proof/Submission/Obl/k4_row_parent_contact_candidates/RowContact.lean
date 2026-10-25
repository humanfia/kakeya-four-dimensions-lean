/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/RowContact.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactParents
import Submission.Obl.k4_row_parent_contact_candidates.RowStrip

/-!
# Row parents: the contact branch

Prop 8.5 of the paper splits frequently occurring row parents (`RowParent`: a
parent with a row normalization and a dense row equation) by the size of the
skew: power-small skew gives strip candidates (`result_of_rowParents_gap`,
`RowStrip.lean`), otherwise the skew is subpolynomially bounded below and the
normalized contact equation holds. `result_of_rowParents_contact` closes the
second branch once a base correction of the native polynomial is supplied, and
`result_of_rowParents_sheet` once a parent affine hidden sheet (Lemma 8.6 at the
parent, fitting the hidden coordinate to `M a_r`) with a calibrated native
restriction `P(base, L(base))` is supplied (`signal_of_sheet`, lib
`affine_correction_error`; incidences are first restricted to native lines).
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point baseCalibratedTest affineBase
  affineSheetRestriction affine_correction_error)
open Submission.Lib.K4ChartLifting (coeffL1)

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- **Row parents with non-small skew and a base correction give the frozen
result.** Frequently occurring row parents at depth `r < U` with row error
`M N^(-e₀)`, skew `|λ⁻¹| ≤ M` and a base correction `Gb` of the native polynomial
(`|P - Gb(base)| ≤ M a_r` on the retained lines, `‖Gb‖ ≤ N^c₁`) are contact
parents with contact exponent `e₀/2`. -/
theorem result_of_rowParents_contact {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (ha : a.Valid p) (hCMP : ContactModelPrinciple) {r e₀ c₁ : ℝ} (hr : 0 < r)
    (hrU : r < p.U) (he₀ : 0 < e₀) (hc₁ : 0 ≤ c₁) (M : ℕ → ℝ) (hM1 : ∀ k, 1 ≤ M k)
    (hM : Subpower p.N M)
    (hfreq : ∃ᶠ k in atTop, ∃ RP : RowParent p a k r (M k * p.N k ^ (-e₀)) (M k),
      ∃ Gb : MvPolynomial (Fin 3) ℝ, RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M k ∧ Gb.totalDegree ≤ 2 ∧
        coeffL1 Gb ≤ p.N k ^ c₁ ∧
        ∀ z ∈ RP.G, ∀ t ∈ a.block k r RP.Q,
          |eval (point (a.b k z.1) t) (baseCalibratedTest (a.P k) Gb)| ≤ M k * width p k r) :
    a.Result p := by
  refine result_of_contact_parents hp ha hCMP hr hrU (half_pos he₀) hc₁ M hM1 hM ?_
  have hev : ∀ᶠ k in atTop, M k * M k ≤ p.N k ^ (e₀ / 2) := by
    filter_upwards [hM (e₀ / 4) (by positivity)] with k hk
    have hN0 : 0 < p.N k := hp.N_pos k
    calc M k * M k ≤ p.N k ^ (e₀ / 4) * p.N k ^ (e₀ / 4) :=
          mul_le_mul hk hk (le_trans zero_le_one (hM1 k)) (by positivity)
      _ = p.N k ^ (e₀ / 2) := by rw [← Real.rpow_add hN0]; ring_nf
  refine (hfreq.and_eventually hev).mono ?_
  rintro k ⟨⟨RP, Gb, hlam, hlamM, hGdeg, hGle, hsig⟩, hMM⟩
  have hN0 : 0 < p.N k := hp.N_pos k
  refine ⟨⟨RP.Q, RP.B, RP.lam, RP.G, Gb, RP.measurable_G, RP.G_sub, RP.mass, hlam, hlamM,
    RP.lam_le, RP.B_le, ?_, hGdeg, hsig, hGle⟩⟩
  intro z hz
  rw [Zoom.nCoeff_contact hlam, abs_div, div_eq_mul_inv, ← abs_inv]
  have hrow := RP.row z hz
  calc |(parentZoom p a k r RP.Q).coeff (a.b k z.1) 4 - RP.B 0 - RP.B 1 * a.b k z.1 3 +
        RP.lam * (parentZoom p a k r RP.Q).coeff (a.b k z.1) 0| * |RP.lam⁻¹|
      ≤ (M k * p.N k ^ (-e₀)) * M k :=
        mul_le_mul hrow hlamM (abs_nonneg _) (mul_nonneg (le_trans zero_le_one (hM1 k)) (by positivity))
    _ = (M k * M k) * p.N k ^ (-e₀) := by ring
    _ ≤ p.N k ^ (e₀ / 2) * p.N k ^ (-e₀) := mul_le_mul_of_nonneg_right hMM (by positivity)
    _ = p.N k ^ (-(e₀ / 2)) := by rw [← Real.rpow_add hN0]; ring_nf


/-- **Signal from a hidden affine sheet.** Along a line where the native polynomial has
bounded hidden derivatives, an affine sheet fitting the hidden coordinate to `Cs a`
makes the base-corrected native polynomial `O((Cs K + Cs² K) a)`. -/
theorem signal_of_sheet (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (L : Fin 4 → ℝ)
    (b : Fin 6 → ℝ) (I : Set ℝ) {Cs K w : ℝ} (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1)
    (hline : ∀ t ∈ I, |eval (point b t) (pderiv 3 P)| ≤ K ∧
      |eval (point b t) (pderiv 3 (pderiv 3 P))| ≤ K)
    (hfit : ∀ t ∈ I, |eval (point b t) (affineBase L) - point b t 3| ≤ Cs * w) :
    ∀ t ∈ I, |eval (point b t) (baseCalibratedTest P (affineSheetRestriction L P))| ≤
      (Cs * K + Cs ^ 2 * K) * w := by
  intro t ht
  have h := affine_correction_error L P hP (point b t) (by positivity) (hfit t ht)
    (hline t ht).1 (hline t ht).2
  refine h.trans ?_
  have hw2 : w ^ 2 ≤ w := by nlinarith
  have : (Cs * w) ^ 2 / 2 * K ≤ Cs ^ 2 * K * w := by
    have : (Cs * w) ^ 2 = Cs ^ 2 * w ^ 2 := by ring
    rw [this]
    have h1 : Cs ^ 2 * w ^ 2 / 2 * K ≤ Cs ^ 2 * w ^ 2 * K := by
      have : 0 ≤ Cs ^ 2 * w ^ 2 * K := by positivity
      linarith
    calc Cs ^ 2 * w ^ 2 / 2 * K ≤ Cs ^ 2 * w ^ 2 * K := h1
      _ ≤ Cs ^ 2 * w * K := by gcongr
      _ = Cs ^ 2 * K * w := by ring
  nlinarith


/-- Lines along which the native polynomial satisfies the common bounds. -/
def nativeLines (p : Parameters) (a : PreparedModel α) (k : ℕ) : Set α :=
  {l | ∀ t ∈ Icc (0 : ℝ) 1, |eval (point (a.b k l) t) (a.P k)| ≤ p.K k ∧
    |eval (point (a.b k l) t) (pderiv 3 (a.P k))| ≤ p.K k ∧
    |eval (point (a.b k l) t) (pderiv 3 (pderiv 3 (a.P k)))| ≤ p.K k}

theorem measurableSet_nativeLines {p : Parameters} {a : PreparedModel α} (hcommon : a.Common p)
    (k : ℕ) : MeasurableSet (nativeLines p a k) :=
  measurableSet_unit_bound₃ (hcommon k).1 _ _ _ _

/-- Almost every incidence lies on a native line. -/
theorem ae_nativeLines {p : Parameters} {a : PreparedModel α} (hcommon : a.Common p) (k : ℕ) :
    ∀ᵐ z ∂a.mu k, z.1 ∈ nativeLines p a k := by
  filter_upwards [(hcommon k).2.2.2.2.2.2.2.2.2] with z hz
  exact hz.1

/-- **Restriction of a row parent to native lines**: same mass, same row equation. -/
def RowParent.native {p : Parameters} {a : PreparedModel α} (hcommon : a.Common p) {k : ℕ}
    {r E M : ℝ} (RP : RowParent p a k r E M) : RowParent p a k r E M where
  Q := RP.Q
  B := RP.B
  lam := RP.lam
  G := RP.G ∩ (nativeLines p a k ×ˢ univ)
  measurable_G := RP.measurable_G.inter ((measurableSet_nativeLines hcommon k).prod MeasurableSet.univ)
  G_sub := inter_subset_left.trans RP.G_sub
  mass := by
    refine RP.mass.trans (le_of_eq ?_)
    have hset : (nativeLines p a k ×ˢ (univ : Set ℝ))ᶜ = {z : α × ℝ | ¬ z.1 ∈ nativeLines p a k} := by
      ext z; simp
    have hmu : a.mu k (nativeLines p a k ×ˢ (univ : Set ℝ))ᶜ = 0 := by
      rw [hset, ← ae_iff]
      exact ae_nativeLines hcommon k
    have hrho : a.rho k (nativeLines p a k ×ˢ (univ : Set ℝ))ᶜ = 0 :=
      le_antisymm ((hcommon.rho_le k _).trans hmu.le) zero_le
    exact (measure_inter_conull hrho).symm
  B_le := RP.B_le
  lam_le := RP.lam_le
  row := fun z hz => RP.row z hz.1

/-- Row parents are monotone in the row error and the constant. -/
def RowParent.mono {p : Parameters} {a : PreparedModel α} {k : ℕ} {r E M E' M' : ℝ}
    (RP : RowParent p a k r E M) (hE : E ≤ E') (hM0 : 0 < M) (hMM : M ≤ M') :
    RowParent p a k r E' M' where
  Q := RP.Q
  B := RP.B
  lam := RP.lam
  G := RP.G
  measurable_G := RP.measurable_G
  G_sub := RP.G_sub
  mass := by
    refine le_trans ?_ RP.mass
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (q_pos a k r).le hM0 hMM)) le_rfl
  B_le := RP.B_le.trans hMM
  lam_le := RP.lam_le.trans hMM
  row := fun z hz => (RP.row z hz).trans hE

/-- **Row parents with non-small skew and a parent affine hidden sheet give the
frozen result**: the sheet `L` fits the hidden coordinate to `M a_r` along the
retained lines over the parent block, and its native restriction
`P(base, L(base))` is calibrated to a fixed power. -/
theorem result_of_rowParents_sheet {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (ha : a.Valid p) (hCMP : ContactModelPrinciple) {r e₀ c₁ : ℝ} (hr : 0 < r)
    (hrU : r < p.U) (he₀ : 0 < e₀) (hc₁ : 0 ≤ c₁) (M : ℕ → ℝ) (hM1 : ∀ k, 1 ≤ M k)
    (hM : Subpower p.N M)
    (hfreq : ∃ᶠ k in atTop, ∃ RP : RowParent p a k r (M k * p.N k ^ (-e₀)) (M k),
      ∃ L : Fin 4 → ℝ, RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M k ∧
        coeffL1 (affineSheetRestriction L (a.P k)) ≤ p.N k ^ c₁ ∧
        ∀ z ∈ RP.G, ∀ t ∈ a.block k r RP.Q,
          |eval (point (a.b k z.1) t) (affineBase L) - point (a.b k z.1) t 3| ≤
            M k * width p k r) :
    a.Result p := by
  have hcommon := ha.1
  have hN : ∀ k, 0 < p.N k := hp.N_pos
  have hK1 : ∀ k, 1 ≤ p.K k := hp.one_le_K
  set M' : ℕ → ℝ := fun k => 2 * M k ^ 2 * p.K k with hM'
  have hM'1 : ∀ k, 1 ≤ M' k := by
    intro k
    have h1 := hM1 k; have h2 := hK1 k
    have : 1 ≤ M k ^ 2 := one_le_pow₀ h1
    show 1 ≤ 2 * M k ^ 2 * p.K k
    nlinarith
  have hMM' : ∀ k, M k ≤ M' k := by
    intro k
    have h1 := hM1 k; have h2 := hK1 k
    show M k ≤ 2 * M k ^ 2 * p.K k
    nlinarith
  have hM'sub : Subpower p.N M' := by
    have h0 : ∀ k, 0 ≤ M k := fun k => le_trans zero_le_one (hM1 k)
    have hMM : Subpower p.N (fun k => M k * M k) := Subpower.mul hN hM hM h0
    have h2MM : Subpower p.N (fun k => 2 * (M k * M k)) :=
      Subpower.mul hN (Subpower.const hp.2.1 2) hMM (fun _ => by norm_num)
    have h3 : Subpower p.N (fun k => 2 * (M k * M k) * p.K k) :=
      Subpower.mul hN h2MM hp.K_subpower
        (fun k => mul_nonneg (by norm_num) (mul_self_nonneg _))
    exact h3.mono (fun k => by show 2 * M k ^ 2 * p.K k ≤ 2 * (M k * M k) * p.K k; nlinarith)
  refine result_of_rowParents_contact hp ha hCMP hr hrU he₀ hc₁ M' hM'1 hM'sub ?_
  refine hfreq.mono ?_
  rintro k ⟨RP, L, hlam, hlamM, hGle, hfit⟩
  have hM0 : 0 < M k := lt_of_lt_of_le zero_lt_one (hM1 k)
  have hE : M k * p.N k ^ (-e₀) ≤ M' k * p.N k ^ (-e₀) :=
    mul_le_mul_of_nonneg_right (hMM' k) (Real.rpow_nonneg (hN k).le _)
  let RP' := (RP.native hcommon).mono hE hM0 (hMM' k)
  have hPdeg : (a.P k).totalDegree ≤ 2 := (hcommon k).2.2.2.2.2.2.2.1
  refine ⟨RP', affineSheetRestriction L (a.P k), hlam, hlamM.trans (hMM' k),
    (Submission.Lib.K4ContactNormalization.affineSheetRestriction_degree L _).trans hPdeg, hGle, ?_⟩
  intro z hz t ht
  have hzG : z ∈ RP.G := hz.1
  have hzN : z.1 ∈ nativeLines p a k := hz.2.1
  have hw := width_pos p hp k r
  have hw1 : width p k r ≤ 1 := by
    unfold width
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k]) (by linarith)
  have hsig := signal_of_sheet (a.P k) hPdeg L (a.b k z.1) (a.block k r RP.Q)
    (le_trans zero_le_one (hM1 k)) (le_trans zero_le_one (hK1 k)) hw.le hw1
    (fun t ht => ⟨(hzN t (interval_sub_unit _ _ ht)).2.1, (hzN t (interval_sub_unit _ _ ht)).2.2⟩)
    (hfit z hzG) t ht
  refine hsig.trans (mul_le_mul_of_nonneg_right ?_ hw.le)
  show M k * p.K k + M k ^ 2 * p.K k ≤ 2 * M k ^ 2 * p.K k
  have h1 := hM1 k; have h2 := hK1 k
  have hMsq : M k ≤ M k ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_right hMsq (le_trans zero_le_one h2)
  linarith

end

end Submission.Obl.k4_row_parent_contact_candidates
