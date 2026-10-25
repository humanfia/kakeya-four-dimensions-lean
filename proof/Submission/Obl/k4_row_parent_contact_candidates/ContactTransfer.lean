/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactTransfer.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactPullback

/-!
# Contact transfer

* budget bounds: the lift, push, skew and unskew coefficient budgets and the
  hidden width `a_r⁻¹` are all at most `20 Kz² N^((κ+ℓ+1) r)`;
* `ZoomSeq.result_pullback`: the zoomed `Result` gives the original `Result`
  (the depth range grows to `R'' = 1 + 4D + R' + (5D + c₀) R' + r + r⁻¹ + 2`,
  `D = 1 + (κ+ℓ+1) r`, `c₀ = 5D + c₀' + 2` with `‖Gb‖ ≤ N^c₀'`);
* `ZoomSeq.contact_transfer`: with `ContactModelPrinciple`, a valid model with a
  good zoomed contact sequence has the frozen `Result`.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point skewBudget)
open Submission.Lib.K4ChartLifting (coeffL1)

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem blockStart_unit (T : ℕ) (j : Fin (2 ^ T)) : 0 ≤ blockStart T j ∧ blockStart T j ≤ 1 := by
  unfold blockStart
  have h2 : (0 : ℝ) < 2 ^ T := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_one h2]
  exact_mod_cast j.2.le

theorem q_le_one (a : PreparedModel α) (k : ℕ) (s : ℝ) : a.q k s ≤ 1 := by
  unfold PreparedModel.q
  exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)

theorem skewBudget_le {B : Fin 2 → ℝ} {lam M₁ : ℝ} (hM₁ : 1 ≤ M₁) (hlam : |lam⁻¹| ≤ M₁)
    (hB : |B 0| + |B 1| ≤ M₁) : skewBudget B lam ≤ 3 * M₁ ^ 2 := by
  unfold skewBudget
  have h0 : 0 ≤ 1 + |B 0| + |B 1| := by positivity
  have : |lam⁻¹| * (1 + |B 0| + |B 1|) ≤ M₁ * (1 + M₁) :=
    mul_le_mul hlam (by linarith) h0 (by linarith)
  nlinarith

theorem unskewBudget_le {B : Fin 2 → ℝ} {lam M₁ : ℝ} (hM₁ : 1 ≤ M₁) (hlam : |lam| ≤ M₁)
    (hB : |B 0| + |B 1| ≤ M₁) : unskewBudget B lam ≤ 3 * M₁ := by
  unfold unskewBudget; linarith

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

theorem pushBudget_le (hp : p.Valid) (hr : 0 ≤ r) {R : ℝ} (hatr : a.AtlasAt p R I.k r) :
    I.Z.pushBudget ≤ 20 * p.K I.k ^ 2 := by
  have hc := (hatr.2.2.2.2.1 I.Q).2.2.2.1
  have hK1 := hp.2.2.1.1 I.k
  have hN1 : 1 ≤ p.N I.k := by linarith [hp.1 I.k]
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  obtain ⟨ht0, ht1⟩ := blockStart_unit (a.T I.k r) (a.j I.k r I.Q)
  have hq := q_pos a I.k r
  have hq1 := q_le_one a I.k r
  have hg := narrow_pos p hp I.k r
  have hg1 : narrow p I.k r ≤ 1 := by
    unfold narrow
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith)
  have hw := width_pos p hp I.k r
  have hw1 : width p I.k r ≤ 1 := by
    unfold width
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have ht : |I.Z.t₀| ≤ 1 := by rw [I.Z_t₀, abs_of_nonneg ht0]; exact ht1
  have hqa : |I.Z.q| ≤ 1 := by rw [I.Z_q, abs_of_pos hq]; exact hq1
  have hz : |I.Z.z₀| ≤ 2 * p.K I.k := by
    have e : I.Z.z₀ = a.c I.k r I.Q 0 + blockStart (a.T I.k r) (a.j I.k r I.Q) * a.c I.k r I.Q 1 :=
      rfl
    rw [e]
    calc |a.c I.k r I.Q 0 + blockStart (a.T I.k r) (a.j I.k r I.Q) * a.c I.k r I.Q 1|
        ≤ |a.c I.k r I.Q 0| + |blockStart (a.T I.k r) (a.j I.k r I.Q)| * |a.c I.k r I.Q 1| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ p.K I.k + 1 * p.K I.k := by
          rw [abs_of_nonneg ht0]
          exact add_le_add (hc 0) (mul_le_mul ht1 (hc 1) (abs_nonneg _) zero_le_one)
      _ = 2 * p.K I.k := by ring
  have h2 : |I.Z.c₂| ≤ p.K I.k := hc 2
  have h3 : |I.Z.c₃| ≤ p.K I.k := hc 3
  have h4 : |I.Z.c₄| ≤ p.K I.k := hc 4
  have hwa : |I.Z.w| ≤ 1 := by
    rw [I.Z_w, abs_of_pos (mul_pos hq hg)]
    nlinarith
  have hh : |I.Z.h₀| = 0 := by rw [I.Z_h₀, abs_zero]
  have haa : |I.Z.a| ≤ 1 := by rw [I.Z_a, abs_of_pos hw]; exact hw1
  have p3 : |I.Z.c₃| * (|I.Z.t₀| + |I.Z.q|) ≤ p.K I.k * 2 :=
    mul_le_mul h3 (by linarith) (by positivity) (by linarith)
  have p4 : |I.Z.c₄| * (|I.Z.z₀| + |I.Z.q|) ≤ p.K I.k * (2 * p.K I.k + 1) :=
    mul_le_mul h4 (by linarith) (by positivity) (by linarith)
  dsimp only [Zoom.pushBudget,
    Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pushBudget]
  nlinarith

theorem liftBudget_le (hp : p.Valid) (hr : 0 ≤ r) {R : ℝ} (hatr : a.AtlasAt p R I.k r) :
    I.Z.liftBudget ≤ 10 * p.K I.k ^ 2 * p.N I.k ^ ((p.kappa + p.ell + 1) * r) := by
  have hc := (hatr.2.2.2.2.1 I.Q).2.2.2.1
  have hK1 := hp.2.2.1.1 I.k
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  have hN1 : 1 ≤ p.N I.k := by linarith [hp.1 I.k]
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  obtain ⟨ht0, ht1⟩ := blockStart_unit (a.T I.k r) (a.j I.k r I.Q)
  have hq := q_pos a I.k r
  have hg := narrow_pos p hp I.k r
  set C := (p.kappa + p.ell + 1) * r with hC
  have hNC : ∀ x, x ≤ C → p.N I.k ^ x ≤ p.N I.k ^ C := fun x hx =>
    Real.rpow_le_rpow_of_exponent_le hN1 hx
  have hNC1 : 1 ≤ p.N I.k ^ C := Real.one_le_rpow hN1 (by positivity)
  -- q⁻¹ ≤ K N^(κ r)
  have hqinv : (a.q I.k r)⁻¹ ≤ p.K I.k * p.N I.k ^ (p.kappa * r) := by
    have h2 := hatr.2.1
    have : (a.q I.k r)⁻¹ = (2 : ℝ) ^ a.T I.k r := by
      simp [PreparedModel.q, zpow_neg, zpow_natCast]
    rw [this]; exact h2
  have hginv : (narrow p I.k r)⁻¹ = p.N I.k ^ (p.ell * r) := by
    unfold narrow; rw [← Real.rpow_neg hN0.le]; ring_nf
  have hainv : (width p I.k r)⁻¹ = p.N I.k ^ r := by
    unfold width; rw [← Real.rpow_neg hN0.le, neg_neg]
  have hq' : |I.Z.q⁻¹| ≤ p.K I.k * p.N I.k ^ C := by
    rw [I.Z_q, abs_of_pos (inv_pos.mpr hq)]
    refine hqinv.trans (mul_le_mul_of_nonneg_left (hNC _ ?_) (by linarith))
    nlinarith
  have hw' : |I.Z.w⁻¹| ≤ p.K I.k * p.N I.k ^ C := by
    rw [I.Z_w, abs_of_pos (inv_pos.mpr (mul_pos hq hg)), mul_inv, hginv]
    calc (a.q I.k r)⁻¹ * p.N I.k ^ (p.ell * r)
        ≤ (p.K I.k * p.N I.k ^ (p.kappa * r)) * p.N I.k ^ (p.ell * r) :=
          mul_le_mul_of_nonneg_right hqinv (by positivity)
      _ = p.K I.k * p.N I.k ^ ((p.kappa + p.ell) * r) := by
          rw [mul_assoc, ← Real.rpow_add hN0]; ring_nf
      _ ≤ p.K I.k * p.N I.k ^ C := mul_le_mul_of_nonneg_left (hNC _ (by nlinarith)) (by linarith)
  have ha' : |I.Z.a⁻¹| ≤ p.N I.k ^ C := by
    rw [I.Z_a, abs_of_pos (inv_pos.mpr (width_pos p hp I.k r)), hainv]
    exact hNC _ (by nlinarith)
  have ht : |I.Z.t₀| ≤ 1 := by rw [I.Z_t₀, abs_of_nonneg ht0]; exact ht1
  have hz : |I.Z.z₀| ≤ 2 * p.K I.k := by
    have e : I.Z.z₀ = a.c I.k r I.Q 0 + blockStart (a.T I.k r) (a.j I.k r I.Q) * a.c I.k r I.Q 1 :=
      rfl
    rw [e]
    calc |a.c I.k r I.Q 0 + blockStart (a.T I.k r) (a.j I.k r I.Q) * a.c I.k r I.Q 1|
        ≤ |a.c I.k r I.Q 0| + |blockStart (a.T I.k r) (a.j I.k r I.Q)| * |a.c I.k r I.Q 1| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ p.K I.k + 1 * p.K I.k := by
          rw [abs_of_nonneg ht0]
          exact add_le_add (hc 0) (mul_le_mul ht1 (hc 1) (abs_nonneg _) zero_le_one)
      _ = 2 * p.K I.k := by ring
  have h2 : |I.Z.c₂| ≤ p.K I.k := hc 2
  have h3 : |I.Z.c₃| ≤ p.K I.k := hc 3
  have h4 : |I.Z.c₄| ≤ p.K I.k := hc 4
  have hh : |I.Z.h₀| = 0 := by rw [I.Z_h₀, abs_zero]
  have p1 : |I.Z.q⁻¹| * (1 + |I.Z.t₀| + |I.Z.z₀|) ≤ (p.K I.k * p.N I.k ^ C) * (2 + 2 * p.K I.k) :=
    mul_le_mul hq' (by linarith) (by positivity) (by positivity)
  have p2 : |I.Z.w⁻¹| * (1 + |I.Z.c₂| + |I.Z.c₃| + |I.Z.c₄|) ≤
      (p.K I.k * p.N I.k ^ C) * (1 + 3 * p.K I.k) :=
    mul_le_mul hw' (by linarith) (by positivity) (by positivity)
  have p3 : |I.Z.a⁻¹| * (1 + |I.Z.h₀|) ≤ p.N I.k ^ C := by rw [hh, add_zero, mul_one]; exact ha'
  dsimp only [Zoom.liftBudget,
    Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.liftBudget]
  have hKN : 0 ≤ p.K I.k * p.N I.k ^ C := by positivity
  nlinarith

end ZoomInput

/-- Renaming the base variables into the four-variable ring keeps the `ℓ¹` norm. -/
theorem coeffL1_rename_castSucc_le (G : MvPolynomial (Fin 3) ℝ) :
    coeffL1 (rename Fin.castSucc G : MvPolynomial (Fin 4) ℝ) ≤ coeffL1 G := by
  have e : (rename Fin.castSucc G : MvPolynomial (Fin 4) ℝ) =
      bind₁ (fun i => (X (Fin.castSucc i) : MvPolynomial (Fin 4) ℝ)) G := by
    induction G using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  rw [e]
  have := Submission.Lib.K4ChartLifting.coeffL1_bind₁_le
    (fun i : Fin 3 => (X (Fin.castSucc i) : MvPolynomial (Fin 4) ℝ)) 1 le_rfl
    (fun i => by rw [Submission.Lib.K4ChartLifting.coeffL1_X]) G
  simpa using this

namespace ZoomSeq

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} {Z : ZoomSeq p a r}

/-- All coefficient budgets at one index are below `20 Kz² N^((κ+ℓ+1) r)`. -/
theorem budgets_le (hp : p.Valid) (hZ : Z.Good) (m : ℕ) :
    skewBudget (Z.I m).B (Z.I m).lam ≤
        20 * Z.Kz m ^ 2 * p.N (Z.I m).k ^ ((p.kappa + p.ell + 1) * r) ∧
      (Z.I m).Z.liftBudget ≤ 20 * Z.Kz m ^ 2 * p.N (Z.I m).k ^ ((p.kappa + p.ell + 1) * r) ∧
      (Z.I m).Z.pushBudget ≤ 20 * Z.Kz m ^ 2 * p.N (Z.I m).k ^ ((p.kappa + p.ell + 1) * r) ∧
      unskewBudget (Z.I m).B (Z.I m).lam ≤
        20 * Z.Kz m ^ 2 * p.N (Z.I m).k ^ ((p.kappa + p.ell + 1) * r) ∧
      |(Z.I m).Z.a⁻¹| ≤ 20 * Z.Kz m ^ 2 * p.N (Z.I m).k ^ ((p.kappa + p.ell + 1) * r) := by
  set J := Z.I m
  have hr := hZ.r_pos
  have hK1 := hp.2.2.1.1 J.k
  have hN0 : 0 < p.N J.k := by linarith [hp.1 J.k]
  have hN1 : 1 ≤ p.N J.k := by linarith [hp.1 J.k]
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  set C := (p.kappa + p.ell + 1) * r with hC
  have hNC1 : 1 ≤ p.N J.k ^ C := Real.one_le_rpow hN1 (by positivity)
  have hKz := hZ.Kz_K m
  have hKz1 : 1 ≤ Z.Kz m := hK1.trans hKz
  have hM₁ := hZ.M₁_ge m
  have hM₁Kz : Z.M₁ m ≤ Z.Kz m := by
    have h := hZ.Kz_caps m
    have hK2 : (1 : ℝ) ≤ 108 * p.K J.k ^ 2 := by
      have := one_le_pow₀ (n := 2) hK1
      linarith
    have : Z.M₁ m ≤ 108 * p.K J.k ^ 2 * Z.M₁ m := by
      calc Z.M₁ m = 1 * Z.M₁ m := (one_mul _).symm
        _ ≤ 108 * p.K J.k ^ 2 * Z.M₁ m := mul_le_mul_of_nonneg_right hK2 (by linarith)
    linarith
  have hKK : p.K J.k ^ 2 ≤ Z.Kz m ^ 2 := pow_le_pow_left₀ (by linarith) hKz 2
  have hMM : Z.M₁ m ^ 2 ≤ Z.Kz m ^ 2 := pow_le_pow_left₀ (by linarith) hM₁Kz 2
  have hKz2 : Z.Kz m ≤ Z.Kz m ^ 2 := by nlinarith
  have hbase : 20 * Z.Kz m ^ 2 ≤ 20 * Z.Kz m ^ 2 * p.N J.k ^ C := by
    have : 0 ≤ 20 * Z.Kz m ^ 2 := by positivity
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := skewBudget_le hM₁ (hZ.lam_inv_le m) (hZ.B_le m)
    nlinarith
  · have := J.liftBudget_le hp hr.le (hZ.atlas_r m)
    have h2 : 10 * p.K J.k ^ 2 * p.N J.k ^ C ≤ 20 * Z.Kz m ^ 2 * p.N J.k ^ C := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith
    linarith
  · have := J.pushBudget_le hp hr.le (hZ.atlas_r m)
    nlinarith
  · have := unskewBudget_le hM₁ (hZ.lam_le m) (hZ.B_le m)
    nlinarith
  · have hw := width_pos p hp J.k r
    rw [J.Z_a, abs_of_pos (inv_pos.mpr hw)]
    have : (width p J.k r)⁻¹ = p.N J.k ^ r := by
      unfold width; rw [← Real.rpow_neg hN0.le, neg_neg]
    rw [this]
    have hrC : p.N J.k ^ r ≤ p.N J.k ^ C :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    have : p.N J.k ^ C ≤ 20 * Z.Kz m ^ 2 * p.N J.k ^ C := by
      have : 1 ≤ 20 * Z.Kz m ^ 2 := by nlinarith
      nlinarith
    linarith

set_option maxHeartbeats 1600000 in
/-- **Pullback of the zoomed result.** The zoomed `Result` gives the original
`Result`. -/
theorem result_pullback (hp : p.Valid) (ha : a.Valid p) (hZ : Z.Good)
    (hres : Z.model.Result Z.params) : a.Result p := by
  obtain ⟨c₀', hc₀', hGbev⟩ := hZ.Gb_coeff
  obtain ⟨R', hR', hR'res⟩ := hres
  have hr := hZ.r_pos
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  set C := (p.kappa + p.ell + 1) * r with hC
  have hC0 : 0 ≤ C := by positivity
  set D := 1 + C with hD
  have hD1 : 1 ≤ D := by linarith
  set c₀ := 5 * D + c₀' + 2 with hc₀def
  have hc₀ : 0 ≤ c₀ := by linarith
  set R'' := 1 + 4 * D + R' + (5 * D + c₀) * R' + (r + r⁻¹ + 2) with hR''def
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hX0 : 0 ≤ (5 * D + c₀) * R' := by
    have : 0 ≤ 5 * D + c₀ := by linarith
    exact mul_nonneg this (by linarith)
  have hR''1 : 1 < R'' := by linarith
  refine ⟨R'', hR''1, fun ε hε => ?_⟩
  have hfreq := hR'res (ε / 2) (half_pos hε)
  have hNt : Tendsto (fun m => p.N (Z.I m).k) atTop atTop := hp.2.1.comp hZ.k_tendsto
  have hR'pos : 0 < R' := by linarith
  have hev : ∀ᶠ m in atTop, (Z.I m).δ ≤ R'⁻¹ ∧ (Z.I m).δ ≤ ε / 2 ∧
      Z.Kz m ≤ p.N (Z.I m).k ^ (ε / 2) ∧ Z.Kz m ≤ p.N (Z.I m).k ^ ((1 : ℝ) / 4) ∧
      (400 : ℝ) ≤ p.N (Z.I m).k ∧ 81 ^ 2 * 2 ^ R' ≤ p.N (Z.I m).k ∧
      (coeffL1 (Z.Gb m) + 1) * (2 + p.K (Z.I m).k) ^ 2 *
        ((2 * p.K (Z.I m).k + Z.M₁ m + 1) * Z.M₁ m * p.K (Z.I m).k) ≤
          p.N (Z.I m).k ^ c₀' := by
    filter_upwards [hZ.δ_tendsto.eventually (ge_mem_nhds (inv_pos.mpr hR'pos)),
      hZ.δ_tendsto.eventually (ge_mem_nhds (half_pos hε)), hZ.Kz_sub (ε / 2) (half_pos hε),
      hZ.Kz_sub (1 / 4) (by norm_num), hNt.eventually_ge_atTop 400,
      hNt.eventually_ge_atTop (81 ^ 2 * 2 ^ R'), hGbev] with m h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine hZ.k_tendsto.frequently ((hfreq.and_eventually hev).mono ?_)
  rintro m ⟨hc, hδ1, hδ2, hKε, hK4, hN400, hN81, hGbm⟩
  set J := Z.I m
  set N := p.N J.k with hNdef
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hK1 := hp.2.2.1.1 J.k
  have hKz := hZ.Kz_K m
  have hKz1 : 1 ≤ Z.Kz m := hK1.trans hKz
  have hM₁ := hZ.M₁_ge m
  have hM₁Kz : Z.M₁ m ≤ Z.Kz m := by
    have h := hZ.Kz_caps m
    have hK2 : (1 : ℝ) ≤ 108 * p.K J.k ^ 2 := by
      have := one_le_pow₀ (n := 2) hK1
      linarith
    have : Z.M₁ m ≤ 108 * p.K J.k ^ 2 * Z.M₁ m := by
      calc Z.M₁ m = 1 * Z.M₁ m := (one_mul _).symm
        _ ≤ 108 * p.K J.k ^ 2 * Z.M₁ m := mul_le_mul_of_nonneg_right hK2 (by linarith)
    linarith
  obtain ⟨hsB, hlB, hpB, huB, haB⟩ := budgets_le hp hZ m
  set Bd := 20 * Z.Kz m ^ 2 * N ^ C with hBd
  -- `N^(1/4)` and `N^(1/2)`
  have hN14 : N ^ ((1 : ℝ) / 4) ≤ N := by
    calc N ^ ((1 : ℝ) / 4) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := Real.rpow_one N
  have hKzN : Z.Kz m ≤ N := hK4.trans hN14
  -- `Bd ≤ N^D`
  have hsq : (20 : ℝ) ≤ N ^ ((1 : ℝ) / 2) := by
    have h400 : (20 : ℝ) = (400 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [show (400 : ℝ) = 20 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h400]
    exact Real.rpow_le_rpow (by norm_num) hN400 (by norm_num)
  have hKz2 : Z.Kz m ^ 2 ≤ N ^ ((1 : ℝ) / 2) := by
    have e : (N ^ ((1 : ℝ) / 4)) ^ 2 = N ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (N ^ ((1 : ℝ) / 4)), ← Real.rpow_mul hN0.le]; norm_num
    calc Z.Kz m ^ 2 ≤ (N ^ ((1 : ℝ) / 4)) ^ 2 := pow_le_pow_left₀ (by linarith) hK4 2
      _ = N ^ ((1 : ℝ) / 2) := e
  have hBdD : Bd ≤ N ^ D := by
    have h20 : 20 * Z.Kz m ^ 2 ≤ N := by
      calc 20 * Z.Kz m ^ 2 ≤ N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) :=
            mul_le_mul hsq hKz2 (by positivity) (by positivity)
        _ = N := by rw [← Real.rpow_add hN0]; norm_num
    calc Bd = 20 * Z.Kz m ^ 2 * N ^ C := rfl
      _ ≤ N * N ^ C := mul_le_mul_of_nonneg_right h20 (by positivity)
      _ = N ^ D := by rw [hD, Real.rpow_add hN0, Real.rpow_one]
  have hBd0 : 0 ≤ Bd := by positivity
  have hBdN : 81 ^ 2 * Bd ^ 4 * N ^ R' * (Bd ^ 5 + N ^ c₀) ^ R' ≤ N ^ R'' := by
    have hND0 : 0 ≤ N ^ D := by positivity
    have h4 : Bd ^ 4 ≤ N ^ (4 * D) := by
      calc Bd ^ 4 ≤ (N ^ D) ^ 4 := pow_le_pow_left₀ hBd0 hBdD 4
        _ = N ^ (4 * D) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have h5 : Bd ^ 5 + N ^ c₀ ≤ 2 * N ^ (5 * D + c₀) := by
      have a1 : Bd ^ 5 ≤ N ^ (5 * D + c₀) := by
        calc Bd ^ 5 ≤ (N ^ D) ^ 5 := pow_le_pow_left₀ hBd0 hBdD 5
          _ = N ^ (5 * D) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
          _ ≤ N ^ (5 * D + c₀) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have a2 : N ^ c₀ ≤ N ^ (5 * D + c₀) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      linarith
    have h5' : (Bd ^ 5 + N ^ c₀) ^ R' ≤ 2 ^ R' * N ^ ((5 * D + c₀) * R') := by
      calc (Bd ^ 5 + N ^ c₀) ^ R' ≤ (2 * N ^ (5 * D + c₀)) ^ R' :=
            Real.rpow_le_rpow (by positivity) h5 (by linarith)
        _ = 2 ^ R' * N ^ ((5 * D + c₀) * R') := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hN0.le]
    calc 81 ^ 2 * Bd ^ 4 * N ^ R' * (Bd ^ 5 + N ^ c₀) ^ R'
        ≤ 81 ^ 2 * N ^ (4 * D) * N ^ R' * (2 ^ R' * N ^ ((5 * D + c₀) * R')) := by
          gcongr
      _ = (81 ^ 2 * 2 ^ R') * (N ^ (4 * D) * N ^ R' * N ^ ((5 * D + c₀) * R')) := by ring
      _ ≤ N * (N ^ (4 * D) * N ^ R' * N ^ ((5 * D + c₀) * R')) := by
          gcongr
      _ = N ^ (1 + 4 * D + R' + (5 * D + c₀) * R') := by
          rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one]; ring
      _ ≤ N ^ R'' := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hzbd : p.K J.k + Z.M₁ m + Z.M₁ m * N ^ R' ≤ N ^ R'' := by
    have hNR' : 0 ≤ N ^ R' := by positivity
    calc p.K J.k + Z.M₁ m + Z.M₁ m * N ^ R' ≤ N + N + N * N ^ R' := by
          have := mul_le_mul_of_nonneg_right (hM₁Kz.trans hKzN) hNR'
          linarith
      _ ≤ N * N ^ (1 + R') := by
          rw [Real.rpow_add hN0 1 R', Real.rpow_one]
          have h1R : 1 ≤ N ^ R' := Real.one_le_rpow hN1 hR'pos.le
          have hNX : N ≤ N * N ^ R' := le_mul_of_one_le_right hN0.le h1R
          have h3 : 3 * (N * N ^ R') ≤ N * (N * N ^ R') :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          linarith
      _ = N ^ (2 + R') := by
          rw [show (2 : ℝ) + R' = 1 + (1 + R') by ring, Real.rpow_add hN0 1 (1 + R'),
            Real.rpow_one]
      _ ≤ N ^ R'' := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hM₁ε : Z.M₁ m * N ^ (ε / 2) ≤ N ^ ε := by
    calc Z.M₁ m * N ^ (ε / 2) ≤ N ^ (ε / 2) * N ^ (ε / 2) :=
          mul_le_mul_of_nonneg_right (hM₁Kz.trans hKε) (by positivity)
      _ = N ^ ε := by rw [← Real.rpow_add hN0]; ring_nf
  have hR''r : R''⁻¹ ≤ r := by
    have : r⁻¹ ≤ R'' := by linarith
    have := inv_anti₀ hri this
    rwa [inv_inv] at this
  -- the native polynomial of the zoomed instance is budgeted by the original one
  have hsh : ∀ (j : Fin J.M) (x : J.Ret j),
      1 + coeffL1 J.Pn ≤ N ^ c₀ * ((1 + coeffL1 (a.F J.k (J.depth j) x.1.1)) +
        coeffL1 (a.P J.k)) := by
    intro j x
    have hPdeg : (Submission.Lib.K4ContactNormalization.baseCalibratedTest (a.P J.k)
        (Z.Gb m)).totalDegree ≤ 2 :=
      Submission.Lib.K4ContactNormalization.baseCalibratedTest_degree
        (ha.1 J.k).2.2.2.2.2.2.2.1 (hZ.Gb_deg m)
    have hP0 := Submission.Lib.K4ChartLifting.coeffL1_nonneg (a.P J.k)
    have hF0 := Submission.Lib.K4ChartLifting.coeffL1_nonneg (a.F J.k (J.depth j) x.1.1)
    have hG0 := Submission.Lib.K4ChartLifting.coeffL1_nonneg (Z.Gb m)
    have hGb : coeffL1 (Z.Gb m) ≤ N ^ c₀' := by
      have h2 : 1 ≤ (2 + p.K J.k) ^ 2 := one_le_pow₀ (by linarith)
      have h3 : 1 ≤ (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.K J.k := by
        have : 1 ≤ (2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m := by nlinarith
        nlinarith
      have : coeffL1 (Z.Gb m) + 1 ≤ (coeffL1 (Z.Gb m) + 1) * (2 + p.K J.k) ^ 2 *
          ((2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.K J.k) := by
        have h4 : 1 ≤ (2 + p.K J.k) ^ 2 * ((2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.K J.k) :=
          one_le_mul_of_one_le_of_one_le h2 h3
        calc coeffL1 (Z.Gb m) + 1 = (coeffL1 (Z.Gb m) + 1) * 1 := (mul_one _).symm
          _ ≤ (coeffL1 (Z.Gb m) + 1) * ((2 + p.K J.k) ^ 2 *
              ((2 * p.K J.k + Z.M₁ m + 1) * Z.M₁ m * p.K J.k)) :=
            mul_le_mul_of_nonneg_left h4 (by linarith)
          _ = _ := by ring
      linarith
    have hPn : J.Pn = Zoom.nPush J.Z J.B J.lam
        (Submission.Lib.K4ContactNormalization.baseCalibratedTest (a.P J.k) (Z.Gb m)) :=
      hZ.Pn_eq m
    have h1 := coeffL1_nPush_le J.Z J.B J.lam _ hPdeg
    have h2 : coeffL1 (Submission.Lib.K4ContactNormalization.baseCalibratedTest (a.P J.k)
        (Z.Gb m)) ≤ coeffL1 (a.P J.k) + coeffL1 (Z.Gb m) :=
      (Submission.Lib.K4ChartLifting.coeffL1_sub_le _ _).trans
        (add_le_add le_rfl (coeffL1_rename_castSucc_le _))
    have hBd5 : Bd ^ 5 ≤ N ^ (5 * D) := by
      calc Bd ^ 5 ≤ (N ^ D) ^ 5 := pow_le_pow_left₀ hBd0 hBdD 5
        _ = N ^ (5 * D) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have hpB0 : 0 ≤ J.Z.pushBudget := le_trans zero_le_one Zoom.one_le_pushBudget
    have huB0 : 0 ≤ unskewBudget J.B J.lam := le_trans zero_le_one (one_le_unskewBudget _ _)
    have hPnle : coeffL1 J.Pn ≤ N ^ (5 * D) * (coeffL1 (a.P J.k) + N ^ c₀') := by
      rw [hPn]
      calc coeffL1 (Zoom.nPush J.Z J.B J.lam
            (Submission.Lib.K4ContactNormalization.baseCalibratedTest (a.P J.k) (Z.Gb m)))
          ≤ |J.Z.a⁻¹| * coeffL1 (Submission.Lib.K4ContactNormalization.baseCalibratedTest
              (a.P J.k) (Z.Gb m)) * J.Z.pushBudget ^ 2 * unskewBudget J.B J.lam ^ 2 := h1
        _ ≤ Bd * (coeffL1 (a.P J.k) + N ^ c₀') * Bd ^ 2 * Bd ^ 2 := by
            gcongr
            all_goals first
              | exact Submission.Lib.K4ChartLifting.coeffL1_nonneg _
              | exact h2.trans (add_le_add le_rfl hGb)
        _ = Bd ^ 5 * (coeffL1 (a.P J.k) + N ^ c₀') := by ring
        _ ≤ N ^ (5 * D) * (coeffL1 (a.P J.k) + N ^ c₀') := by gcongr
    have hND : 1 ≤ N ^ (5 * D) := Real.one_le_rpow hN1 (by linarith)
    have hNc : 1 ≤ N ^ c₀' := Real.one_le_rpow hN1 hc₀'.le
    have hNe : N ^ c₀ = N ^ (5 * D) * N ^ c₀' * N ^ (2 : ℝ) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, hc₀def]
    have hN2 : (2 : ℝ) ≤ N ^ (2 : ℝ) := by
      rw [Real.rpow_two]; nlinarith
    have hA : 0 ≤ N ^ (5 * D) * N ^ c₀' := by positivity
    calc 1 + coeffL1 J.Pn ≤ 1 + N ^ (5 * D) * (coeffL1 (a.P J.k) + N ^ c₀') := by linarith
      _ ≤ N ^ (5 * D) * N ^ c₀' * (2 * (1 + coeffL1 (a.P J.k))) := by
          have e1 : N ^ (5 * D) * coeffL1 (a.P J.k) ≤
              N ^ (5 * D) * N ^ c₀' * coeffL1 (a.P J.k) := by
            have := mul_le_mul_of_nonneg_left hNc (by positivity : 0 ≤ N ^ (5 * D))
            nlinarith
          have e2 : 1 ≤ N ^ (5 * D) * N ^ c₀' := one_le_mul_of_one_le_of_one_le hND hNc
          nlinarith
      _ ≤ N ^ (5 * D) * N ^ c₀' * (N ^ (2 : ℝ) * (1 + coeffL1 (a.P J.k))) := by
          gcongr
      _ = N ^ c₀ * (1 + coeffL1 (a.P J.k)) := by rw [hNe]; ring
      _ ≤ N ^ c₀ * ((1 + coeffL1 (a.F J.k (J.depth j) x.1.1)) + coeffL1 (a.P J.k)) := by
          gcongr
          linarith
  exact candidate_pullback hp ha hZ m (R'' := R'') (ε'' := ε) (Bd := Bd) (c₀ := c₀) hR'
    (half_pos hε) hR''r (by linarith) hδ1 (by linarith) hM₁ε hzbd hsB hlB hpB huB haB hBdN
    hsh hc

/-- **Contact transfer.** Under the contact principle, a valid model with a
good zoomed contact sequence has the frozen `Result`. -/
theorem contact_transfer (hp : p.Valid) (ha : a.Valid p) (hZ : Z.Good)
    (hCMP : ContactModelPrinciple) : a.Result p :=
  result_pullback hp ha hZ (result hp ha hZ hCMP)

end ZoomSeq

end

end Submission.Obl.k4_row_parent_contact_candidates
