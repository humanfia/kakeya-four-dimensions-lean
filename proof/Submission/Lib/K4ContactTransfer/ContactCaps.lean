import Mathlib
import Submission.Lib.K4ContactTransfer.ContactAtlas
import Submission.Lib.K4ContactTransfer.ContactBaseMap

/-!
# Hidden-coordinate caps of the zoomed contact instance

The zoomed hidden coordinate is `x₃/a_r` (no hidden translation), so a zoomed
hidden bin of width `N^(-s')` is exactly an original hidden bin of width
`N^(-(r+s'))`. Original caps at a fine base scale `δ`, transported through the
affine base chart of determinant `1/(q³ g λ)` and divided by the parent weight
`q ν(A_Q) ≥ q · a_r^d q² g / K`, give the zoomed caps with the loss `27 K² |λ|`.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point)
open Submission.Lib.K4MovingMeshBoxes (baseMesh)

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Cells of a prepared model are base meshes of the base coordinates. -/
theorem cell_eq_baseMesh (a : PreparedModel α) (N r : ℝ) (k : ℕ) (w : α × ℝ) :
    a.cell N r k w = baseMesh (N ^ (-r)) (Zoom.baseOf (a.b k w.1) w.2) := by
  funext e
  fin_cases e <;> rfl

/-- Resolution of the zoomed base chart on a fine original mesh. -/
theorem baseMat_resolve {Z : Zoom} {B : Fin 2 → ℝ} {lam q g K M₁ δ σ : ℝ}
    (hq : 0 < q) (hg : 0 < g) (hg1 : g ≤ 1) (hK : 1 ≤ K) (hM₁ : 1 ≤ M₁)
    (hZq : Z.q = q) (hZw : Z.w = q * g) (h3 : |Z.c₃| ≤ K) (h4 : |Z.c₄| ≤ K)
    (hB : |B 0| + |B 1| ≤ M₁) (hlam : |lam⁻¹| ≤ M₁) (hδ : 0 ≤ δ)
    (hres : (2 * K + M₁ + 1) * M₁ * δ ≤ q * g * σ) :
    ∀ i, (∑ j, |Zoom.baseMat Z B lam i j| * δ) ≤ σ := by
  have hqg : 0 < q * g := mul_pos hq hg
  have hδq : δ ≤ q * σ := by
    have h1 : δ ≤ (2 * K + M₁ + 1) * M₁ * δ := by
      have : 1 ≤ (2 * K + M₁ + 1) * M₁ := by nlinarith
      nlinarith
    have hσ : 0 ≤ σ := by
      have h0 : 0 ≤ (2 * K + M₁ + 1) * M₁ * δ := by positivity
      by_contra hneg
      have : q * g * σ < 0 := mul_neg_of_pos_of_neg hqg (lt_of_not_ge hneg)
      linarith
    have h2 : q * g * σ ≤ q * σ := by
      have := mul_le_mul_of_nonneg_left hg1 hq.le
      nlinarith
    linarith
  intro i
  fin_cases i
  · simp [Zoom.baseMat, Fin.sum_univ_three, hZq]
    rw [abs_of_pos hq, inv_mul_le_iff₀ hq]
    linarith
  · simp [Zoom.baseMat, Fin.sum_univ_three, hZq]
    rw [abs_of_pos hq, inv_mul_le_iff₀ hq]
    linarith
  · simp [Zoom.baseMat, Fin.sum_univ_three, hZq, hZw]
    have e1 : ∀ x y : ℝ, |(-(x / q) + -(y / (q * g))) / lam| = |g * x + y| / (q * g) * |lam⁻¹| := by
      intro x y
      rw [div_eq_mul_inv, abs_mul]
      congr 1
      rw [show -(x / q) + -(y / (q * g)) = -((g * x + y) / (q * g)) by field_simp; ring]
      rw [abs_neg, abs_div, abs_of_pos hqg]
    have e2 : |lam|⁻¹ * (|g|⁻¹ * |q|⁻¹) = 1 / (q * g) * |lam⁻¹| := by
      rw [abs_inv lam, abs_of_pos hg, abs_of_pos hq]; ring
    rw [e1, e1, e2]
    have hx : ∀ x y : ℝ, |y| ≤ K → |g * x + y| ≤ |x| + K := by
      intro x y hy
      calc |g * x + y| ≤ |g * x| + |y| := abs_add_le _ _
        _ ≤ |x| + K := by
          rw [abs_mul, abs_of_pos hg]
          have : g * |x| ≤ |x| := by nlinarith [abs_nonneg x]
          linarith
    have hx0 := hx (B 0) Z.c₃ h3
    have hx1 := hx (B 1) Z.c₄ h4
    have hu := abs_nonneg lam⁻¹
    calc |g * B 0 + Z.c₃| / (q * g) * |lam⁻¹| * δ + |g * B 1 + Z.c₄| / (q * g) * |lam⁻¹| * δ +
          1 / (q * g) * |lam⁻¹| * δ
        = (|g * B 0 + Z.c₃| + |g * B 1 + Z.c₄| + 1) * |lam⁻¹| * δ / (q * g) := by ring
      _ ≤ (2 * K + M₁ + 1) * M₁ * δ / (q * g) := by
          apply div_le_div_of_nonneg_right _ hqg.le
          apply mul_le_mul_of_nonneg_right _ hδ
          apply mul_le_mul _ hlam hu (by positivity)
          linarith
      _ ≤ σ := by rw [div_le_iff₀ hqg]; linarith

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

theorem Z_h₀ : I.Z.h₀ = 0 := rfl

/-- The zoomed hidden coordinate is the original one divided by the hidden width. -/
theorem hidden_zoom (hp : p.Valid) (b : Fin 6 → ℝ) (t : ℝ) :
    (point (Zoom.nCoeff I.Z I.B I.lam b) ((t - I.Z.t₀) / I.Z.q)) 3 =
      (point b t) 3 / width p I.k r := by
  have hq := q_pos a I.k r
  have hw := width_pos p hp I.k r
  have hZq : I.Z.q = a.q I.k r := rfl
  have hZa : I.Z.a = width p I.k r := rfl
  simp only [point, Zoom.nCoeff, Submission.Lib.K4ContactNormalization.skewCoeff, Zoom.coeff,
    Matrix.cons_val, Fin.isValue, I.Z_h₀, hZq, hZa]
  field_simp
  ring

/-- Zoomed hidden bins are original hidden bins. -/
theorem hidden_bin_zoom (hp : p.Valid) (b : Fin 6 → ℝ) (t : ℝ) (s' : ℝ) (j : ℤ) :
    ⌊(point (Zoom.nCoeff I.Z I.B I.lam b) ((t - I.Z.t₀) / I.Z.q)) 3 / p.N I.k ^ (-s')⌋ = j ↔
      ⌊(point b t) 3 / p.N I.k ^ (-(r + s'))⌋ = j := by
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  rw [I.hidden_zoom hp]
  have e : (point b t) 3 / width p I.k r / p.N I.k ^ (-s') =
      (point b t) 3 / p.N I.k ^ (-(r + s')) := by
    simp only [width]
    rw [div_div, ← Real.rpow_add hN0]
    ring_nf
  rw [e]

/-- The parent weight is at least `q³ a_r^d g / K`. -/
theorem W_lower {R : ℝ} (hatr : a.AtlasAt p R I.k r) :
    ENNReal.ofReal (a.q I.k r ^ 3 * width p I.k r ^ p.d * narrow p I.k r / p.K I.k) ≤ I.W := by
  have hq := q_pos a I.k r
  have h := hatr.prior_lower I.Q
  unfold W
  calc ENNReal.ofReal (a.q I.k r ^ 3 * width p I.k r ^ p.d * narrow p I.k r / p.K I.k)
      = ENNReal.ofReal (a.q I.k r) * ENNReal.ofReal (width p I.k r ^ p.d * a.q I.k r ^ 2 *
          narrow p I.k r / p.K I.k) := by
        rw [← ENNReal.ofReal_mul hq.le]; congr 1; ring
    _ ≤ _ := by gcongr

/-- **Zoomed caps from original fine caps.** Original caps at the fine mesh
`N^(-r'')` with an extra event `Φ` (the pullback of the zoomed event `Φ'`) give
zoomed caps at the mesh `N^(-r')`, with the loss `27 K |λ| N^(d r)` from the
affine Jacobian and the parent weight. -/
theorem zoom_cap (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r) (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) (hr : 0 ≤ r) (hlam : I.lam ≠ 0) {M₁ : ℝ} (hM₁ : 1 ≤ M₁)
    (hlamM : |I.lam⁻¹| ≤ M₁) (hlamM' : |I.lam| ≤ M₁) (hBle : |I.B 0| + |I.B 1| ≤ M₁)
    {r' r'' C : ℝ} (hC : 0 ≤ C)
    (hres : (2 * p.K I.k + M₁ + 1) * M₁ * p.N I.k ^ (-r'') ≤
      a.q I.k r * narrow p I.k r * p.N I.k ^ (-r'))
    (Φ Φ' : α × ℝ → Prop) (hΦ : ∀ z, Φ' (zoomTime I.Z.t₀ I.Z.q z) ↔ Φ z)
    (hΦm : MeasurableSet {z | Φ' z})
    (horig : ∀ z : Fin 3 → ℤ, a.mu I.k {w | a.cell (p.N I.k) r'' I.k w = z ∧ Φ w} ≤
      ENNReal.ofReal (C * p.N I.k ^ (-3 * r'')))
    (z' : Fin 3 → ℤ) :
    zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W
      {w | baseMesh (p.N I.k ^ (-r'))
          (Zoom.baseOf (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) = z' ∧ Φ' w} ≤
      ENNReal.ofReal (27 * p.K I.k * M₁ * C * p.N I.k ^ (p.d * r) * p.N I.k ^ (-3 * r')) := by
  have hb := (hcommon I.k).1
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  have hN1 : 1 ≤ p.N I.k := by linarith [hp.1 I.k]
  have hK1 := hp.2.2.1.1 I.k
  have hq := q_pos a I.k r
  have hg := narrow_pos p hp I.k r
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hg1 : narrow p I.k r ≤ 1 := by
    unfold narrow
    apply Real.rpow_le_one_of_one_le_of_nonpos hN1
    nlinarith
  have hS := I.measurable_keep hats hGm
  have hδ : 0 < p.N I.k ^ (-r'') := Real.rpow_pos_of_pos hN0 _
  have hσ : 0 < p.N I.k ^ (-r') := Real.rpow_pos_of_pos hN0 _
  have hc := (hatr.2.2.2.2.1 I.Q).2.2.2.1
  have hmeas : MeasurableSet {w : α × ℝ | baseMesh (p.N I.k ^ (-r'))
      (Zoom.baseOf (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) = z' ∧ Φ' w} := by
    refine MeasurableSet.inter ?_ hΦm
    have h1 : Measurable (fun z : α × ℝ => Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) :=
      I.continuous_nCoeff.measurable.comp (hb.comp measurable_fst)
    have hc' : ∀ e, Measurable (fun z : α × ℝ => Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1) e) :=
      fun e => (measurable_pi_apply e).comp h1
    have hm : Measurable (fun w : α × ℝ => baseMesh (p.N I.k ^ (-r'))
        (Zoom.baseOf (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2)) := by
      apply Measurable.of_eval
      intro i
      apply Int.measurable_floor.comp
      apply Measurable.div_const
      fin_cases i <;> simp [Zoom.baseOf]
      · exact measurable_snd
      · exact (hc' 0).add (measurable_snd.mul (hc' 3))
      · exact (hc' 1).add (measurable_snd.mul (hc' 4))
    exact hm (measurableSet_singleton z')
  have hcap := zoom_cell_cap (a.mu I.k) (a.b I.k) (I.Z_ok hp) hlam hS I.W Φ Φ' hΦ hδ hσ hC
    (baseMat_resolve (Z := I.Z) (q := a.q I.k r) (g := narrow p I.k r) hq hg hg1 hK1 hM₁
      rfl rfl (hc 3) (hc 4) hBle hlamM hδ.le hres) ?_ z' hmeas
  · refine hcap.trans ?_
    rw [Zoom.det_baseMat]
    have hdet : |I.Z.q⁻¹ * I.Z.q⁻¹ * (I.Z.w * I.lam)⁻¹|⁻¹ =
        a.q I.k r ^ 3 * narrow p I.k r * |I.lam| := by
      rw [I.Z_q, I.Z_w]
      simp only [abs_mul, abs_inv, abs_of_pos hq, abs_of_pos hg]
      have : |I.lam| ≠ 0 := abs_ne_zero.mpr hlam
      field_simp
    rw [hdet]
    have hW := I.W_lower hatr
    set w₀ := a.q I.k r ^ 3 * width p I.k r ^ p.d * narrow p I.k r / p.K I.k with hw₀def
    have hwd : 0 < width p I.k r ^ p.d := Real.rpow_pos_of_pos (width_pos p hp I.k r) _
    have hw₀ : 0 < w₀ := by positivity
    calc I.W⁻¹ * ENNReal.ofReal (27 * C * (a.q I.k r ^ 3 * narrow p I.k r * |I.lam|) *
          (p.N I.k ^ (-r')) ^ 3)
        ≤ (ENNReal.ofReal w₀)⁻¹ * ENNReal.ofReal (27 * C * (a.q I.k r ^ 3 * narrow p I.k r *
            |I.lam|) * (p.N I.k ^ (-r')) ^ 3) := by
          gcongr
      _ = ENNReal.ofReal (w₀⁻¹ * (27 * C * (a.q I.k r ^ 3 * narrow p I.k r * |I.lam|) *
            (p.N I.k ^ (-r')) ^ 3)) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hw₀.le), ENNReal.ofReal_inv_of_pos hw₀]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hNdr : width p I.k r ^ p.d * p.N I.k ^ (p.d * r) = 1 := by
            unfold width
            rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
            ring_nf
            exact Real.rpow_zero _
          have hσ3 : (p.N I.k ^ (-r')) ^ 3 = p.N I.k ^ (-3 * r') := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
          rw [hσ3, hw₀def]
          have hNdr' : 0 < p.N I.k ^ (p.d * r) := Real.rpow_pos_of_pos hN0 _
          have hwd' : width p I.k r ^ p.d = (p.N I.k ^ (p.d * r))⁻¹ :=
            eq_inv_of_mul_eq_one_left hNdr
          have e : (a.q I.k r ^ 3 * width p I.k r ^ p.d * narrow p I.k r / p.K I.k)⁻¹ *
              (27 * C * (a.q I.k r ^ 3 * narrow p I.k r * |I.lam|) * p.N I.k ^ (-3 * r')) =
              27 * p.K I.k * |I.lam| * C * p.N I.k ^ (p.d * r) * p.N I.k ^ (-3 * r') := by
            rw [hwd']
            field_simp
          rw [e]
          gcongr
  · intro q'
    refine le_trans (measure_mono ?_) ((horig q').trans_eq ?_)
    · intro w hw
      exact ⟨by rw [cell_eq_baseMesh]; exact hw.1, hw.2.2⟩
    · congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      ring_nf

/-- Normalized trajectory points are measurable. -/
theorem measurable_zpoint (hb : Measurable (a.b I.k)) :
    Measurable (fun z : α × ℝ => point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) z.2) := by
  have h1 : Measurable (fun z : α × ℝ => Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) :=
    I.continuous_nCoeff.measurable.comp (hb.comp measurable_fst)
  have hc : ∀ e, Measurable (fun z : α × ℝ => Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1) e) :=
    fun e => (measurable_pi_apply e).comp h1
  unfold point
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp
  · exact measurable_snd
  · exact (hc 0).add (measurable_snd.mul (hc 3))
  · exact (hc 1).add (measurable_snd.mul (hc 4))
  · exact (hc 2).add (measurable_snd.mul (hc 5))

/-- **Zoomed hidden caps** (`h = false`) at one index. -/
theorem zoom_hidden_cap (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r) (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) (hr : 0 ≤ r) (hlam : I.lam ≠ 0) {M₁ : ℝ} (hM₁ : 1 ≤ M₁)
    (hlamM : |I.lam⁻¹| ≤ M₁) (hlamM' : |I.lam| ≤ M₁) (hBle : |I.B 0| + |I.B 1| ≤ M₁)
    {r' r'' s' : ℝ}
    (hres : (2 * p.K I.k + M₁ + 1) * M₁ * p.N I.k ^ (-r'') ≤
      a.q I.k r * narrow p I.k r * p.N I.k ^ (-r'))
    (horig : ∀ (z : Fin 3 → ℤ) (j : ℤ), a.mu I.k {w | a.cell (p.N I.k) r'' I.k w = z ∧
      ⌊(a.x I.k w.1 w.2) 3 / p.N I.k ^ (-(r + s'))⌋ = j} ≤
        ENNReal.ofReal (p.K I.k * p.N I.k ^ (-3 * r'' - p.d * (r + s'))))
    (z' : Fin 3 → ℤ) (j : ℤ) :
    zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W
      {w | baseMesh (p.N I.k ^ (-r'))
          (Zoom.baseOf (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) = z' ∧
        ⌊(point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) 3 / p.N I.k ^ (-s')⌋ = j} ≤
      ENNReal.ofReal (27 * p.K I.k ^ 2 * M₁ * p.N I.k ^ (-3 * r' - p.d * s')) := by
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  have hK0 : 0 ≤ p.K I.k := by linarith [hp.2.2.1.1 I.k]
  have hb := (hcommon I.k).1
  have h := I.zoom_cap hp hcommon hatr hats hGm hr hlam hM₁ hlamM hlamM' hBle
    (C := p.K I.k * p.N I.k ^ (-(p.d * (r + s')))) (by positivity) hres
    (fun w => ⌊(point (a.b I.k w.1) w.2) 3 / p.N I.k ^ (-(r + s'))⌋ = j)
    (fun w => ⌊(point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) 3 / p.N I.k ^ (-s')⌋ = j)
    (fun w => I.hidden_bin_zoom hp (a.b I.k w.1) w.2 s' j)
    ((measurableSet_singleton j).preimage (Int.measurable_floor.comp
      (((measurable_pi_apply 3).comp (I.measurable_zpoint hb)).div_const _)))
    (fun z => (horig z j).trans_eq (by
      congr 1
      rw [mul_assoc, ← Real.rpow_add hN0]
      ring_nf)) z'
  refine h.trans (le_of_eq ?_)
  congr 1
  have e : p.N I.k ^ (-(p.d * (r + s'))) * p.N I.k ^ (p.d * r) * p.N I.k ^ (-3 * r') =
      p.N I.k ^ (-3 * r' - p.d * s') := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
  calc 27 * p.K I.k * M₁ * (p.K I.k * p.N I.k ^ (-(p.d * (r + s')))) * p.N I.k ^ (p.d * r) *
        p.N I.k ^ (-3 * r')
      = 27 * p.K I.k ^ 2 * M₁ * (p.N I.k ^ (-(p.d * (r + s'))) * p.N I.k ^ (p.d * r) *
          p.N I.k ^ (-3 * r')) := by ring
    _ = _ := by rw [e]

/-- **Zoomed joint caps** (`h = false`, with a velocity bin) at one index. -/
theorem zoom_joint_cap (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r) (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) (hr : 0 ≤ r) (hlam : I.lam ≠ 0) {M₁ : ℝ} (hM₁ : 1 ≤ M₁)
    (hlamM : |I.lam⁻¹| ≤ M₁) (hlamM' : |I.lam| ≤ M₁) (hBle : |I.B 0| + |I.B 1| ≤ M₁)
    {r' r'' s' v : ℝ}
    (hres : (2 * p.K I.k + M₁ + 1) * M₁ * p.N I.k ^ (-r'') ≤
      a.q I.k r * narrow p I.k r * p.N I.k ^ (-r'))
    (horig : ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ), a.mu I.k {w | a.cell (p.N I.k) r'' I.k w = z ∧
      ⌊(a.x I.k w.1 w.2) 3 / p.N I.k ^ (-(r + s'))⌋ = j ∧
        ⌊a.b I.k w.1 3 / p.N I.k ^ (-v)⌋ = v₀} ≤
        ENNReal.ofReal (p.K I.k * p.N I.k ^ (-3 * r'' - p.d * (r + s'))) *
          a.pi I.k {w | ⌊w / p.N I.k ^ (-v)⌋ = v₀})
    (z' : Fin 3 → ℤ) (j v₀ : ℤ) :
    zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W
      {w | baseMesh (p.N I.k ^ (-r'))
          (Zoom.baseOf (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) = z' ∧
        ⌊(point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) 3 / p.N I.k ^ (-s')⌋ = j ∧
        ⌊Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1) 3 / p.N I.k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (27 * p.K I.k ^ 2 * M₁ * p.N I.k ^ (-3 * r' - p.d * s')) *
        a.pi I.k {w | ⌊w / p.N I.k ^ (-v)⌋ = v₀} := by
  have hN0 : 0 < p.N I.k := by linarith [hp.1 I.k]
  have hK0 : 0 ≤ p.K I.k := by linarith [hp.2.2.1.1 I.k]
  have hb := (hcommon I.k).1
  haveI := (hcommon I.k).2.2.1
  set πv := (a.pi I.k {w | ⌊w / p.N I.k ^ (-v)⌋ = v₀}).toReal with hπv
  have hπ0 : 0 ≤ πv := ENNReal.toReal_nonneg
  have hπe : a.pi I.k {w | ⌊w / p.N I.k ^ (-v)⌋ = v₀} = ENNReal.ofReal πv := by
    rw [hπv, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hm3 : Measurable (fun w : α × ℝ => Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1) 3) :=
    (measurable_pi_apply 3).comp (I.continuous_nCoeff.measurable.comp (hb.comp measurable_fst))
  have h := I.zoom_cap hp hcommon hatr hats hGm hr hlam hM₁ hlamM hlamM' hBle
    (C := p.K I.k * p.N I.k ^ (-(p.d * (r + s'))) * πv) (by positivity) hres
    (fun w => ⌊(point (a.b I.k w.1) w.2) 3 / p.N I.k ^ (-(r + s'))⌋ = j ∧
      ⌊a.b I.k w.1 3 / p.N I.k ^ (-v)⌋ = v₀)
    (fun w => ⌊(point (Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1)) w.2) 3 / p.N I.k ^ (-s')⌋ = j ∧
      ⌊Zoom.nCoeff I.Z I.B I.lam (a.b I.k w.1) 3 / p.N I.k ^ (-v)⌋ = v₀)
    (fun w => and_congr (I.hidden_bin_zoom hp (a.b I.k w.1) w.2 s' j)
      (by simp only [zoomTime, Zoom.nCoeff_three]))
    (((measurableSet_singleton j).preimage (Int.measurable_floor.comp
      (((measurable_pi_apply 3).comp (I.measurable_zpoint hb)).div_const _))).inter
      ((measurableSet_singleton v₀).preimage (Int.measurable_floor.comp (hm3.div_const _))))
    (fun z => (horig z j v₀).trans_eq (by
      rw [hπe, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show p.K I.k * p.N I.k ^ (-(p.d * (r + s'))) * πv * p.N I.k ^ (-3 * r'') =
        p.K I.k * (p.N I.k ^ (-(p.d * (r + s'))) * p.N I.k ^ (-3 * r'')) * πv by ring,
        ← Real.rpow_add hN0]
      ring_nf)) z'
  refine h.trans (le_of_eq ?_)
  rw [hπe, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e : p.N I.k ^ (-(p.d * (r + s'))) * p.N I.k ^ (p.d * r) * p.N I.k ^ (-3 * r') =
      p.N I.k ^ (-3 * r' - p.d * s') := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
  calc 27 * p.K I.k * M₁ * (p.K I.k * p.N I.k ^ (-(p.d * (r + s'))) * πv) * p.N I.k ^ (p.d * r) *
        p.N I.k ^ (-3 * r')
      = 27 * p.K I.k ^ 2 * M₁ * (p.N I.k ^ (-(p.d * (r + s'))) * p.N I.k ^ (p.d * r) *
          p.N I.k ^ (-3 * r')) * πv := by ring
    _ = _ := by rw [e]

end ZoomInput

end

end Submission.Lib.K4ContactTransfer
