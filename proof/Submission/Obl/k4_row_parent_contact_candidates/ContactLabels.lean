/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactLabels.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactLevels

/-!
# Label hypotheses of the zoomed instance, one retained descendant at a time

For a retained descendant `x` of the parent at grid depth `s`, with the scale
ratios `ρw = a_s/a_r`, `ρq = q_s/q_r`, `ρg = g_s/g_r`:

* `prior_zoom`: its conditioned prior lies in `[ρw^d ρq² ρg / K², K² ρw^d ρq² ρg]`;
* `floor_zoom`: its zoomed residual mass is at least `θ 4^(-j)/2 · ρq ν'(A)`;
* `boxes_zoom`: its three box inequalities hold in the zoomed chart with
  widths `K ρq`, `K ρq ρg/|λ|`, `K ρg/|λ|`;
* `fits_zoom`: its pushed test fits at the zoomed width `ρw`.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- Conditioned prior of a retained descendant. -/
theorem prior_zoom (hp : p.Valid) {R : ℝ} (hatr : a.AtlasAt p R I.k r)
    {j : Fin I.M} (hats : a.AtlasAt p R I.k (I.depth j)) (x : I.Ret j) :
    ENNReal.ofReal ((width p I.k (I.depth j) / width p I.k r) ^ p.d *
        (a.q I.k (I.depth j) / a.q I.k r) ^ 2 *
        (narrow p I.k (I.depth j) / narrow p I.k r) / p.K I.k ^ 2) ≤
      condPrior (a.nu I.k) (a.A I.k r I.Q) (a.A I.k (I.depth j) x.1.1) ∧
    condPrior (a.nu I.k) (a.A I.k r I.Q) (a.A I.k (I.depth j) x.1.1) ≤
      ENNReal.ofReal (p.K I.k ^ 2 * (width p I.k (I.depth j) / width p I.k r) ^ p.d *
        (a.q I.k (I.depth j) / a.q I.k r) ^ 2 *
        (narrow p I.k (I.depth j) / narrow p I.k r)) := by
  set s := I.depth j
  have hK : 0 < p.K I.k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 I.k)
  have hd := hp.2.2.2.1
  have hws := width_pos p hp I.k s
  have hwr := width_pos p hp I.k r
  have hgs := narrow_pos p hp I.k s
  have hgr := narrow_pos p hp I.k r
  have hqs := q_pos a I.k s
  have hqr := q_pos a I.k r
  rw [condPrior_apply _ _ _ (hats.measurable_A _), inter_eq_left.mpr (I.prior_sub x)]
  -- original bounds
  set Lx := width p I.k s ^ p.d * a.q I.k s ^ 2 * narrow p I.k s with hLx
  set Lr := width p I.k r ^ p.d * a.q I.k r ^ 2 * narrow p I.k r with hLr
  have hLx0 : 0 < Lx := by positivity
  have hLr0 : 0 < Lr := by positivity
  have hx1 : ENNReal.ofReal (Lx / p.K I.k) ≤ a.nu I.k (a.A I.k s x.1.1) := hats.prior_lower _
  have hx2 : a.nu I.k (a.A I.k s x.1.1) ≤ ENNReal.ofReal (p.K I.k * Lx) := by
    have := hats.prior_upper x.1.1
    simpa only [hLx, mul_assoc] using this
  have hQ1 : ENNReal.ofReal (Lr / p.K I.k) ≤ a.nu I.k (a.A I.k r I.Q) := hatr.prior_lower _
  have hQ2 : a.nu I.k (a.A I.k r I.Q) ≤ ENNReal.ofReal (p.K I.k * Lr) := by
    have := hatr.prior_upper I.Q
    simpa only [hLr, mul_assoc] using this
  have hratio : (width p I.k s / width p I.k r) ^ p.d * (a.q I.k s / a.q I.k r) ^ 2 *
      (narrow p I.k s / narrow p I.k r) = Lx / Lr := by
    rw [Real.div_rpow hws.le hwr.le]
    simp only [hLx, hLr]
    field_simp
  rw [hratio]
  constructor
  · calc ENNReal.ofReal (Lx / Lr / p.K I.k ^ 2)
        = ENNReal.ofReal (1 / (p.K I.k * Lr)) * ENNReal.ofReal (Lx / p.K I.k) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ ≤ (a.nu I.k (a.A I.k r I.Q))⁻¹ * a.nu I.k (a.A I.k s x.1.1) := by
          gcongr
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div]
          exact ENNReal.inv_le_inv.mpr hQ2
  · calc (a.nu I.k (a.A I.k r I.Q))⁻¹ * a.nu I.k (a.A I.k s x.1.1)
        ≤ ENNReal.ofReal (1 / (Lr / p.K I.k)) * ENNReal.ofReal (p.K I.k * Lx) := by
          gcongr
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div]
          exact ENNReal.inv_le_inv.mpr hQ1
      _ = ENNReal.ofReal (p.K I.k ^ 2 * (Lx / Lr)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ = _ := by
          congr 1
          rw [← hratio]
          ring

/-- The rebased block of a retained descendant. -/
def zblock {j : Fin I.M} (x : I.Ret j) : Set ℝ :=
  interval (a.T I.k (I.depth j) - a.T I.k r) (relFin (I.block_sub x))

theorem Z_ok (hp : p.Valid) : I.Z.Ok := parentZoom_ok p hp a I.k r I.Q

theorem mem_zblock {j : Fin I.M} (x : I.Ret j) (t : ℝ) :
    t ∈ a.block I.k (I.depth j) x.1.1 ↔ (t - I.Z.t₀) / I.Z.q ∈ I.zblock x :=
  zoom_interval (I.block_sub x) t

theorem untime_mem_block {j : Fin I.M} (x : I.Ret j) (hp : p.Valid) {t : ℝ}
    (ht : t ∈ I.zblock x) : I.Z.untime t ∈ a.block I.k (I.depth j) x.1.1 := by
  rw [I.mem_zblock x]
  have := Zoom.time_untime (I.Z_ok hp) t
  simp only [Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time] at this
  rw [this]
  exact ht

/-- Rebased incidence events have the original mass. -/
theorem zoom_label_event {j : Fin I.M} (x : I.Ret j) (μ₀ : Measure (α × ℝ))
    {R : ℝ} (hats : ∀ j, a.AtlasAt p R I.k (I.depth j)) (hGm : MeasurableSet I.G)
    (Φ : α → Prop) (hΦ : MeasurableSet {w : α × ℝ | w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧
      w.2 ∈ I.zblock x ∧ Φ w.1}) :
    zoomLaw μ₀ I.keep I.Z.t₀ I.Z.q I.W {w | w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧
        w.2 ∈ I.zblock x ∧ Φ w.1} =
      I.W⁻¹ * μ₀ (I.keep ∩ {w | w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧
        w.2 ∈ a.block I.k (I.depth j) x.1.1 ∧ Φ w.1}) := by
  rw [zoomLaw_apply μ₀ (I.measurable_keep hats hGm) _ _ _ hΦ]
  congr 2
  ext w
  show (w ∈ I.keep ∧ (w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧ (w.2 - I.Z.t₀) / I.Z.q ∈ I.zblock x ∧
      Φ w.1)) ↔
    (w ∈ I.keep ∧ (w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧ w.2 ∈ a.block I.k (I.depth j) x.1.1 ∧
      Φ w.1))
  rw [← I.mem_zblock x w.2]

/-- Residual floor of a retained descendant in the zoomed instance. -/
theorem floor_zoom (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r) (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hnest : ∀ j j' : Fin I.M, j < j' → ∀ i : Fin (a.n I.k (I.depth j')),
      ∃ h : Fin (a.n I.k (I.depth j)),
        a.A I.k (I.depth j') i ⊆ a.A I.k (I.depth j) h ∧
          a.block I.k (I.depth j') i ⊆ a.block I.k (I.depth j) h)
    (hGm : MeasurableSet I.G) (hθ : 0 ≤ I.θ) {j : Fin I.M} (x : I.Ret j) :
    ENNReal.ofReal (I.θ * (1 / 4 : ℝ) ^ (j : ℕ) / 2 * (a.q I.k (I.depth j) / a.q I.k r)) *
        condPrior (a.nu I.k) (a.A I.k r I.Q) (a.A I.k (I.depth j) x.1.1) ≤
      zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W
        (a.B I.k (I.depth j) x.1.1 ×ˢ I.zblock x) := by
  have := hcommon.prob I.k
  have hqr := q_pos a I.k r
  have hqs := q_pos a I.k (I.depth j)
  have hev : a.B I.k (I.depth j) x.1.1 ×ˢ I.zblock x =
      {w | w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧ w.2 ∈ I.zblock x ∧ True} := by
    ext w; simp [mem_prod]
  have hmeas : MeasurableSet {w : α × ℝ | w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧
      w.2 ∈ I.zblock x ∧ True} := by
    rw [← hev]; exact ((hats j).measurable_B _).prod measurableSet_Icc
  rw [hev, I.zoom_label_event x _ hats hGm (fun _ => True) hmeas]
  have hset : {w : α × ℝ | w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧
      w.2 ∈ a.block I.k (I.depth j) x.1.1 ∧ True} = towerBox (⟨j, x.1⟩ : I.Label) := by
    ext w; simp [towerBox, mem_prod]
  rw [hset]
  have hfl := tower_retained_floor (μ := a.mu I.k) (G := I.G) (lv := I.lv) (X := I.box)
    (w := I.wt) (anc := I.anc) (M := I.M) hθ (fun y => y.1.2)
    (fun y j' hj' => tower_desc_budget (fun jj => hats jj) y j' hj')
    (tower_generic (hcommon.dom I.k) (fun jj => hats jj) hnest I.G) x.2
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
  have hW0 : I.W ≠ 0 := mul_ne_zero (by simp [hqr]) (hatr.prior_pos hp I.Q)
  have hWt : I.W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  calc ENNReal.ofReal (I.θ * (1 / 4 : ℝ) ^ (j : ℕ) / 2 * (a.q I.k (I.depth j) / a.q I.k r)) *
        condPrior (a.nu I.k) (a.A I.k r I.Q) (a.A I.k (I.depth j) x.1.1)
      = I.W⁻¹ * (ENNReal.ofReal (I.θ * (1 / 4 : ℝ) ^ (I.lv ⟨j, x.1⟩) / 2) *
          I.wt ⟨j, x.1⟩) := by
        rw [condPrior_apply _ _ _ ((hats j).measurable_A _),
          inter_eq_left.mpr (I.prior_sub x)]
        simp only [ZoomInput.W, ZoomInput.wt, towerWeight, ZoomInput.lv, towerLv]
        rw [ENNReal.mul_inv (Or.inl (by simp [hqr])) (Or.inl ENNReal.ofReal_ne_top)]
        have h4 : (0 : ℝ) ≤ I.θ * (1 / 4 : ℝ) ^ (j : ℕ) / 2 := by positivity
        rw [ENNReal.ofReal_mul h4, ENNReal.ofReal_div_of_pos hqr, ENNReal.div_eq_inv_mul]
        ring
    _ ≤ I.W⁻¹ * a.mu I.k (I.keep ∩ towerBox (⟨j, x.1⟩ : I.Label)) := by
        gcongr
        exact hfl

theorem time_untime' (hp : p.Valid) (t : ℝ) : (I.Z.untime t - I.Z.t₀) / I.Z.q = t := by
  have := Zoom.time_untime (I.Z_ok hp) t
  simpa only [Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time] using this

theorem untime_preimage_block (hp : p.Valid) {j : Fin I.M} (x : I.Ret j) :
    I.Z.untime ⁻¹' a.block I.k (I.depth j) x.1.1 = I.zblock x := by
  ext t
  simp only [mem_preimage]
  rw [I.mem_zblock x, I.time_untime' hp]

/-- The three box inequalities of a retained descendant in the zoomed chart. -/
theorem boxes_zoom (hp : p.Valid) {R : ℝ} {j : Fin I.M}
    (hats : a.AtlasAt p R I.k (I.depth j)) (x : I.Ret j) (hlam : I.lam ≠ 0)
    {l : α} (hl : l ∈ a.A I.k (I.depth j) x.1.1) {t : ℝ} (ht : t ∈ I.zblock x) :
    let b' := Zoom.nCoeff I.Z I.B I.lam (a.b I.k l)
    let c' := Zoom.zoomBox I.Z I.B I.lam (a.c I.k (I.depth j) x.1.1)
    |b' 0 + t * b' 3 - c' 0 - t * c' 1| ≤
        p.K I.k * (a.q I.k (I.depth j) / a.q I.k r) ∧
      |(b' 1 + t * b' 4) - c' 2 - t * c' 3 - c' 4 * (b' 0 + t * b' 3)| ≤
        p.K I.k * (a.q I.k (I.depth j) / a.q I.k r) *
          (narrow p I.k (I.depth j) / narrow p I.k r) / |I.lam| ∧
      |b' 4 - c' 3 - c' 4 * b' 3| ≤
        p.K I.k * (narrow p I.k (I.depth j) / narrow p I.k r) / |I.lam| := by
  intro b' c'
  have hZ := I.Z_ok hp
  have hq := q_pos a I.k r
  have hg := narrow_pos p hp I.k r
  have hut := I.untime_mem_block x hp ht
  have htt : I.Z.time (I.Z.untime t) = t := Zoom.time_untime hZ t
  have hZq : I.Z.q = a.q I.k r := rfl
  have hZw : I.Z.w = a.q I.k r * narrow p I.k r := rfl
  refine ⟨?_, ?_, ?_⟩
  · have := Zoom.major_box_zoom (Z := I.Z) (B := I.B) (lam := I.lam) hZ
      (hats.major_box x.1.1 hl hut)
    rw [htt, hZq, abs_of_pos hq] at this
    calc _ ≤ p.K I.k * a.q I.k (I.depth j) / a.q I.k r := this
      _ = _ := by ring
  · have := Zoom.transverse_box_zoom (Z := I.Z) (B := I.B) hZ hlam
      (hats.transverse_box x.1.1 hl hut)
    rw [htt, hZw, abs_mul, abs_of_pos (mul_pos hq hg)] at this
    calc _ ≤ p.K I.k * a.q I.k (I.depth j) * narrow p I.k (I.depth j) /
          (a.q I.k r * narrow p I.k r * |I.lam|) := this
      _ = _ := by field_simp
  · have := Zoom.strip_zoom (Z := I.Z) (B := I.B) hZ hlam (hats.strip x.1.1 hl)
    have hwq : I.Z.w / I.Z.q = narrow p I.k r := by rw [hZw, hZq]; field_simp
    rw [hwq, abs_mul, abs_of_pos hg] at this
    calc _ ≤ p.K I.k * narrow p I.k (I.depth j) / (narrow p I.k r * |I.lam|) := this
      _ = _ := by field_simp

/-- The pushed test of a retained descendant fits at the zoomed width. -/
theorem fits_zoom (hp : p.Valid) {R : ℝ} {j : Fin I.M}
    (hats : a.AtlasAt p R I.k (I.depth j)) (x : I.Ret j) (hlam : I.lam ≠ 0)
    {l : α} (hl : l ∈ a.B I.k (I.depth j) x.1.1) :
    Zoom.Fits (Zoom.nPush I.Z I.B I.lam (a.F I.k (I.depth j) x.1.1))
      (Zoom.nCoeff I.Z I.B I.lam (a.b I.k l)) (I.zblock x) (p.K I.k)
      (width p I.k (I.depth j) / width p I.k r) := by
  have hfit : Zoom.Fits (a.F I.k (I.depth j) x.1.1) (a.b I.k l) (a.block I.k (I.depth j) x.1.1)
      (p.K I.k) (width p I.k (I.depth j)) := by
    have := ((hats.2.2.2.2.1 x.1.1).2.2.2.2.2.2.1 l hl)
    intro t ht
    simpa [PreparedModel.fit, PreparedModel.x] using this t ht
  have := Zoom.nPush_fits (B := I.B) (I.Z_ok hp) (width_pos p hp I.k r) hlam hfit
  rw [I.untime_preimage_block hp x] at this
  exact this

theorem continuous_nCoeff : Continuous (Zoom.nCoeff I.Z I.B I.lam) := by
  unfold Zoom.nCoeff Submission.Lib.K4ContactNormalization.skewCoeff Zoom.coeff
    Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- Polynomial evaluations along normalized trajectories are measurable. -/
theorem measurable_eval_line (hb : Measurable (a.b I.k)) (Q : MvPolynomial (Fin 4) ℝ) :
    Measurable (fun z : α × ℝ =>
      MvPolynomial.eval (Submission.Lib.K4ContactNormalization.point
        (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) z.2) Q) := by
  have h1 : Measurable (fun z : α × ℝ => Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) :=
    I.continuous_nCoeff.measurable.comp (hb.comp measurable_fst)
  have h2 : Measurable (fun z : α × ℝ => Submission.Lib.K4ContactNormalization.point
      (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) z.2) := by
    unfold Submission.Lib.K4ContactNormalization.point
    apply Measurable.of_eval
    intro i
    have hc : ∀ e, Measurable (fun z : α × ℝ => Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1) e) :=
      fun e => (measurable_pi_apply e).comp h1
    fin_cases i <;> simp
    · exact measurable_snd
    · exact (hc 0).add (measurable_snd.mul (hc 3))
    · exact (hc 1).add (measurable_snd.mul (hc 4))
    · exact (hc 2).add (measurable_snd.mul (hc 5))
  exact (MvPolynomial.continuous_eval Q).measurable.comp h2

/-- Hidden-derivative lower bound of pushed tests, almost everywhere for the zoomed law. -/
theorem dlower_zoom (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hats : ∀ j, a.AtlasAt p R I.k (I.depth j)) (hGm : MeasurableSet I.G) (hlam : I.lam ≠ 0)
    {j : Fin I.M} (x : I.Ret j) :
    ∀ᵐ z ∂zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W,
      z.1 ∈ a.B I.k (I.depth j) x.1.1 → z.2 ∈ I.zblock x →
        (p.K I.k)⁻¹ ≤ |MvPolynomial.eval (Submission.Lib.K4ContactNormalization.point
          (Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1)) z.2)
            (MvPolynomial.pderiv 3 (Zoom.nPush I.Z I.B I.lam (a.F I.k (I.depth j) x.1.1)))| := by
  have hb := (hcommon I.k).1
  have horig := ((hats j).2.2.2.2.1 x.1.1).2.2.2.2.2.2.2
  apply ae_zoomLaw _ (I.measurable_keep hats hGm)
  · apply MeasurableSet.imp ((hats j).measurable_B _ |>.preimage measurable_fst)
    apply MeasurableSet.imp (measurableSet_Icc.preimage measurable_snd)
    exact measurableSet_le measurable_const
      ((I.measurable_eval_line hb _).abs)
  · filter_upwards [horig] with z hz _ hB hI
    have hI' : z.2 ∈ a.block I.k (I.depth j) x.1.1 := (I.mem_zblock x z.2).mpr hI
    have := hz hB hI'
    simp only [zoomTime]
    rw [Zoom.eval_pderiv_nPush (I.Z_ok hp) hlam]
    have hu : I.Z.untime ((z.2 - I.Z.t₀) / I.Z.q) = z.2 := by
      have := Zoom.untime_time (I.Z_ok hp) z.2
      simpa only [Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time] using this
    rw [hu]
    simpa [PreparedModel.x] using this

/-- Per-label palette bound in the zoomed chart. -/
theorem palette_zoom (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r) (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) {j : Fin I.M} (x : I.Ret j) {v : ℝ} (hv1 : R⁻¹ ≤ v)
    (hv2 : v ≤ R) (v₀ : ℤ) :
    zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W
        {z | z.1 ∈ a.B I.k (I.depth j) x.1.1 ∧ z.2 ∈ I.zblock x ∧
          ⌊Zoom.nCoeff I.Z I.B I.lam (a.b I.k z.1) 3 / p.N I.k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (p.K I.k * (a.q I.k (I.depth j) / a.q I.k r)) *
        condPrior (a.nu I.k) (a.A I.k r I.Q) (a.A I.k (I.depth j) x.1.1) *
          a.pi I.k {w | ⌊w / p.N I.k ^ (-v)⌋ = v₀} := by
  have := hcommon.prob I.k
  have hb := (hcommon I.k).1
  have hqr := q_pos a I.k r
  have hK : 0 ≤ p.K I.k := le_trans zero_le_one (hp.2.2.1.1 I.k)
  simp only [Zoom.nCoeff_three]
  have hmeas : MeasurableSet {z : α × ℝ | z.1 ∈ a.B I.k (I.depth j) x.1.1 ∧
      z.2 ∈ I.zblock x ∧ ⌊a.b I.k z.1 3 / p.N I.k ^ (-v)⌋ = v₀} := by
    refine ((hats j).measurable_B _ |>.preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter ?_)
    exact (measurableSet_singleton v₀).preimage
      (Int.measurable_floor.comp (((measurable_pi_apply 3).comp (hb.comp measurable_fst)).div_const _))
  rw [I.zoom_label_event x _ hats hGm (fun l => ⌊a.b I.k l 3 / p.N I.k ^ (-v)⌋ = v₀) hmeas]
  have horig := (hats j).2.2.2.2.2.2 x.1.1 v v₀ hv1 hv2
  have hW0 : I.W ≠ 0 := mul_ne_zero (by simp [hqr]) (hatr.prior_pos hp I.Q)
  calc I.W⁻¹ * a.mu I.k (I.keep ∩ {w | w.1 ∈ a.B I.k (I.depth j) x.1.1 ∧
        w.2 ∈ a.block I.k (I.depth j) x.1.1 ∧ ⌊a.b I.k w.1 3 / p.N I.k ^ (-v)⌋ = v₀})
      ≤ I.W⁻¹ * (ENNReal.ofReal (p.K I.k * a.q I.k (I.depth j)) *
          a.nu I.k (a.A I.k (I.depth j) x.1.1) * a.pi I.k {w | ⌊w / p.N I.k ^ (-v)⌋ = v₀}) := by
        gcongr
        exact (measure_mono inter_subset_right).trans horig
    _ = _ := by
        rw [condPrior_apply _ _ _ ((hats j).measurable_A _), inter_eq_left.mpr (I.prior_sub x)]
        simp only [ZoomInput.W]
        rw [ENNReal.mul_inv (Or.inl (by simp [hqr])) (Or.inl ENNReal.ofReal_ne_top),
          ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hK, ENNReal.ofReal_div_of_pos hqr,
          ENNReal.div_eq_inv_mul]
        ring

end ZoomInput

end

end Submission.Obl.k4_row_parent_contact_candidates
