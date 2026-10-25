/- Adapted from this LOT tree, o197, session x0692, Window/Witness.lean,
   branch snapshot 07a5fc04; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.Window.Ceiling
import Submission.Obl.k4_finite_width_output_exclusion.Interfaces

/-!
# Normalized laws of earlier witness charts

For an atlas `W` of earlier (true) charts, each chart `e` gives
* its normalization frame `chartFrame W e` (block `[j/2^T, (j+1)/2^T]`,
  center `c + t u`, spatial frame `Q`),
* the normalized point `wz W e q` of an incidence (hidden coordinate scaled by `B`),
* the normalized probability law `wlaw W e` of its selected incidences, with
  original weight `wwt W e = ω · (ν × dt)(F)`,
* its normalized test `wP W e` and normalized native polynomial `wS W e`.

`wlaw_base_le` bounds the projected density of `wlaw W e` by `64 κ³ N^τ` from
the observation density ceiling at the chart's own depth and the saturation
floor of the chart; `wlaw_ae` gives the normalized test bounds almost surely,
and `sum_wwt_le_one` sums the original weights using disjointness in blocks.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Lib.K4ChartLifting (Frame)

noncomputable section

variable {p : Data} {k : ℕ}

/-! ### Accessors of a valid problem -/

theorem valid_prob (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) :
    IsProbabilityMeasure (p.ν k γ) := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  exact ((hfmt k).2.2.2.1 γ).1

theorem valid_omega_nonneg (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) : 0 ≤ p.ω k γ := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  exact (hfmt k).2.1 γ

theorem valid_omega_sum (hp : Valid p) (k : ℕ) : ∑ γ, p.ω k γ = 1 := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  exact (hfmt k).2.2.1

theorem valid_P_degree (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) :
    (p.P k γ).totalDegree ≤ 2 := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  exact ((hfmt k).2.2.2.1 γ).2.2.2.2.1

theorem valid_E_meas (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) : MeasurableSet (p.E k γ) := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  exact ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.1

theorem valid_g_law (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) {r : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) :
    Measurable (p.g k γ r) ∧
      Measure.map (obs (p.B k γ) (δ (p.N k) r)) (selected p k γ) =
        (volume.prod Measure.count).withDensity (p.g k γ r) :=
  hp.2.2.2.2.2.2.2.2.2.1 k γ r hr hrL

theorem delta_zero (N : ℝ) : δ N 0 = 1 := by
  simp [δ]

/-! ### Witness data -/

/-- The normalization frame of one chart of an atlas. -/
def chartFrame (W : Atlas p k) (e : Fin W.C) : Frame where
  t₀ := ((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T
  q := 1 / (2 : ℝ) ^ W.T
  c := W.c e
  u := W.u e
  D := W.Q e

/-- The normalized point of an incidence in the frame of chart `e`. -/
def wz (W : Atlas p k) (e : Fin W.C) (q : Point) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (normPt (chartFrame W e) (p.B k (W.γ e)) (x q.1 q.2))

/-- The original selected mass of chart `e`. -/
def wmass (W : Atlas p k) (e : Fin W.C) : ENNReal := priorMass p k (W.γ e) (W.F e)

/-- The normalized probability law of chart `e`. -/
def wlaw (W : Atlas p k) (e : Fin W.C) : Measure (EuclideanSpace ℝ (Fin 4)) :=
  (wmass W e)⁻¹ • Measure.map (wz W e) ((priorMass p k (W.γ e)).restrict (W.F e))

/-- The original weight of chart `e`. -/
def wwt (W : Atlas p k) (e : Fin W.C) : ENNReal :=
  ENNReal.ofReal (p.ω k (W.γ e)) * wmass W e

/-- The normalized test of chart `e`. -/
def wP (W : Atlas p k) (e : Fin W.C) : MvPolynomial (Fin 4) ℝ :=
  normalizedTest (chartFrame W e) (p.B k (W.γ e)) (W.R e)

/-- The normalized native polynomial of the world of chart `e`. -/
def wS (W : Atlas p k) (e : Fin W.C) : MvPolynomial (Fin 4) ℝ :=
  normalizedTest (chartFrame W e) (p.B k (W.γ e)) (p.P k (W.γ e))

theorem measurable_wz (W : Atlas p k) (e : Fin W.C) : Measurable (wz W e) := by
  have hx : Measurable (fun q : Point => x q.1 q.2) := by
    unfold x
    fun_prop
  exact (PiLp.continuous_toLp 2 _).measurable.comp
    ((continuous_normPt _ _).measurable.comp hx)

theorem base4_wz (W : Atlas p k) (e : Fin W.C) (q : Point) :
    base4 (wz W e q) = (chartFrame W e).obsBase (basePt q) := by
  ext i
  fin_cases i <;> simp [base4, wz, normPt, Frame.obsBase, basePt, x, chartFrame]

theorem wz_apply (W : Atlas p k) (e : Fin W.C) (q : Point) :
    (fun i => wz W e q i) = normPt (chartFrame W e) (p.B k (W.γ e)) (x q.1 q.2) := rfl

theorem measurable_base4 : Measurable base4 := by
  unfold base4
  fun_prop

/-! ### The norm of a three-vector -/

theorem norm_vec3_le (a b c : ℝ) :
    ‖(WithLp.toLp 2 ![a, b, c] : EuclideanSpace ℝ (Fin 3))‖ ≤
      |a| + ‖(WithLp.toLp 2 ![b, c] : EuclideanSpace ℝ (Fin 2))‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, Real.norm_eq_abs,
    sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hs : 0 ≤ Real.sqrt (b ^ 2 + c ^ 2) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (b ^ 2 + c ^ 2) ^ 2 = b ^ 2 + c ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, sq_abs a]

/-! ### Chart conditions at one incidence -/

/-- The normalized coordinates of an incidence of a chart lie in the box of
size `1 + κ`. -/
theorem norm_base4_wz_le (W : Atlas p k) (e : Fin W.C) {κ : ℝ} (q : Point)
    (hq : q.2 ∈ Icc (((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T) ((((W.j e : ℕ) : ℝ) + 1) / (2 : ℝ) ^ W.T))
    (hfit : ‖Matrix.toEuclideanLin (W.Q e)⁻¹ (y q.1 q.2 - W.c e - q.2 • W.u e)‖ ≤ κ) :
    ‖base4 (wz W e q)‖ ≤ 1 + κ := by
  rw [base4_wz]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ W.T := by positivity
  have ht0 : 0 ≤ (q.2 - ((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T) / (1 / (2 : ℝ) ^ W.T) := by
    apply div_nonneg _ (by positivity)
    linarith [hq.1]
  have ht1 : (q.2 - ((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T) / (1 / (2 : ℝ) ^ W.T) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := hq.2
    rw [add_div] at this
    linarith
  have hlin : (WithLp.toLp 2 ![(W.Q e)⁻¹ 0 0 * (x q.1 q.2 1 - W.c e 0 - q.2 * W.u e 0) +
        (W.Q e)⁻¹ 0 1 * (x q.1 q.2 2 - W.c e 1 - q.2 * W.u e 1),
      (W.Q e)⁻¹ 1 0 * (x q.1 q.2 1 - W.c e 0 - q.2 * W.u e 0) +
        (W.Q e)⁻¹ 1 1 * (x q.1 q.2 2 - W.c e 1 - q.2 * W.u e 1)] :
        EuclideanSpace ℝ (Fin 2)) =
      Matrix.toEuclideanLin (W.Q e)⁻¹ (y q.1 q.2 - W.c e - q.2 • W.u e) := by
    ext i
    fin_cases i <;>
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, y, x, Matrix.vecHead, Matrix.vecTail]
  have h := norm_vec3_le ((q.2 - ((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T) / (1 / (2 : ℝ) ^ W.T))
    ((W.Q e)⁻¹ 0 0 * (x q.1 q.2 1 - W.c e 0 - q.2 * W.u e 0) +
        (W.Q e)⁻¹ 0 1 * (x q.1 q.2 2 - W.c e 1 - q.2 * W.u e 1))
    ((W.Q e)⁻¹ 1 0 * (x q.1 q.2 1 - W.c e 0 - q.2 * W.u e 0) +
        (W.Q e)⁻¹ 1 1 * (x q.1 q.2 2 - W.c e 1 - q.2 * W.u e 1))
  rw [hlin, abs_of_nonneg ht0] at h
  have hb : (chartFrame W e).obsBase (basePt q) = WithLp.toLp 2
      ![(q.2 - ((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T) / (1 / (2 : ℝ) ^ W.T),
        (W.Q e)⁻¹ 0 0 * (x q.1 q.2 1 - W.c e 0 - q.2 * W.u e 0) +
          (W.Q e)⁻¹ 0 1 * (x q.1 q.2 2 - W.c e 1 - q.2 * W.u e 1),
        (W.Q e)⁻¹ 1 0 * (x q.1 q.2 1 - W.c e 0 - q.2 * W.u e 0) +
          (W.Q e)⁻¹ 1 1 * (x q.1 q.2 2 - W.c e 1 - q.2 * W.u e 1)] := by
    ext i
    fin_cases i <;> simp [Frame.obsBase, basePt, chartFrame, x]
  rw [hb]
  linarith

/-! ### Scalar measure inequalities -/

theorem smul_measure_le_smul_left {α : Type*} [MeasurableSpace α] {a b : ENNReal}
    (h : a ≤ b) (μ : Measure α) : a • μ ≤ b • μ := by
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left h _

theorem smul_measure_le_smul_right {α : Type*} [MeasurableSpace α] (a : ENNReal)
    {μ ν : Measure α} (h : μ ≤ ν) : a • μ ≤ a • ν := by
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (h s) _

/-! ### The chart conditions of a witness chart -/

/-- The chart conditions of chart `e` of a witness atlas at depth `r`. -/
def WChart (p : Data) (k : ℕ) (W : Atlas p k) (M D : ℕ) (κ r : ℝ) (e : Fin W.C) : Prop :=
  ∃ ex : Prop, chart (p.N k) M D κ W.T ((W.j e : ℕ) : ℝ) r (p.B k (W.γ e)) (p.E k (W.γ e))
    (W.c e) (W.u e) (W.Q e) (W.R e) (W.A e) (W.F e) ex

section ChartFacts

variable {W : Atlas p k} {M D : ℕ} {κ r : ℝ} {e : Fin W.C}

theorem WChart.det_ne (h : WChart p k W M D κ r e) : (W.Q e).det ≠ 0 := by
  obtain ⟨ex, h⟩ := h
  exact h.1

theorem WChart.l1_le (h : WChart p k W M D κ r e) :
    (∑ i : Fin 2, ∑ j : Fin 2, |W.Q e i j|) ≤ κ / (2 : ℝ) ^ W.T := by
  obtain ⟨ex, h⟩ := h
  exact h.2.2.2.1

theorem WChart.R_degree (h : WChart p k W M D κ r e) : (W.R e).totalDegree ≤ 2 := by
  obtain ⟨ex, h⟩ := h
  exact h.2.2.2.2.1

theorem WChart.measA (h : WChart p k W M D κ r e) : MeasurableSet (W.A e) := by
  obtain ⟨ex, h⟩ := h
  exact h.2.2.2.2.2.2.1

theorem WChart.measF (h : WChart p k W M D κ r e) : MeasurableSet (W.F e) := by
  obtain ⟨ex, h⟩ := h
  exact h.2.2.2.2.2.2.2.1

theorem WChart.fit (h : WChart p k W M D κ r e) {l : Line} (hl : l ∈ W.A e) {t : ℝ}
    (ht : t ∈ Icc (((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T) ((((W.j e : ℕ) : ℝ) + 1) / (2 : ℝ) ^ W.T)) :
    ‖Matrix.toEuclideanLin (W.Q e)⁻¹ (y l t - W.c e - t • W.u e)‖ ≤ κ ∧
      |MvPolynomial.eval (x l t) (W.R e)| ≤ κ * δ (p.N k) r ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (W.R e))| ≤
        κ * p.B k (W.γ e) ∧
      |MvPolynomial.eval (x l t)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (W.R e)))| ≤
        κ * p.B k (W.γ e) ^ 2 / δ (p.N k) r := by
  obtain ⟨ex, h⟩ := h
  exact (h.2.2.2.2.2.2.2.2.2.1 l hl).2.2 t ht

theorem WChart.sel (h : WChart p k W M D κ r e) {q : Point} (hq : q ∈ W.F e) :
    q ∈ p.E k (W.γ e) ∧ q.1 ∈ W.A e ∧
      q.2 ∈ Icc (((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T) ((((W.j e : ℕ) : ℝ) + 1) / (2 : ℝ) ^ W.T) ∧
      p.B k (W.γ e) / κ ≤
        |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv (3 : Fin 4) (W.R e))| := by
  obtain ⟨ex, h⟩ := h
  exact h.2.2.2.2.2.2.2.2.2.2.1 q hq

end ChartFacts

theorem delta_pos (N r : ℝ) : 0 < δ N r := by
  unfold δ
  positivity

/-! ### The normalized law -/

theorem wmass_ne_top (hp : Valid p) {W : Atlas p k} {e : Fin W.C} {M D : ℕ} {κ r : ℝ}
    (hW : WChart p k W M D κ r e) : wmass W e ≠ ⊤ := by
  have := valid_prob hp k (W.γ e)
  have hsub : W.F e ⊆ Set.univ ×ˢ Icc (((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T)
      ((((W.j e : ℕ) : ℝ) + 1) / (2 : ℝ) ^ W.T) := fun q hq => ⟨trivial, (hW.sel hq).2.2.1⟩
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [priorMass, Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

theorem wmass_pos {W : Atlas p k} {e : Fin W.C} {κ r : ℝ} (hκ : 0 < κ) (hdet : (W.Q e).det ≠ 0)
    (hfloor : ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| / ((2 : ℝ) ^ W.T * κ)) ≤
      wmass W e) (hN : 0 < p.N k) : 0 < wmass W e := by
  refine lt_of_lt_of_le ?_ hfloor
  rw [ENNReal.ofReal_pos]
  have := abs_pos.mpr hdet
  positivity

theorem wlaw_prob (hp : Valid p) {W : Atlas p k} {e : Fin W.C} {M D : ℕ} {κ r : ℝ}
    (hW : WChart p k W M D κ r e) (hpos : 0 < wmass W e) :
    IsProbabilityMeasure (wlaw W e) := by
  constructor
  rw [wlaw, Measure.smul_apply, Measure.map_apply (measurable_wz W e) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' (wmass_ne_top hp hW)

/-- **Projected density of a normalized witness law.**  The observation density
ceiling at the chart's own depth, the `64 κ²` hidden bins of its test, the
Jacobian `q |det Q|` of normalization and the saturation floor of the chart
give the bounded projected density `64 κ³ N^τ`. -/
theorem wlaw_base_le (hp : Valid p) {W : Atlas p k} {e : Fin W.C} {M D : ℕ} {κ r τ : ℝ}
    (hκ : 1 ≤ κ) (hr : 0 ≤ r) (hrL : r ≤ p.L) (hW : WChart p k W M D κ r e)
    (hfloor : ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| / ((2 : ℝ) ^ W.T * κ)) ≤
      wmass W e)
    (hgood : ∀ q ∈ W.F e, p.g k (W.γ e) r (obs (p.B k (W.γ e)) (δ (p.N k) r) q) ≤
      ENNReal.ofReal (p.N k ^ (-p.f r + τ))) :
    Measure.map base4 (wlaw W e) ≤ ENNReal.ofReal (64 * κ ^ 3 * p.N k ^ τ) • volume := by
  set γ := W.γ e
  set B := p.B k γ
  have hB : 0 < B := hp.B_pos k γ
  have hN : 0 < p.N k := hp.scale_pos k
  have hκ0 : 0 < κ := by linarith
  have hdet : (W.Q e).det ≠ 0 := hW.det_ne
  have hF : MeasurableSet (W.F e) := hW.measF
  have hFE : W.F e ⊆ p.E k γ := fun q hq => (hW.sel hq).1
  set ρ : Measure Point := (priorMass p k γ).restrict (W.F e) with hρdef
  have hρμ : ρ ≤ selected p k γ := Measure.restrict_mono hFE le_rfl
  obtain ⟨hgm, hlaw⟩ := valid_g_law hp k γ hr hrL
  have hceil := chart_depth_base_ceiling (selected p k γ) ρ hρμ hκ (delta_pos (p.N k) r) hB
    (t₀ := ((W.j e : ℕ) : ℝ) / (2 : ℝ) ^ W.T) (t₁ := (((W.j e : ℕ) : ℝ) + 1) / (2 : ℝ) ^ W.T)
    (W.c e) (W.u e) (W.Q e) (W.R e) hW.R_degree (p.g k γ r) hgm hlaw
    (ENNReal.ofReal (p.N k ^ (-p.f r + τ))) (by
      rw [hρdef]
      refine ae_restrict_of_forall_mem hF fun q hq => ?_
      obtain ⟨-, hqA, hqt, hfl⟩ := hW.sel hq
      obtain ⟨h1, h2, h3, h4⟩ := hW.fit hqA hqt
      exact ⟨hqt, h1, h2, h3, h4, hfl, hgood q hq⟩)
  -- transport through the normalization
  set F := chartFrame W e
  have hq : F.q ≠ 0 := by simp [F, chartFrame]
  have hD : IsUnit F.D.det := isUnit_iff_ne_zero.mpr hdet
  have hcomp : base4 ∘ wz W e = F.obsBase ∘ basePt := funext (base4_wz W e)
  have hmap : Measure.map base4 (wlaw W e) =
      (wmass W e)⁻¹ • Measure.map F.obsBase (Measure.map basePt ρ) := by
    rw [wlaw, Measure.map_smul _ measurable_base4.aemeasurable,
      Measure.map_map measurable_base4 (measurable_wz W e), hcomp,
      ← Measure.map_map (Frame.measurable_obsBase F) measurable_basePt]
  rw [hmap]
  have hJ := Frame.map_obsBase_volume F hq hD
  calc (wmass W e)⁻¹ • Measure.map F.obsBase (Measure.map basePt ρ)
      ≤ (wmass W e)⁻¹ • Measure.map F.obsBase
          ((ENNReal.ofReal (p.N k ^ (-p.f r + τ)) * ENNReal.ofReal (64 * κ ^ 2)) • volume) :=
        smul_measure_le_smul_right _ (Measure.map_mono hceil (Frame.measurable_obsBase F))
    _ = ((wmass W e)⁻¹ * (ENNReal.ofReal (p.N k ^ (-p.f r + τ)) * ENNReal.ofReal (64 * κ ^ 2)) *
          ENNReal.ofReal |F.obsMatrix.det|⁻¹) • volume := by
        rw [Measure.map_smul _ (Frame.measurable_obsBase F).aemeasurable, hJ, smul_smul,
          smul_smul]
    _ ≤ ENNReal.ofReal (64 * κ ^ 3 * p.N k ^ τ) • volume := by
        apply smul_measure_le_smul_left
        set F₀ : ℝ := p.N k ^ (-p.f r) * |(W.Q e).det| / ((2 : ℝ) ^ W.T * κ) with hF₀
        have hF₀pos : 0 < F₀ := by
          have := abs_pos.mpr hdet
          positivity
        have hinv : (wmass W e)⁻¹ ≤ ENNReal.ofReal F₀⁻¹ := by
          rw [ENNReal.ofReal_inv_of_pos hF₀pos]
          exact ENNReal.inv_le_inv.mpr hfloor
        have hdetJ : |F.obsMatrix.det|⁻¹ = (1 / (2 : ℝ) ^ W.T) * |(W.Q e).det| := by
          rw [Frame.det_obsMatrix, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
          simp only [F, chartFrame, abs_mul, abs_inv]
          rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ W.T), mul_inv, inv_inv, inv_inv]
        calc (wmass W e)⁻¹ * (ENNReal.ofReal (p.N k ^ (-p.f r + τ)) * ENNReal.ofReal (64 * κ ^ 2)) *
              ENNReal.ofReal |F.obsMatrix.det|⁻¹
            ≤ ENNReal.ofReal F₀⁻¹ * (ENNReal.ofReal (p.N k ^ (-p.f r + τ)) *
                ENNReal.ofReal (64 * κ ^ 2)) * ENNReal.ofReal |F.obsMatrix.det|⁻¹ := by
              gcongr
          _ = ENNReal.ofReal (F₀⁻¹ * (p.N k ^ (-p.f r + τ) * (64 * κ ^ 2)) *
                |F.obsMatrix.det|⁻¹) := by
              conv_rhs => rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (64 * κ ^ 3 * p.N k ^ τ) := by
              congr 1
              rw [hdetJ, hF₀, Real.rpow_add hN]
              have := abs_pos.mpr hdet
              have h2 : (0 : ℝ) < (2 : ℝ) ^ W.T := by positivity
              have hNf : 0 < p.N k ^ (-p.f r) := Real.rpow_pos_of_pos hN _
              field_simp

theorem continuous_evalE4 (P : MvPolynomial (Fin 4) ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin 4) => MvPolynomial.eval (fun i => z i) P) :=
  (MvPolynomial.continuous_eval P).comp (PiLp.continuous_ofLp 2 _)

theorem measurableSet_abs_le (P : MvPolynomial (Fin 4) ℝ) (c : ℝ) :
    MeasurableSet {z : EuclideanSpace ℝ (Fin 4) | |MvPolynomial.eval (fun i => z i) P| ≤ c} :=
  measurableSet_le (continuous_evalE4 P).abs.measurable measurable_const

theorem measurableSet_le_abs (P : MvPolynomial (Fin 4) ℝ) (c : ℝ) :
    MeasurableSet {z : EuclideanSpace ℝ (Fin 4) | c ≤ |MvPolynomial.eval (fun i => z i) P|} :=
  measurableSet_le measurable_const (continuous_evalE4 P).abs.measurable

/-- **Normalized test bounds.**  Almost surely under the normalized law of a
witness chart, the normalized point lies in the box of size `1 + κ`, the
normalized test has value at most `κ δ`, hidden derivative between `κ⁻¹` and `κ`
and second hidden derivative at most `κ / δ`, and the normalized native
polynomial and its two hidden derivatives are at most `K`. -/
theorem wlaw_ae (hp : Valid p) {W : Atlas p k} {e : Fin W.C} {M D : ℕ} {κ r K : ℝ}
    (hW : WChart p k W M D κ r e)
    (hnat : ∀ q ∈ W.F e, |MvPolynomial.eval (x q.1 q.2) (p.P k (W.γ e))| ≤ K ∧
      |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e)))| ≤
        K * p.B k (W.γ e) ∧
      |MvPolynomial.eval (x q.1 q.2)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (p.P k (W.γ e))))| ≤
        K * p.B k (W.γ e) ^ 2) :
    ∀ᵐ z ∂wlaw W e, ‖base4 z‖ ≤ 1 + κ ∧
      |MvPolynomial.eval (fun i => z i) (wP W e)| ≤ κ * δ (p.N k) r ∧
      κ⁻¹ ≤ |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (wP W e))| ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (wP W e))| ≤ κ ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (wP W e)))| ≤
        κ / δ (p.N k) r ∧
      |MvPolynomial.eval (fun i => z i) (wS W e)| ≤ K ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (wS W e))| ≤ K ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (wS W e)))| ≤ K := by
  apply Measure.ae_smul_measure
  have hset : MeasurableSet {z : EuclideanSpace ℝ (Fin 4) | ‖base4 z‖ ≤ 1 + κ ∧
      |MvPolynomial.eval (fun i => z i) (wP W e)| ≤ κ * δ (p.N k) r ∧
      κ⁻¹ ≤ |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (wP W e))| ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (wP W e))| ≤ κ ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (wP W e)))| ≤
        κ / δ (p.N k) r ∧
      |MvPolynomial.eval (fun i => z i) (wS W e)| ≤ K ∧
      |MvPolynomial.eval (fun i => z i) (MvPolynomial.pderiv (3 : Fin 4) (wS W e))| ≤ K ∧
      |MvPolynomial.eval (fun i => z i)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (wS W e)))| ≤ K} :=
    (measurableSet_le (continuous_norm.comp (by unfold base4; fun_prop)).measurable
      measurable_const).inter
      ((measurableSet_abs_le _ _).inter ((measurableSet_le_abs _ _).inter
        ((measurableSet_abs_le _ _).inter ((measurableSet_abs_le _ _).inter
          ((measurableSet_abs_le _ _).inter ((measurableSet_abs_le _ _).inter
            (measurableSet_abs_le _ _)))))))
  rw [ae_map_iff (measurable_wz W e).aemeasurable hset]
  refine ae_restrict_of_forall_mem hW.measF fun q hq => ?_
  obtain ⟨-, hqA, hqt, hfl⟩ := hW.sel hq
  obtain ⟨hfit, hR0, hR1, hR2⟩ := hW.fit hqA hqt
  obtain ⟨hP0, hP1, hP2⟩ := hnat q hq
  have hB : 0 < p.B k (W.γ e) := hp.B_pos k (W.γ e)
  have hqF : (chartFrame W e).q ≠ 0 := by simp [chartFrame]
  have hD : IsUnit (chartFrame W e).D.det := isUnit_iff_ne_zero.mpr hW.det_ne
  obtain ⟨eR0, eR1, eR2⟩ := normalizedTest_bounds (chartFrame W e) hqF hD hB (W.R e) (x q.1 q.2)
  obtain ⟨eP0, eP1, eP2⟩ :=
    normalizedTest_bounds (chartFrame W e) hqF hD hB (p.P k (W.γ e)) (x q.1 q.2)
  have hδ : 0 < δ (p.N k) r := delta_pos _ _
  simp only [Set.mem_ofPred_eq, wz_apply, wP, wS, eR0, eR1, eR2, eP0, eP1, eP2]
  refine ⟨norm_base4_wz_le W e q hqt hfit, hR0, ?_, ?_, ?_, hP0, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hB, le_div_iff₀ hB]
    calc κ⁻¹ * p.B k (W.γ e) = p.B k (W.γ e) / κ := by ring
      _ ≤ _ := hfl
  · rw [abs_div, abs_of_pos hB, div_le_iff₀ hB]
    exact hR1
  · rw [abs_div, abs_of_pos (pow_pos hB 2), div_le_iff₀ (pow_pos hB 2)]
    calc _ ≤ κ * p.B k (W.γ e) ^ 2 / δ (p.N k) r := hR2
      _ = κ / δ (p.N k) r * p.B k (W.γ e) ^ 2 := by ring
  · rw [abs_div, abs_of_pos hB, div_le_iff₀ hB]
    exact hP1
  · rw [abs_div, abs_of_pos (pow_pos hB 2), div_le_iff₀ (pow_pos hB 2)]
    exact hP2

theorem totalDegree_wP_le {W : Atlas p k} {e : Fin W.C} {M D : ℕ} {κ r : ℝ}
    (hW : WChart p k W M D κ r e) : (wP W e).totalDegree ≤ 2 :=
  (totalDegree_normalizedTest_le _ _ _).trans hW.R_degree

theorem totalDegree_wS_le (hp : Valid p) (W : Atlas p k) (e : Fin W.C) :
    (wS W e).totalDegree ≤ 2 :=
  (totalDegree_normalizedTest_le _ _ _).trans (valid_P_degree hp k (W.γ e))

/-- **Original weights of witness charts sum to at most one**, by disjointness of
charts of one world within one time block. -/
theorem sum_wwt_le_one (hp : Valid p) (W : Atlas p k) {M D : ℕ} {κ r : ℝ}
    (hW : ∀ e, WChart p k W M D κ r e)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' → Disjoint (W.A e) (W.A e')) :
    ∑ e, wwt W e ≤ 1 := by
  classical
  have hblock : ∀ γ : Fin (p.W k), ∀ j : Fin (2 ^ W.T),
      ∑ e ∈ (Finset.univ.filter (fun e => W.γ e = γ)).filter (fun e => W.j e = j), wmass W e ≤
        ENNReal.ofReal (1 / (2 : ℝ) ^ W.T) := by
    intro γ j
    set S := (Finset.univ.filter (fun e => W.γ e = γ)).filter (fun e => W.j e = j)
    have hS : ∀ e ∈ S, W.γ e = γ ∧ W.j e = j := by
      intro e he
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact he
    have hpd : Set.PairwiseDisjoint (↑S) W.F := by
      intro e he e' he' hne
      obtain ⟨hγ, hj⟩ := hS e he
      obtain ⟨hγ', hj'⟩ := hS e' he'
      have hA := hdisj e e' hne (hγ.trans hγ'.symm) (hj.trans hj'.symm)
      refine Set.disjoint_left.mpr fun q hq hq' => ?_
      exact Set.disjoint_left.mp hA ((hW e).sel hq).2.1 ((hW e').sel hq').2.1
    have hsum : ∑ e ∈ S, wmass W e = priorMass p k γ (⋃ e ∈ S, W.F e) := by
      rw [measure_biUnion_finset hpd (fun e _ => (hW e).measF)]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [wmass, (hS e he).1]
    rw [hsum]
    have hsub : (⋃ e ∈ S, W.F e) ⊆ Set.univ ×ˢ
        Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ W.T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ W.T) := by
      intro q hq
      simp only [Set.mem_iUnion] at hq
      obtain ⟨e, he, hqe⟩ := hq
      refine ⟨trivial, ?_⟩
      have := ((hW e).sel hqe).2.2.1
      rwa [(hS e he).2] at this
    have := valid_prob hp k γ
    calc priorMass p k γ (⋃ e ∈ S, W.F e)
        ≤ priorMass p k γ (Set.univ ×ˢ
            Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ W.T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ W.T)) :=
          measure_mono hsub
      _ = ENNReal.ofReal (1 / (2 : ℝ) ^ W.T) := by
          rw [priorMass, Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc]
          congr 1
          ring
  have hworld : ∀ γ : Fin (p.W k),
      ∑ e ∈ Finset.univ.filter (fun e => W.γ e = γ), wmass W e ≤ 1 := by
    intro γ
    rw [← Finset.sum_fiberwise (Finset.univ.filter (fun e => W.γ e = γ)) W.j]
    calc ∑ j : Fin (2 ^ W.T), ∑ e ∈ (Finset.univ.filter (fun e => W.γ e = γ)).filter
            (fun e => W.j e = j), wmass W e
        ≤ ∑ _j : Fin (2 ^ W.T), ENNReal.ofReal (1 / (2 : ℝ) ^ W.T) :=
          Finset.sum_le_sum fun j _ => hblock γ j
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          push_cast
          rw [mul_one_div_cancel (by positivity), ENNReal.ofReal_one]
  calc ∑ e, wwt W e
      = ∑ γ : Fin (p.W k), ∑ e ∈ Finset.univ.filter (fun e => W.γ e = γ),
          ENNReal.ofReal (p.ω k γ) * wmass W e := by
        rw [← Finset.sum_fiberwise Finset.univ W.γ]
        refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun e he => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        rw [wwt, he]
    _ = ∑ γ : Fin (p.W k), ENNReal.ofReal (p.ω k γ) *
          ∑ e ∈ Finset.univ.filter (fun e => W.γ e = γ), wmass W e := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ γ : Fin (p.W k), ENNReal.ofReal (p.ω k γ) * 1 :=
        Finset.sum_le_sum fun γ _ => by gcongr; exact hworld γ
    _ = 1 := by
        simp only [mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => valid_omega_nonneg hp k γ),
          valid_omega_sum hp k, ENNReal.ofReal_one]

end
end Submission.Obl.k4_raw_localized_native_systems.Window
