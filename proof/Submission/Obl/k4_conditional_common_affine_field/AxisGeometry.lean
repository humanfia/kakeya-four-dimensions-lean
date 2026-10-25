import Submission.Obl.k4_conditional_common_affine_field.Geometry
import Submission.Obl.k4_conditional_common_affine_field.ChartMenus
import Submission.Lib.K4ScalarCoreTools.Finalization.PolynomialBinSampling

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open Submission.Lib.K4ScalarCoreTools.Finalization

/-- The intercept of the selected axis through an actual base point. -/
def axisIntercept {α : Type*} (b v : α → ℝ) (w : ℝ) (p : α × ℝ) : ℝ :=
  b p.1+p.2*(v p.1-w)

theorem measurable_axisIntercept {α : Type*} [MeasurableSpace α]
    {b v : α → ℝ} (hb : Measurable b) (hv : Measurable v) (w : ℝ) :
    Measurable (axisIntercept b v w) :=
  (hb.comp measurable_fst).add (measurable_snd.mul ((hv.comp measurable_fst).sub_const w))

theorem axisIntercept_eq_base {α : Type*} (b v : α → ℝ) (v₀ w : ℝ) (p : α × ℝ) :
    axisIntercept b v w p = base b v v₀ p 1-p.2*(w-v₀) := by
  dsimp [axisIntercept,base]
  ring

theorem axisIntercept_sub {α : Type*} (b v : α → ℝ) (w₁ w₂ : ℝ) (p : α × ℝ) :
    axisIntercept b v w₁ p-axisIntercept b v w₂ p = p.2*(w₂-w₁) := by
  dsimp [axisIntercept]
  ring

theorem axisIntercept_bound {α : Type*} (b v : α → ℝ) (w K H : ℝ)
    (hH : 0 ≤ H) (hw : |w| ≤ H) {p : α × ℝ}
    (hp : p.2 ∈ Icc (0 : ℝ) 1) (hbv : |b p.1|+|v p.1| ≤ K) :
    |axisIntercept b v w p| ≤ K+H := by
  have ht : |p.2| ≤ 1 := by rw [abs_of_nonneg hp.1]; exact hp.2
  calc
    _ ≤ |b p.1| + |p.2| * |v p.1-w| := by
      simpa only [axisIntercept,abs_mul] using abs_add_le (b p.1) (p.2*(v p.1-w))
    _ ≤ |b p.1|+1*(|v p.1|+|w|) := by gcongr; exact abs_sub _ _
    _ ≤ K+H := by linarith

/-- Within one fine state, a fixed velocity witness's intercept lies near the
selected-axis intercept. -/
theorem witness_axis_intercept {α : Type*} (b v : α → ℝ)
    (v₀ δ e H w : ℝ) (f : α × ℝ → Fin 2 → ℝ)
    (hδ : 0 < δ) (he : 0 < e) (hw : |w-v₀| ≤ H)
    {p q : α × ℝ} (hq : q.2 ∈ Icc (0 : ℝ) 1)
    (hstate : fineState b v v₀ δ e f q = fineState b v v₀ δ e f p)
    (hvel : |v q.1-w| ≤ δ) :
    |b q.1-axisIntercept b v w p| ≤ (H+2)*δ := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hw
  have htq : |q.2| ≤ 1 := by rw [abs_of_nonneg hq.1]; exact hq.2
  have hbounds := (equal_fineState_bounds b v v₀ δ e f hδ he hstate).1
  have htime : |p.2-q.2| ≤ δ := by
    have h := hbounds 0
    change |q.2-p.2| ≤ δ at h
    simpa only [abs_sub_comm] using h
  have hid : b q.1-axisIntercept b v w p =
      (base b v v₀ q 1-base b v v₀ p 1)+(p.2-q.2)*(w-v₀)+q.2*(w-v q.1) := by
    dsimp [axisIntercept,base]
    ring
  have hmul : |(p.2-q.2)*(w-v₀)| ≤ δ*H := by
    rw [abs_mul]
    exact mul_le_mul htime hw (abs_nonneg _) hδ.le
  have hmul' : |q.2*(w-v q.1)| ≤ δ := by
    rw [abs_mul,abs_sub_comm]
    exact (mul_le_mul htq hvel (abs_nonneg _) (by norm_num)).trans_eq (one_mul δ)
  rw [hid]
  have h := (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (hbounds 1) hmul)) hmul')
  nlinarith

/-- The actual source value fits one original chart option in the menu attached
to its selected-axis intercept bin. -/
theorem axis_menu_has_predictor {α : Type*} (b v : α → ℝ)
    (v₀ δ e χb χv ω H w : ℝ) (f : α × ℝ → Fin 2 → ℝ)
    (L : ℤ × ℤ → Finset (Fin 3 → ℝ))
    (hδ : 0 < δ) (he : 0 < e) (hχb : 0 < χb) (hχv : 0 < χv)
    (hH : 1 ≤ H) (hδω : δ ≤ ω) (hδe : δ ≤ e)
    (hχbω : (H+3)*ω ≤ χb) (hχvδ : δ ≤ χv) (hw : |w-v₀| ≤ H)
    {p q : α × ℝ} (hq : q.2 ∈ Icc (0 : ℝ) 1)
    (hstate : fineState b v v₀ δ e f q = fineState b v v₀ δ e f p)
    (hvel : |v q.1-w| ≤ δ)
    (hcoeff : ∀ q, ∀ a ∈ L q, ∀ i, |a i| ≤ H)
    (hfit : ∃ a ∈ L (⌊b q.1/χb⌋,⌊v q.1/χv⌋),
      |f q 0-a 0-a 1*q.2| ≤ H*e ∧ |f q 1-a 2| ≤ H*e) :
    ∃ a ∈ chartMenu L χb χv (ω*(⌊axisIntercept b v w p/ω⌋ : ℝ)) w,
      |f p 0-a 0-a 1*p.2| ≤ 3*H*e ∧ |f p 1-a 2| ≤ 3*H*e := by
  obtain ⟨a, ha, h₀, h₁⟩ := hfit
  have hH0 : 0 ≤ H := by linarith
  have hω : 0 < ω := hδ.trans_le hδω
  have hnear := witness_axis_intercept b v v₀ δ e H w f hδ he hw hq hstate hvel
  have hbin := floor_scaled_error hω (axisIntercept b v w p)
  have hb : |b q.1-ω*(⌊axisIntercept b v w p/ω⌋ : ℝ)| ≤ χb := by
    have h := (abs_sub_le (b q.1) (axisIntercept b v w p)
      (ω*(⌊axisIntercept b v w p/ω⌋ : ℝ))).trans (add_le_add hnear hbin)
    have hm := mul_le_mul_of_nonneg_left hδω (by linarith : 0 ≤ H+2)
    linarith
  have hv : |v q.1-w| ≤ χv := hvel.trans hχvδ
  have herr := equal_fineState_bounds b v v₀ δ e f hδ he hstate
  have htime : |q.2-p.2| ≤ δ := herr.1 0
  have hval (i) : |f p i-f q i| ≤ e := by simpa only [abs_sub_comm] using herr.2 i
  have hmul : |a 1*(q.2-p.2)| ≤ H*δ := by
    rw [abs_mul]
    exact mul_le_mul (hcoeff _ a ha 1) htime (abs_nonneg _) hH0
  refine ⟨a,mem_chartMenu L hχb hχv hb hv ha,?_,?_⟩
  · have hid : f p 0-a 0-a 1*p.2 = (f p 0-f q 0)+(f q 0-a 0-a 1*q.2)+a 1*(q.2-p.2) := by ring
    rw [hid]
    have h := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (hval 0) h₀)) hmul)
    nlinarith [mul_le_mul_of_nonneg_left hδe hH0,
      mul_le_mul_of_nonneg_right hH he.le]
  · have h := (abs_sub_le (f p 1) (f q 1) (a 2)).trans (add_le_add (hval 1) h₁)
    nlinarith [mul_le_mul_of_nonneg_right hH he.le]

end Submission.Obl.k4_conditional_common_affine_field
