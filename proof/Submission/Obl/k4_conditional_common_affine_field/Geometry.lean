import Mathlib

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory

def base {α : Type*} (b v : α → ℝ) (v₀ : ℝ) (p : α × ℝ) : Fin 2 → ℝ :=
  ![p.2, b p.1 + p.2 * (v p.1 - v₀)]

noncomputable def fineState {α : Type*} (b v : α → ℝ) (v₀ δ e : ℝ)
    (f : α × ℝ → Fin 2 → ℝ) (p : α × ℝ) : Fin 4 → ℤ :=
  ![⌊base b v v₀ p 0 / δ⌋, ⌊base b v v₀ p 1 / δ⌋,
    ⌊f p 0 / e⌋, ⌊f p 1 / e⌋]

theorem measurable_base {α : Type*} [MeasurableSpace α]
    {b v : α → ℝ} (hb : Measurable b) (hv : Measurable v) (v₀ : ℝ) :
    Measurable (base b v v₀) := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact measurable_snd
  · exact (hb.comp measurable_fst).add
      (measurable_snd.mul ((hv.comp measurable_fst).sub_const v₀))

theorem measurable_fineState {α : Type*} [MeasurableSpace α]
    {b v : α → ℝ} (hb : Measurable b) (hv : Measurable v) (v₀ δ e : ℝ)
    {f : α × ℝ → Fin 2 → ℝ} (hf : Measurable f) :
    Measurable (fineState b v v₀ δ e f) := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact (((measurable_pi_apply 0).comp (measurable_base hb hv v₀)).div_const δ).floor
  · exact (((measurable_pi_apply 1).comp (measurable_base hb hv v₀)).div_const δ).floor
  · exact (((measurable_pi_apply 0).comp hf).div_const e).floor
  · exact (((measurable_pi_apply 1).comp hf).div_const e).floor

theorem equal_fineState_bounds {α : Type*} (b v : α → ℝ)
    (v₀ δ e : ℝ) (f : α × ℝ → Fin 2 → ℝ)
    (hδ : 0 < δ) (he : 0 < e) {p q : α × ℝ}
    (hpq : fineState b v v₀ δ e f p = fineState b v v₀ δ e f q) :
    (∀ i, |base b v v₀ p i - base b v v₀ q i| ≤ δ) ∧
      ∀ i, |f p i - f q i| ≤ e := by
  have hb (i : Fin 2) : ⌊base b v v₀ p i / δ⌋ = ⌊base b v v₀ q i / δ⌋ := by
    fin_cases i
    · exact congrFun hpq 0
    · exact congrFun hpq 1
  have hf (i : Fin 2) : ⌊f p i / e⌋ = ⌊f q i / e⌋ := by
    fin_cases i
    · exact congrFun hpq 2
    · exact congrFun hpq 3
  have hclose {x y a : ℝ} (ha : 0 < a) (h : ⌊x/a⌋ = ⌊y/a⌋) : |x-y| ≤ a := by
    have hh := Int.abs_sub_lt_one_of_floor_eq_floor h
    rw [← sub_div, abs_div, abs_of_pos ha] at hh
    exact ((div_lt_one ha).mp hh).le
  exact ⟨fun i => hclose hδ (hb i), fun i => hclose he (hf i)⟩

/-- A witness in a fixed fine velocity bin has an old intercept chart near the grid
fiber's intercept, and its affine/constant pair fits the grid time. -/
theorem witness_chart_and_fit
    (b v v₀ t z ur uc x y δ ω e K : ℝ) (a : Fin 3 → ℝ) (F G : Fin 2 → ℝ)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hδω : δ ≤ ω) (hωe : ω ≤ e)
    (hur : |ur| ≤ K) (ht : |t| ≤ 1)
    (hvel : |v - (ur + v₀)| ≤ δ)
    (hpos : |b + t * (v - v₀) - z| ≤ δ)
    (htime : |t - (x + y)| ≤ 3 * ω)
    (hspace : |z - (ur*x + uc*y)| ≤ 2*K*ω)
    (hFG : ∀ i, |G i - F i| ≤ e)
    (ha : ∀ i, |a i| ≤ K)
    (hfit₀ : |F 0 - a 0 - a 1*t| ≤ K*e)
    (hfit₁ : |F 1 - a 2| ≤ K*e) :
    |b - (uc-ur)*y| ≤ 7*K*ω ∧
      |G 0-a 0-a 1*(x+y)| ≤ 5*K*e ∧ |G 1-a 2| ≤ 2*K*e := by
  have hK0 : 0 ≤ K := by linarith
  have hω : 0 ≤ ω := hδ.trans hδω
  have he : 0 ≤ e := hω.trans hωe
  have hid : b-(uc-ur)*y = (b+t*(v-v₀)-z)+(z-(ur*x+uc*y))+
      ur*((x+y)-t)+t*(ur+v₀-v) := by ring
  have hthird : |ur*((x+y)-t)| ≤ K*(3*ω) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul hur htime (abs_nonneg _) hK0
  have hfourth : |t*(ur+v₀-v)| ≤ δ := by
    rw [abs_mul, abs_sub_comm]
    exact (mul_le_mul ht hvel (abs_nonneg _) (by norm_num)).trans_eq (one_mul δ)
  have hb : |b-(uc-ur)*y| ≤ 7*K*ω := by
    rw [hid]
    have h := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add hpos hspace)) hthird)) hfourth)
    nlinarith [mul_le_mul_of_nonneg_right hK hω]
  have hmul : |a 1*(t-(x+y))| ≤ K*(3*ω) := by
    rw [abs_mul]
    exact mul_le_mul (ha 1) htime (abs_nonneg _) hK0
  have hfirst : |G 0-a 0-a 1*(x+y)| ≤ 5*K*e := by
    have hid : G 0-a 0-a 1*(x+y) =
        (G 0-F 0)+(F 0-a 0-a 1*t)+a 1*(t-(x+y)) := by ring
    rw [hid]
    have h := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (hFG 0) hfit₀)) hmul)
    nlinarith [mul_le_mul_of_nonneg_left hωe hK0,
      mul_le_mul_of_nonneg_right hK he]
  have hsecond : |G 1-a 2| ≤ 2*K*e := by
    have h := (abs_sub_le (G 1) (F 1) (a 2)).trans (add_le_add (hFG 1) hfit₁)
    nlinarith [mul_le_mul_of_nonneg_right hK he]
  exact ⟨hb, hfirst, hsecond⟩

end Submission.Obl.k4_conditional_common_affine_field
