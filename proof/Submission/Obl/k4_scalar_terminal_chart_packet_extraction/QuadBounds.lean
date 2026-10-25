import Mathlib

/-!
# Elementary bounds for quadratic polynomials

Quadratic predictors `F(t, y)` of total degree at most two are controlled by their values
on a set of positive measure in a parallelogram (a Remez-type inequality with an explicit
polynomial loss), and their size elsewhere grows at most quadratically in the normalized
distance from the parallelogram. These are the elementary facts used to bound the
predictor norms of the packets in the exact angular packet theorem.
-/

namespace Submission.Obl.k4_scalar_terminal_chart_packet_extraction

open MeasureTheory Set

/-- A real function of two variables that is a polynomial of total degree at most two,
with explicit coefficients. -/
def IsQuad2 (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ c : Fin 6 → ℝ, ∀ t y,
    f t y = c 0 + c 1 * t + c 2 * y + c 3 * t ^ 2 + c 4 * (t * y) + c 5 * y ^ 2

lemma IsQuad2.add {f g : ℝ → ℝ → ℝ} (hf : IsQuad2 f) (hg : IsQuad2 g) :
    IsQuad2 (f + g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  exact ⟨c + d, fun t y => by simp only [Pi.add_apply, hc, hd]; ring⟩

lemma IsQuad2.zero : IsQuad2 0 := ⟨0, fun t y => by simp⟩

lemma IsQuad2.const_mul {f : ℝ → ℝ → ℝ} (a : ℝ) (hf : IsQuad2 f) :
    IsQuad2 (fun t y => a * f t y) := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨a • c, fun t y => by simp only [hc, Pi.smul_apply, smul_eq_mul]; ring⟩

lemma isQuad2_monomial (i j : ℕ) (h : i + j ≤ 2) :
    IsQuad2 (fun t y => t ^ i * y ^ j) := by
  have hi : i ≤ 2 := by omega
  have hj : j ≤ 2 := by omega
  interval_cases i <;> interval_cases j <;> simp at h
  · exact ⟨![1, 0, 0, 0, 0, 0], fun t y => by simp⟩
  · exact ⟨![0, 0, 1, 0, 0, 0], fun t y => by simp⟩
  · exact ⟨![0, 0, 0, 0, 0, 1], fun t y => by simp⟩
  · exact ⟨![0, 1, 0, 0, 0, 0], fun t y => by simp⟩
  · exact ⟨![0, 0, 0, 0, 1, 0], fun t y => by simp⟩
  · exact ⟨![0, 0, 0, 1, 0, 0], fun t y => by simp⟩

/-- Evaluation of a two-variable polynomial of total degree at most two is an explicit
quadratic function. -/
theorem isQuad2_eval (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) :
    IsQuad2 (fun t y => MvPolynomial.eval ![t, y] P) := by
  have hexp : (fun t y => MvPolynomial.eval ![t, y] P) =
      ∑ v ∈ P.support, (fun t y : ℝ => P.coeff v * (t ^ v 0 * y ^ v 1)) := by
    funext t y
    rw [Finset.sum_apply, Finset.sum_apply]
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)]
    simp [Fin.prod_univ_two]
  rw [hexp]
  refine Finset.sum_induction _ IsQuad2 (fun f g hf hg => hf.add hg) IsQuad2.zero ?_
  intro v hv
  have hdeg := MvPolynomial.le_totalDegree hv
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hdeg
  exact (isQuad2_monomial (v 0) (v 1) (by omega)).const_mul (P.coeff v)

lemma IsQuad2.continuous {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) :
    Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
  obtain ⟨c, hc⟩ := hf
  simp only [hc]
  fun_prop

/-- Restricted to an affine line, a quadratic function of two variables is a quadratic
function of one variable. -/
lemma IsQuad2.line {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) (α β γ δ : ℝ) :
    ∃ a b c : ℝ, ∀ s, f (α + β * s) (γ + δ * s) = a + b * s + c * s ^ 2 := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨k 0 + k 1 * α + k 2 * γ + k 3 * α ^ 2 + k 4 * (α * γ) + k 5 * γ ^ 2,
    k 1 * β + k 2 * δ + 2 * k 3 * α * β + k 4 * (α * δ + β * γ) + 2 * k 5 * γ * δ,
    k 3 * β ^ 2 + k 4 * (β * δ) + k 5 * δ ^ 2, fun s => ?_⟩
  rw [hk]
  ring

/-- Lagrange interpolation at three separated points bounds a quadratic everywhere. -/
theorem quad_three_point_bound {a b c A δ x₁ x₂ x₃ : ℝ} (hδ : 0 < δ)
    (h12 : x₁ + δ ≤ x₂) (h23 : x₂ + δ ≤ x₃)
    (h₁ : |a + b * x₁ + c * x₁ ^ 2| ≤ A) (h₂ : |a + b * x₂ + c * x₂ ^ 2| ≤ A)
    (h₃ : |a + b * x₃ + c * x₃ ^ 2| ≤ A) (x : ℝ) :
    |a + b * x + c * x ^ 2| ≤ 3 * A * ((|x - x₁| + (x₃ - x₁)) / δ) ^ 2 := by
  set p : ℝ → ℝ := fun z => a + b * z + c * z ^ 2 with hp
  have hd12 : x₁ - x₂ ≠ 0 := by intro h; linarith
  have hd13 : x₁ - x₃ ≠ 0 := by intro h; linarith
  have hd23 : x₂ - x₃ ≠ 0 := by intro h; linarith
  have hlag : p x = p x₁ * ((x - x₂) * (x - x₃) / ((x₁ - x₂) * (x₁ - x₃))) +
      p x₂ * ((x - x₁) * (x - x₃) / ((x₂ - x₁) * (x₂ - x₃))) +
      p x₃ * ((x - x₁) * (x - x₂) / ((x₃ - x₁) * (x₃ - x₂))) := by
    have hd21 : x₂ - x₁ ≠ 0 := by intro h; linarith
    have hd31 : x₃ - x₁ ≠ 0 := by intro h; linarith
    have hd32 : x₃ - x₂ ≠ 0 := by intro h; linarith
    simp only [hp]
    field_simp
    ring
  set R := |x - x₁| + (x₃ - x₁) with hR
  have hA : 0 ≤ A := le_trans (abs_nonneg _) h₁
  have hRnn : 0 ≤ R := by rw [hR]; have := abs_nonneg (x - x₁); linarith
  -- each Lagrange factor is bounded by `(R / δ) ^ 2`
  have hfac : ∀ u v w z : ℝ, |u| ≤ R → |v| ≤ R → δ ≤ |w| → δ ≤ |z| →
      |u * v / (w * z)| ≤ (R / δ) ^ 2 := by
    intro u v w z hu hv hw hz
    have hw0 : 0 < |w| := lt_of_lt_of_le hδ hw
    have hz0 : 0 < |z| := lt_of_lt_of_le hδ hz
    rw [abs_div, abs_mul, abs_mul, div_pow, div_le_div_iff₀ (mul_pos hw0 hz0) (by positivity)]
    calc |u| * |v| * δ ^ 2 ≤ R * R * δ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hu hv (abs_nonneg _) hRnn
      _ ≤ R ^ 2 * (|w| * |z|) := by
          rw [sq, sq]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hw hz hδ.le (abs_nonneg _)
  have hxx1 : |x - x₁| ≤ R := by rw [hR]; linarith
  have hxx2 : |x - x₂| ≤ R := by
    rw [hR]
    calc |x - x₂| = |(x - x₁) + (x₁ - x₂)| := by ring_nf
      _ ≤ |x - x₁| + |x₁ - x₂| := abs_add_le _ _
      _ ≤ |x - x₁| + (x₃ - x₁) := by
          have : |x₁ - x₂| = x₂ - x₁ := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
          rw [this]; linarith
  have hxx3 : |x - x₃| ≤ R := by
    rw [hR]
    calc |x - x₃| = |(x - x₁) + (x₁ - x₃)| := by ring_nf
      _ ≤ |x - x₁| + |x₁ - x₃| := abs_add_le _ _
      _ = |x - x₁| + (x₃ - x₁) := by
          rw [abs_sub_comm x₁ x₃, abs_of_nonneg (show (0:ℝ) ≤ x₃ - x₁ by linarith)]
  have hsep : ∀ u v : ℝ, u + δ ≤ v → δ ≤ |u - v| ∧ δ ≤ |v - u| := by
    intro u v huv
    constructor
    · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have h13 : x₁ + δ ≤ x₃ := by linarith
  have e1 := hfac _ _ _ _ hxx2 hxx3 (hsep _ _ h12).1 (hsep _ _ h13).1
  have e2 := hfac _ _ _ _ hxx1 hxx3 (hsep _ _ h12).2 (hsep _ _ h23).1
  have e3 := hfac _ _ _ _ hxx1 hxx2 (hsep _ _ h13).2 (hsep _ _ h23).2
  show |p x| ≤ 3 * A * (R / δ) ^ 2
  rw [hlag]
  have t1 : |p x₁ * ((x - x₂) * (x - x₃) / ((x₁ - x₂) * (x₁ - x₃)))| ≤ A * (R / δ) ^ 2 := by
    rw [abs_mul]; exact mul_le_mul h₁ e1 (abs_nonneg _) hA
  have t2 : |p x₂ * ((x - x₁) * (x - x₃) / ((x₂ - x₁) * (x₂ - x₃)))| ≤ A * (R / δ) ^ 2 := by
    rw [abs_mul]; exact mul_le_mul h₂ e2 (abs_nonneg _) hA
  have t3 : |p x₃ * ((x - x₁) * (x - x₂) / ((x₃ - x₁) * (x₃ - x₂)))| ≤ A * (R / δ) ^ 2 := by
    rw [abs_mul]; exact mul_le_mul h₃ e3 (abs_nonneg _) hA
  calc _ ≤ |p x₁ * ((x - x₂) * (x - x₃) / ((x₁ - x₂) * (x₁ - x₃)))| +
        |p x₂ * ((x - x₁) * (x - x₃) / ((x₂ - x₁) * (x₂ - x₃)))| +
        |p x₃ * ((x - x₁) * (x - x₂) / ((x₃ - x₁) * (x₃ - x₂)))| := abs_add_three _ _ _
    _ ≤ A * (R / δ) ^ 2 + A * (R / δ) ^ 2 + A * (R / δ) ^ 2 := by linarith
    _ = 3 * A * (R / δ) ^ 2 := by ring

/-- A set of real numbers of measure at least `m > 0` that is bounded below contains three
points with consecutive gaps at least `m / 6`. -/
theorem exists_three_separated {E : Set ℝ} {m : ℝ} (hm : 0 < m)
    (hvol : ENNReal.ofReal m ≤ volume E) (hbdd : BddBelow E) :
    ∃ x₁ ∈ E, ∃ x₂ ∈ E, ∃ x₃ ∈ E, x₁ + m / 6 ≤ x₂ ∧ x₂ + m / 6 ≤ x₃ := by
  set δ := m / 6 with hδdef
  have hδ : 0 < δ := by positivity
  -- removing an initial piece `[s, s + 2δ)` costs at most `2δ` of measure
  have hsplit : ∀ (F : Set ℝ) (s : ℝ), F ⊆ Ici s →
      volume F ≤ ENNReal.ofReal (2 * δ) + volume (F ∩ Ici (s + 2 * δ)) := by
    intro F s hF
    calc volume F ≤ volume ((F ∩ Iio (s + 2 * δ)) ∪ (F ∩ Ici (s + 2 * δ))) := by
          apply measure_mono
          intro x hx
          rcases lt_or_ge x (s + 2 * δ) with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩
      _ ≤ volume (F ∩ Iio (s + 2 * δ)) + volume (F ∩ Ici (s + 2 * δ)) := measure_union_le _ _
      _ ≤ volume (Ico s (s + 2 * δ)) + volume (F ∩ Ici (s + 2 * δ)) := by
          gcongr
          intro x hx
          exact ⟨hF hx.1, hx.2⟩
      _ = ENNReal.ofReal (2 * δ) + volume (F ∩ Ici (s + 2 * δ)) := by
          rw [Real.volume_Ico]; congr 2; ring
  have hEne : E.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hvol
    linarith
  set s₁ := sInf E with hs₁
  have hEs₁ : E ⊆ Ici s₁ := fun x hx => csInf_le hbdd hx
  obtain ⟨x₁, hx₁E, hx₁lt⟩ := exists_lt_of_csInf_lt hEne (show s₁ < s₁ + δ by linarith)
  set E₂ := E ∩ Ici (s₁ + 2 * δ) with hE₂
  have hv₁ := hsplit E s₁ hEs₁
  -- `E₂` still has measure more than `2δ`
  have hE₂big : ENNReal.ofReal (2 * δ) < volume E₂ := by
    by_contra hle
    push Not at hle
    have : ENNReal.ofReal m ≤ ENNReal.ofReal (2 * δ) + ENNReal.ofReal (2 * δ) :=
      hvol.trans (hv₁.trans (add_le_add le_rfl hle))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    linarith
  have hE₂ne : E₂.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty] at hE₂big
    exact absurd hE₂big (not_lt.mpr bot_le)
  have hbdd₂ : BddBelow E₂ := ⟨s₁ + 2 * δ, fun x hx => hx.2⟩
  set s₂ := sInf E₂ with hs₂
  have hE₂s₂ : E₂ ⊆ Ici s₂ := fun x hx => csInf_le hbdd₂ hx
  obtain ⟨x₂, hx₂E, hx₂lt⟩ := exists_lt_of_csInf_lt hE₂ne (show s₂ < s₂ + δ by linarith)
  have hv₂ := hsplit E₂ s₂ hE₂s₂
  have hE₃ne : (E₂ ∩ Ici (s₂ + 2 * δ)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty, add_zero] at hv₂
    exact absurd (hE₂big.trans_le hv₂) (lt_irrefl _)
  obtain ⟨x₃, hx₃E, hx₃ge⟩ := hE₃ne
  refine ⟨x₁, hx₁E, x₂, hx₂E.1, x₃, hx₃E.1, ?_, ?_⟩
  · have := hx₂E.2
    simp only [Set.mem_Ici] at this
    linarith
  · simp only [Set.mem_Ici] at hx₃ge
    linarith

/-- If a quadratic in `y` is bounded by `A` on a set of measure at least `λ w` inside
`[c - w, c + w]`, it is bounded everywhere by `108 A (3 + |y - c| / w)² / λ²`. -/
theorem quad_slice_remez {g : ℝ → ℝ} {a b c' : ℝ} (hg : ∀ y, g y = a + b * y + c' * y ^ 2)
    {c w A lam : ℝ} (hw : 0 < w) (hlam : 0 < lam)
    (hvol : ENNReal.ofReal (lam * w) ≤ volume {y | |y - c| ≤ w ∧ |g y| ≤ A}) (y : ℝ) :
    |g y| ≤ 108 * A * (3 + |y - c| / w) ^ 2 / lam ^ 2 := by
  have hbdd : BddBelow {y | |y - c| ≤ w ∧ |g y| ≤ A} :=
    ⟨c - w, fun z hz => by have := (abs_le.mp hz.1).1; linarith⟩
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, h12, h23⟩ :=
    exists_three_separated (by positivity) hvol hbdd
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hy₁.2
  have hδ : 0 < lam * w / 6 := by positivity
  have e₁ : |a + b * y₁ + c' * y₁ ^ 2| ≤ A := by rw [← hg]; exact hy₁.2
  have e₂ : |a + b * y₂ + c' * y₂ ^ 2| ≤ A := by rw [← hg]; exact hy₂.2
  have e₃ : |a + b * y₃ + c' * y₃ ^ 2| ≤ A := by rw [← hg]; exact hy₃.2
  have key := quad_three_point_bound hδ h12 h23 e₁ e₂ e₃ y
  rw [← hg] at key
  have hb1 := abs_le.mp hy₁.1
  have hb3 := abs_le.mp hy₃.1
  have hR : |y - y₁| + (y₃ - y₁) ≤ |y - c| + 3 * w := by
    have : |y - y₁| ≤ |y - c| + w := by
      calc |y - y₁| = |(y - c) + (c - y₁)| := by ring_nf
        _ ≤ |y - c| + |c - y₁| := abs_add_le _ _
        _ ≤ |y - c| + w := by
          have : |c - y₁| ≤ w := by rw [abs_sub_comm]; exact hy₁.1
          linarith
    linarith
  have hR0 : 0 ≤ |y - y₁| + (y₃ - y₁) := by
    have := abs_nonneg (y - y₁); linarith
  calc |g y| ≤ 3 * A * ((|y - y₁| + (y₃ - y₁)) / (lam * w / 6)) ^ 2 := key
    _ ≤ 3 * A * ((|y - c| + 3 * w) / (lam * w / 6)) ^ 2 := by
        gcongr
    _ = 108 * A * (3 + |y - c| / w) ^ 2 / lam ^ 2 := by
        field_simp
        ring

/-- **Remez-type bound on a parallelogram.** If a quadratic function of two variables is
bounded by `A` on a subset of the parallelogram
`{(t, y) : t ∈ [t₀, t₀ + q], |y - (c₀ + c₁ t)| ≤ w}` of measure at least `λ` times its area
`2 q w`, then for every time `t` of the parallelogram and every `y`,
`|f t y| ≤ 186624 A (3 + |y - (c₀ + c₁ t)| / w)² / λ⁴`. -/
theorem quad_remez_parallelogram {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) {t₀ q c₀ c₁ w A lam : ℝ}
    (hq : 0 < q) (hw : 0 < w) (hlam : 0 < lam)
    (hvol : ENNReal.ofReal (lam * (q * (2 * w))) ≤ volume {p : ℝ × ℝ |
      p.1 ∈ Icc t₀ (t₀ + q) ∧ |p.2 - (c₀ + c₁ * p.1)| ≤ w ∧ |f p.1 p.2| ≤ A})
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + q)) (y : ℝ) :
    |f t y| ≤ 186624 * A * (3 + |y - (c₀ + c₁ * t)| / w) ^ 2 / lam ^ 4 := by
  set Z : Set (ℝ × ℝ) := {p : ℝ × ℝ |
      p.1 ∈ Icc t₀ (t₀ + q) ∧ |p.2 - (c₀ + c₁ * p.1)| ≤ w ∧ |f p.1 p.2| ≤ A} with hZ
  have hfc := hf.continuous
  have hZm : MeasurableSet Z := by
    show MeasurableSet ((Prod.fst ⁻¹' Icc t₀ (t₀ + q)) ∩
      ({p : ℝ × ℝ | |p.2 - (c₀ + c₁ * p.1)| ≤ w} ∩ {p : ℝ × ℝ | |f p.1 p.2| ≤ A}))
    refine (measurableSet_Icc.preimage measurable_fst).inter ((measurableSet_le ?_ ?_).inter
      (measurableSet_le ?_ ?_))
    · fun_prop
    · fun_prop
    · exact (continuous_abs.comp hfc).measurable
    · fun_prop
  -- slices of `Z`
  have hslice : ∀ s, Prod.mk s ⁻¹' Z =
      {y | s ∈ Icc t₀ (t₀ + q) ∧ |y - (c₀ + c₁ * s)| ≤ w ∧ |f s y| ≤ A} := fun s => rfl
  set Tg : Set ℝ := {s | s ∈ Icc t₀ (t₀ + q) ∧
      ENNReal.ofReal (lam * w) ≤ volume (Prod.mk s ⁻¹' Z)} with hTg
  have hpt : ∀ s, volume (Prod.mk s ⁻¹' Z) ≤
      Tg.indicator (fun _ => ENNReal.ofReal (2 * w)) s +
        (Icc t₀ (t₀ + q)).indicator (fun _ => ENNReal.ofReal (lam * w)) s := by
    intro s
    by_cases hs : s ∈ Icc t₀ (t₀ + q)
    · have hle : volume (Prod.mk s ⁻¹' Z) ≤ ENNReal.ofReal (2 * w) := by
        calc volume (Prod.mk s ⁻¹' Z) ≤
            volume (Icc (c₀ + c₁ * s - w) (c₀ + c₁ * s + w)) := by
              apply measure_mono
              intro y hy
              rw [hslice] at hy
              have := abs_le.mp hy.2.1
              exact ⟨by linarith, by linarith⟩
          _ = ENNReal.ofReal (2 * w) := by rw [Real.volume_Icc]; ring_nf
      by_cases hgood : ENNReal.ofReal (lam * w) ≤ volume (Prod.mk s ⁻¹' Z)
      · rw [Set.indicator_of_mem (show s ∈ Tg from ⟨hs, hgood⟩)]
        exact le_add_right hle
      · push Not at hgood
        rw [Set.indicator_of_mem hs]
        exact le_add_left hgood.le
    · have : Prod.mk s ⁻¹' Z = ∅ := by
        ext y; rw [hslice]; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hs h.1
      rw [this, measure_empty]
      exact bot_le
  have hTgfin : volume Tg ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono (fun s hs => hs.1))
  have hint : volume Z ≤ ENNReal.ofReal (2 * w) * volume Tg +
      ENNReal.ofReal (lam * w) * ENNReal.ofReal q := by
    rw [Measure.volume_eq_prod, Measure.prod_apply hZm]
    calc ∫⁻ s, volume (Prod.mk s ⁻¹' Z) ≤ ∫⁻ s, (Tg.indicator (fun _ => ENNReal.ofReal (2 * w)) s +
        (Icc t₀ (t₀ + q)).indicator (fun _ => ENNReal.ofReal (lam * w)) s) := lintegral_mono hpt
      _ = (∫⁻ s, Tg.indicator (fun _ => ENNReal.ofReal (2 * w)) s) +
          ∫⁻ s, (Icc t₀ (t₀ + q)).indicator (fun _ => ENNReal.ofReal (lam * w)) s :=
          lintegral_add_right _ ((measurable_const.indicator measurableSet_Icc))
      _ ≤ ENNReal.ofReal (2 * w) * volume Tg + ENNReal.ofReal (lam * w) * ENNReal.ofReal q := by
          gcongr
          · exact lintegral_indicator_const_le _ _
          · rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
            ring_nf
            exact le_rfl
  -- a large set of good times
  have hTgbig : ENNReal.ofReal (lam * q / 2) ≤ volume Tg := by
    set v := (volume Tg).toReal with hv
    have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_toReal hTgfin] at hint ⊢
    rw [← hv] at hint ⊢
    have h2 := hvol.trans hint
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hTgbdd : BddBelow Tg := ⟨t₀, fun s hs => hs.1.1⟩
  obtain ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, ht12, ht23⟩ :=
    exists_three_separated (by positivity) hTgbig hTgbdd
  -- the bound along slices at the good times
  have hgood_slice : ∀ s ∈ Tg, ∀ y', |f s y'| ≤ 108 * A * (3 + |y' - (c₀ + c₁ * s)| / w) ^ 2 /
      lam ^ 2 := by
    intro s hs y'
    obtain ⟨a, b, c', habc⟩ := hf.line s 0 0 1
    have hg : ∀ u, f s u = a + b * u + c' * u ^ 2 := by
      intro u; have := habc u; simp only [zero_mul, add_zero, zero_add, one_mul] at this
      exact this
    refine quad_slice_remez hg hw hlam ?_ y'
    refine hs.2.trans (measure_mono ?_)
    intro u hu
    rw [hslice] at hu
    exact ⟨hu.2.1, hu.2.2⟩
  -- the bound along the line parallel to the centre line through `(t, y)`
  set σ := y - (c₀ + c₁ * t) with hσ
  obtain ⟨a, b, c', habc⟩ := hf.line 0 1 (c₀ + σ) c₁
  have hline : ∀ s, f s (c₀ + σ + c₁ * s) = a + b * s + c' * s ^ 2 := by
    intro s; have := habc s; simp only [zero_add, one_mul] at this; exact this
  set A' := 108 * A * (3 + |σ| / w) ^ 2 / lam ^ 2 with hA'
  have hat : ∀ s ∈ Tg, |a + b * s + c' * s ^ 2| ≤ A' := by
    intro s hs
    rw [← hline]
    have := hgood_slice s hs (c₀ + σ + c₁ * s)
    have he : c₀ + σ + c₁ * s - (c₀ + c₁ * s) = σ := by ring
    rw [he] at this
    exact this
  have hδ : 0 < lam * q / 2 / 6 := by positivity
  have key := quad_three_point_bound hδ ht12 ht23 (hat _ ht₁) (hat _ ht₂) (hat _ ht₃) t
  rw [← hline] at key
  have hyy : c₀ + σ + c₁ * t = y := by rw [hσ]; ring
  rw [hyy] at key
  have hA'0 : 0 ≤ A' := le_trans (abs_nonneg _) (hat _ ht₁)
  have hdist : |t - t₁| + (t₃ - t₁) ≤ 2 * q := by
    have h1 := ht₁.1; have h3 := ht₃.1
    have : |t - t₁| ≤ q := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2, h1.1, h1.2]
    linarith [h1.1, h3.2]
  have hd0 : 0 ≤ |t - t₁| + (t₃ - t₁) := by
    have := abs_nonneg (t - t₁); linarith
  calc |f t y| ≤ 3 * A' * ((|t - t₁| + (t₃ - t₁)) / (lam * q / 2 / 6)) ^ 2 := key
    _ ≤ 3 * A' * ((2 * q) / (lam * q / 2 / 6)) ^ 2 := by gcongr
    _ = 186624 * A * (3 + |y - (c₀ + c₁ * t)| / w) ^ 2 / lam ^ 4 := by
        rw [hA', ← hσ]
        field_simp
        ring

end Submission.Obl.k4_scalar_terminal_chart_packet_extraction
