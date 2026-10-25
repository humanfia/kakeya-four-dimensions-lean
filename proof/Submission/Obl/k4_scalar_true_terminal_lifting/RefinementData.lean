import Submission.Obl.k4_scalar_true_terminal_lifting.Interface

noncomputable section

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory
open scoped ENNReal
open k4_scalar_linear_critical_extremizers.Split

/-- Named fields for the data supplied by the literal refinement certificate.
The normalizer is retained explicitly for weighted incidence calculations. -/
structure RefinementData (p q : Code) (r b h : ℝ) where
  φ : ℕ → ℕ
  loss : ℕ → ℝ
  B : ℕ
  T : ℕ → ℕ
  γ : (k : ℕ) → Fin (W q k) → Fin (W p (φ k))
  j : (k : ℕ) → Fin (W q k) → Fin (2 ^ T k)
  A : (k : ℕ) → Fin (W q k) → Set (ℕ × (Fin 5 → ℝ))
  C : (k : ℕ) → Fin (W q k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)
  u : (k : ℕ) → Fin (W q k) → ℝ
  v : (k : ℕ) → Fin (W q k) → ℝ
  J : (k : ℕ) → Fin (W q k) → ℝ
  P : (k : ℕ) → Fin (W q k) → MvPolynomial (Fin 2) ℝ
  Λ : (k : ℕ) → Fin (W p (φ k)) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k))
  θ : (k : ℕ) → Fin (W q k) → (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ))
  mono : StrictMono φ
  loss_pos : ∀ k, 0 < loss k
  loss_zero : Filter.Tendsto loss Filter.atTop (nhds 0)
  B_pos : 1 ≤ B
  resolution : ∀ k, N q k = N p (φ k)
  chart : ∀ k, ChartData p B r b (h + loss k) (loss k) false (φ k) (T k) (W q k)
    (γ k) (j k) (A k) (C k) (u k) (v k) (J k) (P k) (Λ k)
  measurable_θ : ∀ k i, Measurable (θ k i)
  index_θ : ∀ k i l, (θ k i l).1 = l.1
  y_θ : ∀ k i l t, y (θ k i l)
      ((t - (((j k i : ℕ) : ℝ) * ((2 : ℝ) ^ T k)⁻¹)) / ((2 : ℝ) ^ T k)⁻¹) =
    (y l t - u k i - t * v k i) / J k i
  x_θ : ∀ k i l t, x (θ k i l)
      ((t - (((j k i : ℕ) : ℝ) * ((2 : ℝ) ^ T k)⁻¹)) / ((2 : ℝ) ^ T k)⁻¹) =
    (x l t - MvPolynomial.eval ![t, y l t] (P k i)) / N p (φ k) ^ (-r)
  prior_law : ∀ k i, ν q k i = (ν p (φ k) (γ k i) (A k i))⁻¹ •
    Measure.map (θ k i) ((ν p (φ k) (γ k i)).restrict (A k i))
  selected_law : ∀ k i, mu q k i =
    (ENNReal.ofReal (((2 : ℝ) ^ T k)⁻¹) * ν p (φ k) (γ k i) (A k i))⁻¹ •
      Measure.map (fun z => (θ k i z.1,
        (z.2 - (((j k i : ℕ) : ℝ) * ((2 : ℝ) ^ T k)⁻¹)) / ((2 : ℝ) ^ T k)⁻¹))
        ((mu p (φ k) (γ k i)).restrict (C k i))
  Z : ℕ → ℝ
  Z_eq : ∀ k, Z k = ∑ i : Fin (W q k), ω p (φ k) (γ k i) * ((2 : ℝ) ^ T k)⁻¹ *
    (ν p (φ k) (γ k i) (A k i)).toReal
  Z_pos : ∀ k, 0 < Z k
  weights : ∀ k i, ω q k i = (ω p (φ k) (γ k i) * ((2 : ℝ) ^ T k)⁻¹ *
    (ν p (φ k) (γ k i) (A k i)).toReal) / Z k

def dataOfRefBody (p q : Code) (r b h : ℝ) (φ : ℕ → ℕ) (loss : ℕ → ℝ) (B : ℕ)
    (T : ℕ → ℕ)
    (γ : (k : ℕ) → Fin (W q k) → Fin (W p (φ k)))
    (j : (k : ℕ) → Fin (W q k) → Fin (2 ^ T k))
    (A : (k : ℕ) → Fin (W q k) → Set (ℕ × (Fin 5 → ℝ)))
    (C : (k : ℕ) → Fin (W q k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v J : (k : ℕ) → Fin (W q k) → ℝ)
    (P : (k : ℕ) → Fin (W q k) → MvPolynomial (Fin 2) ℝ)
    (Λ : (k : ℕ) → Fin (W p (φ k)) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k)))
    (θ : (k : ℕ) → Fin (W q k) → (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ))) (hw : RefBody p q r b h φ loss B T γ j A C u v J P Λ θ) :
    RefinementData p q r b h := by
  rcases hw with ⟨hmono, hloss, htend, hB, hchart, hθ, hZ⟩
  exact {
    φ := φ, loss := loss, B := B, T := T, γ := γ, j := j, A := A, C := C,
    u := u, v := v, J := J, P := P, Λ := Λ, θ := θ,
    mono := hmono, loss_pos := hloss, loss_zero := htend, B_pos := hB,
    resolution := fun k => (hchart k).1, chart := fun k => (hchart k).2,
    measurable_θ := fun k i => (hθ k i).1,
    index_θ := fun k i => (hθ k i).2.1,
    y_θ := fun k i => (hθ k i).2.2.1,
    x_θ := fun k i => (hθ k i).2.2.2.1,
    prior_law := fun k i => (hθ k i).2.2.2.2.1,
    selected_law := fun k i => (hθ k i).2.2.2.2.2,
    Z := fun k => ∑ i : Fin (W q k), ω p (φ k) (γ k i) * ((2 : ℝ) ^ T k)⁻¹ *
      (ν p (φ k) (γ k i) (A k i)).toReal,
    Z_eq := fun _ => rfl, Z_pos := fun k => (hZ k).1,
    weights := fun k => (hZ k).2 }

theorem refinementData_nonempty {p q : Code} {r b h : ℝ} (hr : Refinement p q r b h) :
    Nonempty (RefinementData p q r b h) := by
  rcases hr with ⟨φ, loss, B, T, γ, j, A, C, u, v, J, P, Λ, θ, hw⟩
  exact ⟨dataOfRefBody p q r b h φ loss B T γ j A C u v J P Λ θ hw⟩

/-- A union over the chart labels is bounded by the sum with each chart's
original world weight. -/
theorem weighted_union_mass_le_sum {Ω I A : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype A] (μ : A → Measure Ω) (w : A → ℝ≥0∞)
    (γ : I → A) (C : I → Set Ω) :
    (∑ a, w a * μ a {z | ∃ i, γ i = a ∧ z ∈ C i}) ≤
      ∑ i, w (γ i) * μ (γ i) (C i) := by
  classical
  have hcover (a : A) : μ a {z | ∃ i, γ i = a ∧ z ∈ C i} ≤
      ∑ i, μ a {z | γ i = a ∧ z ∈ C i} := by
    have he : {z | ∃ i, γ i = a ∧ z ∈ C i} = ⋃ i, {z | γ i = a ∧ z ∈ C i} := by
      ext z
      simp
    rw [he]
    exact measure_iUnion_fintype_le _ _
  have hterm (a : A) (i : I) : w a * μ a {z | γ i = a ∧ z ∈ C i} =
      if γ i = a then w (γ i) * μ (γ i) (C i) else 0 := by
    by_cases hi : γ i = a
    · subst a
      simp
    · simp [hi]
  calc
    _ ≤ ∑ a, w a * ∑ i, μ a {z | γ i = a ∧ z ∈ C i} :=
      Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (hcover a)
    _ = ∑ a, ∑ i, w a * μ a {z | γ i = a ∧ z ∈ C i} := by simp_rw [Finset.mul_sum]
    _ = ∑ a, ∑ i, if γ i = a then w (γ i) * μ (γ i) (C i) else 0 := by simp_rw [hterm]
    _ = _ := by rw [Finset.sum_comm]; simp

namespace RefinementData

variable {p q : Code} {r b h : ℝ} (s : RefinementData p q r b h)

theorem timeWidth_pos (k : ℕ) : 0 < ((2 : ℝ) ^ s.T k)⁻¹ :=
  inv_pos.mpr (pow_pos (by norm_num) _)

theorem positionWidth_pos (k : ℕ) (i : Fin (W q k)) : 0 < s.J k i :=
  ((s.chart k).2.2.2.2.2.1 i).2.1

theorem measurable_assignment (k : ℕ) (i : Fin (W q k)) : MeasurableSet (s.A k i) :=
  ((s.chart k).2.2.1 i).1

theorem measurable_selection (k : ℕ) (i : Fin (W q k)) : MeasurableSet (s.C k i) :=
  ((s.chart k).2.2.1 i).2

theorem selection_subset (k : ℕ) (i : Fin (W q k)) :
    s.C k i ⊆ E p (s.φ k) (s.γ k i) ∩ (s.A k i ×ˢ I (s.T k) (s.j k i)) :=
  (s.chart k).2.2.2.2.1 i

theorem selection_pos (k : ℕ) (i : Fin (W q k)) :
    0 < mu p (s.φ k) (s.γ k i) (s.C k i) :=
  ((s.chart k).2.2.2.2.2.1 i).1

theorem prior_pos (k : ℕ) (i : Fin (W q k)) :
    0 < ν p (s.φ k) (s.γ k i) (s.A k i) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  let ν₀ := ν p (s.φ k) (s.γ k i)
  have hbound : mu p (s.φ k) (s.γ k i) (s.C k i) ≤
      (ν₀.prod (volume : Measure ℝ)) (s.A k i ×ˢ Set.univ) := by
    calc
      _ ≤ (ν₀.prod (volume : Measure ℝ)) (s.C k i) := Measure.restrict_apply_le _ _
      _ ≤ _ := measure_mono (by
        intro z hz
        exact ⟨((s.selection_subset k i) hz).2.1, Set.mem_univ _⟩)
  have hpos := (s.selection_pos k i).trans_le hbound
  rw [Measure.prod_prod, hz, zero_mul] at hpos
  exact lt_irrefl _ hpos

theorem prior_ne_top (hp : Exact p) (k : ℕ) (i : Fin (W q k)) :
    ν p (s.φ k) (s.γ k i) (s.A k i) ≠ ∞ := by
  letI : IsProbabilityMeasure (ν p (s.φ k) (s.γ k i)) :=
    ((hp.2.1 (s.φ k)).2.2.2.1 (s.γ k i)).1
  exact measure_ne_top _ _

theorem list_card (k : ℕ) (a : Fin (W p (s.φ k))) (z : (Fin 2 → ℝ) × ℤ) :
    ((s.Λ k a z).card : ℝ) ≤ N p (s.φ k) ^ s.loss k :=
  (s.chart k).2.2.2.2.2.2.1 a z

theorem measurable_list (k : ℕ) (a : Fin (W p (s.φ k))) (i : Fin (W q k)) :
    MeasurableSet {z | i ∈ s.Λ k a z} :=
  (s.chart k).2.2.2.2.2.2.2.1 a i

theorem list_known (k : ℕ) (i : Fin (W q k)) :
    ∀ᵐ z ∂(mu p (s.φ k) (s.γ k i)).restrict (s.C k i),
      i ∈ s.Λ k (s.γ k i) ((![z.2, y z.1 z.2], ⌊x z.1 z.2 / N p (s.φ k) ^ (-b)⌋)) := by
  rw [ae_restrict_iff' (s.measurable_selection k i), ae_iff]
  simpa only [not_imp] using (s.chart k).2.2.2.2.2.2.2.2.1 i

theorem dyadic_interval_volume (k : ℕ) (i : Fin (W q k)) :
    (volume : Measure ℝ) (I (s.T k) (s.j k i)) = ENNReal.ofReal (((2 : ℝ) ^ s.T k)⁻¹) := by
  rw [I, Real.volume_Icc]
  congr 1
  rw [← sub_div]
  ring

theorem selection_mass_le_budget (k : ℕ) (i : Fin (W q k)) :
    mu p (s.φ k) (s.γ k i) (s.C k i) ≤
      ENNReal.ofReal (((2 : ℝ) ^ s.T k)⁻¹) * ν p (s.φ k) (s.γ k i) (s.A k i) := by
  calc
    _ ≤ ((ν p (s.φ k) (s.γ k i)).prod (volume : Measure ℝ)) (s.C k i) :=
      Measure.restrict_apply_le _ _
    _ ≤ ((ν p (s.φ k) (s.γ k i)).prod (volume : Measure ℝ))
        (s.A k i ×ˢ I (s.T k) (s.j k i)) :=
      measure_mono (fun z hz => ((s.selection_subset k i) hz).2)
    _ = _ := by rw [Measure.prod_prod, s.dyadic_interval_volume]; exact mul_comm _ _

theorem normalizer_ofReal (hp : Exact p) (k : ℕ) :
    ENNReal.ofReal (s.Z k) = ∑ i : Fin (W q k),
      ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
        (ENNReal.ofReal (((2 : ℝ) ^ s.T k)⁻¹) * ν p (s.φ k) (s.γ k i) (s.A k i)) := by
  have hw (i : Fin (W q k)) : 0 ≤ ω p (s.φ k) (s.γ k i) :=
    (hp.2.1 (s.φ k)).2.1 (s.γ k i)
  rw [s.Z_eq, ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hw i) (s.timeWidth_pos k).le) ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (mul_nonneg (hw i) (s.timeWidth_pos k).le),
    ENNReal.ofReal_mul (hw i), ENNReal.ofReal_toReal (s.prior_ne_top hp k i), mul_assoc]

theorem normalizer_lower_bound (hp : Exact p) (k : ℕ) :
    N p (s.φ k) ^ (-s.loss k) ≤ s.Z k := by
  apply (ENNReal.ofReal_le_ofReal_iff (s.Z_pos k).le).mp
  calc
    _ ≤ ∑ a : Fin (W p (s.φ k)), ENNReal.ofReal (ω p (s.φ k) a) *
        mu p (s.φ k) a {z | ∃ i, s.γ k i = a ∧ z ∈ s.C k i} :=
      (s.chart k).2.2.2.2.2.2.2.2.2
    _ ≤ ∑ i : Fin (W q k), ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
        mu p (s.φ k) (s.γ k i) (s.C k i) :=
      weighted_union_mass_le_sum (mu p (s.φ k)) (fun a => ENNReal.ofReal (ω p (s.φ k) a))
        (s.γ k) (s.C k)
    _ ≤ ∑ i : Fin (W q k), ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
        (ENNReal.ofReal (((2 : ℝ) ^ s.T k)⁻¹) * ν p (s.φ k) (s.γ k i) (s.A k i)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (s.selection_mass_le_budget k i)
    _ = _ := (s.normalizer_ofReal hp k).symm

end RefinementData

end Submission.Obl.k4_scalar_true_terminal_lifting
