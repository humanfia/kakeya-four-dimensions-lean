/-
Adapted from: here:o018
-/
import Submission.Lib.K4ContinuousPlanks.Discretization
import Submission.Lib.K4ContinuousPlanks.Finite

/-! The finite weighted plank theorem applied to a continuous finite trace law.
Coefficient discretization is internal to the estimate and preserves actual prior weights. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4ContinuousPlanks

def MeasureFullPlankCap {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (A : ℝ) : Prop :=
  ∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ),
    ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 0 < a → a ≤ β →
    μ {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} ≤ ENNReal.ofReal (A * a * β)

theorem fullTracePlank_of_near {b u b' u' c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)}
    {a β δ : ℝ} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (hnear : ∀ t ∈ Icc (0 : ℝ) 1, ‖(b + t • u) - (b' + t • u')‖ ≤ δ)
    (hp : InFullTracePlank b' u' c w e₁ e₂ a β) :
    InFullTracePlank b u c w e₁ e₂ (a + δ) (β + δ) := by
  intro t ht
  have hsplit : b + t • u - c - t • w =
      (b' + t • u' - c - t • w) + ((b + t • u) - (b' + t • u')) := by abel
  have hi₁ : |inner ℝ ((b + t • u) - (b' + t • u')) e₁| ≤ δ := by
    calc
      _ ≤ ‖(b + t • u) - (b' + t • u')‖ * ‖e₁‖ := abs_real_inner_le_norm _ _
      _ = ‖(b + t • u) - (b' + t • u')‖ := by rw [he₁, mul_one]
      _ ≤ _ := hnear t ht
  have hi₂ : |inner ℝ ((b + t • u) - (b' + t • u')) e₂| ≤ δ := by
    calc
      _ ≤ ‖(b + t • u) - (b' + t • u')‖ * ‖e₂‖ := abs_real_inner_le_norm _ _
      _ = ‖(b + t • u) - (b' + t • u')‖ := by rw [he₂, mul_one]
      _ ≤ _ := hnear t ht
  rw [hsplit, inner_add_left, inner_add_left]
  constructor
  · calc
      _ ≤ |inner ℝ (b' + t • u' - c - t • w) e₁| +
          |inner ℝ ((b + t • u) - (b' + t • u')) e₁| := abs_add_le _ _
      _ ≤ a + δ := add_le_add (hp t ht).1 hi₁
  · calc
      _ ≤ |inner ℝ (b' + t • u' - c - t • w) e₂| +
          |inner ℝ ((b + t • u) - (b' + t • u')) e₂| := abs_add_le _ _
      _ ≤ β + δ := add_le_add (hp t ht).2 hi₂

theorem approximation_fullPlankCap {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {D n : ℕ} (hD : 1 ≤ D)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (q : α → Fin n) (hq : Measurable q)
    (rep : Fin n → α) (A : ℝ) (hA : 0 < A) (hcap : MeasureFullPlankCap μ b u A)
    (hnear : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(b (rep (q x)) + t • u (rep (q x))) - (b x + t • u x)‖ ≤ 1 / D) :
    FiniteFullPlankCap D (b ∘ rep) (u ∘ rep)
      (fun i => (μ (q ⁻¹' {i})).toReal) (4 * A / (D : ℝ) ^ 2) := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ S hS
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hbp : 0 < β := lt_of_lt_of_le hap hab
  have hsource : q ⁻¹' (S : Set (Fin n)) ⊆
      {x | InFullTracePlank (b x) (u x) c w e₁ e₂ ((a + 1) / D) ((β + 1) / D)} := by
    intro x hx
    have hp' : InFullTracePlank (b (rep (q x))) (u (rep (q x))) c w e₁ e₂
        (a / D) (β / D) := by simpa only [Function.comp_apply] using hS (q x) hx
    have hp := fullTracePlank_of_near he₁ he₂
      (fun t ht => by simpa only [norm_sub_rev] using hnear x t ht) hp'
    change InFullTracePlank (b x) (u x) c w e₁ e₂ ((a + 1) / D) ((β + 1) / D)
    simpa only [add_div, one_div, Function.comp_apply] using hp
  have hmass : μ (q ⁻¹' (S : Set (Fin n))) ≤
      ENNReal.ofReal (A * ((a + 1) / D) * ((β + 1) / D)) :=
    (measure_mono hsource).trans (hcap c w e₁ e₂ ((a + 1) / D) ((β + 1) / D)
      he₁ he₂ he (by positivity) (div_le_div_of_nonneg_right (by linarith) hd.le))
  rw [finite_fiber_real_mass μ q hq S]
  calc
    _ ≤ A * ((a + 1) / D) * ((β + 1) / D) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hmass
    _ ≤ A * (2 * a / D) * (2 * β / D) := by
      have ha' : (a + 1) / (D : ℝ) ≤ 2 * a / D :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      have hb' : (β + 1) / (D : ℝ) ≤ 2 * β / D :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left ha' hA.le) hb' (by positivity) (by positivity)
    _ = (4 * A / (D : ℝ) ^ 2) * a * β := by ring

theorem finite_mark_integral {α : Type*} [MeasurableSpace α] {D n : ℕ}
    (μ : Measure α) [IsFiniteMeasure μ] (q : α → Fin n) (hq : Measurable q)
    (rep : Fin n → α) (J : α → Finset (Fin D))
    (hJ : ∀ x, J (rep (q x)) = J x) :
    (∫⁻ x, ((J x).card : ℝ≥0∞) ∂μ) =
      ENNReal.ofReal (∑ i, (μ (q ⁻¹' {i})).toReal * ((J (rep i)).card : ℝ)) := by
  calc
    _ = ∫⁻ x, ((J (rep (q x))).card : ℝ≥0∞) ∂μ :=
      lintegral_congr fun x => by rw [hJ x]
    _ = ∫⁻ i, ((J (rep i)).card : ℝ≥0∞) ∂μ.map q :=
      (lintegral_map (μ := μ) (f := fun i : Fin n => ((J (rep i)).card : ℝ≥0∞))
        (measurable_of_countable _) hq).symm
    _ = ∑ i, ((J (rep i)).card : ℝ≥0∞) * μ.map q {i} := lintegral_fintype _
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Measure.map_apply hq (measurableSet_singleton i),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (measure_ne_top μ _),
        ENNReal.ofReal_natCast, mul_comm]

/-- Continuous weighted trace laws obey the same estimate as finite families. Marking
is an arbitrary measurable finite table; no output complexity is charged to this internal
approximation. The full trace cap, rather than just marked containment, is the hypothesis. -/
theorem continuous_weighted_plank_estimate (Hplank : PlankEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
      Measurable b → Measurable u → (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
      ∀ (J : α → Finset (Fin D)), (∀ S, MeasurableSet (J ⁻¹' {S})) →
      (∀ x, (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ)) →
      ∀ A : ℝ, 0 < A → MeasureFullPlankCap μ b u A →
      ∀ F : Finset (ℕ × (Fin 2 → ℤ)),
      (∀ x, ∀ j ∈ J x, ((j : ℕ), fun k : Fin 2 =>
        ⌊(D : ℝ) * (b x + (((((j : ℕ) : ℝ) + 1 / 2) / D) • u x)) k⌋) ∈ F) →
      (∫⁻ x, ((J x).card : ℝ≥0∞) ∂μ) ≤
        ENNReal.ofReal (C * A * (D : ℝ) ^ ε / (D : ℝ) ^ 2 * (F.card : ℝ)) := by
  classical
  obtain ⟨η, hη, C, hC, H⟩ := nonnegative_weighted_plank_estimate Hplank ε hε
  refine ⟨η, hη, 4 * C, by positivity, ?_⟩
  intro D hD α _ μ _ b u hb hu hbu J hJ hlong A hA hcap F hF
  have hd : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hRb (x : α) (i : Fin 2) : |b x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (b x) i).trans (hbu x).1
  have hRu (x : α) (i : Fin 2) : |u x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (u x) i).trans (hbu x).2
  obtain ⟨n, q, rep, hq, hrep, happrox⟩ := finite_trace_discretization
    b u hb hu 1 hRb hRu J hJ (1 / (4 * D)) (by positivity)
  have hnear : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(b (rep (q x)) + t • u (rep (q x))) - (b x + t • u x)‖ ≤ 1 / D := by
    intro x t ht
    have hscale : (4 : ℝ) * (1 / (4 * D)) = 1 / D := by ring
    simpa only [hscale] using (happrox x).2 t ht
  have hcap' := approximation_fullPlankCap μ hD b u q hq rep A hA hcap hnear
  have h := H D hD n (b ∘ rep) (u ∘ rep) (fun i => (μ (q ⁻¹' {i})).toReal)
    (4 * A / (D : ℝ) ^ 2) (J ∘ rep) (fun i => hbu (rep i)) (fun _ => ENNReal.toReal_nonneg)
    (by positivity) hcap' (fun i => hlong (rep i))
  have hvisited : plankVisited D (b ∘ rep) (u ∘ rep) (J ∘ rep) ⊆ F := by
    intro z hz
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
    exact hF (rep i) j (Finset.mem_sigma.mp hij).2
  rw [finite_mark_integral μ q hq rep J (fun x => (happrox x).1)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C * (4 * A / (D : ℝ) ^ 2) * (D : ℝ) ^ ε * (F.card : ℝ) :=
      h.trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card hvisited)) (by positivity))
    _ = _ := by ring

end Submission.Lib.K4ContinuousPlanks
