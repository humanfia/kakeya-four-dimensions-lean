import Submission.Lib.K4ContinuousPlanks
import Submission.Lib.K4FinitePlankAtlases.Basic

/-!
Adapted from: here:o049

Original proof developed by session x0147 in
Submission/Obl/k4_cap_class_terminal_charts/ScalePlanks.lean.
Uses the accepted K4ContinuousPlanks finite-approximation and weighted APIs.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ContinuousPlanks

/-- Only planks visible above the working mesh scale need a cap. -/
def ScalePlankCap {α : Type*} [MeasurableSpace α] (D : ℕ) (μ : Measure α)
    (b u : α → Plane) (A : ℝ) : Prop :=
  ∀ (c w e₁ e₂ : Plane) (a β : ℝ),
    ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 →
    1 / (D : ℝ) ≤ a → a ≤ β → β ≤ 2 →
    μ {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} ≤ ENNReal.ofReal (A * a * β)

/-- Internal coefficient approximation enlarges each visible side by one mesh
width. No cap below that mesh width is used. -/
theorem approximation_scale_cap {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {D n : ℕ} (hD : 1 ≤ D)
    (b u : α → Plane) (q : α → Fin n) (hq : Measurable q) (rep : Fin n → α)
    {A : ℝ} (hA : 0 < A) (hcap : ScalePlankCap D μ b u A)
    (hnear : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(b (rep (q x)) + t • u (rep (q x))) - (b x + t • u x)‖ ≤ 1 / D) :
    FiniteFullPlankCap D (b ∘ rep) (u ∘ rep)
      (fun i => (μ (q ⁻¹' {i})).toReal) (4 * A / (D : ℝ) ^ 2) := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hd₁ : (1 : ℝ) ≤ D := by exact_mod_cast hD
  intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ S hS
  have hap : 0 < a := zero_lt_one.trans_le ha
  have hbp : 0 < β := hap.trans_le hab
  have hsub : q ⁻¹' (S : Set (Fin n)) ⊆
      {x | InFullTracePlank (b x) (u x) c w e₁ e₂ ((a + 1) / D) ((β + 1) / D)} := by
    intro x hx
    change InFullTracePlank (b x) (u x) c w e₁ e₂ ((a + 1) / D) ((β + 1) / D)
    have hfit := fullTracePlank_of_near he₁ he₂
      (fun t ht => by simpa only [Function.comp_apply, norm_sub_rev] using hnear x t ht) (hS (q x) hx)
    simpa only [Function.comp_apply, add_div, one_div] using hfit
  have hmass := (measure_mono hsub).trans
    (hcap c w e₁ e₂ ((a + 1) / D) ((β + 1) / D) he₁ he₂ he
      (div_le_div_of_nonneg_right (by linarith : (1 : ℝ) ≤ a + 1) hd.le)
      (div_le_div_of_nonneg_right (by linarith : a + 1 ≤ β + 1) hd.le)
      ((div_le_iff₀ hd).mpr (by linarith)))
  rw [finite_fiber_real_mass μ q hq S]
  apply (ENNReal.toReal_le_of_le_ofReal (by positivity) hmass).trans
  have hside₁ : (a + 1) / (D : ℝ) ≤ 2 * a / D :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hside₂ : (β + 1) / (D : ℝ) ≤ 2 * β / D :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  calc
    A * ((a + 1) / D) * ((β + 1) / D) ≤ A * (2 * a / D) * (2 * β / D) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hside₁ hA.le) hside₂ (by positivity) (by positivity)
    _ = _ := by ring

/-- The continuous weighted mark estimate requires caps only between the mesh
width and a fixed chart width. -/
theorem scale_weighted_plank_estimate (H : PlankEstimate) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (b u : α → Plane), Measurable b → Measurable u →
      (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
    ∀ J : α → Finset (Fin D), (∀ S, MeasurableSet (J ⁻¹' {S})) →
      (∀ x, (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ)) →
    ∀ A : ℝ, 0 < A → ScalePlankCap D μ b u A →
    ∀ F : Finset (ℕ × (Fin 2 → ℤ)),
      (∀ x, ∀ j ∈ J x, ((j : ℕ), fun k : Fin 2 =>
        ⌊(D : ℝ) * (b x + (((((j : ℕ) : ℝ) + 1 / 2) / D) • u x)) k⌋) ∈ F) →
    (∫⁻ x, ((J x).card : ℝ≥0∞) ∂μ) ≤
      ENNReal.ofReal (C * A * (D : ℝ) ^ ε / (D : ℝ) ^ 2 * (F.card : ℝ)) := by
  obtain ⟨η, hη, C, hC, hfinite⟩ := nonnegative_weighted_plank_estimate H ε hε
  refine ⟨η, hη, 4 * C, by positivity, ?_⟩
  intro D hD α _ μ _ b u hb hu hbu J hJ hlong A hA hcap F hF
  have hd : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hcoordb (x : α) (i : Fin 2) : |b x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (b x) i).trans (hbu x).1
  have hcoordu (x : α) (i : Fin 2) : |u x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (u x) i).trans (hbu x).2
  obtain ⟨n, q, rep, hq, hrep, happ⟩ := finite_trace_discretization b u hb hu 1
    hcoordb hcoordu J hJ (1 / (4 * D)) (by positivity)
  have hnear : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(b (rep (q x)) + t • u (rep (q x))) - (b x + t • u x)‖ ≤ 1 / D := by
    intro x t ht
    convert (happ x).2 t ht using 1 <;> field_simp
  have hcap' := approximation_scale_cap μ hD b u q hq rep hA hcap hnear
  have hbound := hfinite D hD n (b ∘ rep) (u ∘ rep)
    (fun i => (μ (q ⁻¹' {i})).toReal) (4 * A / (D : ℝ) ^ 2) (J ∘ rep)
    (fun i => hbu (rep i)) (fun _ => ENNReal.toReal_nonneg) (by positivity) hcap'
    (fun i => hlong (rep i))
  have hvisited : plankVisited D (b ∘ rep) (u ∘ rep) (J ∘ rep) ⊆ F := by
    intro z hz
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
    exact hF (rep i) j (Finset.mem_sigma.mp hij).2
  rw [finite_mark_integral μ q hq rep J (fun x => (happ x).1)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C * (4 * A / (D : ℝ) ^ 2) * (D : ℝ) ^ ε * (F.card : ℝ) :=
      hbound.trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card hvisited)) (by positivity))
    _ = _ := by ring

end Submission.Lib.K4FinitePlankAtlases
