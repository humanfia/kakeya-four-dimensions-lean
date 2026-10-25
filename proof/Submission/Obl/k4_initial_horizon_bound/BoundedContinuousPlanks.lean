import Submission.Lib.K4ContinuousPlanks.Continuous
import Submission.Obl.k4_plank_estimate

/-! Only planks at widths between twice the mesh and two are needed
in the continuous estimate. The rounding enlargement stays in this range. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Lib.K4ContinuousPlanks

def MeshPlankCap {α : Type*} [MeasurableSpace α] (D : ℕ) (μ : Measure α)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (A : ℝ) : Prop :=
  ∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ),
    ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 →
    2 / (D : ℝ) ≤ a → a ≤ β → β ≤ 2 →
    μ {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β} ≤ ENNReal.ofReal (A * a * β)

theorem approximation_meshPlankCap {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {D n : ℕ} (hD : 1 ≤ D)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (q : α → Fin n) (hq : Measurable q)
    (rep : Fin n → α) {A : ℝ} (hA : 0 < A) (hcap : MeshPlankCap D μ b u A)
    (hnear : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(b (rep (q x)) + t • u (rep (q x))) - (b x + t • u x)‖ ≤ 1 / D) :
    FiniteFullPlankCap D (b ∘ rep) (u ∘ rep)
      (fun i => (μ (q ⁻¹' {i})).toReal) (4 * A / (D : ℝ) ^ 2) := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ S hS
  have hap : 0 < a := zero_lt_one.trans_le ha
  have hbp : 0 < β := hap.trans_le hab
  have hsource : q ⁻¹' (S : Set (Fin n)) ⊆
      {x | InFullTracePlank (b x) (u x) c w e₁ e₂ ((a + 1) / D) ((β + 1) / D)} := by
    intro x hx
    have hp : InFullTracePlank (b (rep (q x))) (u (rep (q x))) c w e₁ e₂
        (a / D) (β / D) := hS (q x) hx
    have h := fullTracePlank_of_near he₁ he₂
      (fun t ht => by simpa only [norm_sub_rev] using hnear x t ht) hp
    change InFullTracePlank (b x) (u x) c w e₁ e₂ ((a + 1) / D) ((β + 1) / D)
    simpa only [add_div, one_div] using h
  have hmass : μ (q ⁻¹' (S : Set (Fin n))) ≤
      ENNReal.ofReal (A * ((a + 1) / D) * ((β + 1) / D)) := by
    refine (measure_mono hsource).trans
      (hcap c w e₁ e₂ ((a + 1) / D) ((β + 1) / D) he₁ he₂ he ?_ ?_ ?_)
    · exact div_le_div_of_nonneg_right (by linarith) hd.le
    · exact div_le_div_of_nonneg_right (by linarith) hd.le
    · apply (div_le_iff₀ hd).mpr
      linarith
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
    _ = _ := by ring

theorem continuous_mesh_plank_estimate (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
      Measurable b → Measurable u → (∀ x, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
      ∀ (J : α → Finset (Fin D)), (∀ S, MeasurableSet (J ⁻¹' {S})) →
      (∀ x, (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ)) →
      ∀ A : ℝ, 0 < A → MeshPlankCap D μ b u A →
      ∀ F : Finset (ℕ × (Fin 2 → ℤ)),
      (∀ x, ∀ j ∈ J x, ((j : ℕ), fun k : Fin 2 =>
        ⌊(D : ℝ) * (b x + (((((j : ℕ) : ℝ) + 1 / 2) / D) • u x)) k⌋) ∈ F) →
      (∫⁻ x, ((J x).card : ℝ≥0∞) ∂μ) ≤
        ENNReal.ofReal (C * A * (D : ℝ) ^ ε / (D : ℝ) ^ 2 * (F.card : ℝ)) := by
  classical
  obtain ⟨η, hη, C, hC, H⟩ :=
    nonnegative_weighted_plank_estimate Submission.k4_plank_estimate ε hε
  refine ⟨η, hη, 4 * C, by positivity, ?_⟩
  intro D hD α _ μ _ b u hb hu hbu J hJ hlong A hA hcap F hF
  have hd : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hRb (x : α) (i : Fin 2) : |b x i| ≤ 1 :=
    (PiLp.norm_apply_le (b x) i).trans (hbu x).1
  have hRu (x : α) (i : Fin 2) : |u x i| ≤ 1 :=
    (PiLp.norm_apply_le (u x) i).trans (hbu x).2
  obtain ⟨n, q, rep, hq, hrep, happrox⟩ := finite_trace_discretization
    b u hb hu 1 hRb hRu J hJ (1 / (4 * D)) (by positivity)
  have hnear : ∀ x, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(b (rep (q x)) + t • u (rep (q x))) - (b x + t • u x)‖ ≤ 1 / D := by
    intro x t ht
    convert (happrox x).2 t ht using 1 <;> ring
  have hcap' := approximation_meshPlankCap μ hD b u q hq rep hA hcap hnear
  have h := H D hD n (b ∘ rep) (u ∘ rep) (fun i => (μ (q ⁻¹' {i})).toReal)
    (4 * A / (D : ℝ) ^ 2) (J ∘ rep) (fun i => hbu (rep i))
    (fun _ => ENNReal.toReal_nonneg) (by positivity) hcap' (fun i => hlong (rep i))
  have hsub : plankVisited D (b ∘ rep) (u ∘ rep) (J ∘ rep) ⊆ F := by
    intro z hz
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
    exact hF (rep i) j (Finset.mem_sigma.mp hij).2
  rw [finite_mark_integral μ q hq rep J (fun x => (happrox x).1)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C * (4 * A / (D : ℝ) ^ 2) * (D : ℝ) ^ ε * (F.card : ℝ) :=
      h.trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card hsub)) (by positivity))
    _ = _ := by ring

end Submission.Obl.k4_initial_horizon_bound
