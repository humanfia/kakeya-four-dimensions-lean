-- From this LOT obligation o230, session x0803, commit c61a445c,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CorePolyBd.lean.
import Mathlib

/-!
# Functions bounded by a monomial on `[1, ∞)`

`PolyBd f` says that `0 ≤ f Λ ≤ c Λ ^ k` for every `Λ ≥ 1`. The class is closed
under sums, products and powers, which is all the budget bookkeeping of the
Cartesian core needs.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

/-- `f` is nonnegative and bounded by a monomial on `[1, ∞)`. -/
def PolyBd (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∃ k : ℕ, 0 < c ∧ ∀ Λ : ℝ, 1 ≤ Λ → 0 ≤ f Λ ∧ f Λ ≤ c * Λ ^ k

namespace PolyBd

theorem const (a : ℝ) (ha : 0 ≤ a) : PolyBd fun _ => a :=
  ⟨a + 1, 0, by linarith, fun Λ _ => ⟨ha, by simp⟩⟩

theorem id' : PolyBd fun Λ => Λ :=
  ⟨1, 1, one_pos, fun Λ hΛ => ⟨by linarith, by simp⟩⟩

theorem mono_pow {Λ : ℝ} (hΛ : 1 ≤ Λ) {k k' : ℕ} (h : k ≤ k') : Λ ^ k ≤ Λ ^ k' :=
  pow_le_pow_right₀ hΛ h

theorem add {f g : ℝ → ℝ} (hf : PolyBd f) (hg : PolyBd g) : PolyBd fun Λ => f Λ + g Λ := by
  obtain ⟨c₁, k₁, hc₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, hc₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, max k₁ k₂, by linarith, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · linarith [(h₁ Λ hΛ).1, (h₂ Λ hΛ).1]
  · have a1 : c₁ * Λ ^ k₁ ≤ c₁ * Λ ^ max k₁ k₂ :=
      mul_le_mul_of_nonneg_left (mono_pow hΛ (le_max_left _ _)) hc₁.le
    have a2 : c₂ * Λ ^ k₂ ≤ c₂ * Λ ^ max k₁ k₂ :=
      mul_le_mul_of_nonneg_left (mono_pow hΛ (le_max_right _ _)) hc₂.le
    have := (h₁ Λ hΛ).2
    have := (h₂ Λ hΛ).2
    nlinarith

theorem mul {f g : ℝ → ℝ} (hf : PolyBd f) (hg : PolyBd g) : PolyBd fun Λ => f Λ * g Λ := by
  obtain ⟨c₁, k₁, hc₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, hc₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, k₁ + k₂, by positivity, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact mul_nonneg (h₁ Λ hΛ).1 (h₂ Λ hΛ).1
  · calc f Λ * g Λ ≤ (c₁ * Λ ^ k₁) * (c₂ * Λ ^ k₂) :=
          mul_le_mul (h₁ Λ hΛ).2 (h₂ Λ hΛ).2 (h₂ Λ hΛ).1
            ((h₁ Λ hΛ).1.trans (h₁ Λ hΛ).2)
      _ = c₁ * c₂ * Λ ^ (k₁ + k₂) := by rw [pow_add]; ring

theorem pow {f : ℝ → ℝ} (hf : PolyBd f) (n : ℕ) : PolyBd fun Λ => f Λ ^ n := by
  induction n with
  | zero => simpa using const 1 zero_le_one
  | succ n ih =>
    have := mul ih hf
    simpa [pow_succ] using this

theorem smul {f : ℝ → ℝ} (hf : PolyBd f) (a : ℝ) (ha : 0 ≤ a) : PolyBd fun Λ => a * f Λ :=
  mul (const a ha) hf

theorem of_le {f g : ℝ → ℝ} (hf : PolyBd f)
    (h : ∀ Λ : ℝ, 1 ≤ Λ → 0 ≤ g Λ ∧ g Λ ≤ f Λ) : PolyBd g := by
  obtain ⟨c, k, hc, hb⟩ := hf
  exact ⟨c, k, hc, fun Λ hΛ => ⟨(h Λ hΛ).1, (h Λ hΛ).2.trans (hb Λ hΛ).2⟩⟩

theorem congr' {f g : ℝ → ℝ} (hf : PolyBd f) (h : ∀ Λ : ℝ, 1 ≤ Λ → g Λ = f Λ) : PolyBd g :=
  of_le hf fun Λ hΛ => ⟨(h Λ hΛ) ▸ (by
    obtain ⟨c, k, _, hb⟩ := hf; exact (hb Λ hΛ).1), (h Λ hΛ).le⟩

/-- Finitely many monomially bounded functions share one monomial bound. -/
theorem common {f₁ f₂ f₃ : ℝ → ℝ} (h₁ : PolyBd f₁) (h₂ : PolyBd f₂) (h₃ : PolyBd f₃) :
    ∃ c : ℝ, ∃ k : ℕ, 1 ≤ c ∧ ∀ Λ : ℝ, 1 ≤ Λ →
      f₁ Λ ≤ c * Λ ^ k ∧ f₂ Λ ≤ c * Λ ^ k ∧ f₃ Λ ≤ c * Λ ^ k := by
  obtain ⟨c, k, hc, hb⟩ := add (add h₁ h₂) h₃
  refine ⟨c + 1, k, by linarith, fun Λ hΛ => ?_⟩
  obtain ⟨c₁, k₁, _, b₁⟩ := h₁
  obtain ⟨c₂, k₂, _, b₂⟩ := h₂
  obtain ⟨c₃, k₃, _, b₃⟩ := h₃
  have hs := (hb Λ hΛ).2
  have hpos : 0 ≤ Λ ^ k := pow_nonneg (by linarith) k
  have e : c * Λ ^ k ≤ (c + 1) * Λ ^ k := by nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> linarith [(b₁ Λ hΛ).1, (b₂ Λ hΛ).1, (b₃ Λ hΛ).1]

end PolyBd

end Submission.Obl.k4_scalar_grid_cartesian_field
