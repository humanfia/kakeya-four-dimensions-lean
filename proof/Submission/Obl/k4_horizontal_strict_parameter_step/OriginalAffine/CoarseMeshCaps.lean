/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/CoarseMeshCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
/- Adapted from this LOT tree, obligation o202, session x0698, commit
   af82e6f9c71df56ed963f4a992dea84d0d6d83b5, file
   Submission/Obl/k4_horizontal_subcritical_rate_candidates/CoarseMeshCaps.lean.
   This generic kernel uses original finite cell caps and witness mass only. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeMeshCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.TriangularCoordinates

/-! Equal-sized analytical cells inside the original tilted true box. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set


lemma centered_grid_bound {H : ℕ} (hH : 0 < H) {r : ℝ} (hr : 0 < r)
    (p : Fin H) (u c : ℝ)
    (hround : |(p : ℕ) - (H : ℝ) * ((1 + (u - c) / r) / 2)| ≤ 1) :
    |u - (c + r * (2 * (p : ℕ) / (H : ℝ) - 1))| ≤ 2 * r / H := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hid : u - (c + r * (2 * (p : ℕ) / (H : ℝ) - 1)) =
      -(2 * r / H) * ((p : ℕ) - (H : ℝ) * ((1 + (u - c) / r) / 2)) := by
    field_simp
    ring
  rw [hid, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * r / (H : ℝ))]
  exact (mul_le_mul_of_nonneg_left hround (by positivity)).trans_eq (mul_one _)

/-- An original fine-mesh cap yields a uniform cap C/H^3 for each cell of the
normalized tilted box. The original affine fit supplies the signal band. -/
lemma normalized_cell_affine_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z : Ω → Fin 3 → ℝ) (f : Ω → ℝ)
    (g : Fin 3 → ℝ) (c t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ η a K M : ℝ)
    {H : ℕ} (hH : 0 < H) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hη : 0 < η) (ha : 0 < a) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg₀ : η ≤ 2 * r₀ / H) (hg₁ : (|l₁| + 1) * η ≤ 2 * r₁ / H)
    (hg₂ : (|l₂| + |l₃| + 1) * η ≤ 2 * r₂ / H)
    (hresolve : η * ∑ j, |g j| ≤ a)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {ω | (fun i => ⌊z ω i / η⌋) = q ∧ ⌊f ω / a⌋ = j} ≤
        ENNReal.ofReal (M * η ^ 3))
    (tag : Ω → Fin 3 → Fin H) {E : Set Ω}
    (hround : ∀ ω ∈ E, ∀ j,
      |(tag ω j : ℕ) - (H : ℝ) * triangularCoordinates t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ (z ω) j| ≤ 1)
    (hfit : ∀ ω ∈ E, |f ω - (c + ∑ j, g j * z ω j)| ≤ K * a)
    (p : Fin 3 → Fin H) :
    μ {ω | ω ∈ E ∧ tag ω = p} ≤
      ENNReal.ofReal (512 * (2 * K + 7) * M * r₀ * r₁ * r₂ / (H : ℝ) ^ 3) := by
  let α : Fin 3 → ℝ := fun j => 2 * (p j : ℕ) / (H : ℝ) - 1
  let tc := t₀ + r₀ * α 0
  let Zc := z₀ + l₁ * (tc - t₀) + r₁ * α 1
  let Yc := y₀ + l₂ * (tc - t₀) + l₃ * (Zc - z₀) + r₂ * α 2
  have hbox (ω : Ω) (hω : ω ∈ {ω | ω ∈ E ∧ tag ω = p}) :
      |z ω 0 - tc| ≤ 2 * r₀ / H ∧
      |z ω 1 - Zc - l₁ * (z ω 0 - tc)| ≤ 2 * r₁ / H ∧
      |z ω 2 - Yc - l₂ * (z ω 0 - tc) - l₃ * (z ω 1 - Zc)| ≤ 2 * r₂ / H := by
    have h := hround ω hω.1
    rw [hω.2] at h
    have h₀ := centered_grid_bound hH hr₀ (p 0) (z ω 0) t₀
      (by simpa only [triangularCoordinates, Matrix.cons_val_zero] using h 0)
    let u₁ := z ω 1 - z₀ - l₁ * (z ω 0 - t₀)
    let u₂ := z ω 2 - y₀ - l₂ * (z ω 0 - t₀) - l₃ * (z ω 1 - z₀)
    have h₁ := centered_grid_bound hH hr₁ (p 1) u₁ 0
      (by simpa [triangularCoordinates, u₁] using h 1)
    have h₂ := centered_grid_bound hH hr₂ (p 2) u₂ 0
      (by simpa [triangularCoordinates, u₂] using h 2)
    have heq₁ : z ω 1 - Zc - l₁ * (z ω 0 - tc) =
        u₁ - (0 + r₁ * (2 * (p 1 : ℕ) / (H : ℝ) - 1)) := by
      dsimp [Zc, α, u₁]
      ring
    have heq₂ : z ω 2 - Yc - l₂ * (z ω 0 - tc) - l₃ * (z ω 1 - Zc) =
        u₂ - (0 + r₂ * (2 * (p 2 : ℕ) / (H : ℝ) - 1)) := by
      dsimp [Yc, α, u₂]
      ring
    refine ⟨h₀, ?_, ?_⟩
    · rw [heq₁]
      exact h₁
    · rw [heq₂]
      exact h₂
  have hb := tilted_affine_band_mass μ z f g c tc Zc Yc l₁ l₂ l₃
    (2 * r₀ / H) (2 * r₁ / H) (2 * r₂ / H) η a K M hη ha hK hM
    hg₀ hg₁ hg₂ hresolve hcap hbox (fun ω hω => hfit ω hω.1)
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have heq : 64 * (2 * K + 7) * M * (2 * r₀ / H) * (2 * r₁ / H) * (2 * r₂ / H) =
      512 * (2 * K + 7) * M * r₀ * r₁ * r₂ / (H : ℝ) ^ 3 := by
    field_simp
    ring
  simpa only [heq] using hb

end Submission.Obl.k4_horizontal_strict_parameter_step
