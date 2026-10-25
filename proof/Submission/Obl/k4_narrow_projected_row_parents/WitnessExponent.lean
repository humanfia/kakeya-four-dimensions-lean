import Submission.Obl.k4_narrow_projected_row_parents.Witness
import Submission.Obl.k4_narrow_projected_row_parents.Scales

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Filter

variable {α : Type} [MeasurableSpace α]

/-- The frozen narrow witness supplies the limiting projected-width exponent
with exactly the scale range needed in the true-parent comparison. -/
theorem Model.NarrowWitness.has_exponent {cfg : Model α}
    {L a m s : ℝ} {τ : ℕ → ℕ} {H : ℕ → ℝ}
    {ρ' : ℕ → Measure (α × ℝ)} {β : ℕ → ℝ → ℝ} {n' : ℕ → ℝ → ℕ}
    {C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α}
    {tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ}
    {u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ}
    {G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ}
    (hv : Model.Valid cfg) (hw : Model.NarrowWitness cfg L a m s τ H ρ' β n' C tag u v G)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ B : ℝ,
      cfg.ℓ * s < B ∧ B ≤ cfg.ℓ * s + L * a ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
        cfg.N (τ (φ k)) ^ (-B - δ) ≤ β (φ k) s ∧
        β (φ k) s ≤ cfg.N (τ (φ k)) ^ (-B + δ) := by
  have hN (k : ℕ) : 0 < cfg.N (τ k) := by linarith [hv.scale (τ k)]
  have hlow : ∀ k, cfg.N (τ k) ^ (-(cfg.ℓ * s + L * a)) / H k ≤ β k s := by
    intro k
    have h := (hw.slice k).2.1
    change (cfg.N (τ k) ^ (-cfg.ℓ * s) * cfg.N (τ k) ^ (-L * a)) / H k ≤ β k s at h
    convert h using 1
    rw [← Real.rpow_add (hN k)]
    congr 2
    ring
  obtain ⟨e, he, hnarrow⟩ := hw.narrow
  obtain ⟨φ, hφ, B, hB, hBA, hfit⟩ := narrow_exponent_subsequence
    (cfg.N ∘ τ) H (fun k => β k s) (cfg.ℓ * s) (cfg.ℓ * s + L * a) e
    (fun k => hv.scale _) (hv.scale_limit.comp hw.mono.tendsto_atTop)
    (fun k => (hw.loss k).1) hw.loss_subpower
    (mul_nonneg hv.transverse_pos.le hs) (by nlinarith [mul_nonneg hL ha]) he hlow (by simpa only [Function.comp_apply, neg_mul] using hnarrow)
  exact ⟨φ, hφ, B, by linarith, hBA, hfit⟩

/-- A true-parent scale chosen from a narrow exponent stays below the same
linear depth bound used when choosing the initial mesh. -/
theorem exists_true_depth_below {κ ℓ L a s B U : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (ha : 0 < a) (hs : 0 < s)
    (hs2 : s ≤ 2 * a) (hB : ℓ * s < B) (hBA : B ≤ ℓ * s + L * a)
    (hU : (2 + L / ℓ) * a < U) :
    ∃ r : ℝ, s < r ∧ r < U ∧ ℓ * r < B ∧ B < (κ + ℓ) * r := by
  obtain ⟨r, hsr, hrB, hBr, hr⟩ := exists_true_depth hκ hℓ hs hB
  have hbound : B / ℓ ≤ (2 + L / ℓ) * a := by
    apply (div_le_iff₀ hℓ).mpr
    have hid : ((2 + L / ℓ) * a) * ℓ = 2 * a * ℓ + L * a := by field_simp
    rw [hid]
    nlinarith
  exact ⟨r, hsr, hr.trans_le hbound |>.trans hU, hrB, hBr⟩

/-- There is room for the deep row labels whenever both required scale gaps
fit inside the remaining depth range. -/
theorem exists_deeper_true_depth {κ ℓ r e aξ U : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (he : 0 < e) (haξ : 0 < aξ)
    (hroom : r + aξ / κ + e / ℓ < U) :
    ∃ r' : ℝ, r < r' ∧ r' < U ∧ aξ < κ * (r' - r) ∧ e < ℓ * (r' - r) := by
  have hm : r + max (aξ / κ) (e / ℓ) < U := by
    have hsum : max (aξ / κ) (e / ℓ) ≤ aξ / κ + e / ℓ :=
      max_le (le_add_of_nonneg_right (div_nonneg he.le hℓ.le))
        (le_add_of_nonneg_left (div_nonneg haξ.le hκ.le))
    linarith
  obtain ⟨r', hrlo, hrU⟩ := exists_between hm
  have hpos : 0 < max (aξ / κ) (e / ℓ) :=
    (div_pos haξ hκ).trans_le (le_max_left _ _)
  have h1 : aξ / κ < r' - r := by linarith [le_max_left (aξ / κ) (e / ℓ)]
  have h2 : e / ℓ < r' - r := by linarith [le_max_right (aξ / κ) (e / ℓ)]
  refine ⟨r', by linarith, hrU, ?_, ?_⟩
  · nlinarith [(div_lt_iff₀ hκ).mp h1]
  · nlinarith [(div_lt_iff₀ hℓ).mp h2]

end Submission.Obl.k4_narrow_projected_row_parents
