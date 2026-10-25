import Submission.Obl.k4_raw_localized_native_systems.Window.GoodSets

/-!
# The weighted omission tail is power small

The omission of the good sets (`good_set_omission`, and its long-heavy wrapper)
is bounded by `6 X₁ + X₂ + N^(-S u + 2τ) (9 κ_C κ₁ + 9 κ₁)`, where `X₁` is the
original-weighted density-mask complement and `X₂` the original-weighted
short-major union.  If `X₁ ≤ N^(-c₁)`, `X₂ ≤ N^(-c₂)`, the list sizes are
`κ_C ≤ N^ℓ`, `κ₁ ≤ N^σ` and `ℓ + σ + 2τ ≤ S u / 2`, then the total is at most
`N^(-a₀)` for any `a₀ ≤ min (c₁, c₂, S u / 2) / 2` once `N^a₀ ≥ 25`.
`eventually_omission_tail` packages the threshold along a valid problem.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

theorem ofReal_rpow_le_of_exp {N a b : ℝ} (hN : 1 ≤ N) (hab : a ≤ b) :
    ENNReal.ofReal (N ^ (-b)) ≤ ENNReal.ofReal (N ^ (-a)) :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN (by linarith))

/-- **The numerical omission tail.** -/
theorem omission_tail_le {N c₁ c₂ a₀ ℓ σ τ Su : ℝ} (hN : 1 ≤ N)
    {X₁ X₂ : ENNReal} (hX₁ : X₁ ≤ ENNReal.ofReal (N ^ (-c₁)))
    (hX₂ : X₂ ≤ ENNReal.ofReal (N ^ (-c₂)))
    {κC κ₁ : ℕ} (hκC : (κC : ℝ) ≤ N ^ ℓ) (hκ₁ : (κ₁ : ℝ) ≤ N ^ σ)
    (hℓ : 0 ≤ ℓ) (hσ : 0 ≤ σ) (hsum : ℓ + σ + 2 * τ ≤ Su / 2)
    (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ c₁ / 2) (ha₂ : a₀ ≤ c₂ / 2) (ha₃ : a₀ ≤ Su / 4)
    (hN25 : 25 ≤ N ^ a₀) :
    6 * X₁ + X₂ + ENNReal.ofReal (N ^ (-Su + 2 * τ)) * ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal) ≤
      ENNReal.ofReal (N ^ (-a₀)) := by
  have hN0 : 0 < N := by linarith
  have hpos : ∀ t : ℝ, 0 < N ^ t := fun t => Real.rpow_pos_of_pos hN0 t
  -- every term is at most a multiple of `N^(-2 a₀)`
  have h1 : X₁ ≤ ENNReal.ofReal (N ^ (-(2 * a₀))) :=
    hX₁.trans (ofReal_rpow_le_of_exp hN (by linarith))
  have h2 : X₂ ≤ ENNReal.ofReal (N ^ (-(2 * a₀))) :=
    hX₂.trans (ofReal_rpow_le_of_exp hN (by linarith))
  have hκprod : ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ℝ) ≤ 18 * N ^ (ℓ + σ) := by
    push_cast
    have hκC' : (κC : ℝ) ≤ N ^ ℓ := hκC
    have h1' : (1 : ℝ) ≤ N ^ ℓ := Real.one_le_rpow hN hℓ
    have hprod : (κC : ℝ) * κ₁ ≤ N ^ ℓ * N ^ σ :=
      mul_le_mul hκC' hκ₁ (Nat.cast_nonneg _) (hpos ℓ).le
    have hκ₁' : (κ₁ : ℝ) ≤ N ^ ℓ * N ^ σ := hκ₁.trans (le_mul_of_one_le_left (hpos σ).le h1')
    rw [Real.rpow_add hN0]
    nlinarith
  have h3 : ENNReal.ofReal (N ^ (-Su + 2 * τ)) * ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal) ≤
      ENNReal.ofReal (18 * N ^ (-(2 * a₀))) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (hpos _).le]
    apply ENNReal.ofReal_le_ofReal
    calc N ^ (-Su + 2 * τ) * ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ℝ)
        ≤ N ^ (-Su + 2 * τ) * (18 * N ^ (ℓ + σ)) :=
          mul_le_mul_of_nonneg_left hκprod (hpos _).le
      _ = 18 * N ^ (-Su + 2 * τ + (ℓ + σ)) := by
          rw [Real.rpow_add hN0 (-Su + 2 * τ) (ℓ + σ)]; ring
      _ ≤ 18 * N ^ (-(2 * a₀)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have htot : 6 * X₁ + X₂ + ENNReal.ofReal (N ^ (-Su + 2 * τ)) *
      ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal) ≤ ENNReal.ofReal (25 * N ^ (-(2 * a₀))) := by
    calc 6 * X₁ + X₂ + ENNReal.ofReal (N ^ (-Su + 2 * τ)) *
          ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal)
        ≤ 6 * ENNReal.ofReal (N ^ (-(2 * a₀))) + ENNReal.ofReal (N ^ (-(2 * a₀))) +
          ENNReal.ofReal (18 * N ^ (-(2 * a₀))) := by gcongr
      _ = ENNReal.ofReal (25 * N ^ (-(2 * a₀))) := by
          rw [show (6 : ENNReal) = ENNReal.ofReal 6 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
              (hpos _).le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  refine htot.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsplit : N ^ (-(2 * a₀)) = N ^ (-a₀) * N ^ (-a₀) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hinv : N ^ (-a₀) * N ^ a₀ = 1 := by
    rw [← Real.rpow_add hN0]; simp
  rw [hsplit]
  have hNa : 0 < N ^ a₀ := hpos a₀
  have hNma : 0 < N ^ (-a₀) := hpos _
  nlinarith

/-- Along a valid problem, `N^a₀ ≥ 25` eventually for every fixed `a₀ > 0`. -/
theorem eventually_rpow_ge {p : Data} (hp : Valid p) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∀ᶠ k in atTop, (25 : ℝ) ≤ p.N k ^ a₀ := by
  have ht : Tendsto (fun k => p.N k ^ a₀) atTop atTop :=
    (tendsto_rpow_atTop ha₀).comp hp.scale_tendsto
  exact ht.eventually_ge_atTop 25

/-- **The omission tail along a valid problem.**  Fixed power-small bounds for the
density-mask complement and the short-major union give one `a₀ > 0` such that,
eventually, every admissible sample has omission at most `N^(-a₀)`. -/
theorem eventually_omission_tail {p : Data} (hp : Valid p) {c₁ c₂ Su : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hSu : 0 < Su) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ᶠ k in atTop, ∀ (X₁ X₂ : ENNReal) (κC κ₁ : ℕ) (ℓ σ τ : ℝ),
      X₁ ≤ ENNReal.ofReal (p.N k ^ (-c₁)) → X₂ ≤ ENNReal.ofReal (p.N k ^ (-c₂)) →
      (κC : ℝ) ≤ p.N k ^ ℓ → (κ₁ : ℝ) ≤ p.N k ^ σ → 0 ≤ ℓ → 0 ≤ σ →
      ℓ + σ + 2 * τ ≤ Su / 2 →
      6 * X₁ + X₂ + ENNReal.ofReal (p.N k ^ (-Su + 2 * τ)) *
          ((9 * κC * κ₁ + 9 * κ₁ : ℕ) : ENNReal) ≤ ENNReal.ofReal (p.N k ^ (-a₀)) := by
  have hmin : 0 < min (min c₁ c₂) (Su / 2) := lt_min (lt_min hc₁ hc₂) (by linarith)
  refine ⟨min (min c₁ c₂) (Su / 2) / 2, by linarith, ?_⟩
  filter_upwards [eventually_rpow_ge hp (show 0 < min (min c₁ c₂) (Su / 2) / 2 by linarith)]
    with k hk
  intro X₁ X₂ κC κ₁ ℓ σ τ hX₁ hX₂ hκC hκ₁ hℓ hσ hsum
  have hmin1 : min (min c₁ c₂) (Su / 2) ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hmin2 : min (min c₁ c₂) (Su / 2) ≤ c₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hmin3 : min (min c₁ c₂) (Su / 2) ≤ Su / 2 := min_le_right _ _
  exact omission_tail_le (hp.scale_ge_one k) hX₁ hX₂ hκC hκ₁ hℓ hσ hsum (by linarith)
    (by linarith) (by linarith) (by linarith) hk

end
end Submission.Obl.k4_raw_localized_native_systems.Window
