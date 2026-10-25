-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Gain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Basic
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Scalar

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory

/-- The coarse/fine product estimate before using the small-volume bound to gain a power. -/
abbrev TwoScaleProduct (σ ω u ζ β e : ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ d : ℝ, 0 < d ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ η → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
    ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      FactoredBound β ν δ m n x v Y (fun a b => a * b ≤ δ ^ (ζ / 2) →
        ENNReal.ofReal (A * δ ^ (u + e) * b ^ (ω - u + e) * weight σ δ m n) ≤
          volume (⋃ i, Y i))

/-- The exact parameter order required of the geometric two-scale argument. -/
abbrev HasTwoScaleProduct (σ ω u : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∀ e : ℝ, 0 < e →
    ∃ β : ℝ, 0 < β ∧ β ≤ ζ / 4 ∧ TwoScaleProduct σ ω u ζ β e

/-- Named form of the conclusion, preserving the frozen order of every parameter. -/
abbrev NonflatImprovement (σ u ζ : ℝ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ ∃ α : ℝ, 0 < α ∧
    ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ d : ℝ, 0 < d ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ η → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d →
      ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        FamilyHypotheses ν δ n x v Y (CountHypotheses δ m (δ ^ (-ν)) n x v
          ((∀ i, ENNReal.ofReal (δ ^ ν * δ ^ 2) ≤ volume (Y i)) →
            ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 2 → Factorization ν δ a b m n x v →
              a * b ≤ δ ^ (ζ / 2) → δ ^ β * b < a →
                target σ (u - α) ε A δ m n ≤ volume (⋃ i, Y i)))

/-- A two-scale bound supplies the gain uniformly before the requested epsilon is selected. -/
theorem improvement_of_product {σ ω u : ℝ} (hgap : ω < u)
    (hproduct : HasTwoScaleProduct σ ω u) (ζ : ℝ) (hζ : 0 < ζ) :
    NonflatImprovement σ u ζ := by
  let e := min ((u - ω) / 2) (ζ * (u - ω) / 32)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  obtain ⟨β, hβ, hβζ, A, hA, η, hη, d, hd, hprod⟩ := hproduct ζ hζ e he
  refine ⟨β, hβ, ζ * (u - ω) / 32, by positivity, ?_⟩
  intro ε hε
  refine ⟨A, hA, η, hη, d, hd, ?_⟩
  intro ν hν hνη δ hδ hδ100 hδd m hm n x v Y
    hn hv hball hdist hYm hYT hden hconv hslab hind a b hδa hab hb2 hfact hvol hnonflat
  have hb : 0 < b := hδ.trans_le (hδa.trans hab)
  have hδ1 : δ ≤ 1 := by linarith
  have hbδ := coarse_width_bound hδ hδ1 hb.le hβζ hvol hnonflat
  have hpow := two_scale_power_gain hδ hδ1 hb hbδ hgap
    (min_le_left _ _) (min_le_right _ _) hζ
  have hresult := hprod ν hν hνη δ hδ hδ100 hδd m hm n x v Y
    hn hv hball hdist hYm hYT hden hconv hslab hind a b hδa hab hb2 hfact hnonflat hvol
  apply le_trans (ENNReal.ofReal_le_ofReal _) hresult
  rw [show A * δ ^ (u - ζ * (u - ω) / 32 + ε) * m⁻¹ * (n * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * (n * δ)) ^ (-σ) =
      A * δ ^ (u - ζ * (u - ω) / 32 + ε) * weight σ δ m n by dsimp [weight]; ring]
  calc
    _ ≤ A * (δ ^ (u + e) * b ^ (ω - u + e)) * weight σ δ m n := by
      gcongr
      exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans hpow
    _ = A * δ ^ (u + e) * b ^ (ω - u + e) * weight σ δ m n := by ring

end WangZahlLot.Obl.wz_nonflat_factored_improvement
