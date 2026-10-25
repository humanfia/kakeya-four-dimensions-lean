-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy.Tower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_katz_tao_dichotomy.Scales

namespace WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

abbrev ConvexCount (d L : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  KatzTao d L x v

abbrev SlabCount (d L : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  Frostman d L x v

abbrev Admissibility (d η M L : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  Admissible d η M L x v Y

/-- A bounded finite tower. `false` records convex counts in each assigned fiber;
`true` records convex counts for each entire level. -/
def Tower (b : Bool) (d L g : ℝ) (B n : ℕ) (x v : Fin n → Space) : Prop :=
  ∃ J : ℕ, 1 ≤ J ∧ J ≤ B ∧
    ∃ (r : ℕ → ℝ) (N : ℕ → ℕ) (y w : ∀ j, Fin (N j) → Space)
      (f : ∀ j, Fin (N (j + 1)) → Fin (N j)),
      r 0 = 1 ∧ r J = d ∧ N 0 = 1 ∧
      (∃ u : Fin n ≃ Fin (N J), ∀ i, y J (u i) = x i ∧ w J (u i) = v i) ∧
      (∀ j, j ≤ J → ∀ k, ‖w j k‖ = 1) ∧
      (∀ j, j < J → 0 < r (j + 1) ∧ r (j + 1) < r j ∧ d ^ g * r j ≤ r (j + 1) ∧
        ∀ i, Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i) ⊆
          Tube (r j) (y j (f j i)) (w j (f j i))) ∧
      (if b then
        ∀ j, j ≤ J → ConvexCount (r j) L (N j) (y j) (w j)
      else
        ∀ j, j < J → ∀ k W, Convex ℝ W →
          ENNReal.ofReal (Set.ncard {i | f j i = k ∧
            Tube (r (j + 1)) (y (j + 1) i) (w (j + 1) i) ⊆ W} * (r (j + 1)) ^ 2) ≤
            ENNReal.ofReal L * volume W)

abbrev Large (σ ω κ α d : ℝ) (n : ℕ) (Y : Fin n → Set Space) : Prop :=
  ENNReal.ofReal (κ * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ)) ≤
    volume (⋃ i, Y i)

/-- Two retained-mass losses consume the sum of their exponents. -/
theorem retained_mass_trans {δ a b c : ℝ} {s t u : ENNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hab : a + b ≤ c)
    (h₁ : ENNReal.ofReal (δ ^ a) * s ≤ t)
    (h₂ : ENNReal.ofReal (δ ^ b) * t ≤ u) :
    ENNReal.ofReal (δ ^ c) * s ≤ u := by
  calc
    ENNReal.ofReal (δ ^ c) * s ≤ ENNReal.ofReal (δ ^ (a + b)) * s :=
      mul_le_mul_left
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hab)) s
    _ = ENNReal.ofReal (δ ^ b) * (ENNReal.ofReal (δ ^ a) * s) := by
      rw [Real.rpow_add hδ, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le a)]
      ac_rfl
    _ ≤ ENNReal.ofReal (δ ^ b) * t := mul_le_mul_right h₁ _
    _ ≤ u := h₂

end WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy
