import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Model
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.ResidualCaps

set_option maxHeartbeats 800000

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The original three-coordinate point associated to a normalized scalar time. -/
def normalizedPoint {α : Type} [MeasurableSpace α]
    (cfg : Data α) (k : ℕ) (t₀ q : ℝ) (p : α × ℝ) : Fin 3 → ℝ :=
  ![t₀ + q * p.2, cfg.x k p.1 (t₀ + q * p.2) 1,
    cfg.x k p.1 (t₀ + q * p.2) 2]

theorem normalizedPoint_eq {α : Type} [MeasurableSpace α]
    (cfg : Data α) (k : ℕ) (t₀ q : ℝ) (p : α × ℝ) :
    normalizedPoint cfg k t₀ q p = cfg.x k p.1 (t₀ + q * p.2) ∘ Fin.castSucc := by
  ext i
  fin_cases i <;> rfl

/-- Scalar base bins and the original transverse tube lie in one moving box.
The box velocity may be large; resolving it with the fine mesh is enough. -/
theorem scalar_cell_mem_movingBox
    {α : Type} (point : α × ℝ → Fin 3 → ℝ) (coeff : α → Fin 5 → ℝ)
    {q g ξ K t₀ z₀ zv : ℝ} (hq : 0 < q) (hg : 0 < g) (hξ : 0 < ξ)
    (hK : 0 ≤ K) (hξg : ξ ≤ g) (c : Fin 5 → ℝ) (hc : |c 4| ≤ K)
    (p : α × ℝ) (β : Fin 2 → ℤ)
    (ht : point p 0 = t₀ + q * p.2)
    (hY : scalarY (coeff p.1) p.2 = (point p 1 - z₀ - zv * point p 0) / q)
    (hcell : scalarCell (coeff p.1) p.2 ξ = β)
    (htrans : |point p 2 - c 2 - point p 0 * c 3 - c 4 * point p 1| ≤ K * q * g) :
    point p ∈ Submission.Lib.K4MovingMeshBoxes.movingBox
      (t₀ + q * ξ * (β 0 : ℝ)) (q * ξ)
      ![z₀ + q * ξ * (β 1 : ℝ), c 2 + c 4 * (z₀ + q * ξ * (β 1 : ℝ))]
      ![zv, c 3 + c 4 * zv] ![q * ξ, 2 * K * q * g] := by
  have hcell0 : ⌊p.2 / ξ⌋ = β 0 := congrFun hcell 0
  have hcell1 : ⌊scalarY (coeff p.1) p.2 / ξ⌋ = β 1 := congrFun hcell 1
  have htime : |p.2 - (β 0 : ℝ) * ξ| ≤ ξ := by
    have hlo := (le_div_iff₀ hξ).mp (Int.floor_le (p.2 / ξ))
    have hhi := (div_lt_iff₀ hξ).mp (Int.lt_floor_add_one (p.2 / ξ))
    rw [hcell0] at hlo hhi
    rw [abs_le]
    constructor <;> nlinarith only [hlo, hhi]
  have hspace : |scalarY (coeff p.1) p.2 - (β 1 : ℝ) * ξ| ≤ ξ := by
    have hlo := (le_div_iff₀ hξ).mp (Int.floor_le (scalarY (coeff p.1) p.2 / ξ))
    have hhi := (div_lt_iff₀ hξ).mp (Int.lt_floor_add_one (scalarY (coeff p.1) p.2 / ξ))
    rw [hcell1] at hlo hhi
    rw [abs_le]
    constructor <;> nlinarith only [hlo, hhi]
  have hqY := (eq_div_iff hq.ne').mp hY
  have hz : |point p 1 - ((z₀ + q * ξ * (β 1 : ℝ)) + point p 0 * zv)| ≤ q * ξ := by
    calc
      _ = |q * (scalarY (coeff p.1) p.2 - (β 1 : ℝ) * ξ)| := by
        congr 1
        nlinarith only [hqY]
      _ = q * |scalarY (coeff p.1) p.2 - (β 1 : ℝ) * ξ| := by
        rw [abs_mul, abs_of_pos hq]
      _ ≤ q * ξ := mul_le_mul_of_nonneg_left hspace hq.le
  refine ⟨?_, ?_⟩
  · rw [ht]
    calc
      _ = |q * (p.2 - (β 0 : ℝ) * ξ)| := by congr 1; ring
      _ = q * |p.2 - (β 0 : ℝ) * ξ| := by rw [abs_mul, abs_of_pos hq]
      _ ≤ q * ξ := mul_le_mul_of_nonneg_left htime hq.le
  · intro i
    fin_cases i
    · exact hz
    · change |point p 2 - (c 2 + c 4 * (z₀ + q * ξ * (β 1 : ℝ)) +
          point p 0 * (c 3 + c 4 * zv))| ≤ 2 * K * q * g
      calc
        _ = |(point p 2 - c 2 - point p 0 * c 3 - c 4 * point p 1) +
            c 4 * (point p 1 - ((z₀ + q * ξ * (β 1 : ℝ)) + point p 0 * zv))| := by
          congr 1
          ring
        _ ≤ |point p 2 - c 2 - point p 0 * c 3 - c 4 * point p 1| +
            |c 4 * (point p 1 - ((z₀ + q * ξ * (β 1 : ℝ)) + point p 0 * zv))| :=
          abs_add_le _ _
        _ ≤ K * q * g + K * (q * ξ) := by
          rw [abs_mul]
          exact add_le_add htrans (mul_le_mul hc hz (abs_nonneg _) hK)
        _ ≤ 2 * K * q * g := by nlinarith [mul_le_mul_of_nonneg_left hξg (mul_nonneg hK hq.le)]

/-- A scalar residual cell inherits the original fine joint caps, retaining
any external palette factor and the full physical volume q^3*g*mesh^2. -/
theorem normalized_residual_cell_cap
    {α : Type} [MeasurableSpace α]
    (law : Measure (α × ℝ)) (point : α × ℝ → Fin 3 → ℝ)
    (signal : α × ℝ → ℝ) (coeff : α → Fin 5 → ℝ)
    (background : (Fin 3 → ℝ) → ℝ) (condition : α × ℝ → Prop)
    (E : Set (α × ℝ)) {q g ξ δ Δ K L C t₀ z₀ zv : ℝ}
    (hq : 0 < q) (hg : 0 < g) (hξ : 0 < ξ) (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hC : 0 ≤ C) (hξg : ξ ≤ g)
    (c : Fin 5 → ℝ) (hc : |c 4| ≤ K)
    (hδcell : δ ≤ q * ξ) (hδtrans : δ ≤ 2 * K * q * g)
    (hmcell : L * δ ≤ q * ξ) (hmtrans : L * δ ≤ 2 * K * q * g)
    (hv₁ : |zv| ≤ L) (hv₂ : |c 3 + c 4 * zv| ≤ L)
    (β : Fin 2 → ℤ) (j : ℤ)
    (ht : ∀ p ∈ E, point p 0 = t₀ + q * p.2)
    (hY : ∀ p ∈ E, scalarY (coeff p.1) p.2 =
      (point p 1 - z₀ - zv * point p 0) / q)
    (hX : ∀ p ∈ E, scalarX (coeff p.1) p.2 = signal p - background (point p))
    (htrans : ∀ p ∈ E,
      |point p 2 - c 2 - point p 0 * c 3 - c 4 * point p 1| ≤ K * q * g)
    (hcell : ∀ p ∈ E, scalarCell (coeff p.1) p.2 ξ = β)
    (hsignal : ∀ p ∈ E, ⌊scalarX (coeff p.1) p.2 / Δ⌋ = j)
    (hcondition : ∀ p ∈ E, condition p)
    (hbackground : ∀ p ∈ E, ∀ y : Fin 3 → ℝ,
      (∀ i, |point p i - y i| ≤ δ) → |background (point p) - background y| ≤ Δ)
    (weight : ℝ≥0∞)
    (hcap : ∀ (β : Fin 3 → ℤ) (j : ℤ),
      law {p | (fun i => ⌊point p i / δ⌋) = β ∧
        ⌊signal p / Δ⌋ = j ∧ condition p} ≤ ENNReal.ofReal (C * δ ^ 3) * weight) :
    law E ≤ ENNReal.ofReal (8400 * K * C * q ^ 3 * g * ξ ^ 2) * weight := by
  have hv (i : Fin 2) : |(![zv, c 3 + c 4 * zv] : Fin 2 → ℝ) i| ≤ L := by
    fin_cases i <;> assumption
  have hdw (i : Fin 2) : δ ≤ (![q * ξ, 2 * K * q * g] : Fin 2 → ℝ) i := by
    fin_cases i <;> assumption
  have hmove (i : Fin 2) : L * δ ≤ (![q * ξ, 2 * K * q * g] : Fin 2 → ℝ) i := by
    fin_cases i <;> assumption
  have hwindow (p : α × ℝ) (hp : p ∈ E) :
      |signal p - background (point p) - (j : ℝ) * Δ| ≤ Δ := by
    have hlo := (le_div_iff₀ hΔ).mp (Int.floor_le (scalarX (coeff p.1) p.2 / Δ))
    have hhi := (div_lt_iff₀ hΔ).mp (Int.lt_floor_add_one (scalarX (coeff p.1) p.2 / Δ))
    rw [hsignal p hp, hX p hp] at hlo hhi
    rw [abs_le]
    constructor <;> nlinarith only [hlo, hhi]
  have hbound := measure_resolved_moving_slab law point signal background condition E
    hδ hΔ hδcell hL hC (t₀ + q * ξ * (β 0 : ℝ)) ((j : ℝ) * Δ)
    ![z₀ + q * ξ * (β 1 : ℝ), c 2 + c 4 * (z₀ + q * ξ * (β 1 : ℝ))]
    ![zv, c 3 + c 4 * zv] ![q * ξ, 2 * K * q * g]
    hv hdw hmove
    (fun p hp => scalar_cell_mem_movingBox point coeff hq hg hξ hK hξg c hc p β
      (ht p hp) (hY p hp) (hcell p hp) (htrans p hp))
    hcondition hwindow hbackground weight hcap
  convert hbound using 1
  congr 2
  dsimp
  ring

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
