import Submission.Obl.k4_horizontal_wide_interval_return.AngularCaps
import Submission.Obl.k4_horizontal_wide_interval_return.NormalizeCaps

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set
open Submission.Lib.K4MovingMeshBoxes
open scoped ENNReal

namespace CellFrame

variable {F : CellFrame}

/-- The complete ordinary and angular scalar cap families follow from the
original finite joint caps, the unchanged assignment floor, and a sufficiently
fine fixed mesh. Very small angular rates use the ordinary cap and the input
loss; the original palette hypotheses are needed only above `rmin`. -/
theorem scalar_caps_from_original {α : Type*} [MeasurableSpace α]
    (lam : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (mass : ℝ≥0∞) (E : Set (α × ℝ))
    {N η S v U rmin H Lbound σ δ C K P d : ℝ} (weight : ℝ → ℤ → ℝ≥0∞)
    (hN : 2 ≤ N) (hη : 0 < η) (hS : 0 < S) (hv : 0 ≤ v)
    (hrmin : S * rmin ≤ η / 2)
    (hH : 1 ≤ H) (hLbound : 0 ≤ Lbound)
    (hq : 0 < F.q) (hg : 0 < F.g) (hg1 : F.g ≤ 1) (ha : 0 < F.a)
    (hσ : 0 < σ) (hσg : σ ≤ F.g) (hδ : 0 < δ)
    (hmesh₀ : 4 * H ^ 2 * δ ≤ F.q * σ)
    (hmesh₁ : 4 * H ^ 2 * δ ≤ F.q * F.g)
    (hmeshOffset : (3 * Lbound * (F.q * F.g) + 40 * F.a * H ^ 3) * δ ≤
      F.a * N ^ (-v) * (F.q * F.g))
    (hc : ∀ i, |F.c i| ≤ H) (hC : ∀ i, |F.C i| ≤ H)
    (hL : ∀ i, |F.L i| ≤ Lbound) (hcapC : 0 ≤ C) (hK : 0 < K) (hP : 0 ≤ P)
    (hfloor : ENNReal.ofReal (F.a ^ d * F.q ^ 2 * F.g / K) ≤ mass)
    (hordinaryBudget : 3000 * C * H * K ≤ N ^ (η / 2))
    (hangularBudget : 6000 * C * H * P * K ≤ N ^ (η / 2))
    (hsupp : ∀ᵐ p ∂lam, p ∈ E)
    (hE : ∀ p ∈ E, p.2 ∈ Icc F.t₀ (F.t₀ + F.q) ∧
      |F.zZ p.2 (lineZ (b p.1) p.2)| ≤ H ∧
      |F.U p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2)| ≤ H)
    (hcap : ∀ r : ℝ, 0 ≤ r → r ≤ v → ∀ c j, lam
      {p | baseMesh δ (![p.2, lineZ (b p.1) p.2, lineY (b p.1) p.2] : Fin 3 → ℝ) = c ∧
        ⌊lineX (b p.1) p.2 / (F.a * N ^ (-r))⌋ = j} ≤
      ENNReal.ofReal (C * δ ^ 3 * (F.a * N ^ (-r)) ^ d))
    (hpalette : ∀ r : ℝ, rmin ≤ r → r ≤ U → ∀ ℓ,
      weight r ℓ ≤ ENNReal.ofReal (P * N ^ (-S * r)))
    (hjoint : ∀ r : ℝ, rmin ≤ r → r ≤ U → ∀ c j ℓ, lam
      {p | baseMesh δ (![p.2, lineZ (b p.1) p.2, lineY (b p.1) p.2] : Fin 3 → ℝ) = c ∧
        ⌊lineX (b p.1) p.2 / (F.a * N ^ (-v))⌋ = j ∧ ⌊b p.1 3 / N ^ (-r)⌋ = ℓ} ≤
      ENNReal.ofReal (C * δ ^ 3 * (F.a * N ^ (-v)) ^ d) * weight r ℓ) :
    (∀ (r : ℝ) (q₀ : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ v →
      lam {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
        ⌊F.cellSig (b p.1) p.2 / N ^ (-r)⌋ = j} ≤
        ENNReal.ofReal (N ^ η * σ ^ 2 * (N ^ (-r)) ^ d) * (ENNReal.ofReal F.q * mass)) ∧
    (∀ (r : ℝ) (q₀ : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U →
      lam {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
        ⌊F.cellSig (b p.1) p.2 / N ^ (-v)⌋ = j ∧ ⌊F.y₁ (b p.1) / N ^ (-r)⌋ = k} ≤
        ENNReal.ofReal (N ^ η * σ ^ 2 * (N ^ (-v)) ^ d * N ^ (-S * r)) *
          (ENNReal.ofReal F.q * mass)) := by
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hηhalf : N ^ (η / 2) ≤ N ^ η :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hforget (G : Set (α × ℝ)) : lam (E ∩ G) = lam G := by
    apply measure_congr
    filter_upwards [hsupp] with p hp
    simp only [mem_inter_iff, hp, true_and]
  have hordinary : ∀ (r : ℝ) (q₀ : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ v →
      lam {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
        ⌊F.cellSig (b p.1) p.2 / N ^ (-r)⌋ = j} ≤
        ENNReal.ofReal (N ^ (η / 2) * σ ^ 2 * (N ^ (-r)) ^ d) *
          (ENNReal.ofReal F.q * mass) := by
    intro r q₀ j hr hrv
    have hρ : 0 < N ^ (-r) := Real.rpow_pos_of_pos hNpos _
    have hρle : N ^ (-v) ≤ N ^ (-r) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hoff : (3 * Lbound * (F.q * F.g) + 40 * F.a * H ^ 3) * δ ≤
        F.a * N ^ (-r) * (F.q * F.g) :=
      hmeshOffset.trans (by gcongr)
    have hraw := cell_residual_cap lam b (1 : ℝ≥0∞) hH hLbound hq hg hg1 ha hσ hσg hρ hδ
      hmesh₀ hmesh₁ hoff hc hC hL hcapC E hE q₀ j (by
        intro c j'; simpa only [mul_one] using hcap r hr hrv c j')
    rw [hforget] at hraw
    simp only [mul_one] at hraw
    have hnorm := cell_cap_normalization (σ := σ) ha hq hg hρ hK
      (show 0 ≤ 3000 * C * H by positivity) mass (1 : ℝ≥0∞) hfloor
    simp only [mul_one] at hnorm
    refine (hraw.trans hnorm).trans ?_
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    gcongr
  constructor
  · intro r q₀ j hr hrv
    refine (hordinary r q₀ j hr hrv).trans ?_
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · intro r q₀ j k hr hrU
    by_cases hlarge : rmin ≤ r
    · have hρ : 0 < N ^ (-v) := Real.rpow_pos_of_pos hNpos _
      have hraw := cell_residual_angular_cap lam b hb (weight r) hH hLbound hq hg hg1 ha
        hσ hσg hρ hδ hmesh₀ hmesh₁ hmeshOffset hc hC hL hcapC
        (mul_nonneg hP (Real.rpow_nonneg hNpos.le _)) E hE q₀ j k
        (hpalette r hlarge hrU) (hjoint r hlarge hrU)
      rw [hforget] at hraw
      have hnorm := cell_cap_normalization (σ := σ) ha hq hg hρ hK
        (show 0 ≤ 6000 * C * H * (P * N ^ (-S * r)) by positivity)
        mass (1 : ℝ≥0∞) hfloor
      simp only [mul_one] at hnorm
      refine (hraw.trans hnorm).trans ?_
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      calc 6000 * C * H * (P * N ^ (-S * r)) * K * σ ^ 2 * (N ^ (-v)) ^ d
          = (6000 * C * H * P * K) * σ ^ 2 * (N ^ (-v)) ^ d * N ^ (-S * r) := by ring
        _ ≤ N ^ η * σ ^ 2 * (N ^ (-v)) ^ d * N ^ (-S * r) := by
          gcongr
          exact hangularBudget.trans hηhalf
    · have hsmall : S * r ≤ η / 2 := by
        have h := mul_le_mul_of_nonneg_left (le_of_not_ge hlarge) hS.le
        linarith
      have hsub : {p : α × ℝ | F.cellCode σ (b p.1) p.2 = q₀ ∧
          ⌊F.cellSig (b p.1) p.2 / N ^ (-v)⌋ = j ∧ ⌊F.y₁ (b p.1) / N ^ (-r)⌋ = k} ⊆
          {p : α × ℝ | F.cellCode σ (b p.1) p.2 = q₀ ∧ ⌊F.cellSig (b p.1) p.2 / N ^ (-v)⌋ = j} :=
        fun _ hp => ⟨hp.1, hp.2.1⟩
      refine ((measure_mono hsub).trans (hordinary v q₀ j hv le_rfl)).trans ?_
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      calc N ^ (η / 2) * σ ^ 2 * (N ^ (-v)) ^ d
          ≤ (N ^ η * N ^ (-S * r)) * σ ^ 2 * (N ^ (-v)) ^ d := by
            gcongr
            exact angular_saving_at_small_rate hN1 hsmall
        _ = N ^ η * σ ^ 2 * (N ^ (-v)) ^ d * N ^ (-S * r) := by ring

end CellFrame

end Submission.Obl.k4_horizontal_wide_interval_return
