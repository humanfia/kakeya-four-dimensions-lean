import Submission.Obl.k4_scalar_mesh_projection.Interfaces
import Submission.Obl.k4_scalar_mesh_projection.Extrapolation

namespace Submission.Obl.k4_scalar_mesh_projection

open Set Filter

/-- The original scalar mesh conclusion, used only to shorten the glue. -/
def FullTimeProjection : Prop :=
  (∀ d s m C S U ε : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (c : ℝ) (angular : Bool), (fun a : ℝ => (fun σ : ℝ => (fun y : α → ℝ → ℝ => (fun x : α → ℝ → ℝ => (fun z : α × ℝ → Fin 2 → ℤ => Measurable b → MeasureTheory.IsProbabilityMeasure ν → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ l i, |b l i| ≤ N ^ η) → N ^ (-C) ≤ c → c ≤ N ^ C → (∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s → μ {p | z p = q ∧ ⌊x p.1 p.2 / (N ^ (-r))⌋ = j} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * (N ^ (-r)) ^ d)) → (∃ F : Finset ((Fin 2 → ℤ) × ℤ), (F.card : ℝ) * σ ^ 2 ≤ N ^ η * c⁻¹ * a ^ (-d) ∧ ∀ᵐ p ∂μ, (z p, ⌊x p.1 p.2 / a⌋) ∈ F) → (angular = true → ∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U → μ {p | z p = q ∧ ⌊x p.1 p.2 / a⌋ = j ∧ ⌊b p.1 1 / (N ^ (-r))⌋ = k} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * a ^ d * N ^ (-S * r))) → ∃ (n : ℕ) (β : ℝ) (A : Fin n → Set α) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), σ / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * a) ∧ ENNReal.ofReal (c * a ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i, p.1 ∈ A i}) (fun p => ![⌊p.2 / σ⌋, ⌊y p.1 p.2 / σ⌋])) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4)) (fun l t => b l 0 + t * b l 1)) (N ^ (-m))) (N ^ (-s)))

/-- Fixed constants are absorbed after the requested output tolerance is fixed. -/
theorem exists_loss_threshold {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ N : ℝ, R ≤ N → 8 ≤ N ^ δ := by
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hδ).eventually_ge_atTop 8)
  exact ⟨max 2 R, le_max_left _ _, fun N hN => hR N ((le_max_right _ _).trans hN)⟩

/-- The block extrapolation losses fit within the final power budget. -/
theorem extrapolation_loss_budget {N ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε)
    (h8 : 8 ≤ N ^ (ε / 2)) : 8 * (N ^ (ε / 8)) ^ 3 ≤ N ^ ε := by
  have hN₀ : 0 ≤ N := by linarith
  have hmul : N ^ (ε / 2) * (N ^ (ε / 8)) ^ 3 = N ^ (7 * ε / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀, ← Real.rpow_add (by linarith : 0 < N)]
    congr 1
    ring
  calc
    8 * (N ^ (ε / 8)) ^ 3 ≤ N ^ (ε / 2) * (N ^ (ε / 8)) ^ 3 := by gcongr
    _ = N ^ (7 * ε / 8) := hmul
    _ ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- Long-block scalar mesh packets give the required whole-time packets. -/
theorem full_time_of_blocks (H : MeshBlockPackets) : FullTimeProjection := by
  intro d s m C S U ε hd hd₁ hs hsm hC hS hU hUm hε
  obtain ⟨R, hR₂, hR⟩ := exists_loss_threshold (by linarith : 0 < ε / 2)
  obtain ⟨η, hη, N₀, hN₀, h⟩ :=
    H d s m C S U (ε / 8) hd hd₁ hs hsm hC hS hU hUm (by linarith)
  refine ⟨η, hη, max N₀ R, hN₀.trans (le_max_left _ _), ?_⟩
  intro N hN α _ ν μ b c angular
  dsimp only
  intro hb hν hdom htime hmass hbnd hc₀ hc₁ hcap hsupport hang
  obtain ⟨n, β, t₀, q, A, u, v, P, hq, ht₀, ht₁, hβ₀, hβ₁, hβa,
      hA, hdA, hpack, htotal⟩ :=
    h N ((le_max_left _ _).trans hN) α ν μ b c angular hb hν hdom htime hmass
      hbnd hc₀ hc₁ hcap hsupport hang
  have hN₂ : 2 ≤ N := hN₀.trans ((le_max_left _ _).trans hN)
  have hN₁ : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hsmall : ε / 8 ≤ ε := by linarith
  have hpow : N ^ (ε / 8) ≤ N ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN₁ hsmall
  have hnegpow : N ^ (-ε) ≤ N ^ (-(ε / 8)) :=
    Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)
  have hqpos : 0 < q := (Real.rpow_pos_of_pos hNpos _).trans_le hq
  have hbudget : 8 * (N ^ (ε / 8)) ^ 3 ≤ N ^ ε :=
    extrapolation_loss_budget hN₁ hε (hR N ((le_max_right _ _).trans hN))
  have hfit : 8 * N ^ (ε / 8) / q ^ 2 ≤ N ^ ε := by
    have hqp : N ^ (ε / 8) * q ≥ 1 := by
      have h₁ := mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hNpos.le (ε / 8))
      rw [← Real.rpow_add hNpos] at h₁
      simpa only [add_neg_cancel, Real.rpow_zero] using h₁
    have hqinv : q⁻¹ ≤ N ^ (ε / 8) := by
      simpa only [one_div] using (div_le_iff₀ hqpos).2 (by linarith : 1 ≤ N ^ (ε / 8) * q)
    calc
      8 * N ^ (ε / 8) / q ^ 2 = 8 * N ^ (ε / 8) * (q⁻¹) ^ 2 := by
        rw [div_eq_mul_inv, inv_pow]
      _ ≤ 8 * N ^ (ε / 8) * (N ^ (ε / 8)) ^ 2 := by gcongr
      _ = 8 * (N ^ (ε / 8)) ^ 3 := by ring
      _ ≤ N ^ ε := hbudget
  have haff : 2 * N ^ (ε / 8) / q ≤ N ^ ε := by
    have hq₁ : q ≤ 1 := by linarith
    have hq₂ : q ^ 2 ≤ q := by nlinarith
    calc
      2 * N ^ (ε / 8) / q ≤ 8 * N ^ (ε / 8) / q ^ 2 := by
        apply (div_le_div_iff₀ hqpos (sq_pos_of_pos hqpos)).2
        nlinarith [Real.rpow_pos_of_pos hNpos (ε / 8)]
      _ ≤ N ^ ε := hfit
  have hβpos : 0 < β :=
    (div_pos (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hNpos _)).trans_le hβ₀
  have hcpos : 0 < c := (Real.rpow_pos_of_pos hNpos _).trans_le hc₀
  have hap : 0 ≤ N ^ (-s) := Real.rpow_nonneg hNpos.le _
  refine ⟨n, β, A, u, v, P, ?_, hβ₁.trans hpow,
    (fun hangular => hnegpow.trans (hβa hangular)), hA, hdA, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _) 
      (Real.rpow_pos_of_pos hNpos _) hpow).trans hβ₀
  · intro i
    obtain ⟨hcenter, hdeg, hnorm, hgeom, hfloor⟩ := hpack i
    refine ⟨hcenter.trans hpow, hdeg, ?_, ?_, ?_⟩
    · intro t ht w hw
      exact (scalar_adapted_norm_extrapolate (P i) hdeg (u i) (v i) β
        hqpos ht₀ ht₁ hnorm t ht w hw).trans hfit
    · intro l hl t ht
      have hconf := scalar_confinement_extrapolate hqpos ht₀ ht₁
        (fun t ht => (hgeom l hl t ht).1) t ht
      have hres := scalar_fit_extrapolate (P i) hdeg
        (b l 0) (b l 1) (b l 2) (b l 3) (b l 4)
        hqpos ht₀ ht₁ (fun t ht => (hgeom l hl t ht).2) t ht
      constructor
      · calc
          |b l 0 + t * b l 1 - u i - t * v i| ≤ 2 * (N ^ (ε / 8) * β) / q := hconf
          _ = (2 * N ^ (ε / 8) / q) * β := by ring
          _ ≤ N ^ ε * β := mul_le_mul_of_nonneg_right haff hβpos.le
      · calc
          |b l 2 + t * b l 3 + t ^ 2 * b l 4 -
            MvPolynomial.eval ![t, b l 0 + t * b l 1] (P i)| ≤
              8 * (N ^ (ε / 8) * N ^ (-s)) / q ^ 2 := hres
          _ = (8 * N ^ (ε / 8) / q ^ 2) * N ^ (-s) := by ring
          _ ≤ N ^ ε * N ^ (-s) := mul_le_mul_of_nonneg_right hfit hap
    · exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hcpos.le (Real.rpow_nonneg hap d)) hβpos.le)
        (Real.rpow_pos_of_pos hNpos _) hpow)).trans hfloor
  · exact (ENNReal.ofReal_le_ofReal hnegpow).trans htotal

end Submission.Obl.k4_scalar_mesh_projection
