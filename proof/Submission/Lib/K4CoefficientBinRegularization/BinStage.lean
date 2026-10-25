-- Adapted from: here:o202 (session x0952), Regularization/BinStage.lean.
import Submission.Lib.K4CoefficientBinRegularization.BinRegularization

namespace Submission.Lib.K4CoefficientBinRegularization.Reg

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- The instantaneous coefficient counting cost has a fixed polynomial bound. -/
theorem packingBound_le {K : ℝ} (hK : 1 ≤ K) :
    packingBound K ≤ (81 * 23 ^ 4) * K ^ 11 := by
  have hK0 : 0 ≤ K := by linarith
  have hKsq : 1 ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  calc
    packingBound K ≤ (9 * K) ^ 2 * K * (23 * K ^ 2) ^ 4 := by
      dsimp [packingBound]
      gcongr <;> linarith
    _ = _ := by ring

/-- Relative coefficient-bin regularization in the exact four-stage bootstrap interface. -/
theorem stageBin : StageBin := by
  intro d hd hd1 c hc ε hε
  let η : ℝ := ε / 100
  let σ : ℝ := ε / (4 * c)
  have hη : 0 < η := by dsimp [η]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  let D : ℝ := 1 - (2 : ℝ) ^ (-σ)
  have hD : 0 < D := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith : -σ < 0))
  let A : ℝ := 4 * 81 * 23 ^ 4
  have hA : 0 < A := by norm_num [A]
  have hcompare (C a b : ℝ) (hab : a < b) :
      ∀ᶠ N : ℝ in atTop, C * N ^ a ≤ N ^ b := by
    have hlarge := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C
    filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with N hC hNp
    have heq : N ^ (b - a) * N ^ a = N ^ b := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    exact (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hNp.le a)).trans_eq heq
  have hev := hcompare (4 * A / D) (13 * η) (ε / 2) (by dsimp [η]; linarith)
  have hev' := hcompare 2 η ε (by dsimp [η]; linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hev.and hev')
  refine ⟨η, hη, by dsimp [η]; linarith, max N₁ 2, le_max_right _ _, ?_⟩
  intro N hN Ω _ ν hν y β γ E F hU _hLocal _hRow hSlope
  letI := hν
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  obtain ⟨hbudget, hfinal⟩ := hN₁ N ((le_max_left _ _).trans hN)
  let K : ℝ := N ^ η
  let ζ : ℝ := N ^ (-c)
  let δ : ℝ := 1 / (4 * K)
  let θ : ℝ := N ^ (-(ε / 2))
  have hK : 1 ≤ K := Real.one_le_rpow hN1 hη.le
  have hK0 : 0 < K := by linarith
  have hζ : 0 < ζ := Real.rpow_pos_of_pos hN0 _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hθ : 0 < θ := Real.rpow_pos_of_pos hN0 _
  have hpacking : packingBound K / δ ≤ A * K ^ 12 := by
    calc
      _ = packingBound K * (4 * K) := by dsimp [δ]; field_simp
      _ ≤ ((81 * 23 ^ 4) * K ^ 11) * (4 * K) :=
        mul_le_mul_of_nonneg_right (packingBound_le hK) (by positivity)
      _ = _ := by dsimp [A]; ring
  have hK13 : K ^ 13 = N ^ (13 * η) := by
    dsimp [K]
    rw [← Real.rpow_mul_natCast hN0.le]
    congr 1
    ring
  have hbudget' : (4 * A / D) * K ^ 13 ≤ N ^ (ε / 2) := by rw [hK13]; exact hbudget
  have hlight : ((packingBound K / δ) * θ) / D ≤ 1 / (4 * K) := by
    calc
      _ ≤ ((A * K ^ 12) * θ) / D := by gcongr
      _ ≤ 1 / (4 * K) := by
        apply (le_div_iff₀ (show 0 < 4 * K by positivity)).mpr
        have heq : (((A * K ^ 12) * θ) / D) * (4 * K) =
            ((4 * A / D) * K ^ 13) / N ^ (ε / 2) := by
          dsimp [θ]
          rw [Real.rpow_neg hN0.le]
          field_simp
          <;> ring
        rw [heq]
        exact (div_le_one (Real.rpow_pos_of_pos hN0 _)).mpr hbudget'
  obtain ⟨E', hsub, hE', hdel, hbin⟩ :=
    exists_bin_regularization hU hSlope hK hζ hδ hσ hθ
  have hdel' : (ν.prod volume) (E \ E') ≤ ENNReal.ofReal (1 / (2 * K)) := by
    refine hdel.trans (ENNReal.ofReal_le_ofReal ?_)
    change δ + ((packingBound K / δ) * θ) / D ≤ _
    calc
      _ ≤ δ + 1 / (4 * K) := add_le_add le_rfl hlight
      _ = _ := by dsimp [δ]; field_simp; ring
  have hmass : ENNReal.ofReal (1 / (2 * K)) ≤ (ν.prod volume) E' := by
    have horig : ENNReal.ofReal K⁻¹ ≤
        (ν.prod volume) E' + ENNReal.ofReal (1 / (2 * K)) := by
      calc
        _ ≤ (ν.prod volume) E := hU.mass
        _ ≤ (ν.prod volume) (E' ∪ (E \ E')) := by
          apply measure_mono
          intro p hp
          by_cases hp' : p ∈ E'
          · exact Or.inl hp'
          · exact Or.inr ⟨hp, hp'⟩
        _ ≤ (ν.prod volume) E' + (ν.prod volume) (E \ E') := measure_union_le _ _
        _ ≤ _ := add_le_add le_rfl hdel'
    have heq : ENNReal.ofReal K⁻¹ = ENNReal.ofReal (1 / (2 * K)) +
        ENNReal.ofReal (1 / (2 * K)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    rw [heq] at horig
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp horig
  have hNε : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 _
  have hmass' : ENNReal.ofReal (N ^ ε)⁻¹ ≤ (ν.prod volume) E' := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans hmass
    simpa only [one_div] using inv_anti₀ (by positivity : 0 < 2 * K) hfinal
  have hKK : K ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [η]; linarith)
  have hcap : K / (θ * ζ ^ σ) ≤ N ^ ε := by
    have heq : θ * ζ ^ σ = N ^ (-(3 * ε / 4)) := by
      dsimp [θ, ζ]
      rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      congr 1
      dsimp [σ]
      field_simp
      ring
    rw [heq]
    change N ^ η / N ^ (-(3 * ε / 4)) ≤ N ^ ε
    rw [← Real.rpow_sub hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    dsimp [η]
    linarith
  refine ⟨E', hsub, (hU.mono_bound hK0 hKK hζ.le).restrict_labels hE' hsub hmass', ?_⟩
  exact hbin.mono (Subset.refl E') hcap hζ

end
end Submission.Lib.K4CoefficientBinRegularization.Reg
