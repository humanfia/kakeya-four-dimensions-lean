-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Direct.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Iteration
import Submission.WZ.Obl.wz_multiscale_finite_tower.Elementary
import Submission.WZ.Obl.wz_hairbrush_seed

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A single edge suffices whenever the permitted gap exponent is at least one. -/
theorem depth_of_mesh_ge_one {σ ω : ℝ} (hE : Endpoint σ ω) (hσ : σ ≤ 1 / 2)
    {q : ℕ} (hmesh : 1 ≤ 2 * (1 - ω / 100) ^ q) : DepthProperty σ ω q := by
  intro ε D hε hD
  obtain ⟨κ, hκ, η₀, hη₀, hcut⟩ := hE.away_from_zero hσ zero_lt_one hD
  refine ⟨1, zero_lt_one, κ, hκ, min ε η₀, lt_min hε hη₀, ?_⟩
  intro d hd hd100 n x v Y hA
  have hd1 : d < 1 := by linarith
  by_cases hsmall : d ≤ D
  · have hA' := hA.mono_error hd hd1.le (min_le_left ε η₀)
    refine Or.inr ⟨hsmall, n, x, v, Y, d ^ (-ε), d ^ (-ε), hA', Set.Subset.rfl,
      ?_, ?_⟩
    · exact mul_le_of_le_one_left (by positivity)
        (ENNReal.ofReal_le_one.mpr (Real.rpow_le_one hd.le hd1.le hε.le))
    · exact (tower_one hd hd1 hmesh hA.1 (fun i => (hA.2.1 i).1)
        (fun i => (hA.2.1 i).2.1) hA'.2.2.2.2.1).mono hd hd1.le le_rfl le_rfl
          (Nat.one_le_pow q 2 (by omega))
  · exact Or.inl (hcut d hd hd100 (le_of_not_ge hsmall) n x v Y
      (hA.mono_error hd hd1.le (min_le_right ε η₀)))

/-- Compare the desired expression with the hairbrush expression using the convex count. -/
lemma hairbrush_expression_comparison {σ ω α ε η a d : ℝ} {n : ℕ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hn : 0 < n) (ha : 0 ≤ a)
    (hσ : σ ≤ 1 / 2) (hcard : (n : ℝ) * d ^ 2 ≤ 16 * d ^ (-η))
    (hbudget : ε + α + (1 + η) * (1 / 2 - σ) ≤ ω) :
    (a / (16 : ℝ) ^ (1 / 2 - σ)) * d ^ (ω - α) * (n * d ^ 2) *
        (n * d) ^ (-σ) ≤
      a * d ^ ε * (n * d ^ 2) * (n * d) ^ (-(1 / 2 : ℝ)) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnd : 0 < (n : ℝ) * d := mul_pos hn' hd
  have ht : 0 ≤ (1 / 2 : ℝ) - σ := by linarith
  have h16 : 0 < (16 : ℝ) ^ (1 / 2 - σ) := Real.rpow_pos_of_pos (by norm_num) _
  have hnd_bound : (n : ℝ) * d ≤ 16 * d ^ (-η - 1) := by
    apply (mul_le_mul_iff_left₀ hd).mp
    calc
      (n : ℝ) * d * d = n * d ^ 2 := by ring
      _ ≤ 16 * d ^ (-η) := hcard
      _ = 16 * d ^ (-η - 1) * d := by
        have hid : d ^ (-η - 1) * d = d ^ (-η) := by
          calc
            _ = d ^ (-η - 1) * d ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = d ^ ((-η - 1) + 1) := (Real.rpow_add hd _ _).symm
            _ = _ := by congr 1; ring
        rw [mul_assoc, hid]
  have hpow := Real.rpow_le_rpow hnd.le hnd_bound ht
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (Real.rpow_nonneg hd.le _),
    ← Real.rpow_mul hd.le] at hpow
  have hcoeff : (a / (16 : ℝ) ^ (1 / 2 - σ)) * d ^ (ω - α) *
      (n * d) ^ (1 / 2 - σ) ≤ a * d ^ ε := by
    calc
      _ ≤ (a / (16 : ℝ) ^ (1 / 2 - σ)) * d ^ (ω - α) *
          ((16 : ℝ) ^ (1 / 2 - σ) * d ^ ((-η - 1) * (1 / 2 - σ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = a * d ^ (ω - α + (-η - 1) * (1 / 2 - σ)) := by
        rw [Real.rpow_add hd]
        field_simp
      _ ≤ a * d ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by nlinarith)) ha
  have hexp : (n * d) ^ (-σ) =
      (n * d) ^ (1 / 2 - σ) * (n * d) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hnd]
    congr 1
    ring
  rw [hexp]
  calc
    _ = ((a / (16 : ℝ) ^ (1 / 2 - σ)) * d ^ (ω - α) * (n * d) ^ (1 / 2 - σ)) *
        (n * d ^ 2) * (n * d) ^ (-(1 / 2 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity)

/-- Above the hairbrush threshold, the volume alternative holds at every scale and depth. -/
theorem volume_improvement_of_hairbrush {σ ω : ℝ}
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 2) (hgain : 1 / 2 - σ < ω) :
    ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n x v Y,
      Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
      VolumeBound σ ω κ α d n Y := by
  let t : ℝ := (ω - (1 / 2 - σ)) / 4
  have ht : 0 < t := by dsimp [t]; linarith
  obtain ⟨a, ha, η₀, hη₀, hseed⟩ := WangZahlLot.wz_hairbrush_seed t ht
  refine ⟨2 * t, by positivity, a / (16 : ℝ) ^ (1 / 2 - σ), by positivity,
    min η₀ t, lt_min hη₀ ht, ?_⟩
  intro d hd hd100 n x v Y hA
  have hd1 : d ≤ 1 := by linarith
  have hA' := hA.mono_error hd hd1 (min_le_left η₀ t)
  have hV := hseed d hd hd100 n x v Y hA'.1 (fun i => (hA'.2.1 i).1)
    (fun i => (hA'.2.1 i).2.1) hA'.2.2.1 (fun i => (hA'.2.1 i).2.2.1)
    (fun i => (hA'.2.1 i).2.2.2) hA'.2.2.2.1 hA'.2.2.2.2.1 hA'.2.2.2.2.2
  simp only [zero_add] at hV
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hV
  apply hairbrush_expression_comparison hd hd1 hA.1 ha.le hσ
    ((show FrameAdmissible d d (min η₀ t) n x v Y from hA).card_bound hd)
  have hη : min η₀ t ≤ t := min_le_right _ _
  have hη0 : 0 ≤ min η₀ t := (lt_min hη₀ ht).le
  dsimp [t] at *
  nlinarith

theorem depth_of_hairbrush {σ ω : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 2)
    (hgain : 1 / 2 - σ < ω) (q : ℕ) : DepthProperty σ ω q := by
  intro ε D hε hD
  obtain ⟨α, hα, κ, hκ, η, hη, hV⟩ := volume_improvement_of_hairbrush hσ0 hσ hgain
  exact ⟨α, hα, κ, hκ, η, hη, fun d hd hd100 n x v Y hA =>
    Or.inl (hV d hd hd100 n x v Y hA)⟩

end WangZahlLot.Obl.wz_multiscale_finite_tower
