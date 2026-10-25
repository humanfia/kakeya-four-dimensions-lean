-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.CoarseClassMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.WeightedClassMass
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.NormalizedQuotas

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

lemma relative_dyadic_scale {j L : ℕ} (hjL : j ≤ L) :
    ((2 : ℝ) ^ L)⁻¹ = (2 * ((2 : ℝ) ^ j)⁻¹) * ((2 : ℝ) ^ (L - j + 1))⁻¹ := by
  have he : (2 : ℝ) ^ L = 2 ^ j * 2 ^ (L - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjL]
  rw [he, pow_succ]
  field_simp

/-- Apply the cinematic light-mass estimate to a class supplied by the maximal-density
partition, including the rescaling of its dyadic quotas. -/
theorem coarse_cell_light_mass {δ c s η ε R : ℝ} (hδ : 0 < δ)
    {n j L q : ℕ} (hj3 : 3 ≤ j) (hjL : j ≤ L)
    (hwidth : 13 * δ ≤ ((2 : ℝ) ^ L)⁻¹)
    (x v : Fin n → Space) (Y : Fin n → Set Space) (Q : Finset (Fin n))
    (i₀ : Fin n) (hi₀ : i₀ ∈ Q)
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hY : ∀ i ∈ Q, Y i ⊆ Tube δ (x i) (v i))
    (hc : |c| ≤ 3) (hthin : ∀ i ∈ Q, |slope (v i) 0 - c| ≤ δ)
    (hcell : ∀ i ∈ Q, dyadicLabel j (parameters (x i) (v i)) =
      dyadicLabel j (parameters (x i₀) (v i₀)))
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hcount : ∀ k, j ≤ k → k ≤ L → ∀ l : Fin 3 → ℤ,
      ((Q.filter (fun i => dyadicLabel k (parameters (x i) (v i)) = l)).card : ℝ) ≤
        (Q.card : ℝ) * ((((2 : ℝ) ^ k)⁻¹ / ((2 : ℝ) ^ j)⁻¹) ^ s))
    (hR : 1 < R) (hq : 0 < q) (hsize : 2 * (Q.card : ℝ) < R ^ q)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    (hη : 54 ≤ (((2 : ℝ) ^ (L - j + 1))⁻¹) ^ (-η))
    (hC : CinematicMomentAt (((2 : ℝ) ^ (L - j + 1))⁻¹) η ε f)
    {X A : Set (ℝ × ℝ)} {θ : ℝ≥0∞}
    (hX : ∀ i ∈ Q, projection f '' Y i ⊆ X)
    (hlight : ∀ S : Set (ℝ × ℝ), volume (X ∩ A ∩ S) ≤
      θ * volume (thickening (2 * ((2 : ℝ) ^ j)⁻¹) S)) :
    let ρ := 2 * ((2 : ℝ) ^ j)⁻¹
    let τ := ((2 : ℝ) ^ (L - j + 1))⁻¹
    (∑ i ∈ Q, volume (Y i ∩ projection f ⁻¹' A)) ^ 3 ≤
      ENNReal.ofReal (6048 * q * R * τ ^ s * Q.card) ^ 3 *
        (ENNReal.ofReal (6 * δ) ^ 3 * ENNReal.ofReal ρ ^ 2 *
          (θ * ENNReal.ofReal (432 * ρ)) * ENNReal.ofReal (τ ^ (-ε)) ^ 2) := by
  let ρ := 2 * ((2 : ℝ) ^ j)⁻¹
  let τ := ((2 : ℝ) ^ (L - j + 1))⁻¹
  let σ := ((2 : ℝ) ^ L)⁻¹
  let q₀ := parameters (x i₀) (v i₀)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hσρ : σ ≤ ρ := by
    have hh := (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjL)
    change ((2 : ℝ) ^ L)⁻¹ ≤ 2 * ((2 : ℝ) ^ j)⁻¹
    nlinarith [show (0 : ℝ) < ((2 : ℝ) ^ j)⁻¹ by positivity]
  have hρ1 : ρ ≤ 1 := by
    have hh := (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj3)
    norm_num at hh
    dsimp [ρ]
    linarith
  have hquotas := normalized_dyadic_quota Q (fun i => parameters (x i) (v i)) q₀ hjL hs hs1 hcount
  have hD : 1 ≤ 108 * τ ^ s * Q.card := by
    have hl := hquotas (L - j + 1) le_rfl
      (dyadicLabel (L - j + 1) (normalizedParameters ρ q₀ (parameters (x i₀) (v i₀))))
    have hc1 : 1 ≤ (Q.filter (fun i => dyadicLabel (L - j + 1)
        (normalizedParameters ρ q₀ (parameters (x i) (v i))) =
        dyadicLabel (L - j + 1) (normalizedParameters ρ q₀ (parameters (x i₀) (v i₀))))).card :=
      Finset.one_le_card.mpr ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, rfl⟩⟩
    simpa only [Nat.cast_one] using (Nat.cast_le.mpr hc1).trans hl
  have hdiam : ∀ i ∈ Q, dist (parameters (x i) (v i)) q₀ ≤ ρ := by
    intro i hi
    have hh := dist_le_of_dyadicLabel_eq (hcell i hi)
    have hroot : Real.sqrt 3 ≤ 2 := by
      have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith [Real.sqrt_nonneg 3]
    exact hh.trans (mul_le_mul_of_nonneg_right hroot (by positivity))
  have hnorm : ‖q₀‖ ≤ 6 := by
    have hx := hball i₀ ((self_subset_thickening hδ _) (left_mem_segment ℝ _ _))
    have hxn : ‖x i₀‖ ≤ 1 := (by simpa only [mem_ball, dist_zero_right] using hx : ‖x i₀‖ < 1).le
    exact (parameters_norm_le_five hxn (hv i₀) (htrans i₀)).trans (by norm_num)
  have hh : 0 ≤ σ - 12 * δ := by dsimp [σ]; linarith
  have hstrip : 12 * δ + (σ - 12 * δ) = σ := by ring
  have hm := light_mass_of_dyadic_quotas Q x v Y hf hderiv hf0 hδ hh
    (by rw [hstrip]; exact hσρ) hρ1 hc q₀ hnorm
    (fun i _ => hv i) (fun i _ => htrans i) (fun i _ => hball i) hY
    (fun i hi => (hthin i hi).trans (by dsimp [σ]; linarith)) hdiam
    (L - j + 1) (by rw [hstrip]; exact relative_dyadic_scale hjL) hD hR hq hsize
    (dyadic_frostman_linear_quota Q (fun i => normalizedParameters ρ q₀ (parameters (x i) (v i)))
      (L - j + 1) (by norm_num : (0 : ℝ) ≤ 108) hs1 hquotas)
    hη hC hX hlight
  have he : 2 * q * R * ((108 * τ ^ s * Q.card) * 28) =
      6048 * q * R * τ ^ s * Q.card := by ring
  rw [he] at hm
  exact hm

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
