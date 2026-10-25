/- Adapted from: here:o222, session x0774, commit 3c748bb8.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactSampleSequence.lean. -/
import Submission.Lib.K4ContactAffine.NativeCoarseBudget
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.SubpowerEnvelope
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! Coarse affine preparation directly on the retained original incidence law. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set Filter
open Submission.Lib.K4ContactAffine (NativeSample native_coarse_cover_with_polynomial_budget)
open Submission.Obl.k4_contact_fine_labels_from_coarse_cover (exists_subpower_envelope)
open Submission.Obl.k4_profile_density_bounds
  (eventually_const_mul_rpow_lt eventually_subpower_mul_rpow_lt)

noncomputable section

/-- The contact affine palette is prepared on an arbitrary original sample
space. Its time map may already be the parent-block time normalization. -/
theorem exists_subpower_sample_palettes {Ω : Type} [MeasurableSpace Ω]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hKsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (ι : ℕ → Type*) (s : (k : ℕ) → ι k → NativeSample Ω)
    (hπfin : ∀ k j, IsFiniteMeasure (s k j).π)
    {S e₀ : ℝ} (hS : 0 < S) (he₀ : 0 < e₀)
    (hdata : ∀ᶠ k in atTop, ∀ j : ι k, (s k j).P.totalDegree ≤ 2 ∧
      (∀ᵐ u ∂(s k j).μ, (s k j).Good (K k) (N k ^ (-e₀)) u) ∧
      ENNReal.ofReal ((K k)⁻¹) ≤ (s k j).μ univ)
    (hcaps : ∀ r v : ℝ, 0 < r → 0 < v → ∀ᶠ k in atTop, ∀ j : ι k,
      (s k j).PureCap (N k ^ (-r)) (K k) ∧
      (s k j).JointCap (N k ^ (-r)) (N k ^ (-v)) (K k) ∧
      ∀ l : ℤ, (s k j).π {w | ⌊w / N k ^ (-v)⌋ = l} ≤
        ENNReal.ofReal (K k * N k ^ (-S * v))) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, ∀ j : ι k, (s k j).Cover (H k) := by
  have hN1 : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
  have hNp : ∀ k, 0 < N k := fun k => by linarith [hN k]
  obtain ⟨D, hD, hpal⟩ := native_coarse_cover_with_polynomial_budget
  apply exists_subpower_envelope N hN1 (fun k E => ∀ j : ι k, (s k j).Cover E)
  intro ε hε
  let θ : ℝ := min ε (min e₀ 1) / 1000
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθε : 80 * θ < ε := by
    have := min_le_left ε (min e₀ 1)
    dsimp [θ]
    linarith
  have hθe : 80 * θ < e₀ := by
    have := (min_le_right ε (min e₀ 1)).trans (min_le_left e₀ 1)
    dsimp [θ]
    linarith
  have hθ1 : 80 * θ < 1 := by
    have := (min_le_right ε (min e₀ 1)).trans (min_le_right e₀ 1)
    dsimp [θ]
    linarith
  let v : ℝ := θ / 2
  have hv : 0 < v := by dsimp [v]; positivity
  have hθv : 0 < θ - v := by dsimp [v]; linarith
  filter_upwards [hdata, hcaps 1 v one_pos hv, hNt.eventually (eventually_ge_atTop 4),
    eventually_subpower_mul_rpow_lt hN1 hNt hK hKsub 1 hθ
      (show (0 : ℝ) ≤ 432 by norm_num),
    eventually_subpower_mul_rpow_lt hN1 hNt hK hKsub 1 hθv
      (show (0 : ℝ) ≤ 32 / 3 by norm_num),
    eventually_subpower_mul_rpow_lt hN1 hNt hK hKsub 4 hθ
      (show (0 : ℝ) ≤ 497664 by norm_num),
    eventually_subpower_mul_rpow_lt hN1 hNt hK hKsub 5
      (show -S * v < (0 : ℝ) by nlinarith)
      (show (0 : ℝ) ≤ 12 * 243 * 32 ^ 2 by norm_num),
    eventually_const_mul_rpow_lt hNt (show 80 * θ - e₀ < (0 : ℝ) by linarith) (2 * D),
    eventually_const_mul_rpow_lt hNt (show 80 * θ - 1 < (0 : ℝ) by linarith) (6 * D),
    eventually_const_mul_rpow_lt hNt hθε D]
    with k hkdata hkcaps hN4 hΛK hgap0 hdensity0 hheavy hmarginE hmarginδ herror
  intro j
  have hk := hkdata j
  have hcap := hkcaps j
  simp only [Real.rpow_zero, pow_one, mul_one] at hΛK hgap0 hdensity0 hheavy hmarginE hmarginδ
  letI : IsFiniteMeasure (s k j).π := hπfin k j
  have hKp : 0 < K k := zero_lt_one.trans_le (hK k)
  let R : ℝ := 32 * K k
  let Λ : ℝ := N k ^ θ
  let δ : ℝ := N k ^ (-(1 : ℝ))
  let η : ℝ := N k ^ (-v)
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [hK k]
  have hΛ : 0 < Λ := Real.rpow_pos_of_pos (hNp k) _
  have hδ : 0 < δ := Real.rpow_pos_of_pos (hNp k) _
  have hη : 0 < η := Real.rpow_pos_of_pos (hNp k) _
  have hδ4 : δ ≤ 1 / 4 := by
    simpa only [δ, Real.rpow_neg_one, one_div] using
      one_div_le_one_div_of_le (show (0 : ℝ) < 4 by norm_num) hN4
  have hgap : Λ⁻¹ ≤ 3 * η / R := by
    apply (le_div_iff₀ hR).mpr
    calc
      Λ⁻¹ * R = R / Λ := by ring
      _ ≤ 3 * η := by
        apply (div_le_iff₀ hΛ).mpr
        calc
          R ≤ 3 * N k ^ (θ - v) := by dsimp [R]; nlinarith [hgap0.le]
          _ = 3 * η * Λ := by
            dsimp [η, Λ]
            rw [sub_eq_add_neg, Real.rpow_add (hNp k)]
            ring
  have hdensity : Λ⁻¹ ≤ (K k)⁻¹ / (2 * (243 * K k * R ^ 2)) := by
    have h := inv_anti₀ (by positivity : 0 < 497664 * K k ^ 4) hdensity0.le
    apply h.trans_eq
    dsimp [R]
    field_simp
    ring
  have hheavyreal : 6 * (243 * K k * R ^ 2) * (K k * N k ^ (-S * v)) <
      (K k)⁻¹ / 2 := by
    have heq : (K k)⁻¹ / 2 = 1 / (2 * K k) := by field_simp
    rw [heq, lt_div_iff₀ (by positivity : 0 < 2 * K k)]
    calc
      _ = (12 * 243 * 32 ^ 2) * K k ^ 5 * N k ^ (-S * v) := by dsimp [R]; ring
      _ < 1 := hheavy
  have hsmall : 6 * ENNReal.ofReal (243 * K k * R ^ 2) *
      ENNReal.ofReal (K k * N k ^ (-S * v)) < ENNReal.ofReal ((K k)⁻¹ / 2) := by
    calc
      _ = ENNReal.ofReal (6 * (243 * K k * R ^ 2) * (K k * N k ^ (-S * v))) := by
        rw [show (6 : ENNReal) = ENNReal.ofReal 6 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hheavyreal
  have hpow : Λ ^ 80 = N k ^ (80 * θ) := by
    dsimp [Λ]
    rw [← Real.rpow_mul_natCast (hNp k).le]
    congr 1
    ring
  have hmargin : D * Λ ^ 80 * (N k ^ (-e₀) / R + 3 * δ) ≤ 1 := by
    calc
      _ ≤ D * N k ^ (80 * θ) * (N k ^ (-e₀) + 3 * δ) := by
        rw [hpow]
        exact mul_le_mul_of_nonneg_left
          (add_le_add (div_le_self (Real.rpow_nonneg (hNp k).le _) hR1) le_rfl)
          (by positivity)
      _ = D * N k ^ (80 * θ - e₀) + 3 * D * N k ^ (80 * θ - 1) := by
        dsimp [δ]
        rw [sub_eq_add_neg, sub_eq_add_neg, Real.rpow_add (hNp k), Real.rpow_add (hNp k)]
        ring
      _ ≤ 1 := by linarith
  have hcover := hpal (s k j) (K k) R Λ (N k ^ (-e₀)) δ η ((K k)⁻¹) (K k)
    (K k * N k ^ (-S * v)) (hK k) le_rfl
    (Real.one_le_rpow (hN1 k) hθ.le) hΛK.le hKp (inv_pos.mpr hKp) hδ hδ4 hη
    hgap hdensity (by positivity) hk.1 hk.2.1 hk.2.2 hcap.1 hcap.2.1 hcap.2.2 hsmall hmargin
  exact NativeSample.Cover.mono (s k j) hcover (by simpa only [hpow] using herror.le)


/-- Coarse preparation on the indices where the original row source exists. -/
theorem exists_subpower_sample_palette_on {Ω : Type} [MeasurableSpace Ω]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hKsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (ok : ℕ → Prop) (s : ℕ → NativeSample Ω) (hπfin : ∀ k, IsFiniteMeasure (s k).π)
    {S e₀ : ℝ} (hS : 0 < S) (he₀ : 0 < e₀)
    (hdata : ∀ᶠ k in atTop, ok k → (s k).P.totalDegree ≤ 2 ∧
      (∀ᵐ u ∂(s k).μ, (s k).Good (K k) (N k ^ (-e₀)) u) ∧
      ENNReal.ofReal ((K k)⁻¹) ≤ (s k).μ univ)
    (hcaps : ∀ r v : ℝ, 0 < r → 0 < v → ∀ᶠ k in atTop, ok k →
      (s k).PureCap (N k ^ (-r)) (K k) ∧
      (s k).JointCap (N k ^ (-r)) (N k ^ (-v)) (K k) ∧
      ∀ j : ℤ, (s k).π {w | ⌊w / N k ^ (-v)⌋ = j} ≤
        ENNReal.ofReal (K k * N k ^ (-S * v))) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, ok k → (s k).Cover (H k) := by
  obtain ⟨H, hH, hHsub, hcover⟩ := exists_subpower_sample_palettes N K hN hNt hK hKsub
    (fun k => PLift (ok k)) (fun k _ => s k) (fun k _ => hπfin k) hS he₀
    (hdata.mono fun _ hk j => hk j.down)
    (fun r v hr hv => (hcaps r v hr hv).mono fun _ hk j => hk j.down)
  exact ⟨H, hH, hHsub, hcover.mono fun _ hk ho => hk ⟨ho⟩⟩

/-- The unconditional version of coarse affine preparation. -/
theorem exists_subpower_sample_palette {Ω : Type} [MeasurableSpace Ω]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hKsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (s : ℕ → NativeSample Ω) (hπfin : ∀ k, IsFiniteMeasure (s k).π)
    {S e₀ : ℝ} (hS : 0 < S) (he₀ : 0 < e₀)
    (hdata : ∀ᶠ k in atTop, (s k).P.totalDegree ≤ 2 ∧
      (∀ᵐ u ∂(s k).μ, (s k).Good (K k) (N k ^ (-e₀)) u) ∧
      ENNReal.ofReal ((K k)⁻¹) ≤ (s k).μ univ)
    (hcaps : ∀ r v : ℝ, 0 < r → 0 < v → ∀ᶠ k in atTop,
      (s k).PureCap (N k ^ (-r)) (K k) ∧
      (s k).JointCap (N k ^ (-r)) (N k ^ (-v)) (K k) ∧
      ∀ j : ℤ, (s k).π {w | ⌊w / N k ^ (-v)⌋ = j} ≤
        ENNReal.ofReal (K k * N k ^ (-S * v))) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      ∀ᶠ k in atTop, (s k).Cover (H k) := by
  obtain ⟨H, hH, hHsub, hcover⟩ := exists_subpower_sample_palette_on N K hN hNt hK hKsub
    (fun _ => True) s hπfin hS he₀
    (hdata.mono fun _ hk _ => hk) (fun r v hr hv => (hcaps r v hr hv).mono fun _ hk _ => hk)
  exact ⟨H, hH, hHsub, hcover.mono fun _ hk => hk trivial⟩

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
