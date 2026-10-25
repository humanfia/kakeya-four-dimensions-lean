import Submission.Obl.k4_raw_native_atlas_normalization.Samples
import Submission.Obl.k4_finite_width_output_exclusion.Interfaces

namespace Submission.Obl.k4_raw_native_atlas_normalization

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

/-- A single sequence of retained atlases with polynomially positive priors. -/
structure Prepared (p : Data) (r h w : ℝ) where
  φ : ℕ → ℕ
  M : ℕ
  D : ℕ
  error : ℕ → ℝ
  loss : ℕ → ℝ
  a : (k : ℕ) → Atlas p (φ k)
  mono : StrictMono φ
  error_pos : ∀ k, 0 < error k
  error_le : ∀ k, error k ≤ 1
  error_lim : Tendsto error atTop (nhds 0)
  loss_ge : ∀ k, 1 ≤ loss k
  known : ∀ k, (a k).KnownAt M D (loss k) r
  bound : ∀ k, max (p.K (φ k)) (3 * loss k) ≤ p.N (φ k) ^ error k
  time : ∀ k, (2 : ℝ) ^ (a k).T ≤ p.N (φ k) ^ (h + error k)
  width : ∀ k b, |Matrix.det ((a k).Q b)| * (4 : ℝ) ^ (a k).T ≤
    p.N (φ k) ^ (-w + error k)
  prior_pos : ∀ k b, 0 < p.ν (φ k) ((a k).γ b) ((a k).A b)
  prior_inv : ∀ k b, (p.ν (φ k) ((a k).γ b) ((a k).A b)).toReal⁻¹ ≤ p.N (φ k) ^ M
  time_poly : ∀ k, (2 : ℝ) ^ (a k).T ≤ p.N (φ k) ^ M

noncomputable section

/-- Diagonalize frequent successful samples and pay the pruning and constant losses. -/
theorem prepare_atlases {p : Data} (hp : Valid p) {r h w : ℝ} (hr : 0 ≤ r)
    (hk : Known p r h w) : Nonempty (Prepared p r h w) := by
  classical
  obtain ⟨M, D, hat⟩ := hk
  obtain ⟨Mp, Dp, hf⟩ := hp.2.2.2.2.2.2.2.2.1
  let error : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < error n := by dsimp [error]; positivity
  have hele (n : ℕ) : error n ≤ 1 := by
    dsimp [error]
    exact (div_le_one (by positivity)).mpr
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have he0 : Tendsto error atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hfreq (n : ℕ) : ∃ᶠ k in atTop,
      ∃ κ : ℝ, p.K k ≤ p.N k ^ (error n / 4) ∧ 6 ≤ p.N k ^ (error n / 4) ∧
        1 ≤ κ ∧ κ ≤ p.N k ^ (error n / 4) ∧
        ∃ a : Atlas p k, (2 : ℝ) ^ a.T ≤ p.N k ^ (h + error n / 4) ∧
          (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w + error n / 4)) ∧
          a.KnownAt M D κ r := by
    have hα : 0 < error n / 4 := div_pos (hepos n) (by norm_num)
    exact ((hat _ hα).and_eventually
      ((hp.slack_subpower _ hα).and
        (((tendsto_rpow_atTop hα).comp hp.scale_tendsto).eventually_ge_atTop 6))).mono
      (fun k hk => by
        obtain ⟨κ, hκ, hκα, a, hT, hw, ha⟩ := hk.1
        exact ⟨κ, hk.2.1, hk.2.2, hκ, hκα, a, hT, hw, ha⟩)
  obtain ⟨φ, hφ, hs⟩ := extraction_forall_of_frequently hfreq
  choose κ hK h6 hκ hκα a hT hw ha using hs
  have hκN (n : ℕ) : κ n ≤ p.N (φ n) := by
    have hα1 : error n / 4 ≤ 1 := by linarith [hele n]
    exact (hκα n).trans ((Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) hα1).trans_eq
      (Real.rpow_one _))
  have hω n : ∀ γ, 0 ≤ p.ω (φ n) γ := (hf (φ n)).2.1
  have hωs n : ∑ γ, p.ω (φ n) γ = 1 := (hf (φ n)).2.2.1
  have hν n : ∀ γ, IsProbabilityMeasure (p.ν (φ n) γ) :=
    fun γ => ((hf (φ n)).2.2.2.1 γ).1
  choose s has hprior using (fun n =>
    prune_small_priors (a n) (ha n) (hp.scale_ge_two _) (hκ n) (hκN n)
      (hω n) (hωs n) (hν n) (fun b => (hp.B_pos _ b).le))
  let M' : ℕ := M + ⌈max h 0⌉₊ + 4
  have hMM' : M ≤ M' := by dsimp [M']; omega
  have hM3 : M + 3 ≤ M' := by dsimp [M']; omega
  have hknown n : (restrictAtlas (a n) (s n)).KnownAt M' D (2 * κ n) r := by
    exact known_mono (has n) (hp.scale_ge_one _) hMM' le_rfl
      (by linarith [hκ n]) le_rfl (fun b => (hp.B_pos _ b).le)
  refine ⟨⟨φ, M', D, error, fun n => 2 * κ n, fun n => restrictAtlas (a n) (s n),
    hφ, hepos, hele, he0, fun n => by linarith [hκ n], hknown, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro n
    have hN := hp.scale_ge_one (φ n)
    have hα : error n / 4 ≤ error n := by linarith [hepos n]
    have h2α : error n / 4 + error n / 4 ≤ error n := by linarith [hepos n]
    apply max_le
    · exact (hK n).trans (Real.rpow_le_rpow_of_exponent_le hN hα)
    · calc
        3 * (2 * κ n) = 6 * κ n := by ring
        _ ≤ p.N (φ n) ^ (error n / 4) * p.N (φ n) ^ (error n / 4) :=
          mul_le_mul (h6 n) (hκα n) (by linarith [hκ n]) (by positivity)
        _ = p.N (φ n) ^ (error n / 4 + error n / 4) :=
          (Real.rpow_add (hp.scale_pos _) _ _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN h2α
  · intro n
    exact (hT n).trans (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _)
      (by linarith [hepos n]))
  · intro n b
    exact (hw n (retainedIndex (a n) (s n) b)).trans
      (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) (by linarith [hepos n]))
  · exact fun n b => (hprior n b).1
  · intro n b
    exact (hprior n b).2.trans (pow_le_pow_right₀ (hp.scale_ge_one _) hM3)
  · intro n
    have hh : h ≤ (⌈max h 0⌉₊ : ℝ) := le_trans (le_max_left _ _) (Nat.le_ceil _)
    have hbound : h + error n / 4 ≤ (M' : ℝ) := by
      dsimp [M']
      push_cast
      linarith [hele n, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    exact (hT n).trans ((Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) hbound).trans_eq
      (Real.rpow_natCast _ _))

end
end Submission.Obl.k4_raw_native_atlas_normalization
