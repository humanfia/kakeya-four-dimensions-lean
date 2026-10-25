import Submission.Obl.k4_homogeneous_native_pair_preparation.ChartAxes
import Submission.Obl.k4_scalar_pair_atlas_assembly.SparseTablesProof
import Submission.Obl.k4_scalar_angular_pair_agreement.Extrap
import Submission.Obl.k4_pair_bin_atlas_assembly.Interpolation
import Submission.Obl.k4_quadratic_finite_greedy_cover.DerivativeLoss

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split (I)

def nativeCoarseIndex {T s : ℕ} (j : Fin (2 ^ (T + s))) : Fin (2 ^ T) :=
  Submission.Obl.k4_scalar_pair_atlas_assembly.coarse (by omega) j

theorem nativeCoarseIndex_val {T s : ℕ} (j : Fin (2 ^ (T + s))) :
    (nativeCoarseIndex j : ℕ) = (j : ℕ) / 2 ^ s := by
  simp [nativeCoarseIndex, Submission.Obl.k4_scalar_pair_atlas_assembly.coarse]

theorem nativeCoarseInterval_eq {T s : ℕ} (j : Fin (2 ^ (T + s))) :
    coarseInterval T s (j : ℕ) = I T (nativeCoarseIndex j) := by
  simp [coarseInterval, I, nativeCoarseIndex,
    Submission.Obl.k4_scalar_pair_atlas_assembly.coarse]

theorem fine_interval_subset_coarse {T s : ℕ} (j : Fin (2 ^ (T + s))) :
    I (T + s) j ⊆ coarseInterval T s (j : ℕ) := by
  rw [nativeCoarseInterval_eq]
  exact Submission.Obl.k4_scalar_pair_atlas_assembly.I_subset_coarse (by omega) j

/-- Quadratic extrapolation to the actual coarse parent, with its exact gain. -/
theorem quadratic_native_coarse_extension {T s : ℕ} (j : Fin (2 ^ (T + s)))
    {g : ℝ → ℝ} (hg : ∃ a b c : ℝ, ∀ t, g t = a + b * t + c * t ^ 2)
    {V : ℝ} (hbound : ∀ t ∈ I (T + s) j, |g t| ≤ V) :
    ∀ t ∈ coarseInterval T s (j : ℕ), |g t| ≤ 48 * ((2 : ℝ) ^ s) ^ 2 * V := by
  have hb := Submission.Obl.k4_scalar_angular_pair_agreement.quad_extrap_block
    (show T ≤ T + s by omega)
    (Submission.Obl.k4_scalar_pair_atlas_assembly.I_subset_coarse (by omega) j) hg hbound
  simp only [Nat.add_sub_cancel_left] at hb
  intro t ht
  have ht' : t ∈ I T (nativeCoarseIndex j) := by
    rw [← nativeCoarseInterval_eq]
    exact ht
  exact hb t ht'

/-- Whole-coarse-block confinement and native test bounds for every trajectory
assigned to an old chart. -/
theorem chart_native_coarse_extension {N κ r B a : ℝ} {M D T s : ℕ}
    (j : Fin (2 ^ (T + s)))
    {E F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))} {ex : Prop}
    (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hbudget : 48 * κ * ((2 : ℝ) ^ s) ^ 2 ≤ N ^ a)
    (hc : chart N M D κ (T + s) ((j : ℕ) : ℝ) r B E c u Q R A F ex) :
    ∀ l ∈ A, ∀ t ∈ coarseInterval T s (j : ℕ),
      ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ 3 * κ * (2 : ℝ) ^ s ∧
      |MvPolynomial.eval (x l t) R| ≤ δ N r * N ^ a ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ B * N ^ a := by
  obtain ⟨_, _, _, _, hR, _, _, _, _, hwhole, _, _⟩ := hc
  intro l hl t ht
  have hbound := (hwhole l hl).2.2
  have hδ : 0 ≤ δ N r := by unfold δ; positivity
  have hquad : ∃ a b c : ℝ, ∀ t, MvPolynomial.eval (x l t) R = a + b * t + c * t ^ 2 := by
    obtain ⟨a, b, c, hq⟩ := Submission.Obl.k4_pair_bin_atlas_assembly.quadratic_eval_x R hR l
    change ∀ t, MvPolynomial.eval (x l t) R = a * t ^ 2 + b * t + c at hq
    refine ⟨c, b, a, fun t => ?_⟩
    rw [hq]
    ring
  have haff : ∃ a b c : ℝ, ∀ t,
      MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R) = a + b * t + c * t ^ 2 := by
    obtain ⟨a, b, hq⟩ :=
      Submission.Obl.k4_quadratic_finite_greedy_cover.trajectory_native_derivative_affine R hR l
    change ∀ t, MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R) = a * t + b at hq
    refine ⟨b, a, 0, fun t => ?_⟩
    rw [hq]
    ring
  have hv := quadratic_native_coarse_extension j hquad (fun t ht => (hbound t ht).2.1) t ht
  have hd := quadratic_native_coarse_extension j haff (fun t ht => (hbound t ht).2.2.1) t ht
  refine ⟨?_, ?_, ?_⟩
  · let t₀ : ℝ := ((j : ℕ) : ℝ) / (2 : ℝ) ^ (T + s)
    let q₀ : ℝ := ((2 : ℝ) ^ (T + s))⁻¹
    have hq₀ : 0 < q₀ := by dsimp [q₀]; positivity
    have hend : t₀ + q₀ = (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s) := by
      dsimp [t₀, q₀]
      field_simp
    have hleft : t₀ ∈ I (T + s) j := by
      change t₀ ≤ t₀ ∧ t₀ ≤ (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s)
      rw [← hend]
      exact ⟨le_rfl, by linarith only [hq₀]⟩
    have hright : t₀ + q₀ ∈ I (T + s) j := by
      change t₀ ≤ t₀ + q₀ ∧ t₀ + q₀ ≤ (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s)
      rw [← hend]
      exact ⟨by linarith only [hq₀], le_rfl⟩
    have h0 : ‖Construction.frameOffset c u Q l 0 +
        t₀ • Matrix.toEuclideanLin Q⁻¹ (v l - u)‖ ≤ κ := by
      rw [← Construction.frameOffset_affine]
      exact (hbound t₀ hleft).1
    have h1 : ‖Construction.frameOffset c u Q l 0 +
        (t₀ + q₀) • Matrix.toEuclideanLin Q⁻¹ (v l - u)‖ ≤ κ := by
      rw [← Construction.frameOffset_affine]
      exact (hbound (t₀ + q₀) hright).1
    have hn := (Construction.affine_extension_bound (t := t) hq₀ h0 h1).1
    have hdist : |t - t₀| ≤ ((2 : ℝ) ^ T)⁻¹ := by
      have h0c := fine_interval_subset_coarse j hleft
      rw [nativeCoarseInterval_eq] at h0c ht
      simp only [I, mem_Icc, add_div, one_div] at h0c ht
      rw [abs_le]
      constructor <;> linarith only [h0c.1, h0c.2, ht.1, ht.2]
    have hratio : ((2 : ℝ) ^ T)⁻¹ / q₀ = (2 : ℝ) ^ s := by
      dsimp [q₀]
      rw [div_inv_eq_mul, pow_add]
      field_simp
    have hfrac : |t - t₀| / q₀ ≤ (2 : ℝ) ^ s := by
      rw [← hratio]
      exact div_le_div_of_nonneg_right hdist hq₀.le
    have hg : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
    change ‖Construction.frameOffset c u Q l t‖ ≤ _
    rw [Construction.frameOffset_affine]
    calc
      _ ≤ κ * (1 + 2 * |t - t₀| / q₀) := hn
      _ ≤ κ * (1 + 2 * (2 : ℝ) ^ s) := by
        apply mul_le_mul_of_nonneg_left ?_ hκ
        apply add_le_add_right
        simpa only [mul_div_assoc] using
          mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ κ * (3 * (2 : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_left (by linarith only [hg]) hκ
      _ = _ := by ring
  · calc
      _ ≤ 48 * ((2 : ℝ) ^ s) ^ 2 * (κ * δ N r) := hv
      _ = δ N r * (48 * κ * ((2 : ℝ) ^ s) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hδ
  · calc
      _ ≤ 48 * ((2 : ℝ) ^ s) ^ 2 * (κ * B) := hd
      _ = B * (48 * κ * ((2 : ℝ) ^ s) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hB

end Submission.Obl.k4_homogeneous_native_pair_preparation
