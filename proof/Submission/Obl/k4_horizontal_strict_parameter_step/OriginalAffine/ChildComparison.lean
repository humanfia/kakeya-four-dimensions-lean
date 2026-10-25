/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/ChildComparison.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.TiltedComparison
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.ChildNumerics

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- Agreement of the genuine child and parent affine fits on the unrestricted
original child witness extends to its whole true box.  The only density input
is the original finite joint mesh cap.  No current-law floor or critical-rate
validity record is used.  The second conclusion gives native first jets at
all base points of that box. -/
theorem original_child_affine_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (z : Ω → Fin 3 → ℝ) (f : Ω → ℝ)
    (L P : Fin 4 → ℝ) (t₀ z₀ y₀ l₁ l₂ l₃ K q g η a a₀ d : ℝ)
    {H : ℕ} (hH : 0 < H) (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g)
    (hη : 0 < η) (ha : 0 < a) (ha₀ : 0 < a₀) (haa₀ : a ≤ a₀)
    (hqg : q ≤ K * g) (hgq : g ≤ K * q)
    (hl₁ : |l₁| ≤ K) (hl₂ : |l₂ + z₀| ≤ K * q) (hl₃ : |l₃ - t₀| ≤ K * q)
    (hmass : ENNReal.ofReal (q ^ 4 * a ^ d / K ^ 3) ≤ μ E)
    (hmesh₀ : η ≤ q / H)
    (hmesh₁ : (|l₁| + 1) * η ≤ 2 * (K * q) / H)
    (hmesh₂ : (|l₂| + |l₃| + 1) * η ≤ 2 * (K * q * g) / H)
    (hresolve : η * ∑ j : Fin 3, |L j.succ| ≤ a)
    (hcap : ∀ (p : Fin 3 → ℤ) (j : ℤ),
      μ {ω | (fun i => ⌊z ω i / η⌋) = p ∧ ⌊f ω / a⌋ = j} ≤
        ENNReal.ofReal (K * a ^ d * η ^ 3))
    (hbox : ∀ ω ∈ E, |z ω 0 - t₀| ≤ q / 2 ∧
      |z ω 1 - z₀ - l₁ * (z ω 0 - t₀)| ≤ K * q ∧
      |z ω 2 - y₀ - l₂ * (z ω 0 - t₀) - l₃ * (z ω 1 - z₀)| ≤ K * q * g)
    (hchild : ∀ ω ∈ E, |f ω - (L 0 + ∑ j : Fin 3, L j.succ * z ω j)| ≤ K * a)
    (hparent : ∀ ω ∈ E, |f ω - (P 0 + ∑ j : Fin 3, P j.succ * z ω j)| ≤ K * a₀)
    (hfine : 69120 * K ^ 8 ≤ (H : ℝ)) :
    (∀ v : Fin 3 → ℝ, |v 0 - t₀| ≤ q / 2 →
      |v 1 - z₀ - l₁ * (v 0 - t₀)| ≤ K * q →
      |v 2 - y₀ - l₂ * (v 0 - t₀) - l₃ * (v 1 - z₀)| ≤ K * q * g →
      |(L 0 - P 0) + ∑ j : Fin 3, (L j.succ - P j.succ) * v j| ≤
        262144 * K ^ 9 * a₀) ∧
    (∀ t Z : ℝ, |t - t₀| ≤ q / 2 → |Z - z₀ - l₁ * (t - t₀)| ≤ K * q →
      |L 3 - P 3| ≤ (262144 * K ^ 9 * a₀) / q ^ 2 ∧
      |L 1 - P 1 - Z * (L 3 - P 3)| + |L 2 - P 2 + t * (L 3 - P 3)| ≤
        8 * K * (262144 * K ^ 9 * a₀) / q) := by
  have hK0 : 0 < K := by linarith
  let m := q ^ 4 * a ^ d / K ^ 3
  let C := 512 * (2 * K + 7) * (K * a ^ d) * (q / 2) * (K * q) * (K * q * g)
  have hm : 0 < m := by dsimp [m]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hratio : C ≤ 2304 * K ^ 8 * m :=
    original_child_cap_ratio hK hq hg (Real.rpow_pos_of_pos ha _) hgq
  have hfine' : 30 * C ≤ m * H := by
    calc
      _ ≤ 30 * (2304 * K ^ 8 * m) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = m * (69120 * K ^ 8) := by ring
      _ ≤ m * H := mul_le_mul_of_nonneg_left hfine hm.le
  have hcomparison (ω : Ω) (hω : ω ∈ E) :
      |(L 0 - P 0) + ∑ j : Fin 3, (L j.succ - P j.succ) * z ω j| ≤ 2 * K * a₀ := by
    have hid : (L 0 - P 0) + ∑ j : Fin 3, (L j.succ - P j.succ) * z ω j =
        (f ω - (P 0 + ∑ j : Fin 3, P j.succ * z ω j)) -
          (f ω - (L 0 + ∑ j : Fin 3, L j.succ * z ω j)) := by
      simp only [Fin.sum_univ_three]
      ring
    rw [hid]
    exact (abs_sub _ _).trans (by
      nlinarith [hchild ω hω, hparent ω hω, mul_le_mul_of_nonneg_left haa₀ hK0.le])
  have hb (v : Fin 3 → ℝ) (ht : |v 0 - t₀| ≤ q / 2)
      (hZ : |v 1 - z₀ - l₁ * (v 0 - t₀)| ≤ K * q)
      (hY : |v 2 - y₀ - l₂ * (v 0 - t₀) - l₃ * (v 1 - z₀)| ≤ K * q * g) :
      |(L 0 - P 0) + ∑ j : Fin 3, (L j.succ - P j.succ) * v j| ≤
        262144 * K ^ 9 * a₀ := by
    have hmesh₀' : η ≤ 2 * (q / 2) / H := by convert hmesh₀ using 1 <;> ring
    have h := tilted_affine_comparison μ E z f (fun j => L j.succ)
      (fun j => L j.succ - P j.succ) (L 0) (L 0 - P 0)
      t₀ z₀ y₀ l₁ l₂ l₃ (q / 2) (K * q) (K * q * g) η a K (K * a ^ d)
      (2 * K * a₀) m hH (by positivity) (by positivity) (by positivity)
      hη ha hK0.le (by positivity) (by positivity) hm hmass
      hmesh₀' hmesh₁ hmesh₂ hresolve hcap hbox hchild hcomparison hfine' v ⟨ht, hZ, hY⟩
    exact h.trans (original_child_comparison_error hK hm ha₀.le hC hratio)
  refine ⟨hb, ?_⟩
  intro t Z ht hZ
  have hbox' : ∀ t Z Y : ℝ, |t - t₀| ≤ q / 2 →
      |Z - z₀ - l₁ * (t - t₀)| ≤ K * q →
      |Y - y₀ - l₂ * (t - t₀) - l₃ * (Z - z₀)| ≤ K * q * g →
      |(L 0 - P 0) + (L 1 - P 1) * t + (L 2 - P 2) * Z + (L 3 - P 3) * Y| ≤
        262144 * K ^ 9 * a₀ := by
    intro t Z Y ht hZ hY
    simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Fin.reduceSucc, add_assoc] using hb ![t, Z, Y] ht hZ hY
  exact Submission.Lib.K4AffineMesh.horizontal_triangular_jet_bounds_at_point
    (L 0 - P 0) (L 1 - P 1) (L 2 - P 2) (L 3 - P 3)
    t₀ z₀ y₀ l₁ l₂ l₃ K q g (262144 * K ^ 9 * a₀) t Z hK hq hg
    (by positivity) hqg hl₁ hl₂ hl₃ hbox' ht hZ

end Submission.Obl.k4_horizontal_strict_parameter_step
