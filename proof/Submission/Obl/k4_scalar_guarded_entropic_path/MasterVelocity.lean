import Submission.Obl.k4_scalar_guarded_entropic_path.Interface
import Submission.Lib.K4QuadraticSublevel

/-! A single original velocity record has logarithmic cost bounded by
its finest exponent plus two, independently of the original world count. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Set

noncomputable section

theorem exists_master_velocity_bins {N K U : ℝ} (hN : 7 ≤ N)
    (hK : 0 ≤ K) (hKN : K ≤ N) (hU : 0 ≤ U) :
    ∃ Sv : Finset ℤ, ((max Sv.card 1 : ℕ) : ℝ) ≤ N ^ (U + 2) ∧
      ∀ v : ℝ, |v| ≤ K → velocityBin N U v ∈ Sv := by
  classical
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  let A : Set ℝ := {v | |v| ≤ K}
  have hdiam : ∀ v ∈ A, ∀ w ∈ A, dist v w ≤ 2 * K := by
    intro v hv w hw
    change |v| ≤ K at hv
    change |w| ≤ K at hw
    rw [Real.dist_eq]
    calc |v - w| ≤ |v| + |w| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  obtain ⟨hfinite, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    A (by positivity : 0 ≤ 2 * K) (Real.rpow_pos_of_pos hN0 (-U)) 0 hdiam
  have hfinite' : (velocityBin N U '' A).Finite := by
    change ((fun v : ℝ => (⌊v / N ^ (-U)⌋ : ℤ)) '' A).Finite
    simpa only [sub_zero] using hfinite
  have hcard' : ((velocityBin N U '' A).ncard : ℝ) ≤ 4 * K * N ^ U + 2 := by
    change (((fun v : ℝ => (⌊v / N ^ (-U)⌋ : ℤ)) '' A).ncard : ℝ) ≤ _
    simpa only [sub_zero, Real.rpow_neg hN0.le, div_eq_mul_inv, inv_inv,
      show (2 : ℝ) * (2 * K) = 4 * K by ring] using hcard
  have hKNpow : 4 * K * N ^ U + 2 ≤ 4 * N ^ (U + 1) + 2 := by
    have hm := mul_le_mul_of_nonneg_right hKN (by positivity : 0 ≤ 4 * N ^ U)
    have heq : N ^ (U + 1) = N ^ U * N := by rw [Real.rpow_add hN0, Real.rpow_one]
    rw [heq]
    nlinarith only [hm]
  have hpower : 1 ≤ N ^ (U + 1) := Real.one_le_rpow hN1 (by linarith)
  have htail : 4 * N ^ (U + 1) + 2 ≤ N ^ (U + 2) := by
    have heq : N ^ (U + 2) = N ^ (U + 1) * N := by
      rw [show U + 2 = (U + 1) + 1 by ring, Real.rpow_add hN0, Real.rpow_one]
    rw [heq]
    nlinarith only [hN, hpower]
  refine ⟨hfinite'.toFinset, ?_, ?_⟩
  · rw [Nat.cast_max, max_le_iff]
    constructor
    · rw [← Set.ncard_eq_toFinset_card _ hfinite']
      exact hcard'.trans (hKNpow.trans htail)
    · have hone : (1 : ℝ) ≤ N ^ (U + 2) := Real.one_le_rpow hN1 (by linarith)
      simpa only [Nat.cast_one] using hone
  · intro v hv
    exact hfinite'.mem_toFinset.mpr ⟨v, hv, rfl⟩

theorem master_velocity_log_bound {N U : ℝ} {Sv : Finset ℤ} (hN : 0 < N)
    (hcard : ((max Sv.card 1 : ℕ) : ℝ) ≤ N ^ (U + 2)) :
    Real.log ((max Sv.card 1 : ℕ) : ℝ) ≤ (U + 2) * Real.log N := by
  have hpos : (0 : ℝ) < (max Sv.card 1 : ℕ) := by
    exact_mod_cast (show 0 < max Sv.card 1 from zero_lt_one.trans_le (le_max_right _ _))
  exact (Real.log_le_log hpos hcard).trans_eq (Real.log_rpow hN _)

end

end Submission.Obl.k4_scalar_guarded_entropic_path
