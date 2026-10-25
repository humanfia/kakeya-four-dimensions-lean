/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/LiftBounds.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftGeometry
import Submission.Obl.k4_native_finite_terminal_atlas_lift.TestCoefficientBounds

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open scoped BigOperators

theorem power_absorbs_constant {N C : ℝ} (hN : 2 ≤ N) (m s : ℕ) (hC : C ≤ (2 : ℝ) ^ s) :
    C * N ^ m ≤ N ^ (m + s) := by
  rw [pow_add]
  have hs : C ≤ N ^ s := hC.trans (pow_le_pow_left₀ (by norm_num) hN s)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ N ^ m)

theorem sum_powers_le {N : ℝ} (hN : 2 ≤ N) (a b : ℕ) :
    N ^ a + N ^ b ≤ N ^ (a + b + 1) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have ha := one_le_pow₀ (n := a) hN1
  have hb := one_le_pow₀ (n := b) hN1
  calc
    N ^ a + N ^ b ≤ 2 * (N ^ a * N ^ b) := by nlinarith
    _ ≤ N * (N ^ a * N ^ b) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = _ := by rw [pow_add, pow_add, pow_one]; ring

/-- Separate the two nonnegative halves of the frozen frame budget. -/
theorem frame_budget_separate {Q : Frame} {H : ℝ}
    (hQ : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) ≤ H) :
    frameSize Q ≤ H ∧ frameSize Q⁻¹ ≤ H := by
  constructor
  · exact le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      le_add_of_nonneg_right (abs_nonneg _)) hQ
  · exact le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      le_add_of_nonneg_left (abs_nonneg _)) hQ

theorem frame_entry_le_size (Q : Frame) (i j : Fin 2) : |Q i j| ≤ frameSize Q := by
  exact (Finset.single_le_sum (f := fun j : Fin 2 => |Q i j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)).trans (frameSize_row_le Q i)

namespace Remainder

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

noncomputable def parameterExponent : ℕ := rem.M + ⌈|h| + 1⌉₊

noncomputable def liftingExponent (M : ℕ) : ℕ := M + 4 * rem.parameterExponent + 20

theorem time_polynomial_bound (hp : p.Valid) (k : ℕ) :
    (2 : ℝ) ^ (rem.parent k).T ≤ p.N (rem.φ k) ^ rem.parameterExponent := by
  have hN1 : 1 ≤ p.N (rem.φ k) := le_trans (by norm_num) (hp.1 _)
  have hexp : h + rem.error k ≤ (rem.parameterExponent : ℝ) := by
    have hc := Nat.le_ceil (|h| + 1)
    have hM : (0 : ℝ) ≤ rem.M := by positivity
    simp only [parameterExponent, Nat.cast_add]
    linarith [le_abs_self h, rem.error_le_one k]
  exact (rem.time_bound k).trans ((Real.rpow_le_rpow_of_exponent_le hN1 hexp).trans_eq
    (Real.rpow_natCast _ _))

theorem parent_parameter_bounds (hp : p.Valid) (k : ℕ) (b : Fin (q.W k)) :
    |rem.initialTime k b| ≤ 1 ∧ |(rem.timeLength k)⁻¹| ≤ p.N (rem.φ k) ^ rem.parameterExponent ∧
    ‖(rem.parent k).c (rem.parentIndex k b)‖ + ‖(rem.parent k).u (rem.parentIndex k b)‖ ≤
      p.N (rem.φ k) ^ rem.parameterExponent ∧
    frameSize ((rem.parent k).Q (rem.parentIndex k b)) ≤ p.N (rem.φ k) ^ rem.parameterExponent ∧
    frameSize ((rem.parent k).Q (rem.parentIndex k b))⁻¹ ≤ p.N (rem.φ k) ^ rem.parameterExponent := by
  have hN1 : 1 ≤ p.N (rem.φ k) := le_trans (by norm_num) (hp.1 _)
  have hm : p.N (rem.φ k) ^ rem.M ≤ p.N (rem.φ k) ^ rem.parameterExponent :=
    pow_le_pow_right₀ hN1 (by dsimp [parameterExponent]; omega)
  have hc := (rem.parent_valid k).2.2 (rem.parentIndex k b)
  rcases hc with ⟨_, hcenter, hframe, _⟩
  have hframes := frame_budget_separate hframe
  refine ⟨?_, ?_, hcenter.trans hm, hframes.1.trans hm, hframes.2.trans hm⟩
  · rw [abs_of_nonneg (rem.initialTime_bounds k b).1]
    exact (rem.initialTime_bounds k b).2
  · simpa only [timeLength, inv_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (rem.parent k).T)] using
      rem.time_polynomial_bound hp k

/-- One fixed exponent controls centers, both frames, and all native quadratic
coefficients of every child pullback, independently of tolerance and horizon. -/
theorem liftAtlas_parameter_bounds (hp : p.Valid) (hr : 0 ≤ r) {k M D : ℕ}
    {a : Atlas q k} (ha : a.TrueAt M D q.L) (b : Fin a.C) :
    ‖(rem.liftAtlas k a).c b‖ + ‖(rem.liftAtlas k a).u b‖ ≤
        p.N (rem.φ k) ^ rem.liftingExponent M ∧
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|(rem.liftAtlas k a).Q b i j| + |((rem.liftAtlas k a).Q b)⁻¹ i j|)) ≤
        p.N (rem.φ k) ^ rem.liftingExponent M ∧
    ((rem.liftAtlas k a).R b).totalDegree ≤ 2 ∧
    ∀ e, |((rem.liftAtlas k a).R b).coeff e| ≤ p.N (rem.φ k) ^ rem.liftingExponent M := by
  let N := p.N (rem.φ k)
  let H := N ^ rem.parameterExponent
  let H' := N ^ M
  have hN2 : 2 ≤ N := hp.1 _
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN2
  have hH : 1 ≤ H := one_le_pow₀ hN1
  have hH' : 1 ≤ H' := one_le_pow₀ hN1
  obtain ⟨ht, hq, hcenter₀, hframe₀, hinverse₀⟩ := rem.parent_parameter_bounds hp k (a.γ b)
  have hc := ha.2.2.1 b
  rcases hc with ⟨_, hcenter₁, hframe₁, _, hdegree, hcoeff, _⟩
  simp only [rem.same_base k] at hcenter₁ hframe₁ hcoeff
  have hframes := frame_budget_separate hframe₁
  have hcent := composite_center_velocity_bound hH hH' ht hq hcenter₀ hcenter₁ hframe₀
  have hfs₀ : frameSize ((rem.liftAtlas k a).Q b) ≤ H * H' :=
    (frameSize_mul _ _).trans (mul_le_mul hframe₀ hframes.1 (frameSize_nonneg _) (by positivity))
  have hfs₁ : frameSize ((rem.liftAtlas k a).Q b)⁻¹ ≤ H' * H := by
    change frameSize (((rem.parent k).Q (rem.parentIndex k (a.γ b)) * a.Q b)⁻¹) ≤ H' * H
    rw [Matrix.mul_inv_rev]
    exact (frameSize_mul _ _).trans
      (mul_le_mul hframes.2 hinverse₀ (frameSize_nonneg _) (by positivity))
  have hframe : (∑ i : Fin 2, ∑ j : Fin 2,
      (|(rem.liftAtlas k a).Q b i j| + |((rem.liftAtlas k a).Q b)⁻¹ i j|)) ≤ 2 * H * H' := by
    have hh := add_le_add hfs₀ hfs₁
    simpa only [frameSize, Finset.sum_add_distrib, show H * H' + H' * H = 2 * H * H' by ring] using hh
  have hcompc (i : Fin 2) : |(rem.parent k).c (rem.parentIndex k (a.γ b)) i| ≤ H :=
    (PiLp.norm_apply_le _ i).trans ((le_add_of_nonneg_right (norm_nonneg _)).trans hcenter₀)
  have hcompu (i : Fin 2) : |(rem.parent k).u (rem.parentIndex k (a.γ b)) i| ≤ H :=
    (PiLp.norm_apply_le _ i).trans ((le_add_of_nonneg_left (norm_nonneg _)).trans hcenter₀)
  have hcompV (i j : Fin 2) : |((rem.parent k).Q (rem.parentIndex k (a.γ b)))⁻¹ i j| ≤ H :=
    (frame_entry_le_size _ _ _).trans hinverse₀
  have hδ : |δ N r| ≤ 1 := by
    rw [abs_of_pos (by unfold δ; positivity)]
    exact thickness_le_one hN1 hr
  have hcoeff' (e : Fin 4 →₀ ℕ) : |((rem.liftAtlas k a).R b).coeff e| ≤ 5184 * H' * H ^ 4 :=
    liftedTest_coefficient_bound (a.R b) hdegree hcoeff (by positivity) hH hδ ht hq hcompc hcompu hcompV e
  have hpow₀ : H ^ 2 * H' = N ^ (2 * rem.parameterExponent + M) := by
    dsimp [H, H']
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hpow₁ : H * H' = N ^ (rem.parameterExponent + M) := by dsimp [H, H']; rw [pow_add]
  have hpow₂ : H' * H ^ 4 = N ^ (M + 4 * rem.parameterExponent) := by
    dsimp [H, H']
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  refine ⟨?_, ?_, ?_, fun e => ?_⟩
  · apply hcent.trans
    change 4 * H ^ 2 * H' ≤ N ^ rem.liftingExponent M
    rw [mul_assoc, hpow₀]
    apply (power_absorbs_constant hN2 (2 * rem.parameterExponent + M) 2 (by norm_num)).trans
    apply pow_le_pow_right₀ hN1
    dsimp [liftingExponent]
    omega
  · apply hframe.trans
    rw [mul_assoc, hpow₁]
    apply (power_absorbs_constant hN2 (rem.parameterExponent + M) 1 (by norm_num)).trans
    apply pow_le_pow_right₀ hN1
    dsimp [liftingExponent]
    omega
  · exact (liftedTest_degree _ _ _ _ _ _ _).trans hdegree
  · apply (hcoeff' e).trans
    rw [mul_assoc, hpow₂]
    apply (power_absorbs_constant hN2 (M + 4 * rem.parameterExponent) 13 (by norm_num)).trans
    apply pow_le_pow_right₀ hN1
    dsimp [liftingExponent]
    omega

end Remainder

end Submission.Obl.k4_native_finite_terminal_atlas_lift
