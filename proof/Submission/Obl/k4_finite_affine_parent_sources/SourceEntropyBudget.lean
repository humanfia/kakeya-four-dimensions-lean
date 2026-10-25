import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildWindow
import Submission.Obl.k4_finite_affine_parent_sources.TangentWindowSchedule
import Submission.Obl.k4_finite_affine_parent_sources.TangentVelocityAlphabet

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- The original planar velocity alphabet, including its extra unused code,
has a bound at the native scale. -/
theorem log_winCount_le {N R v : ℝ} (hN : 4 ≤ N) (hR : 0 ≤ R) (hRN : R ≤ N)
    (hv : 0 ≤ v) :
    Real.log (winCount R (N ^ (-v))) ≤ (2 * v + 5) * Real.log N := by
  have hN0 : 0 < N := by linarith
  have hc := velocity_vector_alphabet_small_power (N := N) (mesh := N ^ (-v))
    (R := R) (u := 1) (v := v) 2 (by linarith) (by positivity) hR (by norm_num) hv
    (by simpa using hRN) (by simp) (by simpa using hN)
  have hc' : (winCount R (N ^ (-v)) : ℝ) ≤ N ^ (2 * v + 5) := by
    convert hc using 1 <;> simp only [winCount, Nat.cast_ofNat, mul_one] <;> congr 1 <;> ring
  have hpos : 0 < (winCount R (N ^ (-v)) : ℝ) := by
    exact_mod_cast (show 0 < winCount R (N ^ (-v)) by unfold winCount; omega)
  have hh := Real.log_le_log hpos hc'
  rwa [Real.log_rpow hN0] at hh

/-- The balanced likelihood constant fits a prescribed power once the
window count and logarithmic alphabet budget are explicit. -/
theorem winBase_half_le_power {N R mesh D unit A b : ℝ} {J : ℕ}
    (hN : 1 < N) (hD : 0 < D) (hunit : 0 < unit) (hA : 0 ≤ A) (hJ : 0 < J)
    (hcount : (1 / (32 * D)) / unit ≤ (J : ℝ))
    (halphabet : Real.log (winCount R mesh) ≤ A * Real.log N)
    (hbudget : 64 * A * D * unit ≤ b / 2)
    (hlarge : 2 ≤ (b / 2) * Real.log N) :
    winBase R mesh J ^ (1 / 2 : ℝ) ≤ N ^ b := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hcount' : 1 / (32 * D * unit) ≤ (J : ℝ) := by
    simpa only [div_div] using hcount
  have hInv : (J : ℝ)⁻¹ ≤ 32 * D * unit := by
    have hh := inv_anti₀ (show 0 < 1 / (32 * D * unit) by positivity) hcount'
    simpa only [one_div, inv_inv] using hh
  have hterm : Real.log (winCount R mesh) / J ≤ (A * Real.log N) * (32 * D * unit) := by
    calc Real.log (winCount R mesh) / J ≤ (A * Real.log N) / J :=
          div_le_div_of_nonneg_right halphabet hJ0.le
      _ ≤ _ := by rw [div_eq_mul_inv]; gcongr
  rw [winBase, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    Real.rpow_def_of_pos hN0]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hbudget hlog.le
  nlinarith [hterm, hlarge]

/-- The lookahead is independent of the path's polynomial-format exponent. -/
def selectionLookahead (κ₁ T : ℝ) : ℝ := 10000 * T / κ₁

/-- The numerical hypothesis of `SelectionSample` pays the likelihood
loss of an entire fixed-band window schedule. -/
theorem selection_window_constants {n : ℕ} {κ₁ ρ unit T C : ℝ}
    (hn : 2 ≤ n) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 4)
    (hu : 0 < unit) (hT : (n : ℝ) < T) (hC : 1 ≤ C)
    (hsmall : unit * T * (((n : ℝ) + 2) ^ 2 * (C + 2)) * 10 ^ 15 ≤ κ₁ * ρ) :
    4 ≤ selectionLookahead κ₁ T ∧ selectionLookahead κ₁ T * unit ≤ 1 / 64 ∧
      64 * (2 * (n : ℝ) + 9) * selectionLookahead κ₁ T * unit ≤
        (ρ / (1000000 * ((n : ℝ) + 1)) / (100 * (C + 2))) / 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0 : 0 < T := by linarith
  have hD : 4 ≤ selectionLookahead κ₁ T := by
    unfold selectionLookahead
    rw [le_div_iff₀ hκ]
    nlinarith
  have hD0 : 0 < selectionLookahead κ₁ T := by linarith
  have hpoly : 128000000000000 * (2 * (n : ℝ) + 9) * ((n : ℝ) + 1) ≤
      (10 : ℝ) ^ 15 * ((n : ℝ) + 2) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hprod := mul_le_mul_of_nonneg_right hpoly
    (show 0 ≤ unit * T * (C + 2) by positivity)
  have hbound : 64 * (2 * (n : ℝ) + 9) * selectionLookahead κ₁ T * unit ≤
      (ρ / (1000000 * ((n : ℝ) + 1)) / (100 * (C + 2))) / 2 := by
    have heq : 64 * (2 * (n : ℝ) + 9) * selectionLookahead κ₁ T * unit =
        (640000 * (2 * (n : ℝ) + 9) * T * unit) / κ₁ := by
      unfold selectionLookahead
      ring
    have heq' : (ρ / (1000000 * ((n : ℝ) + 1)) / (100 * (C + 2))) / 2 =
        ρ / (200000000 * ((n : ℝ) + 1) * (C + 2)) := by
      simp only [div_div]
      congr 1
      ring
    rw [heq, heq', div_le_div_iff₀ hκ (by positivity)]
    calc (640000 * (2 * (n : ℝ) + 9) * T * unit) *
          (200000000 * ((n : ℝ) + 1) * (C + 2))
        ≤ (10 : ℝ) ^ 15 * ((n : ℝ) + 2) ^ 2 * (unit * T * (C + 2)) := by
          convert hprod using 1 <;> ring
      _ ≤ ρ * κ₁ := by convert hsmall using 1 <;> ring
  have hb : ρ / (1000000 * ((n : ℝ) + 1)) / (100 * (C + 2)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    have hfirst : ρ / (1000000 * ((n : ℝ) + 1)) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hDu : selectionLookahead κ₁ T * unit ≤ 1 / 64 := by
    have haux : 0 ≤ ((2 * (n : ℝ) + 9) - 1) * (selectionLookahead κ₁ T * unit) := by
      exact mul_nonneg (by linarith) (mul_pos hD0 hu).le
    nlinarith [hbound, hb]
  exact ⟨hD, hDu, hbound⟩

/-- The actual fine grid supplies sufficiently many fixed-band windows,
with a middle level beyond all model depths. -/
theorem source_entropy_windows {n m : ℕ} {sg : ℕ → ℝ} {κ₁ ρ gain unit T C : ℝ}
    (hs : FineGrid m sg gain ρ)
    (hn : 2 ≤ n) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 4)
    (hu : 0 < unit) (hT : (n : ℝ) < T) (hC : 1 ≤ C)
    (hsmall : unit * T * (((n : ℝ) + 2) ^ 2 * (C + 2)) * 10 ^ 15 ≤ κ₁ * ρ)
    (hmesh0 : 0 ≤ ρ * gain) (hmesh : ρ * gain ≤ unit) :
    Nonempty (TangentWindows m sg (selectionLookahead κ₁ T) unit (ρ * gain)) := by
  obtain ⟨hD, hDu, -⟩ := selection_window_constants hn hκ hκ1 hρ hρ1 hu hT hC hsmall
  exact exists_tangent_windows_of_grid hs hD hu hDu hmesh0 hmesh

/-- The selected schedule gives its entropy numerator within a fixed
native power, uniformly over the original velocity radius. -/
theorem source_window_likelihood_bound {n m : ℕ} {sg : ℕ → ℝ}
    {κ₁ ρ unit T C mesh N R : ℝ}
    (hn : 2 ≤ n) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 4)
    (hu : 0 < unit) (hT : (n : ℝ) < T) (hC : 1 ≤ C)
    (hsmall : unit * T * (((n : ℝ) + 2) ^ 2 * (C + 2)) * 10 ^ 15 ≤ κ₁ * ρ)
    (q : TangentWindows m sg (selectionLookahead κ₁ T) unit mesh)
    (hN : 4 ≤ N) (hR : 0 ≤ R) (hRN : R ≤ N)
    (hlarge : 4 ≤ (ρ / (1000000 * ((n : ℝ) + 1)) / (100 * (C + 2))) * Real.log N) :
    winBase R (N ^ (-((n : ℝ) + 2))) q.count ^ (1 / 2 : ℝ) ≤
      N ^ (ρ / (1000000 * ((n : ℝ) + 1)) / (100 * (C + 2))) := by
  obtain ⟨hD, -, hbudget⟩ := selection_window_constants hn hκ hκ1 hρ hρ1 hu hT hC hsmall
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply winBase_half_le_power (A := 2 * (n : ℝ) + 9) (by linarith) (by linarith : 0 < selectionLookahead κ₁ T)
    hu (by positivity) q.count_pos q.count_lower
  · have h := log_winCount_le hN hR hRN (by positivity : 0 ≤ (n : ℝ) + 2)
    convert h using 1 <;> congr 1 <;> ring
  · exact hbudget
  · nlinarith [hlarge]

end
end Submission.Obl.k4_finite_affine_parent_sources
