import Submission.Obl.k4_horizon_chart_assembly.GroupGeometry

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

noncomputable section

def packetSize (H K R q τ₀ : ℝ) (D : ℕ) : ℝ :=
  1 + H + K + R + (D : ℝ) + q⁻¹ + τ₀⁻¹

def packetEnvelope (H K R q τ₀ : ℝ) (D : ℕ) : ℝ :=
  1024 * packetSize H K R q τ₀ D ^ 4

/-- Each native midpoint group has bounded spatial center and test shift. -/
theorem nativeGroup_center_shift_bounds
    (P : MvPolynomial (Fin 4) ℝ) (B K H mid q a : ℝ)
    (hq : 0 < q) (ha : 0 < a) (hmid : mid ∈ Icc (0 : ℝ) 1)
    (Γ : (Fin 2 → ℤ) × ℤ) {A : Set Trajectory} (hA : A.Nonempty)
    (hAU : A ⊆ nativeGroup P B K H mid q a Γ) :
    ‖midpointGroupCenter q Γ‖ ≤ K + 2 * q ∧ |a * (Γ.2 : ℝ)| ≤ K + a := by
  obtain ⟨l, hl⟩ := hA
  have hgroup := hAU hl
  have hy : ‖planarPoint (0, l.2) mid‖ ≤ K := nativeEligible_planar_norm hgroup.1 hmid
  have hgeom := planeBinCenter_error hq (planarPoint (0, l.2) mid)
  rw [← midpointGroupCenter_eq P mid q a l.2 Γ hgroup.2] at hgeom
  have hnorm := norm_le_norm_add_norm_sub (planarPoint (0, l.2) mid) (midpointGroupCenter q Γ)
  have hcode : ⌊eval (graphPoint (0, l.2) mid) P / a⌋ = Γ.2 := congrArg Prod.snd hgroup.2
  have hval : |eval (graphPoint (0, l.2) mid) P| ≤ K := by
    simpa only [mul_one] using (hgroup.1.2.2 mid hmid).2.1
  have hsig := signal_bin_center_bound hval ha
  rw [hcode] at hsig
  exact ⟨by linarith, hsig⟩

/-- Bounds for lifted center and speed before any asymptotic power choice. -/
theorem lifted_center_speed_bound (origin c w : Plane) {s q R : ℝ}
    (hq : 0 < q) (hR : 0 ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (hcw : ‖c‖ + ‖w‖ ≤ 2) :
    ‖liftedBlockCenter origin c w s q (R * q)‖ +
      ‖liftedBlockSpeed w q (R * q)‖ ≤ ‖origin‖ + 2 * (R * q) + 4 * R := by
  have hdiv : (R * q) / q = R := by field_simp
  have hc : ‖c‖ ≤ 2 := by linarith [norm_nonneg w]
  have hw : ‖w‖ ≤ 2 := by linarith [norm_nonneg c]
  have hsabs : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hr : 0 ≤ R * q := mul_nonneg hR hq.le
  simp only [liftedBlockCenter, liftedBlockSpeed, hdiv]
  calc
    _ ≤ (‖origin‖ + (R * q) * ‖c‖ + |s| * (R * ‖w‖)) + R * ‖w‖ := by
      have h := norm_sub_le (origin + (R * q) • c) (s • (R • w))
      have h' := norm_add_le origin ((R * q) • c)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR, abs_of_nonneg hr] at h h' ⊢
      linarith
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left hc hr
      have h2 := mul_le_mul_of_nonneg_left hw hR
      have h3 := mul_le_mul_of_nonneg_right hsabs (mul_nonneg hR (norm_nonneg w))
      nlinarith

/-- All the explicit chart budgets fit into a single fourth power envelope. -/
theorem packet_envelope_bounds {H K R q τ₀ : ℝ} {D m : ℕ}
    (hH : 0 ≤ H) (hK : 1 ≤ K) (hR : 2 * K + 2 ≤ R)
    (hq : 0 < q) (hq1 : q ≤ 1) (hτ : 0 < τ₀)
    (hm : (m : ℝ) ≤ (D : ℝ) ^ 2 / (4 * τ₀)) :
    H ≤ packetEnvelope H K R q τ₀ D ∧
    H + 114 + 16 * (m : ℝ) ≤ packetEnvelope H K R q τ₀ D ∧
    K + 2 * q + 2 * (R * q) + 4 * R ≤ packetEnvelope H K R q τ₀ D ∧
    H + K + 1 ≤ packetEnvelope H K R q τ₀ D ∧
    (R * q + (R * q)⁻¹) * (16 * (D : ℝ)) ≤ packetEnvelope H K R q τ₀ D := by
  let V := packetSize H K R q τ₀ D
  have hR₀ : 0 < R := by linarith
  have hqinv : 0 < q⁻¹ := inv_pos.mpr hq
  have hτinv : 0 < τ₀⁻¹ := inv_pos.mpr hτ
  have hD₀ : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hV : 1 ≤ V := by dsimp [V, packetSize]; linarith
  have hHV : H ≤ V := by dsimp [V, packetSize]; linarith
  have hKV : K ≤ V := by dsimp [V, packetSize]; linarith
  have hRV : R ≤ V := by dsimp [V, packetSize]; linarith
  have hDV : (D : ℝ) ≤ V := by dsimp [V, packetSize]; linarith
  have hqV : q⁻¹ ≤ V := by dsimp [V, packetSize]; linarith
  have hτV : τ₀⁻¹ ≤ V := by dsimp [V, packetSize]; linarith
  have hV₀ : 0 ≤ V := by linarith
  have hV1 : V ≤ V ^ 4 := by simpa using pow_le_pow_right₀ hV (show 1 ≤ 4 by omega)
  have hV2 : V ^ 2 ≤ V ^ 4 := pow_le_pow_right₀ hV (by omega)
  have hV3 : V ^ 3 ≤ V ^ 4 := pow_le_pow_right₀ hV (by omega)
  have hV4 : 1 ≤ V ^ 4 := one_le_pow₀ hV
  have hmV : (m : ℝ) ≤ V ^ 3 := by
    calc
      _ ≤ (D : ℝ) ^ 2 / (4 * τ₀) := hm
      _ = ((D : ℝ) ^ 2 * τ₀⁻¹) / 4 := by ring
      _ ≤ (D : ℝ) ^ 2 * τ₀⁻¹ := by nlinarith [mul_nonneg (sq_nonneg (D : ℝ)) hτinv.le]
      _ ≤ V ^ 2 * V := mul_le_mul (pow_le_pow_left₀ hD₀ hDV 2) hτV hτinv.le (sq_nonneg V)
      _ = _ := by ring
  have hrV : R * q ≤ V := by
    have h := mul_le_mul_of_nonneg_left hq1 hR₀.le
    nlinarith
  have hqr : q ≤ R * q := by nlinarith
  have hr : 0 < R * q := mul_pos hR₀ hq
  have hriV : (R * q)⁻¹ ≤ V := ((inv_le_inv₀ hr hq).mpr hqr).trans hqV
  have hlast : (R * q + (R * q)⁻¹) * (16 * (D : ℝ)) ≤ 32 * V ^ 2 := by
    calc
      _ ≤ (2 * V) * (16 * V) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  change H ≤ 1024 * V ^ 4 ∧ _
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · change H + 114 + 16 * (m : ℝ) ≤ 1024 * V ^ 4
    linarith
  · change K + 2 * q + 2 * (R * q) + 4 * R ≤ 1024 * V ^ 4
    linarith
  · change H + K + 1 ≤ 1024 * V ^ 4
    linarith
  · change _ ≤ 1024 * V ^ 4
    linarith

/-- The unscaled entry-plus-inverse budget controls the scaled one. -/
theorem scaled_packet_budget {D : ℕ} {r : ℝ} (hr : 0 < r)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (hbudget : (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ 16 * D) :
    (∑ e : Fin 2, ∑ e' : Fin 2, (|(r • Q) e e'| + |(r • Q)⁻¹ e e'|)) ≤
      (r + r⁻¹) * (16 * (D : ℝ)) := by
  simp only [Finset.sum_add_distrib] at hbudget
  have hQ₀ : (0 : ℝ) ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| := by positivity
  have hI₀ : (0 : ℝ) ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'| := by positivity
  have hQle : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ 16 * D := by linarith
  have hIle : (∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'|) ≤ 16 * D := by linarith
  rw [scaled_frame_entry_budget hr Q hQ]
  calc
    _ ≤ r * (16 * D) + r⁻¹ * (16 * D) :=
      add_le_add (mul_le_mul_of_nonneg_left hQle hr.le)
        (mul_le_mul_of_nonneg_left hIle (inv_nonneg.mpr hr.le))
    _ = _ := by ring

/-- The numerical assumptions of the exact packet-to-chart conversion hold at
one polynomial budget, independent of the selected plank's parameters. -/
theorem uniform_packet_budgets
    (P : MvPolynomial (Fin 4) ℝ) (B H K R s mid q a τ₀ : ℝ) (D m : ℕ)
    (hH : 0 ≤ H) (hK : 1 ≤ K) (hR : 2 * K + 2 ≤ R)
    (hq : 0 < q) (ha1 : a ≤ 1) (hqa : q ≤ a) (ha : 0 < a) (hτ : 0 < τ₀)
    (hm : (m : ℝ) ≤ (D : ℝ) ^ 2 / (4 * τ₀))
    (hPcoeff : ∀ e, |P.coeff e| ≤ H)
    (hs : s ∈ Icc (0 : ℝ) 1) (hmid : mid ∈ Icc (0 : ℝ) 1)
    (Γ : (Fin 2 → ℤ) × ℤ) (A : Set Trajectory) (hA : A.Nonempty)
    (hAU : A ⊆ nativeGroup P B K H mid q a Γ)
    (c w : Plane) (hcw : ‖c‖ + ‖w‖ ≤ 2)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (hQbudget : (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ 16 * D) :
    H ≤ packetEnvelope H K R q τ₀ D ∧
    H + 114 + 16 * (m : ℝ) ≤ packetEnvelope H K R q τ₀ D ∧
    ‖liftedBlockCenter (midpointGroupCenter q Γ) c w s q (R * q)‖ +
      ‖liftedBlockSpeed w q (R * q)‖ ≤ packetEnvelope H K R q τ₀ D ∧
    (∑ e : Fin 2, ∑ e' : Fin 2,
      (|((R * q) • Q) e e'| + |((R * q) • Q)⁻¹ e e'|)) ≤ packetEnvelope H K R q τ₀ D ∧
    ∀ e, |(shiftedTest P (a * (Γ.2 : ℝ))).coeff e| ≤ packetEnvelope H K R q τ₀ D := by
  have hR₀ : 0 < R := by linarith
  have h := packet_envelope_bounds hH hK hR hq (hqa.trans ha1) hτ hm
  have hgroup := nativeGroup_center_shift_bounds P B K H mid q a hq ha hmid Γ hA hAU
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · exact (lifted_center_speed_bound (midpointGroupCenter q Γ) c w hq hR₀.le hs hcw).trans
      ((by linarith : ‖midpointGroupCenter q Γ‖ + 2 * (R * q) + 4 * R ≤
        K + 2 * q + 2 * (R * q) + 4 * R).trans h.2.2.1)
  · exact (scaled_packet_budget (mul_pos hR₀ hq) Q hQ hQbudget).trans h.2.2.2.2
  · intro e
    exact (shiftedTest_coeff_le hPcoeff (a * (Γ.2 : ℝ)) e).trans
      ((by linarith : H + |a * (Γ.2 : ℝ)| ≤ H + K + 1).trans h.2.2.2.1)

end
end Submission.Obl.k4_horizon_chart_assembly
