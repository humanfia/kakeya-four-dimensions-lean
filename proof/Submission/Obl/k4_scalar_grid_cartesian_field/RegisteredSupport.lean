import Submission.Obl.k4_scalar_grid_cartesian_field.PacketSupport

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory MvPolynomial

/-- The exact part of preparation used to transfer original physical support counts. -/
def RegisteredSupportControl {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (N H d : ℝ) (M : ℕ) (R : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / M) →
    (activeCodes ρ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / N ^ (-r)⌋ : ℤ))).Finite ∧
    ∀ q₀ : Fin 3 → ℤ,
      ({q : Fin 3 → ℤ | ρ {p |
        (fun e : Fin 3 => (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / N ^ (-r)⌋ : ℤ)) = q ∧
        (fun e : Fin 3 => (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / N ^ (-1 : ℝ)⌋ : ℤ)) = q₀} ≠ 0}.ncard : ℝ) ≤
          H * N ^ ((2 + d) * (r - 1))

/-- Hereditary preparation counts at one registered exponent, localized to a low-gradient packet. -/
theorem registered_packet_physical_count {Ω : Type*} [MeasurableSpace Ω]
    (ρ μ : Measure Ω) (hμ : μ ≤ ρ) (S : Set Ω) (hsupport : μ Sᶜ = 0)
    (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    {N H d h L R r : ℝ} {M : ℕ} (hN : 0 < N) (hH : 0 ≤ H)
    (hh : 0 < h) (hL : 1 ≤ L) (hscale : N ^ (-1 : ℝ) ≤ L * h)
    (origin : Fin 2 → ℝ)
    (hbase : ∀ p ∈ S, ∀ e, |z p e - origin e| ≤ L * h)
    (hfit : ∀ p ∈ S, |x p - eval (z p) F| ≤ L * N ^ (-1 : ℝ))
    (hgrad : ∀ p ∈ S, ∀ e, |eval (z p) (pderiv e F)| ≤ L)
    (hprep : RegisteredSupportControl ρ z x N H d M R)
    (hr : 1 ≤ r) (hrR : r ≤ R) (hreg : ∃ m : ℕ, r = (m : ℝ) / M) :
    (activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / N ^ (-r)⌋ : ℤ))).Finite ∧
    ((activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / N ^ (-r)⌋ : ℤ))).ncard : ℝ) ≤
        (1000 * L ^ 3 * H) * (h / N ^ (-r)) ^ 2 * (N ^ (-1 : ℝ) / N ^ (-r)) ^ d := by
  obtain ⟨hfin, hcount⟩ := hprep r hr hrR hreg
  have hδ : 0 < N ^ (-1 : ℝ) := Real.rpow_pos_of_pos hN _
  have hb : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN _
  obtain ⟨hf, hn⟩ := physical_support_of_coarse_graph ρ μ hμ S hsupport z x F hF
    hδ hh hL hscale (mul_nonneg hH (Real.rpow_nonneg hN.le _)) origin
    hbase hfit hgrad hfin hcount
  refine ⟨hf, hn.trans_eq ?_⟩
  rw [hereditary_exponent_eq_width_ratio hN]
  calc
    _ = (1000 * L ^ 3 * H) * ((h / N ^ (-1 : ℝ)) ^ 2 *
        (N ^ (-1 : ℝ) / N ^ (-r)) ^ (2 + d)) := by ring
    _ = _ := by rw [hereditary_ratio_identity hh hδ hb]; ring

/-- The fixed final physical grid inherits the same original packet count after rounding. -/
theorem registered_packet_fine_count {Ω : Type*} [MeasurableSpace Ω]
    (ρ μ : Measure Ω) (hμ : μ ≤ ρ) (S : Set Ω) (hsupport : μ Sᶜ = 0)
    (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    {N H d h L R B : ℝ} {M : ℕ} (hN : 2 ≤ N) (hH : 1 ≤ H)
    (hM : 1 ≤ M) (hstep : N ^ (1 / (M : ℝ)) ≤ H)
    (hd : 0 ≤ d) (hdone : d ≤ 1) (hh : 0 < h) (hL : 1 ≤ L)
    (hscale : N ^ (-1 : ℝ) ≤ L * h) (hB : 1 ≤ B) (hBR : B + 1 ≤ R)
    (origin : Fin 2 → ℝ)
    (hbase : ∀ p ∈ S, ∀ e, |z p e - origin e| ≤ L * h)
    (hfit : ∀ p ∈ S, |x p - eval (z p) F| ≤ L * N ^ (-1 : ℝ))
    (hgrad : ∀ p ∈ S, ∀ e, |eval (z p) (pderiv e F)| ≤ L)
    (hprep : RegisteredSupportControl ρ z x N H d M R) :
    (activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / N ^ (-B)⌋ : ℤ))).Finite ∧
    ((activeCodes μ (fun p (e : Fin 3) =>
      (⌊(![z p 0, z p 1, x p] : Fin 3 → ℝ) e / N ^ (-B)⌋ : ℤ))).ncard : ℝ) ≤
        (8000 * L ^ 3 * H ^ 4) * (h / N ^ (-B)) ^ 2 * (N ^ (-1 : ℝ) / N ^ (-B)) ^ d := by
  have hNp : 0 < N := by linarith
  have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hMone : (1 : ℝ) / M ≤ 1 := (div_le_one hMp).mpr (by exact_mod_cast hM)
  obtain ⟨m, hmlo, hmhi⟩ := exists_registered_exponent hM (by linarith : 0 ≤ B)
  let r : ℝ := (m : ℝ) / M
  have hr : 1 ≤ r := hB.trans hmlo
  have hrR : r ≤ R := by dsimp [r]; linarith
  obtain ⟨hfin, hn⟩ := registered_packet_physical_count ρ μ hμ S hsupport z x F hF
    hNp (by linarith) hh hL hscale origin hbase hfit hgrad hprep hr hrR ⟨m, rfl⟩
  obtain ⟨hbw, hwb⟩ := registered_width_comparison (by linarith : 1 ≤ N) hMp hstep hmlo hmhi
  have hb : 0 < N ^ (-r) := Real.rpow_pos_of_pos hNp _
  have hw : 0 < N ^ (-B) := Real.rpow_pos_of_pos hNp _
  have hδ : 0 < N ^ (-1 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hhround : h / N ^ (-r) ≤ H * (h / N ^ (-B)) := by
    simpa only [Real.rpow_one] using rounded_width_rpow_bound hh hb hw hH
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl hwb
  have hdround := rounded_width_rpow_bound hδ hb hw hH hd hdone hwb
  obtain ⟨hf, hc⟩ := physical_code_coarsening_count μ
    (fun p => ![z p 0, z p 1, x p]) hb hbw hfin
  refine ⟨hf, hc.trans ?_⟩
  calc
    _ ≤ (2 : ℝ) ^ 3 * ((1000 * L ^ 3 * H) * (h / N ^ (-r)) ^ 2 *
        (N ^ (-1 : ℝ) / N ^ (-r)) ^ d) := by gcongr
    _ ≤ (2 : ℝ) ^ 3 * ((1000 * L ^ 3 * H) * (H * (h / N ^ (-B))) ^ 2 *
        (H * (N ^ (-1 : ℝ) / N ^ (-B)) ^ d)) := by gcongr
    _ = _ := by ring

/-- All real hidden widths in a fixed compact range inherit the sharp normalized count. -/
theorem registered_packet_joint_count {Ω : Type*} [MeasurableSpace Ω]
    (ρ μ : Measure Ω) (hμ : μ ≤ ρ) (S : Set Ω) (hsupport : μ Sᶜ = 0)
    (z : Ω → Fin 2 → ℝ) (x : Ω → ℝ)
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    {N H d h L R w ξ : ℝ} {M : ℕ} (hN : 2 ≤ N) (hH : 1 ≤ H)
    (hM : 1 ≤ M) (hstep : N ^ (1 / (M : ℝ)) ≤ H)
    (hd : 0 ≤ d) (hdone : d ≤ 1) (hh : 0 < h) (hL : 1 ≤ L)
    (hscale : N ^ (-1 : ℝ) ≤ L * h) (hR : 3 ≤ R)
    (hξ : 0 < ξ) (hsmall : h * ξ ≤ N ^ (-3 : ℝ)) (origin : Fin 2 → ℝ)
    (hbase : ∀ p ∈ S, ∀ e, |z p e - origin e| ≤ L * h)
    (hfit : ∀ p ∈ S, |x p - eval (z p) F| ≤ L * N ^ (-1 : ℝ))
    (hgrad : ∀ p ∈ S, ∀ e, |eval (z p) (pderiv e F)| ≤ L)
    (hprep : RegisteredSupportControl ρ z x N H d M R)
    (hwlo : N ^ (-2 : ℝ) ≤ w) (hwhi : w ≤ N ^ (-1 : ℝ)) :
    (activeCodes μ (fun p => ((fun e : Fin 2 => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)),
      (⌊x p / w⌋ : ℤ)))).Finite ∧
    ((activeCodes μ (fun p => ((fun e : Fin 2 => (⌊(z p e - origin e) / h / ξ⌋ : ℤ)),
      (⌊x p / w⌋ : ℤ)))).ncard : ℝ) ≤
        (32000 * L ^ 3 * H ^ 2) * ξ⁻¹ ^ 2 * (N ^ (-1 : ℝ) / w) ^ d := by
  have hN1 : 1 < N := by linarith
  have hNp : 0 < N := by linarith
  obtain ⟨r, m, hr, hr3, hreg, hbw, hwb⟩ := exists_registered_width hN1 hM hstep hwlo hwhi
  obtain ⟨hfin, hcount⟩ := registered_packet_physical_count ρ μ hμ S hsupport z x F hF
    hNp (by linarith) hh hL hscale origin hbase hfit hgrad hprep hr (hr3.trans hR) ⟨m, hreg⟩
  have hsmall' : h * ξ ≤ N ^ (-r) := hsmall.trans
    (Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith))
  obtain ⟨hf, hn⟩ := joint_support_of_physical_count μ z x origin
    (Real.rpow_pos_of_pos hNp _) hh hξ (Real.rpow_pos_of_pos hNp _) (by positivity)
    hH hd hdone hsmall' hbw hwb hfin hcount
  refine ⟨hf, hn.trans_eq ?_⟩
  ring

end Submission.Obl.k4_scalar_grid_cartesian_field
