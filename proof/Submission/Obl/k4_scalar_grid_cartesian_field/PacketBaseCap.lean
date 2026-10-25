import Submission.Obl.k4_scalar_grid_cartesian_field.PacketGeometry
import Submission.Obl.k4_scalar_grid_cartesian_field.PacketPolynomial
import Submission.Obl.k4_scalar_grid_cartesian_field.RectangularCaps

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_scalar_noisy_block_packets (blockLeft blockLength blockInterval)

/-- The original rectangular cap controls every normalized base cell of a packet.
Only the fixed original exponent `10 + κ` is used, so no scale is chosen after the data. -/
theorem packet_base_cap_raw (ρ μ : Measure Incidence) (hμ : μ ≤ ρ)
    {N K d κ u v : ℝ} (hN : 0 < N) (hK : 1 ≤ K)
    (T : ℕ) (j : Fin (2 ^ T)) (A : Set Trajectory)
    (hsupport : μ (A ×ˢ blockInterval T j)ᶜ = 0)
    (hhupper : blockLength T ≤ K * N ^ (-κ)) (huv : |u| + |v| ≤ K)
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    (hnorm : ∀ t ∈ blockInterval T j, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + w / (2 : ℝ) ^ T] F| ≤ K)
    (hy : ∀ l ∈ A, ∀ t ∈ blockInterval T j,
      |scalarY l t - u - t * v| ≤ K / (2 : ℝ) ^ T)
    (hfit : ∀ l ∈ A, ∀ t ∈ blockInterval T j,
      |scalarX l t - eval ![t, scalarY l t] F| ≤ K * N ^ (-1 : ℝ))
    (hcap : ∀ (q : Fin 2 → ℤ) (c : ℤ),
      ρ {p | (fun e : Fin 2 => (⌊(![p.2, scalarY p.1 p.2] : Fin 2 → ℝ) e /
        N ^ (-(10 + κ))⌋ : ℤ)) = q ∧ (⌊scalarX p.1 p.2 / N ^ (-1 : ℝ)⌋ : ℤ) = c} ≤
        ENNReal.ofReal (K * N ^ (-2 * (10 + κ) - d)))
    (hsmall : 2880 * K ^ 3 ≤ N ^ (9 : ℝ)) :
    ∀ q : Fin 2 → ℤ,
      μ {p | (fun e => (⌊normalizedBase (blockLength T) (packetOrigin T j u v) p e /
        N ^ (-10 : ℝ)⌋ : ℤ)) = q} ≤
        ((2 * ⌈2 * K + 1⌉₊ + 1) ^ 3 : ℕ) *
          ENNReal.ofReal (K * N ^ (-2 * (10 + κ) - d)) := by
  let z : Incidence → Fin 2 → ℝ := fun p => ![p.2, scalarY p.1 p.2]
  have hh := blockLength_pos T
  have hδ : 0 < N ^ (-1 : ℝ) := Real.rpow_pos_of_pos hN _
  have hξ : 0 < N ^ (-10 : ℝ) := Real.rpow_pos_of_pos hN _
  have hα : 0 < N ^ (-(10 + κ)) := Real.rpow_pos_of_pos hN _
  have hC : 2 * K + 1 ≤ (⌈2 * K + 1⌉₊ : ℝ) := Nat.le_ceil _
  have hwidth : blockLength T * N ^ (-10 : ℝ) ≤
      (⌈2 * K + 1⌉₊ : ℝ) * N ^ (-(10 + κ)) := by
    calc
      _ ≤ (K * N ^ (-κ)) * N ^ (-10 : ℝ) := mul_le_mul_of_nonneg_right hhupper hξ.le
      _ = K * N ^ (-(10 + κ)) := by
        rw [mul_assoc, ← Real.rpow_add hN]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hα.le
  have hv : |v| ≤ K := by linarith [abs_nonneg u]
  have hbound : ∀ t ∈ Icc (blockLeft T j) (blockLeft T j + blockLength T),
      ∀ w ∈ Icc (-1 : ℝ) 1, |eval ![t, u + t * v + blockLength T * w] F| ≤ K := by
    intro t ht w hw
    simpa only [blockLength, div_eq_mul_inv, mul_comm w] using hnorm t ht w hw
  have hvar : ∀ p ∈ A ×ˢ blockInterval T j, ∀ p' ∈ A ×ˢ blockInterval T j,
      (fun e => (⌊(z p e - packetOrigin T j u v e) / blockLength T / N ^ (-10 : ℝ)⌋ : ℤ)) =
        (fun e => (⌊(z p' e - packetOrigin T j u v e) / blockLength T / N ^ (-10 : ℝ)⌋ : ℤ)) →
      |eval (z p) F - eval (z p') F| ≤ N ^ (-1 : ℝ) := by
    intro p hp p' hp' hcell
    have hdiam := normalized_cell_diameter hh hξ hcell
    have hdt : |p.2 - p'.2| ≤ blockLength T * N ^ (-10 : ℝ) := by
      simpa [z] using hdiam 0
    have hdy : |scalarY p.1 p.2 - scalarY p'.1 p'.2| ≤ blockLength T * N ^ (-10 : ℝ) := by
      simpa [z] using hdiam 1
    have hyp : |scalarY p.1 p.2 - u - p.2 * v| ≤ K * blockLength T := by
      simpa only [blockLength, div_eq_mul_inv] using hy p.1 hp.1 p.2 hp.2
    have hyp' : |scalarY p'.1 p'.2 - u - p'.2 * v| ≤ K * blockLength T := by
      simpa only [blockLength, div_eq_mul_inv] using hy p'.1 hp'.1 p'.2 hp'.2
    have h := packet_polynomial_cell_variation F hF hh hK hξ.le hv hbound
      hp.2 hp'.2 hyp hyp' hdt hdy
    apply h.trans
    calc
      _ ≤ N ^ (9 : ℝ) * N ^ (-10 : ℝ) := mul_le_mul_of_nonneg_right hsmall hξ.le
      _ = N ^ (-1 : ℝ) := by rw [← Real.rpow_add hN]; norm_num
  simpa only [normalizedBase, z] using
    normalized_graph_cell_cap ρ μ hμ z (fun p => scalarX p.1 p.2)
      (A ×ˢ blockInterval T j) hsupport (fun z => eval z F) hh hξ hδ hα
      (packetOrigin T j u v) ⌈2 * K + 1⌉₊ hwidth hC
      (ENNReal.ofReal (K * N ^ (-2 * (10 + κ) - d))) hcap
      (fun p hp => hfit p.1 hp.1 p.2 hp.2) hvar

/-- The base ceiling is calibrated to the unchanged full trajectory mass `ν(A)`. -/
theorem packet_base_cap_calibration {N K d κ h : ℝ}
    (hN : 0 < N) (hK : 1 ≤ K) (hh : 0 < h)
    (hscale : N ^ (-κ) / K ≤ h) (m : ENNReal)
    (hfloor : ENNReal.ofReal (N ^ (-d) * h / K) ≤ m) :
    ((2 * ⌈2 * K + 1⌉₊ + 1) ^ 3 : ℕ) *
        ENNReal.ofReal (K * N ^ (-2 * (10 + κ) - d)) ≤
      ENNReal.ofReal ((100000 * K ^ 7 * h) * N ^ (-20 : ℝ)) * m := by
  have hKpos : 0 < K := by linarith
  let q := N ^ (-κ)
  let ξ := N ^ (-10 : ℝ)
  let a := N ^ (-d)
  let M : ℕ := (2 * ⌈2 * K + 1⌉₊ + 1) ^ 3
  have hq : 0 ≤ q := (Real.rpow_pos_of_pos hN _).le
  have hξ : 0 ≤ ξ := (Real.rpow_pos_of_pos hN _).le
  have ha : 0 ≤ a := (Real.rpow_pos_of_pos hN _).le
  have hqscale : q ≤ K * h := by
    have := (div_le_iff₀ hKpos).mp hscale
    nlinarith
  have hcount : (M : ℝ) ≤ 729 * K ^ 3 := by
    have hceil := (Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * K + 1)).le
    dsimp [M]
    push_cast
    calc
      _ ≤ (9 * K) ^ 3 := by gcongr; linarith
      _ = _ := by ring
  have hξpow : ξ ^ 2 = N ^ (-20 : ℝ) := by
    dsimp [ξ]
    rw [← Real.rpow_mul_natCast hN.le]
    norm_num
  have hpowers : N ^ (-2 * (10 + κ) - d) = q ^ 2 * ξ ^ 2 * a := by
    dsimp [q, ξ, a]
    rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_mul_natCast hN.le,
      ← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  have hreal : (M : ℝ) * (K * N ^ (-2 * (10 + κ) - d)) ≤
      ((100000 * K ^ 7 * h) * N ^ (-20 : ℝ)) * (N ^ (-d) * h / K) := by
    rw [hpowers, ← hξpow]
    calc
      _ ≤ (729 * K ^ 3) * (K * (q ^ 2 * ξ ^ 2 * a)) := by
        exact mul_le_mul_of_nonneg_right hcount (by positivity)
      _ ≤ (729 * K ^ 3) * (K * ((K * h) ^ 2 * ξ ^ 2 * a)) := by
        gcongr
      _ = 729 * K ^ 6 * h ^ 2 * ξ ^ 2 * a := by ring
      _ ≤ 100000 * K ^ 6 * h ^ 2 * ξ ^ 2 * a := by gcongr; norm_num
      _ = _ := by dsimp [a]; field_simp
  calc
    _ = ENNReal.ofReal ((M : ℝ) * (K * N ^ (-2 * (10 + κ) - d))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((100000 * K ^ 7 * h) * N ^ (-20 : ℝ)) *
        (N ^ (-d) * h / K)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((100000 * K ^ 7 * h) * N ^ (-20 : ℝ)) *
        ENNReal.ofReal (N ^ (-d) * h / K) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (100000 * K ^ 7 * h) * N ^ (-20 : ℝ))]
    _ ≤ _ := mul_le_mul' le_rfl hfloor

end Submission.Obl.k4_scalar_grid_cartesian_field
