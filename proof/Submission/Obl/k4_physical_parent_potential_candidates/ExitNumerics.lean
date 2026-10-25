import Submission.Obl.k4_physical_parent_potential_candidates.Restoration

/-!
# Numerics of the direct exit

All losses of the exit are polynomial in the source constant `K ≤ N^(loss*gain*L)`. With the
group width `w = N^(-(1-ρ) gain L) / (4 Cr)` and a sufficiently small `loss`, they fit the
slack `N^(ρ gain L + τ)` of the frozen direct candidate at `ag = gain`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MeasureTheory Set

noncomputable section

/-- A polynomial bound for the counting resolution. -/
def resolutionConst (q : ℕ) : ℝ := 4 + 9 * (q : ℝ) * ((q + 1) ^ 3 : ℕ)

lemma resolutionConst_pos (q : ℕ) : 0 < resolutionConst q := by
  unfold resolutionConst; positivity

lemma countingResolution_le {q : ℕ} {K : ℝ} (hK : 1 ≤ K) :
    countingResolution K (physicalPotentialLip q K) ≤ resolutionConst q * K ^ (100 + q) := by
  unfold countingResolution physicalPotentialLip resolutionConst
  have hK0 : 0 ≤ K := by linarith
  have h1 : K ^ 100 ≤ K ^ (100 + q) := pow_le_pow_right₀ hK (by omega)
  have h2 : K ^ (q + 1) ≤ K ^ (100 + q) := pow_le_pow_right₀ hK (by omega)
  have h3 : (1:ℝ) ≤ K ^ (100 + q) := one_le_pow₀ hK
  have hq : (0:ℝ) ≤ (q:ℝ) * ((q + 1) ^ 3 : ℕ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hq]

/-- Powers of a quantity below a real power. -/
lemma pow_le_rpow_mul {K N x : ℝ} (n : ℕ) (hK0 : 0 ≤ K) (hN : 0 ≤ N)
    (hK : K ≤ N ^ x) : K ^ n ≤ N ^ ((n : ℝ) * x) := by
  calc K ^ n ≤ (N ^ x) ^ n := pow_le_pow_left₀ hK0 hK n
    _ = N ^ ((n : ℝ) * x) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN, mul_comm]

lemma rpow_le_rpow_exp {N x y : ℝ} (hN : 1 ≤ N) (hxy : x ≤ y) : N ^ x ≤ N ^ y :=
  Real.rpow_le_rpow_of_exponent_le hN hxy

set_option maxHeartbeats 1000000 in
/-- The exit numerics, in real form. -/
theorem exit_numerics {N G ρ d τ loss C0 K Cbig PML : ℝ} {q E m P : ℕ}
    (hN : 1 ≤ N) (hG : 0 < G) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hd : 0 ≤ d) (hd1 : d < 1)
    (hτ : 0 < τ) (hloss : 0 < loss)
    (hlossE : loss * ((309 : ℝ) + 2 * (E : ℝ) + (q : ℝ) + (P : ℝ)) ≤ ρ / 4)
    (hlossm : loss * (m : ℝ) ≤ ρ / 4)
    (hC0 : 1 ≤ C0) (hK1 : 1 ≤ K) (hK : K ≤ N ^ (loss * G)) (hPML : 0 < PML)
    (hbig : 8 * resolutionConst q * C0 + 4 * PML * C0 ^ 2 + 8 * C0 ^ 2 + 3 ≤ Cbig)
    (hbigN : Cbig ≤ N ^ (ρ * G / 4)) (Cr w : ℝ) (hCrdef : Cr = C0 * K ^ E)
    (hwdef : w = N ^ (-((1 - ρ) * G)) / (4 * Cr)) :
    0 < w ∧ 2 * w ≤ 1 ∧ 1 ≤ Cr ∧
    Cr ≤ N ^ (ρ * G / 2) ∧
    resolutionConst q * K ^ (100 + q + P) * (2 * N ^ (-(2 * G))) ≤ w ∧
    2 * (Cr * w) ≤ N ^ (ρ * G) * N ^ (-G) ∧
    2 * Cr * N ^ (-G) ≤ N ^ (ρ * G) * w ∧
    N ^ (-((d * G + ρ * G)) - τ) ≤ w ^ d / (PML * K ^ m * Cr) := by
  have hN0 : 0 < N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hE : (E : ℝ) ≤ 309 + 2 * E + q + P := by
    have := (Nat.cast_nonneg (α := ℝ) q)
    have := (Nat.cast_nonneg (α := ℝ) P)
    linarith
  -- K^E ≤ N^(ρG/4)
  have hKE : K ^ E ≤ N ^ (ρ * G / 4) := by
    refine (pow_le_rpow_mul E hK0 hN0.le hK).trans (rpow_le_rpow_exp hN ?_)
    have : loss * (E : ℝ) ≤ ρ / 4 :=
      (mul_le_mul_of_nonneg_left hE hloss.le).trans hlossE
    nlinarith
  have hC0N : C0 ≤ N ^ (ρ * G / 4) := by
    refine le_trans ?_ hbigN
    nlinarith [sq_nonneg C0, mul_pos hPML (by positivity : (0:ℝ) < C0 ^ 2),
      resolutionConst_pos q]
  have hKE1 : 1 ≤ K ^ E := one_le_pow₀ hK1
  have hCr1 : 1 ≤ Cr := by rw [hCrdef]; simpa using mul_le_mul hC0 hKE1 zero_le_one (by linarith)
  have hCrN : Cr ≤ N ^ (ρ * G / 2) := by
    calc Cr = C0 * K ^ E := hCrdef
      _ ≤ N ^ (ρ * G / 4) * N ^ (ρ * G / 4) :=
          mul_le_mul hC0N hKE (by positivity) (by positivity)
      _ = N ^ (ρ * G / 2) := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hCr0 : 0 < Cr := by linarith
  have hpowle : N ^ (-((1 - ρ) * G)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  have hw0 : 0 < w := by rw [hwdef]; positivity
  refine ⟨hw0, ?_, hCr1, hCrN, ?_, ?_, ?_, ?_⟩
  · -- 2 w ≤ 1
    have : w ≤ 1 / 4 := by
      rw [hwdef, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · -- the counting resolution
    have hKq : K ^ (100 + q + P) ≤ N ^ (ρ * G / 4) := by
      refine (pow_le_rpow_mul (100 + q + P) hK0 hN0.le hK).trans (rpow_le_rpow_exp hN ?_)
      push_cast
      have h1 : loss * ((100 : ℝ) + q + P) ≤ ρ / 4 := by
        refine le_trans ?_ hlossE
        apply mul_le_mul_of_nonneg_left _ hloss.le
        have := (Nat.cast_nonneg (α := ℝ) E); linarith
      nlinarith
    have hRC : 8 * resolutionConst q * C0 ≤ N ^ (ρ * G / 4) := by
      refine le_trans ?_ hbigN
      nlinarith [sq_nonneg C0, mul_pos hPML (by positivity : (0:ℝ) < C0 ^ 2)]
    -- target: RC K^(100+q) * 2 N^(-2G) * 4 Cr ≤ N^(-(1-ρ)G)
    rw [hwdef, le_div_iff₀ (by positivity)]
    have hCrK : Cr ≤ C0 * N ^ (ρ * G / 4) := by
      rw [hCrdef]; exact mul_le_mul_of_nonneg_left hKE (by linarith)
    calc resolutionConst q * K ^ (100 + q + P) * (2 * N ^ (-(2 * G))) * (4 * Cr)
        = (8 * resolutionConst q * K ^ (100 + q + P)) * Cr * N ^ (-(2 * G)) := by ring
      _ ≤ (8 * resolutionConst q * N ^ (ρ * G / 4)) * (C0 * N ^ (ρ * G / 4)) *
            N ^ (-(2 * G)) := by
          have hRC0 := resolutionConst_pos q
          gcongr
      _ = (8 * resolutionConst q * C0) * (N ^ (ρ * G / 4) * N ^ (ρ * G / 4) *
            N ^ (-(2 * G))) := by ring
      _ ≤ N ^ (ρ * G / 4) * (N ^ (ρ * G / 4) * N ^ (ρ * G / 4) * N ^ (-(2 * G))) := by
          gcongr
      _ = N ^ (3 * (ρ * G / 4) - 2 * G) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
      _ ≤ N ^ (-((1 - ρ) * G)) := rpow_le_rpow_exp hN (by nlinarith)
  · -- the value bound, with a = 2 N^(-0) normalized away
    have hw4 : Cr * w = N ^ (-((1 - ρ) * G)) / 4 := by
      rw [hwdef]; field_simp
    calc 2 * (Cr * w) = N ^ (-((1 - ρ) * G)) / 2 := by rw [hw4]; ring
      _ ≤ N ^ (-((1 - ρ) * G)) := by
          have : 0 < N ^ (-((1 - ρ) * G)) := by positivity
          linarith
      _ = N ^ (ρ * G) * N ^ (-G) := by rw [← Real.rpow_add hN0]; congr 1; ring
  · -- the curvature bound
    have hsq : Cr ^ 2 ≤ N ^ (ρ * G) := by
      calc Cr ^ 2 ≤ (N ^ (ρ * G / 2)) ^ 2 := pow_le_pow_left₀ hCr0.le hCrN 2
        _ = N ^ (ρ * G) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; ring
    have h8 : 8 ≤ N ^ (ρ * G) := by
      have h3 : (8:ℝ) ≤ Cbig := by nlinarith [sq_nonneg C0, mul_pos hPML (by positivity :
        (0:ℝ) < C0 ^ 2), resolutionConst_pos q]
      refine h3.trans (hbigN.trans (rpow_le_rpow_exp hN (by nlinarith)))
    have h8sq : 8 * Cr ^ 2 ≤ N ^ (2 * ρ * G) := by
      calc 8 * Cr ^ 2 ≤ N ^ (ρ * G) * N ^ (ρ * G) := mul_le_mul h8 hsq (by positivity)
            (by positivity)
        _ = N ^ (2 * ρ * G) := by rw [← Real.rpow_add hN0]; congr 1; ring
    -- 2 Cr N^(-G) ≤ N^(ρG) * N^(-(1-ρ)G) / (4 Cr)
    have hw' : N ^ (ρ * G) * w = N ^ (ρ * G) * N ^ (-((1 - ρ) * G)) / (4 * Cr) := by
      rw [hwdef]; ring
    rw [hw', le_div_iff₀ (by positivity)]
    have hsplit : N ^ (ρ * G) * N ^ (-((1 - ρ) * G)) = N ^ (2 * ρ * G) * N ^ (-G) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
    rw [hsplit]
    have hNG : 0 < N ^ (-G) := by positivity
    calc 2 * Cr * N ^ (-G) * (4 * Cr) = 8 * Cr ^ 2 * N ^ (-G) := by ring
      _ ≤ N ^ (2 * ρ * G) * N ^ (-G) := mul_le_mul_of_nonneg_right h8sq hNG.le
  · -- the mass bound
    have hwd : N ^ (-(d * G)) / (4 * Cr) ≤ w ^ d := by
      have hbase : N ^ (-(d * G)) ≤ (N ^ (-((1 - ρ) * G))) ^ d := by
        rw [← Real.rpow_mul hN0.le]
        exact rpow_le_rpow_exp hN (by nlinarith [mul_nonneg (mul_nonneg hd hG.le) hρ.le])
      have h4 : (4 * Cr)⁻¹ ≤ ((4 * Cr)⁻¹) ^ d := by
        have h41 : (4 * Cr)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        have h40 : (0:ℝ) ≤ (4 * Cr)⁻¹ := inv_nonneg.mpr (by linarith)
        exact Real.self_le_rpow_of_le_one h40 h41 hd1.le
      calc N ^ (-(d * G)) / (4 * Cr) = N ^ (-(d * G)) * (4 * Cr)⁻¹ := by ring
        _ ≤ (N ^ (-((1 - ρ) * G))) ^ d * ((4 * Cr)⁻¹) ^ d :=
            mul_le_mul hbase h4 (by positivity) (by positivity)
        _ = w ^ d := by
            rw [← Real.mul_rpow (by positivity) (by positivity), hwdef, div_eq_mul_inv]
    have hK208 : K ^ m ≤ N ^ (ρ * G / 4) := by
      refine (pow_le_rpow_mul m hK0 hN0.le hK).trans (rpow_le_rpow_exp hN ?_)
      calc (m:ℝ) * (loss * G) = (loss * m) * G := by ring
        _ ≤ (ρ / 4) * G := mul_le_mul_of_nonneg_right hlossm hG.le
        _ = ρ * G / 4 := by ring
    have hPC : 4 * PML * C0 ^ 2 ≤ N ^ (ρ * G / 4) := by
      refine le_trans ?_ hbigN
      have h1 : 0 < 8 * resolutionConst q * C0 :=
        mul_pos (mul_pos (by norm_num) (resolutionConst_pos q)) (by linarith)
      have h2 : 0 ≤ C0 ^ 2 := sq_nonneg C0
      linarith
    -- PML * K^208 * Cr * 4 Cr ≤ N^(ρ G)
    have hX0 : 0 ≤ N ^ (ρ * G / 4) := by positivity
    have hden : PML * K ^ m * Cr * (4 * Cr) ≤ N ^ (ρ * G) := by
      have hCrK : Cr ≤ C0 * N ^ (ρ * G / 4) := by
        rw [hCrdef]; exact mul_le_mul_of_nonneg_left hKE (by linarith)
      have hCr2 : Cr * Cr ≤ (C0 * N ^ (ρ * G / 4)) * (C0 * N ^ (ρ * G / 4)) :=
        mul_le_mul hCrK hCrK hCr0.le (mul_nonneg (by linarith) hX0)
      have hK208' : 0 ≤ K ^ m := pow_nonneg hK0 m
      have hstep1 : (4 * PML) * K ^ m * (Cr * Cr) ≤
          (4 * PML) * N ^ (ρ * G / 4) * ((C0 * N ^ (ρ * G / 4)) * (C0 * N ^ (ρ * G / 4))) := by
        have h4P : (0:ℝ) ≤ 4 * PML := by linarith
        have hC0X : (0:ℝ) ≤ 4 * PML * N ^ (ρ * G / 4) := mul_nonneg h4P hX0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hK208 h4P) hCr2
          (mul_nonneg hCr0.le hCr0.le) hC0X
      have hstep2 : (4 * PML) * N ^ (ρ * G / 4) * ((C0 * N ^ (ρ * G / 4)) *
          (C0 * N ^ (ρ * G / 4))) = (4 * PML * C0 ^ 2) *
            (N ^ (ρ * G / 4) * N ^ (ρ * G / 4) * N ^ (ρ * G / 4)) := by
        ring
      have hstep3 : (4 * PML * C0 ^ 2) * (N ^ (ρ * G / 4) * N ^ (ρ * G / 4) * N ^ (ρ * G / 4)) ≤
          N ^ (ρ * G / 4) * (N ^ (ρ * G / 4) * N ^ (ρ * G / 4) * N ^ (ρ * G / 4)) :=
        mul_le_mul_of_nonneg_right hPC (by positivity)
      have hstep4 : N ^ (ρ * G / 4) * (N ^ (ρ * G / 4) * N ^ (ρ * G / 4) * N ^ (ρ * G / 4)) =
          N ^ (ρ * G) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
      calc PML * K ^ m * Cr * (4 * Cr)
          = (4 * PML) * K ^ m * (Cr * Cr) := by ring
        _ ≤ N ^ (ρ * G) := by rw [← hstep4]; linarith
    have hPK : 0 < PML * K ^ m * Cr :=
      mul_pos (mul_pos hPML (pow_pos (by linarith) m)) hCr0
    rw [le_div_iff₀ hPK]
    calc N ^ (-((d * G + ρ * G)) - τ) * (PML * K ^ m * Cr)
        ≤ N ^ (-((d * G + ρ * G))) * (PML * K ^ m * Cr) :=
          mul_le_mul_of_nonneg_right (rpow_le_rpow_exp hN (by linarith)) hPK.le
      _ = N ^ (-(d * G)) * N ^ (-(ρ * G)) * (PML * K ^ m * Cr) := by
          rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ N ^ (-(d * G)) / (4 * Cr) := by
          rw [le_div_iff₀ (by positivity)]
          have hρG : N ^ (-(ρ * G)) * N ^ (ρ * G) = 1 := by
            rw [← Real.rpow_add hN0]; simp
          calc N ^ (-(d * G)) * N ^ (-(ρ * G)) * (PML * K ^ m * Cr) * (4 * Cr)
              = N ^ (-(d * G)) * N ^ (-(ρ * G)) * (PML * K ^ m * Cr * (4 * Cr)) := by
                ring
            _ ≤ N ^ (-(d * G)) * N ^ (-(ρ * G)) * N ^ (ρ * G) :=
                mul_le_mul_of_nonneg_left hden (by positivity)
            _ = N ^ (-(d * G)) := by rw [mul_assoc, hρG, mul_one]
      _ ≤ w ^ d := hwd

end

end Submission.Obl.k4_physical_parent_potential_candidates
