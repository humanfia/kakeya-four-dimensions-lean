import Submission.Obl.k4_physical_parent_potential_candidates.ExitNumerics

/-!
# Small facts for the final glue
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MeasureTheory Set MvPolynomial PhysicalPotentialData

noncomputable section

/-- A large base dominates a fixed constant at a fixed positive exponent. -/
lemma const_le_rpow_of_large {N Cbig x : ℝ} (hx : 0 < x) (hC : 1 ≤ Cbig)
    (hN : Cbig ^ (1 / x) ≤ N) : Cbig ≤ N ^ x := by
  have hC0 : 0 ≤ Cbig := by linarith
  have h1 : (Cbig ^ (1 / x)) ^ x = Cbig := by
    rw [← Real.rpow_mul hC0, one_div, inv_mul_cancel₀ hx.ne', Real.rpow_one]
  calc Cbig = (Cbig ^ (1 / x)) ^ x := h1.symm
    _ ≤ N ^ x := Real.rpow_le_rpow (by positivity) hN hx.le

/-- The coefficient format of the restored test fits the requested format. -/
lemma restored_coeff_le {N K C0 G loss : ℝ} {Mp Mr Ecoef Mi : ℕ}
    (hN : 1 ≤ N) (hC0 : C0 ≤ N) (hK0 : 0 ≤ K) (hK : K ≤ N ^ (loss * G)) (hloss : loss ≤ 1)
    (hloss0 : 0 ≤ loss) (hG : 0 ≤ G)
    (hMi : Ecoef * (⌈G⌉₊ + Mp + Mr + 1) + 1 ≤ Mi) :
    C0 * (K * N ^ (Mp + Mr + 1)) ^ Ecoef ≤ N ^ Mi := by
  have hN0 : 0 < N := by linarith
  have hKc : K ≤ N ^ ⌈G⌉₊ := by
    calc K ≤ N ^ (loss * G) := hK
      _ ≤ N ^ ((⌈G⌉₊ : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hN
          calc loss * G ≤ 1 * G := mul_le_mul_of_nonneg_right hloss hG
            _ = G := one_mul G
            _ ≤ (⌈G⌉₊ : ℝ) := Nat.le_ceil G
      _ = N ^ ⌈G⌉₊ := Real.rpow_natCast N _
  have hbase : K * N ^ (Mp + Mr + 1) ≤ N ^ (⌈G⌉₊ + Mp + Mr + 1) := by
    calc K * N ^ (Mp + Mr + 1) ≤ N ^ ⌈G⌉₊ * N ^ (Mp + Mr + 1) :=
          mul_le_mul_of_nonneg_right hKc (by positivity)
      _ = N ^ (⌈G⌉₊ + Mp + Mr + 1) := by rw [← pow_add]; congr 1; omega
  calc C0 * (K * N ^ (Mp + Mr + 1)) ^ Ecoef
      ≤ N * (N ^ (⌈G⌉₊ + Mp + Mr + 1)) ^ Ecoef := by
        apply mul_le_mul hC0 (pow_le_pow_left₀ (by positivity) hbase Ecoef) (by positivity)
          (by linarith)
    _ = N ^ (Ecoef * (⌈G⌉₊ + Mp + Mr + 1) + 1) := by
        rw [← pow_mul, pow_succ]; ring
    _ ≤ N ^ Mi := pow_le_pow_right₀ hN hMi

/-- The mass chain of the direct exit: heavy floor, restoration fraction and numerics. -/
lemma direct_mass_chain {μ : Measure Ev} {G G' : Set Ev} {Cr floor h priorR x : ℝ}
    {prior : ENNReal} (hprior : prior ≠ ⊤) (hpriorR : priorR = prior.toReal)
    (hh : 0 ≤ h) (hCr : 0 < Cr) (hx : 0 ≤ x)
    (hfloor : floor ≤ μ.real G) (hGfin : μ G ≠ ⊤)
    (hfrac : μ G ≤ ENNReal.ofReal Cr * μ G')
    (hnum : x * (h * priorR) ≤ floor / Cr) :
    ENNReal.ofReal (x * h) * prior ≤ μ G' := by
  have h1 : ENNReal.ofReal (x * h) * prior = ENNReal.ofReal (x * (h * priorR)) := by
    rw [hpriorR, ← mul_assoc, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ x * h),
      ENNReal.ofReal_toReal hprior]
  rw [h1]
  have h2 : ENNReal.ofReal (x * (h * priorR)) ≤ ENNReal.ofReal (μ.real G / Cr) :=
    ENNReal.ofReal_le_ofReal (hnum.trans (div_le_div_of_nonneg_right hfloor hCr.le))
  refine h2.trans ?_
  rw [ENNReal.ofReal_div_of_pos hCr, measureReal_def, ENNReal.ofReal_toReal hGfin]
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by simpa using hCr)) (Or.inl ENNReal.ofReal_ne_top)]
  calc μ G ≤ ENNReal.ofReal Cr * μ G' := hfrac
    _ = μ G' * ENNReal.ofReal Cr := mul_comm _ _

end

end Submission.Obl.k4_physical_parent_potential_candidates
