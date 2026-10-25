import Submission.Obl.k4_matching_endpoint_volume.EndpointRegular
import Submission.Obl.k4_matching_endpoint_volume.Pullback

/-!
# Polynomial pullback bound at a fixed final time
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open Set MeasureTheory
open scoped BigOperators Matrix ENNReal NNReal ContDiff

/-- At fixed final time the pullback estimate loses only a fixed polynomial in
`K`. In particular no semialgebraic fiber theorem is required. -/
theorem endpoint_slice_polynomial_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 2 ≤ K → ∀ (U : Fin (m + 1) → ℝ),
      (∀ p : Fin (m + 1), |U p| ≤ K) →
      (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) →
      ∀ (s₀ s : ℝ), |s| ≤ 1 → ∀ A : Set (Fin m → ℝ), MeasurableSet A →
      volume (separatedUnitCube m K⁻¹ ∩ (endpointLow U s₀ s) ⁻¹' A) ≤
        ENNReal.ofReal (C * K ^ (m * (m + 1) * (m + 2))) * volume A := by
  let P : ℝ := ∏ k : Fin m, ((k : ℕ).factorial : ℝ)
  let Q : ℝ := (m : ℝ) * (m.factorial : ℝ) * (2 * (2 : ℝ) ^ m) ^ m
  let H : ℝ := 2 * (m : ℝ) ^ 2 * (2 : ℝ) ^ m
  let R : ℝ := 2 * P * Q * H
  let e : ℕ := m + m * m
  let E : ℕ := e + m + 1
  let C : ℝ := P * ((4 * R + 2) ^ m + 1)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : 0 < P := factorialProduct_pos m
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro K hK U hU hgap s₀ s hs A hA
  have hKpos : 0 < K := by linarith
  have hKone : 1 ≤ K := by linarith
  let w : Fin m → ℝ := fun p => U p.succ - U p.castSucc
  let d₀ : ℝ := 1 / (P * K ^ e)
  let δ : ℝ := 1 / (P * Q * K ^ (e + m))
  let r : ℝ := 1 / (R * K ^ E)
  let L : ℝ≥0 := ⟨(2 * K) * (m : ℝ) ^ 2 * (2 : ℝ) ^ m, by positivity⟩
  have hd₀ : 0 < d₀ := by dsimp [d₀]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hq0 : 0 ≤ K⁻¹ := by positivity
  have hq1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hKone
  have hw : ∀ p : Fin m, |w p| ≤ 2 * K := by
    intro p
    exact (abs_sub (U p.succ) (U p.castSucc)).trans (by linarith [hU p.succ, hU p.castSucc])
  have hB : 1 ≤ (2 * K) * (2 : ℝ) ^ m := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hdet (t : Fin m → ℝ) (ht : t ∈ separatedUnitCube m K⁻¹) :
      d₀ ≤ |(endpointJacobian w t s).det| := by
    have h := endpointJacobian_det_lower w t s hq0 hq1 hgap ht.2
    simpa [d₀, e, P, div_eq_mul_inv, mul_inv, inv_pow, mul_comm, mul_left_comm, mul_assoc] using h
  have hQK : (m : ℝ) * (m.factorial : ℝ) * ((2 * K) * (2 : ℝ) ^ m) ^ m = Q * K ^ m := by
    dsimp [Q]
    simp only [mul_pow]
    ring
  have hδeq : d₀ / ((m : ℝ) * (m.factorial : ℝ) * ((2 * K) * (2 : ℝ) ^ m) ^ m) = δ := by
    rw [hQK]
    dsimp [d₀, δ]
    rw [pow_add]
    field_simp
    <;> ring
  have hsmall : (L : ℝ) * r < δ := by
    have heq : (L : ℝ) * r = δ / 2 := by
      change ((2 * K) * (m : ℝ) ^ 2 * (2 : ℝ) ^ m) * r = δ / 2
      dsimp [r, R, δ, H, E]
      simp only [pow_add, pow_one]
      field_simp
      <;> ring
    rw [heq]
    linarith
  have hlip : LipschitzOnWith L (fderiv ℝ (endpointLow U s₀ s)) (Metric.closedBall 0 1) := by
    have heq : fderiv ℝ (endpointLow U s₀ s) =
        (fun t : Fin m → ℝ => endpointDerivative w t s) := by
      funext t
      exact fderiv_endpointLow U s₀ s t
    rw [heq]
    exact endpointDerivative_lipschitzOn_unitCube w hs (by positivity : 0 ≤ 2 * K) hw
  have hlower (t : Fin m → ℝ) (ht : t ∈ separatedUnitCube m K⁻¹) (v : Fin m → ℝ) :
      δ * ‖v‖ ≤ ‖fderiv ℝ (endpointLow U s₀ s) t v‖ := by
    rw [fderiv_endpointLow, ← hδeq]
    apply endpointDerivative_lower_norm hm w t s hB _ (hdet t ht) v
    intro k p
    exact endpointJacobian_entry_bound w t s (by positivity : 0 ≤ 2 * K) (by norm_num) hw
      (abs_offset_le_two hs ht.1) k p
  have hjac (t : Fin m → ℝ) (ht : t ∈ separatedUnitCube m K⁻¹) :
      d₀ ≤ |(fderiv ℝ (endpointLow U s₀ s) t).det| := by
    simpa only [fderiv_endpointLow, det_endpointDerivative] using hdet t ht
  have hf : ContDiff ℝ 1 (endpointLow U s₀ s) := (contDiff_endpointLow U s₀ s).of_le (by simp)
  have hvol := unitCube_pullback_bound (endpointLow U s₀ s) (separatedUnitCube m K⁻¹)
    (isClosed_separatedUnitCube m K⁻¹).measurableSet (separatedUnitCube_subset_ball m K⁻¹)
    hf L hr hd₀ hsmall hlip hlower hjac A hA
  apply hvol.trans
  gcongr
  have hpowE : 1 ≤ K ^ E := one_le_pow₀ hKone
  have hbase : 4 / r + 2 ≤ (4 * R + 2) * K ^ E := by
    have heq : 4 / r = 4 * R * K ^ E := by dsimp [r]; field_simp
    rw [heq]
    nlinarith
  have hpow : (4 / r + 2) ^ m ≤ (4 * R + 2) ^ m * K ^ (E * m) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 4 / r + 2) hbase m
    simpa only [mul_pow, ← pow_mul] using h
  have hpowEm : 1 ≤ K ^ (E * m) := one_le_pow₀ hKone
  have hcoeff : ((4 / r + 2) ^ m + 1) / d₀ ≤ C * K ^ (E * m + e) := by
    rw [div_eq_mul_inv, show d₀⁻¹ = P * K ^ e by dsimp [d₀]; simp]
    calc
      ((4 / r + 2) ^ m + 1) * (P * K ^ e) ≤
          (((4 * R + 2) ^ m + 1) * K ^ (E * m)) * (P * K ^ e) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ = C * K ^ (E * m + e) := by dsimp [C]; rw [pow_add]; ring
  have hdegree : E * m + e = m * (m + 1) * (m + 2) := by dsimp [E, e]; ring
  simpa only [hdegree] using hcoeff

end Submission.Obl.k4_matching_endpoint_volume
