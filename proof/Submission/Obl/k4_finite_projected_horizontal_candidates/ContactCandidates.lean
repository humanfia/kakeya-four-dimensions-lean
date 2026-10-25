import Submission.Obl.k4_finite_projected_horizontal_candidates.RowNormalization
import Submission.Obl.k4_finite_projected_horizontal_candidates.ContactGeometry
import Submission.Obl.k4_finite_projected_horizontal_candidates.ReferenceBudget
import Submission.Obl.k4_horizon_chart_assembly.ParameterScales
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! Candidates in a true parent after contact normalization. -/

namespace Submission.Obl.k4_finite_projected_horizontal_candidates

open MeasureTheory Set Filter
open Submission.Lib.K4ChartLifting (timeBlock)

noncomputable section

/-- Contact geometry supplies a strip in a label heavy for the original full
assignment budget. The residual and its reference prior are kept distinct. -/
theorem contact_packet_candidate {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ ρ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (T : ℕ) (j : ι → Fin (2 ^ T))
    (A B : ι → Set α) (c : ι → Fin 5 → ℝ) {K delta : ℝ} (hK : 1 ≤ K)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, B i ⊆ A i)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hc : ∀ i, |c i 0| ≤ K ∧ |c i 1| ≤ K)
    (hpacket : ∀ i l, l ∈ A i → ∀ t ∈ timeBlock T (j i),
      |b l 0 + t * b l 3 - c i 0 - t * c i 1| ≤ K * ((2 : ℝ) ^ T)⁻¹)
    (hcontact : ∀ᵐ p ∂μ, |b p.1 4 + b p.1 0| ≤ delta ∧ |b p.1 3| ≤ K)
    (hρ : ρ ≤ μ) {m : ENNReal} (hm : m ≠ 0) (hmass : m ≤ ρ univ)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ timeBlock T (j i)) :
    ∃ (i : ι) (z : Fin 2 → ℝ), (∀ e, |z e| ≤ 2 * K) ∧
      m * ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) * ν (A i) ≤
        ρ {p | p.1 ∈ B i ∧ p.2 ∈ timeBlock T (j i) ∧
          |b p.1 4 - z 0 - z 1 * b p.1 3| ≤ delta + 3 * K * ((2 : ℝ) ^ T)⁻¹} := by
  obtain ⟨i, hi⟩ := exists_heavy_true_label ν ρ T j A B hA hdisj hm hmass
    (ae_mono hρ hcover)
  let tc : ℝ := (j i : ℝ) / (2 : ℝ) ^ T
  let q : ℝ := ((2 : ℝ) ^ T)⁻¹
  let z : Fin 2 → ℝ := ![-(c i 0 + tc * c i 1), tc]
  have hg := Submission.Obl.k4_horizon_chart_assembly.dyadic_block_geometry T (j i)
  dsimp only at hg
  have htc : tc ∈ Icc (0 : ℝ) 1 := by simpa only [tc, div_eq_mul_inv] using hg.1
  have ht : ∀ t ∈ timeBlock T (j i), |t - tc| ≤ q := by
    intro t ht
    apply hg.2.2 t
    simpa [timeBlock, div_eq_mul_inv, add_mul, tc, q] using ht
  refine ⟨i, z, ?_, ?_⟩
  · intro e
    have htcabs : |tc| ≤ 1 := abs_le.mpr ⟨by linarith [htc.1], htc.2⟩
    fin_cases e
    · change |-(c i 0 + tc * c i 1)| ≤ 2 * K
      rw [abs_neg]
      calc
        _ ≤ |c i 0| + |tc * c i 1| := abs_add_le _ _
        _ ≤ K + 1 * K := by
          rw [abs_mul]
          exact add_le_add (hc i).1 (mul_le_mul htcabs (hc i).2 (abs_nonneg _) zero_le_one)
        _ = _ := by ring
    · change |tc| ≤ 2 * K
      linarith
  · apply (show m * ENNReal.ofReal q * ν (A i) ≤ ρ (B i ×ˢ timeBlock T (j i)) by
      simpa only [q, timeBlock, mul_assoc] using hi).trans
    apply measure_mono_ae
    filter_upwards [ae_mono hρ hcontact] with p hp hpBI
    refine ⟨hpBI.1, hpBI.2, ?_⟩
    have hs := contact_strip_in_packet hp.1 (hpacket i p.1 (hB i hpBI.1) p.2 hpBI.2)
      (ht p.2 hpBI.2) (hc i).2 hp.2
    simpa only [z, Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add, q] using hs

/-- A strict separation between time and transverse rates leaves a positive
fixed gain, safely below the accuracy of the approximate contact equation. -/
theorem exists_contact_gain {kap ell U e0 : ℝ}
    (hell : 0 < ell) (hgap : ell < kap) (hU : 0 < U) (he0 : 0 < e0) :
    ∃ s v : ℝ, 0 < s ∧ 0 < v ∧ s + v ≤ U ∧
      ell * s + v < kap * s ∧ ell * s + v < e0 := by
  have hkap : 0 < kap := hell.trans hgap
  let s : ℝ := min U e0 / (4 * (kap + 1))
  let v : ℝ := (kap - ell) * s / 2
  have hs : 0 < s := div_pos (lt_min hU he0) (by positivity)
  have hv : 0 < v := div_pos (mul_pos (sub_pos.mpr hgap) hs) (by norm_num)
  have heq : 4 * (kap + 1) * s = min U e0 := by
    dsimp [s]
    exact mul_div_cancel₀ _ (by positivity)
  have hprod : 0 < ell * s := mul_pos hell hs
  have hprod' : 0 < kap * s := mul_pos hkap hs
  refine ⟨s, v, hs, hv, ?_, ?_, ?_⟩
  · dsimp only [v]
    nlinarith [min_le_left U e0]
  · dsimp only [v]
    nlinarith [mul_pos (sub_pos.mpr hgap) hs]
  · dsimp only [v]
    nlinarith [min_le_right U e0]

/-- The geometric error of a contact packet is power-smaller than the desired
strip width whenever both relevant rate gaps are strict. -/
theorem eventually_contact_strip_error {N K : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {kap ell s v e0 : ℝ} (hgap : ell * s + v < kap * s)
    (he0 : ell * s + v < e0) :
    ∀ᶠ k in atTop, N k ^ (-e0) + 3 * K k ^ 2 * N k ^ (-kap * s) ≤
      N k ^ (-ell * s - v) := by
  have hN1 (k) : 1 ≤ N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hN k)
  have h1 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hNt hK hsub 0 (a := -e0) (b := -ell * s - v) (by linarith) (A := 2) (by norm_num)
  have h2 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hNt hK hsub 2 (a := -kap * s) (b := -ell * s - v) (by linarith) (A := 6) (by norm_num)
  filter_upwards [h1, h2] with k hk1 hk2
  simp only [pow_zero, mul_one] at hk1
  nlinarith


/-- Fixed positive gaps give the strip alternative at every sufficiently late
sample and every requested exponent loss. These are exactly the mass units
used by the prepared-parent candidate conclusion. -/
theorem contact_packet_power_gain {α : Type*} [MeasurableSpace α]
    (N K : ℕ → ℝ) (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ))
    (b : ℕ → α → Fin 6 → ℝ) (T n : ℕ → ℕ)
    (j : (k : ℕ) → Fin (n k) → Fin (2 ^ T k))
    (A B : (k : ℕ) → Fin (n k) → Set α) (c : (k : ℕ) → Fin (n k) → Fin 5 → ℝ)
    {kap ell s v e0 R : ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hgap : ell * s + v < kap * s) (he0 : ell * s + v < e0) (hR : 0 < R)
    (hν : ∀ k, IsProbabilityMeasure (ν k)) (hρ : ∀ k, ρ k ≤ μ k)
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ ρ k univ)
    (hcontact : ∀ k, ∀ᵐ p ∂μ k,
      |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e0) ∧ |b k p.1 3| ≤ K k)
    (hparents : ∀ᶠ k in atTop,
      N k ^ (kap * s) / K k ≤ (2 : ℝ) ^ T k ∧
      (∀ i, MeasurableSet (A k i) ∧ B k i ⊆ A k i) ∧
      (∀ i i', i ≠ i' → j k i = j k i' → Disjoint (A k i) (A k i')) ∧
      (∀ i, |c k i 0| ≤ K k ∧ |c k i 1| ≤ K k) ∧
      (∀ i l, l ∈ A k i → ∀ t ∈ timeBlock (T k) (j k i),
        |b k l 0 + t * b k l 3 - c k i 0 - t * c k i 1| ≤
          K k * ((2 : ℝ) ^ T k)⁻¹) ∧
      (∀ᵐ p ∂μ k, ∃ i, p.1 ∈ B k i ∧ p.2 ∈ timeBlock (T k) (j k i))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∃ (i : Fin (n k)) (z : Fin 2 → ℝ), (∀ e, |z e| ≤ N k ^ R) ∧
        ENNReal.ofReal (N k ^ (-ε) / (2 : ℝ) ^ T k) * ν k (A k i) ≤
          ρ k {p | p.1 ∈ B k i ∧ p.2 ∈ timeBlock (T k) (j k i) ∧
            |b k p.1 4 - z 0 - z 1 * b k p.1 3| ≤
              N k ^ ε * N k ^ (-ell * s - v)} := by
  intro ε hε
  have hN1 (k) : 1 ≤ N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hN k)
  have hcoeff := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hNt hK hsub 1 (a := 0) (b := R) hR (A := 2) (by norm_num)
  have herr := eventually_contact_strip_error hN hNt hK hsub hgap he0
  filter_upwards [hparents, hcoeff, herr, hsub ε hε] with k hp hc he hkε
  obtain ⟨hT, hAB, hd, hci, hpacket, hcover⟩ := hp
  haveI := hν k
  have hKp : 0 < K k := lt_of_lt_of_le zero_lt_one (hK k)
  have hNp : 0 < N k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hN k)
  have hm : ENNReal.ofReal ((K k)⁻¹) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hKp))
  obtain ⟨i, z, hz, hmz⟩ := contact_packet_candidate (ν k) (μ k) (ρ k) (b k)
    (T k) (j k) (A k) (B k) (c k) (hK k) (fun i => (hAB i).1)
    (fun i => (hAB i).2) hd hci hpacket (hcontact k) (hρ k) hm (hmass k) hcover
  have hq : ((2 : ℝ) ^ T k)⁻¹ ≤ K k * N k ^ (-kap * s) := by
    have ht := one_div_le_one_div_of_le
      (div_pos (Real.rpow_pos_of_pos hNp _) hKp) hT
    simpa [one_div, inv_div, div_eq_mul_inv, neg_mul, Real.rpow_neg hNp.le] using ht
  have herror : N k ^ (-e0) + 3 * K k * ((2 : ℝ) ^ T k)⁻¹ ≤
      N k ^ (-ell * s - v) := by
    calc
      _ ≤ N k ^ (-e0) + 3 * K k * (K k * N k ^ (-kap * s)) := by gcongr
      _ = N k ^ (-e0) + 3 * K k ^ 2 * N k ^ (-kap * s) := by ring
      _ ≤ _ := he
  have hinv : N k ^ (-ε) ≤ (K k)⁻¹ := by
    have hh := one_div_le_one_div_of_le hKp hkε
    simpa only [one_div, Real.rpow_neg hNp.le] using hh
  have hfloor : ENNReal.ofReal (N k ^ (-ε) / (2 : ℝ) ^ T k) ≤
      ENNReal.ofReal ((K k)⁻¹) * ENNReal.ofReal (((2 : ℝ) ^ T k)⁻¹) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hKp.le), div_eq_mul_inv]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hinv (by positivity))
  have heps : 1 ≤ N k ^ ε := Real.one_le_rpow (hN1 k) hε.le
  have herror' : N k ^ (-e0) + 3 * K k * ((2 : ℝ) ^ T k)⁻¹ ≤
      N k ^ ε * N k ^ (-ell * s - v) := by
    have hp := Real.rpow_pos_of_pos hNp (-ell * s - v)
    nlinarith
  refine ⟨i, z, ?_, ?_⟩
  · intro e
    exact (hz e).trans (by simpa only [pow_one, Real.rpow_zero, mul_one] using hc.le)
  · calc
      _ ≤ (ENNReal.ofReal ((K k)⁻¹) * ENNReal.ofReal (((2 : ℝ) ^ T k)⁻¹)) *
          ν k (A k i) := mul_le_mul_left hfloor _
      _ ≤ _ := hmz.trans (measure_mono (by
        intro p hp
        exact ⟨hp.1, hp.2.1, hp.2.2.trans herror'⟩))

end
end Submission.Obl.k4_finite_projected_horizontal_candidates
