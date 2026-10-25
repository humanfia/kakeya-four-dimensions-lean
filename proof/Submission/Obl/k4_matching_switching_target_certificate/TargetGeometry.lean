import Submission.Obl.k4_matching_switching_target_certificate.Tubes
import Submission.Obl.k4_matching_switching_target_certificate.PathJets

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory

/-- The exponents of the reverse-order jet coordinates sum to `(m + 1)/2`. -/
lemma sum_jet_weights {m : ℕ} (hm : 1 ≤ m) :
    (∑ j : Fin m, ((j : ℝ) + 1) / (m : ℝ)) = ((m : ℝ) + 1) / 2 := by
  have hsum : ∀ m : ℕ, (∑ j : Fin m, ((j : ℝ) + 1)) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one] at *
      rw [ih]
      ring
  rw [← Finset.sum_div, hsum]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp

lemma prod_power_widths {m : ℕ} {N : ℝ} (hN : 0 < N) (B : ℝ) (e : Fin m → ℝ) :
    (∏ j, B * N ^ (-e j)) = B ^ m * N ^ (-(∑ j, e j)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_sum_of_pos hN]
  simp only [Finset.sum_neg_distrib]

/-- A family of moving boxes has the predicted volume for arbitrary measurable centers. -/
theorem volume_power_tube_union_le {m : ℕ} {ι : Type*} (I : Finset ι)
    {S : ι → Set ℝ} {c : ι → Fin m → ℝ → ℝ}
    {N B A b₀ Δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (e : Fin m → ℝ) (hS : ∀ i, MeasurableSet (S i))
    (hc : ∀ i j, Measurable (c i j))
    (hvol : ∀ i ∈ I, volume (S i) ≤ ENNReal.ofReal (B * N ^ (-b₀)))
    (hcard : (I.card : ℝ) ≤ A * N ^ Δ) :
    volume (⋃ i ∈ I, tube (S i) (c i) (fun j => B * N ^ (-e j))) ≤
      ENNReal.ofReal (A * B * (2 * B) ^ m * N ^ (Δ - b₀ - ∑ j, e j)) := by
  have hprod : (∏ j : Fin m, ENNReal.ofReal (2 * (B * N ^ (-e j)))) =
      ENNReal.ofReal ((2 * B) ^ m * N ^ (-(∑ j, e j))) := by
    rw [← ENNReal.ofReal_prod_of_nonneg
      (f := fun j : Fin m => 2 * (B * N ^ (-e j))) (by intro j _; positivity)]
    congr 1
    convert prod_power_widths hN (2 * B) e using 1
    congr 1
    funext j
    ring
  have hbound := volume_iUnion_tube_le I (fun j => B * N ^ (-e j)) hS hc hvol
  rw [hprod] at hbound
  calc _ ≤ (I.card : ENNReal) *
        (ENNReal.ofReal (B * N ^ (-b₀)) *
          ENNReal.ofReal ((2 * B) ^ m * N ^ (-(∑ j, e j)))) := hbound
    _ ≤ ENNReal.ofReal (A * N ^ Δ) *
        (ENNReal.ofReal (B * N ^ (-b₀)) *
          ENNReal.ofReal ((2 * B) ^ m * N ^ (-(∑ j, e j)))) := by
      gcongr
      simpa using ENNReal.ofReal_le_ofReal hcard
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show Δ - b₀ - ∑ j, e j = Δ + (-b₀ + -(∑ j, e j)) by ring,
        Real.rpow_add hN, Real.rpow_add hN]
      ring

/-- The target volume at one refinement step, in the endpoint's reverse jet order. -/
theorem volume_step_target_le {m q : ℕ} (hm : 1 ≤ m) {ι : Type*} (I : Finset ι)
    {S : ι → Set ℝ} {c : ι → Fin m → ℝ → ℝ}
    {N B A Δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hS : ∀ i, MeasurableSet (S i)) (hc : ∀ i j, Measurable (c i j))
    (hvol : ∀ i ∈ I, volume (S i) ≤ ENNReal.ofReal (B * N ^ (-(1 / (m : ℝ)) / (q : ℝ))))
    (hcard : (I.card : ℝ) ≤ A * N ^ Δ) :
    volume (⋃ i ∈ I, tube (S i) (c i)
      (fun j : Fin m => B * N ^ (-(((j : ℝ) + 1) / (m : ℝ)) / (q : ℝ)))) ≤
      ENNReal.ofReal (A * B * (2 * B) ^ m *
        N ^ (Δ - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ))) := by
  have h := volume_power_tube_union_le I hN hB hA
    (fun j : Fin m => (((j : ℝ) + 1) / (m : ℝ)) / (q : ℝ)) hS hc
    (b₀ := (1 / (m : ℝ)) / (q : ℝ)) (by simpa only [neg_div] using hvol) hcard
  simp only [← neg_div] at h
  rw [← Finset.sum_div, sum_jet_weights hm] at h
  rw [show Δ - 1 / (m : ℝ) / (q : ℝ) - ((m : ℝ) + 1) / 2 / (q : ℝ) =
    Δ - (1 / (m : ℝ) + ((m : ℝ) + 1) / 2) / (q : ℝ) by ring] at h
  simpa only [neg_div] using h

end Submission.Obl.k4_matching_switching_target_certificate
