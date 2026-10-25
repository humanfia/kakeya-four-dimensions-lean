import Submission.Obl.k4_matching_switching_target_certificate.RecordControls

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set
open Submission.Obl.k4_matching_homogeneous_records (dyadicCenter)

/-- The two palette controls retain the active derivative gap, with explicit errors. -/
theorem referenceControl_separation {J m hz : ℕ} (hmJ : m ≤ J) {β : ℕ → ℝ}
    {N ε γ b a ta frame t : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (hγ0 : γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a - β m)
    (hγ : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) a + (i : ℝ) * jetRadius J β a - β m)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hg : ContDiffOn ℝ (J + 1 : ℕ) g (Ioo (-1 : ℝ) 2))
    (hfB : ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f x| ≤ N ^ ε)
    (hgB : ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) g x| ≤ N ^ ε)
    (ht : t ∈ Ico (0 : ℝ) 1) (hta : ta ∈ Icc (0 : ℝ) 1)
    (hdist : |ta - t| ≤ N ^ (-jetRadius J β a))
    (hdistz : |ta - dyadicCenter hz t| ≤ N ^ (-jetRadius J β a))
    (hlow : N ^ (-(β m + ε)) ≤ |iteratedDeriv m f t - iteratedDeriv m g t|)
    (hgap : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      |iteratedDeriv (m + i) f t - iteratedDeriv (m + i) g t| ≤ N ^ (-β (m + i) + ε)) :
    N ^ (-ε) - (2 * N ^ (-b) + (6 + 8 * N ^ ε) * N ^ (-γ)) ≤
      |referenceControl J m hz β N a b ta frame f g t true -
        referenceControl J m hz β N a b ta frame f g t false| := by
  have hN0 : 0 < N := by linarith
  have hW : 0 < N ^ β m := Real.rpow_pos_of_pos hN0 _
  let E := N ^ (-b) + (3 + N ^ ε) * N ^ (-γ)
  let uf := referenceControl J m hz β N a b ta frame f g t true
  let ug := referenceControl J m hz β N a b ta frame f g t false
  have huf : |N ^ β m * (iteratedDeriv m f ta - frame) - uf| ≤ E := by
    simpa only [ite_true] using
      referenceControl_error hmJ hN hγ0 hγ f g true hf hfB ht hta hdistz
  have hug : |N ^ β m * (iteratedDeriv m g ta - frame) - ug| ≤ E := by
    simpa only [Bool.false_eq_true, ite_false] using
      referenceControl_error hmJ hN hγ0 hγ f g false hg hgB ht hta hdistz
  have hvar := active_gap_variation hmJ hN hε ha hγ0 hγ hf hg hfB hgB
    ⟨ht.1, ht.2.le⟩ hta hdist hgap
  have hctrl : |N ^ β m * (iteratedDeriv m f ta - iteratedDeriv m g ta) - (uf - ug)| ≤ 2 * E := by
    calc _ = |(N ^ β m * (iteratedDeriv m f ta - frame) - uf) -
          (N ^ β m * (iteratedDeriv m g ta - frame) - ug)| := by congr 1; ring
      _ ≤ _ := (abs_sub _ _).trans (by linarith)
  have hl : N ^ (-ε) ≤ |N ^ β m * (iteratedDeriv m f t - iteratedDeriv m g t)| := by
    calc N ^ (-ε) = N ^ β m * N ^ (-(β m + ε)) := by
          rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ N ^ β m * |iteratedDeriv m f t - iteratedDeriv m g t| :=
        mul_le_mul_of_nonneg_left hlow hW.le
      _ = _ := by rw [abs_mul, abs_of_pos hW]
  have htriangle : |N ^ β m * (iteratedDeriv m f t - iteratedDeriv m g t)| ≤
      6 * N ^ ε * N ^ (-γ) + 2 * E + |uf - ug| := by
    calc _ = |(N ^ β m * (iteratedDeriv m f t - iteratedDeriv m g t) -
          N ^ β m * (iteratedDeriv m f ta - iteratedDeriv m g ta)) +
          (N ^ β m * (iteratedDeriv m f ta - iteratedDeriv m g ta) - (uf - ug)) +
          (uf - ug)| := by congr 1; ring
      _ ≤ |N ^ β m * (iteratedDeriv m f t - iteratedDeriv m g t) -
          N ^ β m * (iteratedDeriv m f ta - iteratedDeriv m g ta)| +
          |N ^ β m * (iteratedDeriv m f ta - iteratedDeriv m g ta) - (uf - ug)| +
          |uf - ug| := abs_add_three _ _ _
      _ ≤ _ := by
        have hv : |N ^ β m * (iteratedDeriv m f t - iteratedDeriv m g t) -
            N ^ β m * (iteratedDeriv m f ta - iteratedDeriv m g ta)| ≤ 6 * N ^ ε * N ^ (-γ) := by
          rw [abs_sub_comm, ← mul_sub]
          exact hvar
        linarith
  change _ ≤ |uf - ug|
  dsimp [E] at htriangle
  linarith

end Submission.Obl.k4_matching_switching_target_certificate
