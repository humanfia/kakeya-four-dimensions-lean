-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SelectedFactorization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.AssignedCover
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorRetention
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.StableSelection

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces

open Finset MeasureTheory

/-- The complete selection and convex factorization at the start of the large-count
argument. The error `ν` remains free to be chosen below later density thresholds. -/
theorem large_factored_coarse_cover {ν ζ : ℝ} (hν : 0 < ν) (hνζ : 6 * ν ≤ ζ) :
    ∃ h d : ℝ, 0 < h ∧ h ≤ ν / 20 ∧ 0 < d ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ η : ℝ, η ≤ h →
      ∀ (n N : ℕ) (x v : Fin n → V) (Y Z : Fin n → Set V) (S : Finset (Fin n))
        (ρ : ℝ) (y w : Fin N → V) (f : Fin n → Fin N),
      δ ≤ ρ → ρ ≤ 1 → A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      C δ h n x v Y S Z ρ N y w f →
      (∀ U : Finset (Fin N),
        o (δ ^ (ζ / 2)) * ∑ i ∈ S, μ (Z i) ≤ ∑ i ∈ S with f i ∈ U, μ (Z i) →
        ¬ ∀ W, Convex ℝ W →
          o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o (δ ^ (-ζ)) * μ W) →
      ∃ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → V)
        (e : Fin L → V ≃ₗᵢ[ℝ] V) (g : Fin N → Fin L),
        U.Nonempty ∧ δ ^ (-ζ) < m ∧
        Factor.AssignedCover 4 ρ (δ ^ (-ν)) y w U m a b L z e g ∧
        o (δ ^ (h + 2 * ν + ν / 10)) * ∑ i, μ (Y i) ≤
          ∑ i ∈ S with f i ∈ U, μ (Z i) ∧
        (∀ j ∈ U, ∀ k ∈ U,
          coarseWeight S Z f j ≤ δ ^ (-(ν / 20)) * coarseWeight S Z f k) ∧
        ∀ k ∈ U,
          o (δ ^ (2 * h + η + ν + ν / 10) * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤
            ∑ i ∈ S with f i = k, μ (Z i) := by
  classical
  let C₀ : ℝ := max 768 wz_endpoint_bootstrap.ballConstant
  have hC₀ : 0 < C₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨p, d₁, -, hd₁, hselect⟩ := stable_coarse_tubes_power hν hC₀
  obtain ⟨d₂, hd₂, hfactor⟩ := factor_assignment_power_bound hν
  let h : ℝ := min (1 / 4) (ν / 20)
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hhν : h ≤ ν / 20 := min_le_right _ _
  have hhquarter : h ≤ 1 / 4 := min_le_left _ _
  refine ⟨h, min d₁ d₂, hh, hhν, lt_min hd₁ hd₂, ?_⟩
  intro δ hδ hδd η hη n N x v Y Z S ρ y w f hδρ hρ1 hA hC hno
  obtain ⟨hhalf, hCδ, -, hsel⟩ := hselect δ hδ (hδd.trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (c_coarse_pos hδ hA hC)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
  have h768 : 768 * δ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le).trans hCδ
  have hball : wz_endpoint_bootstrap.ballConstant * δ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le).trans hCδ
  let A₀ : ℝ := 384 * δ ^ (-h) * n * δ ^ 2 / N
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  have hsize := c_coarse_size_le_sixth_power hδ hδ1 hδρ (by linarith : η ≤ 2) hball hA hC
  obtain ⟨Q, hQ, hkeep, hcmp, -⟩ := hsel ρ A₀ hρ hρ1 hA₀ N y w
    (coarseWeight S Z f)
    (c_coarseWeight_upper hδ hδ1 hA hC)
    ((by positivity : 0 < δ ^ (h + η) * n * δ ^ 2).trans_le
      (c_coarseWeight_density hδ hA hC))
    (c_coarseWeight_tail hδ hδ1 (by linarith) h768 hA hC) hsize
  obtain ⟨U, m, a, b, L, z, e, g, hUQ, hU, hcard, hcover⟩ :=
    (c_factor_family hδ hδρ hρ1 hA hC).assigned_cover_subset (by norm_num) Q hQ
  have herror : 2 * Factor.Kc 4 Q.card ρ ^ 3 ≤ δ ^ (-ν) := by
    apply hfactor δ hδ (hδd.trans (min_le_right _ _)) Q.card ρ
      (Finset.card_pos.mpr hQ) hρ hρ1
    refine le_trans ?_ hsize
    gcongr
    exact_mod_cast (show Q.card ≤ N by simpa using Q.card_le_univ)
  have hcard' : (Q.card : ℝ) ≤ δ ^ (-ν) * U.card :=
    hcard.trans (mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg _))
  have hkeepo : o (δ ^ (ν + ν / 20)) * ∑ i ∈ S, μ (Z i) ≤
      ∑ i ∈ S with f i ∈ Q, μ (Z i) := by
    have ho := ENNReal.ofReal_le_ofReal hkeep
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)] at ho
    change o (δ ^ (ν + ν / 20)) * o (∑ k, coarseWeight S Z f k) ≤
      o (∑ k ∈ Q, coarseWeight S Z f k) at ho
    rw [ofReal_sum_coarseWeight hA hC Q] at ho
    have hall : o (∑ k, coarseWeight S Z f k) = ∑ i ∈ S, μ (Z i) := by
      simpa using ofReal_sum_coarseWeight hA hC (Finset.univ : Finset (Fin N))
    rwa [hall] at ho
  have hK : ∀ W, Convex ℝ W →
      o (q {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ W} * ρ ^ 2) ≤ o m * μ W := by
    intro W hW
    simpa only [q, T, o, μ, Factor.ncard_sub] using hcover.upper W hW
  have hlarge := large_coefficient_of_no_small_retained_cover hδ hδ1
    (by linarith : (ν + ν / 20) + ν / 20 + ν ≤ ζ / 2)
    hA hC Q U hU hUQ hkeepo hcmp hcard' hK hno
  have hretain := c_mass_retention_of_card_retention hδ hA hC Q U hU hUQ hkeepo hcmp hcard'
  refine ⟨U, m, a, b, L, z, e, g, hU, hlarge, hcover.mono herror, ?_,
    fun j hj k hk => hcmp j (hUQ hj) k (hUQ hk), ?_⟩
  · calc
      _ = o (δ ^ ((ν + ν / 20) + ν / 20 + ν)) * (o (δ ^ h) * ∑ i, μ (Y i)) := by
        rw [← mul_assoc]
        congr 1
        change ENNReal.ofReal _ = ENNReal.ofReal _ * ENNReal.ofReal _
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ o (δ ^ ((ν + ν / 20) + ν / 20 + ν)) * ∑ i ∈ S, μ (Z i) :=
        mul_le_mul_right hC.2.1 _
      _ ≤ _ := hretain
  · have hkeepReal : δ ^ (h + ν + ν / 20) * ∑ i, (μ (Y i)).toReal ≤
        ∑ j ∈ Q, coarseWeight S Z f j := by
      calc
        _ = δ ^ (ν + ν / 20) * (δ ^ h * ∑ i, (μ (Y i)).toReal) := by
          rw [← mul_assoc, ← Real.rpow_add hδ]
          congr 2
          ring
        _ ≤ δ ^ (ν + ν / 20) * ∑ k, coarseWeight S Z f k :=
          mul_le_mul_of_nonneg_left (c_coarseWeight_retention hδ hA hC)
            (Real.rpow_nonneg hδ.le _)
        _ ≤ _ := hkeep
    intro k hk
    rw [show 2 * h + η + ν + ν / 10 = (h + ν + ν / 20) + η + ν / 20 + h by ring]
    exact c_selected_fiber_density hδ hA hC Q hkeepReal hcmp k (hUQ hk)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces
