import Submission.Obl.k4_compatible_pair_frame_preparation.FrameScales
import Submission.Obl.k4_compatible_pair_frame_preparation.FramePowers
import Submission.Obl.k4_compatible_pair_frame_preparation.FrameBudgets
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepBudget

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Set MvPolynomial Construction
open scoped ENNReal

namespace NativeSample

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ}
    {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ}
    {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}

variable (p : NativeSample True 4 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)

noncomputable def sigma : ℝ := Nk ^ (-f L) * p.R₁ * p.R₂

theorem sigma_pos (hN : 2 ≤ Nk) : 0 < p.sigma := by
  have hR₁ : 0 < p.R₁ := p.hR₂pos.trans_le p.hR21
  unfold sigma
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hR₁) p.hR₂pos

/-- The base-density estimate holds for either role of an entry. -/
theorem base_density_le [hν : ∀ γ, IsProbabilityMeasure (νk γ)]
    (hN : 2 ≤ Nk) (ha : 0 < a) (he : 0 < e) (hB : ∀ γ, 0 < Bk γ)
    (hκX : frameSlack p.κ ≤ Nk ^ (a + e)) (hκa : p.κ ≤ Nk ^ a)
    (hX : (2 : ℝ) ^ 100 ≤ Nk ^ (a + e)) (hLmem : L ∈ depths)
    (hmap : ∀ γ, Measurable (gk γ L) ∧
      Measure.map (obs (Bk γ) (δ Nk L)) (((νk γ).prod volume).restrict (Ek γ)) =
        (volume.prod Measure.count).withDensity (gk γ L))
    (s : Fin p.toPrep.m) (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U)
    (role : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) → Prop)
    (hrole : ∀ z, role z → (∃ s', z ∈ p.toPrep.H s s') ∨ ∃ s', z ∈ p.toPrep.H s' s) :
    ENNReal.ofReal ((2 : ℝ) ^ p.T) ^ 2 *
      ((νk (p.toPrep.fγ (p.toPrep.frame s))).prod (volume.prod volume))
        {z | role z ∧ base p.T ((p.toPrep.fj (p.toPrep.frame s) : ℕ) : ℝ)
          (frameSlack p.κ) (p.toPrep.fc (p.toPrep.frame s)) (p.toPrep.fu (p.toPrep.frame s))
          (p.toPrep.fQ (p.toPrep.frame s)) z.1 z.2.1 ∈ U} ≤
      ENNReal.ofReal (p.sigma * Nk ^ (100 * (a + e))) * volume U := by
  let hp := p.toPrep_hyp hN hB
  letI : ∀ γ : Fin p.toPrep.W, IsProbabilityMeasure (νk γ) := fun γ => hν γ
  letI : ∀ γ : Fin p.toPrep.W, SFinite (νk γ) := fun γ => by
    letI : IsProbabilityMeasure (νk γ) := hν γ
    infer_instance
  have hN0 : 0 < Nk := by linarith
  have hN1 : 1 ≤ Nk := by linarith
  have hκ0 : 0 ≤ p.κ := zero_le_one.trans p.κ_one
  have hK0 : 0 ≤ frameSlack p.κ := zero_le_one.trans (frameSlack_one p.κ_one)
  have hκleX : p.κ ≤ Nk ^ (a + e) := (frameSlack_input p.κ_one).trans hκX
  have hNa : Nk ^ a ≤ Nk ^ (a + e) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hq : (2 : ℝ) ^ p.s ≤ 2 * Nk ^ (a + e) :=
    p.hgainhi.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num))
  have hb : 0 < p.toPrep.dfl := Real.rpow_pos_of_pos hN0 _
  have hbi : p.toPrep.dfl⁻¹ ≤ Nk ^ (a + e) := by
    change (Nk ^ (-a))⁻¹ ≤ _
    rw [Real.rpow_neg hN0.le, inv_inv]
    exact hNa
  have hb1 : p.toPrep.dfl ≤ p.toPrep.κ₀⁻¹ := by
    change Nk ^ (-a) ≤ p.κ⁻¹
    rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ (by linarith [p.κ_one]) hκa
  have hGood : ∀ γ, ∀ z ∈ p.Good γ,
      gk γ L (obs (Bk γ) (δ Nk L) z) ≤ ENNReal.ofReal (Nk ^ (-f L + a)) := by
    intro γ z hz
    exact ((p.hGood γ).2.2 z hz).2.2.2.1 L hLmem
  have hbound := hp.beta_le νk (fun γ => gk γ L) (fun γ => (hmap γ).1)
    (fun γ => (hmap γ).2) (Real.rpow_nonneg hN0.le _) hGood
    (frameSlack_two p.κ_one) hb hb1 s U hU role hrole
  apply hbound.trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hR₁ : 0 ≤ p.R₁ := (p.hR₂pos.trans_le p.hR21).le
  have hR₂ : 0 ≤ p.R₂ := p.hR₂pos.le
  have hd : |(p.toPrep.fQ (p.toPrep.frame s)).det| ≤
      p.toPrep.Afr ^ 2 * ((2 : ℝ) ^ p.s) ^ 2 * (8 * Nk ^ (a + e)) * (p.R₁ * p.R₂) :=
    (p.determinant_le hN hB ha.le _).trans (by gcongr)
  have hc := frame_density_coefficient_le hX hκ0 hκleX hK0 hκX
    (by positivity : (0 : ℝ) ≤ 2 ^ p.s) hq ((by norm_num : (0 : ℝ) ≤ 1).trans hp.Afr_one)
    hp.Afr_le hp.R₁pos.le p.hR₂pos.le (Real.rpow_nonneg hN0.le (-f L))
    (Real.rpow_nonneg hN0.le a) hNa hb hbi (abs_nonneg _) hd
  change Nk ^ (-f L + a) * _ * _ ≤ p.sigma * Nk ^ (100 * (a + e))
  rw [Real.rpow_add hN0]
  have hpower : (Nk ^ (a + e)) ^ 100 = Nk ^ (100 * (a + e)) := by
    rw [← Real.rpow_mul_natCast hN0.le]
    congr 1
    ring
  rw [hpower] at hc
  exact hc

/-- True native floors control the number of entries at the same sigma. -/
theorem entry_count_le [hν : ∀ γ, IsProbabilityMeasure (νk γ)]
    (hN : 2 ≤ Nk) (ha : 0 < a) (he : 0 < e) (hB : ∀ γ, 0 < Bk γ)
    (hκX : frameSlack p.κ ≤ Nk ^ (a + e))
    (hX : (2 : ℝ) ^ 100 ≤ Nk ^ (a + e))
    (γ₀ : Fin p.toPrep.W) (j₀ : Fin (2 ^ p.toPrep.T)) :
    ((Finset.univ.filter (fun s : Fin p.toPrep.m =>
      p.toPrep.fγ (p.toPrep.frame s) = γ₀ ∧ p.toPrep.fj (p.toPrep.frame s) = j₀)).card : ℝ) ≤
      Nk ^ (100 * (a + e)) / p.sigma := by
  let hp := p.toPrep_hyp hN hB
  letI : ∀ γ : Fin p.toPrep.W, IsProbabilityMeasure (νk γ) := fun γ => hν γ
  letI : ∀ γ : Fin p.toPrep.W, SFinite (νk γ) := fun γ => by
    letI : IsProbabilityMeasure (νk γ) := hν γ
    infer_instance
  have hN0 : 0 < Nk := by linarith
  have hN1 : 1 ≤ Nk := by linarith
  have hfloor b : ENNReal.ofReal (Nk ^ (-f L) * |(p.Q b).det| /
      ((2 : ℝ) ^ (p.T + p.s) * p.κ)) ≤ ((νk (p.γ b)).prod volume) (p.F b) := by
    rcases p.hchart b with ⟨_, _, _, _, _, _, _, _, _, _, _, hex⟩
    exact hex.1
  have hc := hp.count_le νk hfloor γ₀ j₀
  apply (le_div_iff₀ (p.sigma_pos hN)).mpr
  apply (mul_le_mul_of_nonneg_right hc (p.sigma_pos hN).le).trans
  have hmult : p.κ * (98 * (2 * (p.toPrep.Kb : ℝ) + 1) ^ 4 + 1) ≤ frameSlack p.κ := by
    have hm := frameSlack_lists p.κ_one
    push_cast at hm
    exact hm
  have hcancel : ((2 : ℝ) ^ p.s * (p.κ * Nk ^ f L / (p.R₁ * p.R₂)) *
      (98 * (2 * (p.toPrep.Kb : ℝ) + 1) ^ 4 + 1)) * p.sigma =
      (2 : ℝ) ^ p.s * (p.κ * (98 * (2 * (p.toPrep.Kb : ℝ) + 1) ^ 4 + 1)) := by
    unfold sigma
    rw [Real.rpow_neg hN0.le]
    have hR₁ : p.R₁ ≠ 0 := (p.hR₂pos.trans_le p.hR21).ne'
    have hR₂ : p.R₂ ≠ 0 := p.hR₂pos.ne'
    have hf : Nk ^ f L ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    field_simp [hR₁, hR₂, hf]
  change ((2 : ℝ) ^ p.s * (p.κ * Nk ^ f L / (p.R₁ * p.R₂)) *
    (98 * (2 * (p.toPrep.Kb : ℝ) + 1) ^ 4 + 1)) * p.sigma ≤ Nk ^ (100 * (a + e))
  rw [hcancel]
  have hq : (2 : ℝ) ^ p.s ≤ 2 * Nk ^ (a + e) :=
    p.hgainhi.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num))
  have hX2 : 2 ≤ Nk ^ (a + e) := by norm_num at hX; linarith
  calc
    (2 : ℝ) ^ p.s * (p.κ * (98 * (2 * (p.toPrep.Kb : ℝ) + 1) ^ 4 + 1)) ≤
        (2 : ℝ) ^ p.s * frameSlack p.κ := mul_le_mul_of_nonneg_left hmult (by positivity)
    _ ≤ (Nk ^ (a + e)) ^ 3 := frame_count_coefficient_le hX2 (by positivity) hq
      (zero_le_one.trans (frameSlack_one p.κ_one)) hκX
    _ ≤ (Nk ^ (a + e)) ^ 100 := pow_le_pow_right₀ (by linarith) (by omega)
    _ = Nk ^ (100 * (a + e)) := by
      rw [← Real.rpow_mul_natCast hN0.le]
      congr 1
      ring

end NativeSample
end Submission.Obl.k4_compatible_pair_frame_preparation
