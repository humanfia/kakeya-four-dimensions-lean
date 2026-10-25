/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/SteepPacketMass.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.FieldFreezing
import Submission.Obl.k4_scalar_grid_parameter_preparation.PhysicalSupportCover

/-! Original steep-gradient packet mass, summed over its actual fine rectangular cells. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory MvPolynomial
open scoped Classical BigOperators ENNReal

theorem steep_quadratic_packet_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (f : Ω → Fin 3 → ℝ) (V : Ω → ℝ)
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2) (π : Measure ℝ)
    (δ ξ h A K D M β U W B R t₀ y₀ : ℝ)
    (hδ : 0 < δ) (hξ : 0 < ξ) (hδh : δ ≤ h) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hU : 0 ≤ U) (hW : 0 ≤ W) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hM : 0 < M) (hβ : 0 < β) (hforecast : D + 1 + K ≤ M * β)
    (hcoeff : ∀ b, |F.coeff b| ≤ B)
    (hfreeze : 162 * B * R ^ 4 * δ ≤ 1) (hvalue : 162 * B * R ^ 4 * δ ≤ ξ)
    (htime : ∀ p ∈ E, f p 0 ∈ Set.Icc t₀ (t₀ + h))
    (hY : ∀ p ∈ E, |f p 1 - y₀| ≤ A * h)
    (hbox : ∀ p ∈ E, ∀ i : Fin 2, |(![f p 0,f p 1] : Fin 2 → ℝ) i| ≤ R)
    (hfit : ∀ p ∈ E, |f p 2 - eval ![f p 0,f p 1] F| ≤ K * ξ)
    (hV : ∀ p ∈ E, |V p| ≤ K)
    (hdir : ∀ p ∈ E, |eval ![f p 0,f p 1] (pderiv 0 F) +
      eval ![f p 0,f p 1] (pderiv 1 F) * V p| ≤ D)
    (hsteep : ∀ p ∈ E, M ≤ |eval ![f p 0,f p 1] (pderiv 1 F)|)
    (P : ℝ≥0∞)
    (hjoint : ∀ i j a c : ℤ, μ {p | (⌊f p 0 / δ⌋ : ℤ) = i ∧
      (⌊f p 1 / δ⌋ : ℤ) = j ∧ (⌊f p 2 / ξ⌋ : ℤ) = a ∧
      V p ∈ scalarVelocityBin β c} ≤ ENNReal.ofReal (U * δ ^ 2 * W) * π (scalarVelocityBin β c))
    (hangular : ∀ c : ℤ, π (scalarVelocityBin β c) ≤ P) :
    μ E ≤ ENNReal.ofReal (1600 * (4 * A + 2) * (4 * K + 4) * U * h ^ 2 * W) * P := by
  let z : (Fin 3 → ℝ) → Fin 2 → ℝ := fun p => ![p 0,p 1]
  have hdist (p p' : Fin 3 → ℝ)
      (ht : (⌊p 0 / δ⌋ : ℤ) = ⌊p' 0 / δ⌋)
      (hy : (⌊p 1 / δ⌋ : ℤ) = ⌊p' 1 / δ⌋) : dist (z p) (z p') ≤ δ := by
    apply (dist_pi_le_iff hδ.le).mpr
    intro i
    fin_cases i
    · exact scalarVelocityBin_diameter_le hδ (q := ⌊p 0 / δ⌋) rfl ht.symm
    · exact scalarVelocityBin_diameter_le hδ (q := ⌊p 1 / δ⌋) rfl hy.symm
  have hosc : ∀ p ∈ E, ∀ p' ∈ E,
      (⌊f p 0 / δ⌋ : ℤ) = ⌊f p' 0 / δ⌋ → (⌊f p 1 / δ⌋ : ℤ) = ⌊f p' 1 / δ⌋ →
        dist (f p 2) (f p' 2) ≤ (2 * K + 1) * ξ := by
    intro p hp p' hp' ht hy
    have hb := binary_polynomial_lipschitz F 2 hF hB hR hcoeff
      (z (f p)) (z (f p')) (hbox p hp) (hbox p' hp')
    norm_num at hb
    have hf : |eval (z (f p)) F - eval (z (f p')) F| ≤ ξ := by
      calc
        _ ≤ 54 * B * R ^ 4 * dist (z (f p)) (z (f p')) := hb
        _ ≤ 54 * B * R ^ 4 * δ := mul_le_mul_of_nonneg_left (hdist _ _ ht hy) (by positivity)
        _ ≤ 162 * B * R ^ 4 * δ := by gcongr <;> norm_num
        _ ≤ ξ := hvalue
    rw [Real.dist_eq]
    calc
      _ ≤ |f p 2 - eval (z (f p)) F| +
          (|eval (z (f p)) F - eval (z (f p')) F| + |eval (z (f p')) F - f p' 2|) :=
        (abs_sub_le _ _ _).trans (add_le_add le_rfl (abs_sub_le _ _ _))
      _ ≤ K * ξ + (ξ + K * ξ) := add_le_add (hfit p hp)
        (add_le_add hf (by simpa only [abs_sub_comm] using hfit p' hp'))
      _ = _ := by ring
  obtain ⟨hcfinite, hccount⟩ := physical_rectangular_grid_cover_of_base_fibers (f '' E)
    δ ξ h A (2 * K + 1) t₀ y₀ hδ hξ hδh hA (by positivity)
    (by rintro _ ⟨p, hp, rfl⟩; exact htime p hp)
    (by rintro _ ⟨p, hp, rfl⟩; exact hY p hp)
    (by rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩ ht hy; exact hosc p hp p' hp' ht hy)
  let Q := hcfinite.toFinset
  have hQ : (Q.card : ℝ) ≤ 4 * (4 * A + 2) * (4 * K + 4) * (h / δ) ^ 2 := by
    rw [← Set.ncard_eq_toFinset_card _ hcfinite]
    exact hccount.trans_eq (by ring)
  let C : (Fin 3 → ℤ) → Set Ω := fun q =>
    {p | p ∈ E ∧ physicalScalarRectangularTag δ ξ (f p) = q}
  have hvar (q : Fin 3 → ℤ) (p : Ω) (hp : p ∈ C q) (p' : Ω) (hp' : p' ∈ C q) :
      ∀ e, |eval (z (f p)) (pderiv e F) - eval (z (f p')) (pderiv e F)| ≤ 1 := by
    apply binary_gradient_freezing_on_grid F hF B R δ hB hR hδ hcoeff hfreeze
      (z (f p)) (z (f p')) (hbox p hp.1) (hbox p' hp'.1)
    have he := hp.2.trans hp'.2.symm
    ext i
    fin_cases i
    · exact congrFun he 0
    · exact congrFun he 1
  have hcell (q : Fin 3 → ℤ) : μ (C q) ≤ 400 * (ENNReal.ofReal (U * δ ^ 2 * W) * P) := by
    apply steep_field_original_mass_le μ (C q)
      (fun p => eval (z (f p)) (pderiv 0 F)) (fun p => eval (z (f p)) (pderiv 1 F)) V π
      D K M β hK hM hβ hforecast
      (fun p hp => hV p hp.1) (fun p hp => hdir p hp.1) (fun p hp => hsteep p hp.1)
      (fun p hp p' hp' => hvar q p hp p' hp' 0)
      (fun p hp p' hp' => hvar q p hp p' hp' 1)
      (ENNReal.ofReal (U * δ ^ 2 * W)) P
    · intro c
      have hs : {p | p ∈ C q ∧ V p ∈ scalarVelocityBin β c} ⊆
          {p | (⌊f p 0 / δ⌋ : ℤ) = q 0 ∧ (⌊f p 1 / δ⌋ : ℤ) = q 1 ∧
            (⌊f p 2 / ξ⌋ : ℤ) = q 2 ∧ V p ∈ scalarVelocityBin β c} := by
        intro p hp
        exact ⟨congrFun hp.1.2 0, congrFun hp.1.2 1, congrFun hp.1.2 2, hp.2⟩
      exact (measure_mono hs).trans (hjoint (q 0) (q 1) (q 2) c)
    · exact hangular
  have hcover : E ⊆ ⋃ q ∈ Q, C q := by
    intro p hp
    exact Set.mem_iUnion₂.mpr ⟨physicalScalarRectangularTag δ ξ (f p),
      hcfinite.mem_toFinset.mpr ⟨f p, ⟨p, hp, rfl⟩, rfl⟩, hp, rfl⟩
  have hmass : μ E ≤ (Q.card : ℝ≥0∞) * (400 * (ENNReal.ofReal (U * δ ^ 2 * W) * P)) := by
    calc
      _ ≤ μ (⋃ q ∈ Q, C q) := measure_mono hcover
      _ ≤ ∑ q ∈ Q, μ (C q) := measure_biUnion_finset_le _ _
      _ ≤ ∑ q ∈ Q, 400 * (ENNReal.ofReal (U * δ ^ 2 * W) * P) :=
        Finset.sum_le_sum fun q hq => hcell q
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hnum : (Q.card : ℝ) * 400 * (U * δ ^ 2 * W) ≤
      1600 * (4 * A + 2) * (4 * K + 4) * U * h ^ 2 * W := by
    calc
      _ ≤ (4 * (4 * A + 2) * (4 * K + 4) * (h / δ) ^ 2) * 400 * (U * δ ^ 2 * W) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ (by norm_num)) (by positivity)
      _ = _ := by field_simp; ring
  have heq : (Q.card : ℝ≥0∞) * (400 * (ENNReal.ofReal (U * δ ^ 2 * W) * P)) =
      ENNReal.ofReal ((Q.card : ℝ) * 400 * (U * δ ^ 2 * W)) * P := by
    simp [ENNReal.ofReal_mul, mul_assoc]
  rw [heq] at hmass
  exact hmass.trans (mul_le_mul (ENNReal.ofReal_le_ofReal hnum) le_rfl bot_le bot_le)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
