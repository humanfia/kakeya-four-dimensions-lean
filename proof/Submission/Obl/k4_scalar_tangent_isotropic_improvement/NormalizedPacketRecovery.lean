import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridLawRecovery
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.PacketCoordinates

/-! A complete finite recovery step on the same original packet time block. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_matching_endpoint_volume (gridTag)
open scoped BigOperators Classical

def quadraticBase (a : Fin 5 → ℝ) (t : ℝ) : Fin 2 → ℝ := ![t, a 0 + t * a 1]

def quadraticHidden (a : Fin 5 → ℝ) (t : ℝ) : ℝ := a 2 + t * a 3 + t ^ 2 * a 4

def quadraticPhysical (a : Fin 5 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, a 0 + t * a 1, quadraticHidden a t]

/-- Finite normalized-packet recovery, with original-law conditional ceilings.
The recovered quadratic fits almost every original trajectory throughout the
entire original block. Its coefficient budget does not depend on the angular
separation used to recover it. -/
theorem quadratic_recovery_on_normalized_packet (D : ℕ) :
    ∃ C₀ C₁ Cₜ Cq Ca : ℝ,
      0 < C₀ ∧ 0 < C₁ ∧ 0 < Cₜ ∧ 0 < Cq ∧ 0 < Ca ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
      (π : Measure ℝ) [IsProbabilityMeasure π]
      (a : Ω → Fin 5 → ℝ) (t : Ω → ℝ)
      (p : MvPolynomial (Fin 2) ℝ) (z₀ : Fin 2 → ℝ)
      (H L h t₀ E ξ₀ ξᵥ δ K F M η : ℝ),
      Measurable a → Measurable t → p.totalDegree ≤ D → (∀ b, |p.coeff b| ≤ H) →
      1 ≤ H → 2 * H ≤ L → Ca * H * (4 * H) ^ (2 * D) ≤ L →
      0 < h → h ≤ 1 → 0 ≤ t₀ → t₀ + h ≤ 1 → z₀ 0 = t₀ →
      (∀ e, |z₀ e| ≤ H) → 0 ≤ E → 0 < ξ₀ → ξ₀ ≤ H →
      0 < ξᵥ → ξᵥ ≤ L / 2 → 0 < δ → ξᵥ ≤ δ →
      L ≤ K → K⁻¹ ≤ δ → 0 < F → 0 ≤ M → 0 < η → η ≤ 1 →
      0 < μ Set.univ →
      (∀ᵐ ω ∂μ, t ω ∈ Set.Icc t₀ (t₀ + h) ∧ (∀ e, |a ω e| ≤ H) ∧
        (∀ s ∈ Set.Icc t₀ (t₀ + h), ∀ e,
          |(quadraticBase (a ω) s e - z₀ e) / h| ≤ H) ∧
        ∀ s ∈ Set.Icc t₀ (t₀ + h),
          |quadraticHidden (a ω) s -
            eval (fun e => (quadraticBase (a ω) s e - z₀ e) / h) p| ≤ E) →
      (∀ (q : Fin 3 → ℤ) (b : ℤ),
        μ {ω | gridTag ξᵥ (quadraticPhysical (a ω) (t ω)) = q ∧
          a ω 1 ∈ scalarVelocityBin ξᵥ b} ≤
        ENNReal.ofReal L * μ {ω | gridTag ξᵥ (quadraticPhysical (a ω) (t ω)) = q} *
          π (scalarVelocityBin ξᵥ b)) →
      (∀ b : ℤ, π (scalarVelocityBin δ b) ≤ ENNReal.ofReal M) →
      5 * M ≤ L⁻¹ / 8 →
      (∀ q : Fin 2 → ℤ,
        μ {ω | baseGridTag 0 ξ₀
          (fun e => (quadraticBase (a ω) (t ω) e - z₀ e) / h) = q} ≤
        ENNReal.ofReal F * ENNReal.ofReal (ξ₀ ^ 2)) →
      (4 * H) ^ 2 * F * η ≤ (L⁻¹ / 2) ^ 4 * (μ Set.univ).toReal →
      ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ b, |Q.coeff b| ≤ Cq * L * (H / h) ^ 4) ∧
        ∀ᵐ ω ∂μ, ∀ s ∈ Set.Icc t₀ (t₀ + h),
          |quadraticHidden (a ω) s - eval (quadraticBase (a ω) s) Q| ≤
            E + C₀ * K ^ 18 * (16 * ((D : ℝ) + 1) / η) ^ (2 * D) *
              (Cₜ * H ^ 3 * E + C₁ * L ^ (2 * D + 4) *
                (ξ₀ / (4 * H) + ξᵥ / (4 * H * h) + ξᵥ)) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hcore⟩ := quadratic_recovery_from_grid_law D
  obtain ⟨Cₜ, hCₜ, htests⟩ := exists_unitbox_trajectory_cubicTest_bound D
  obtain ⟨Cq, hCq, hpull⟩ := exists_normalized_quadratic_pullback
  obtain ⟨Ca, hCa, hcoeffchange⟩ := exists_affine_substitution_coefficient_bound D
  refine ⟨C₀, C₁, Cₜ, Cq, Ca, hC₀, hC₁, hCₜ, hCq, hCa, ?_⟩
  intro Ω instΩ μ instμ π instπ a t p z₀ H L h t₀ E ξ₀ ξᵥ δ K F M η
    ha ht hp hcoeff hH hHL hcoeffL hh hh1 ht₀ ht₁ hz₀ hzbound hE hξ₀ hξH
    hξᵥ hξL hδ hξδ hLK hsep hF hM hη hη1 hμ hgood hcond hcoarse hsmall hgrid hmass
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hL : 1 ≤ L := by linarith
  let raw : Ω → Fin 2 → ℝ := fun ω e => (quadraticBase (a ω) (t ω) e - z₀ e) / h
  let z : Ω → Fin 2 → ℝ := fun ω => normalizeBase H (raw ω)
  let f : Ω → Fin 3 → ℝ := fun ω => quadraticPhysical (a ω) (t ω)
  let p' : MvPolynomial (Fin 2) ℝ := affineBaseHom (fun _ => -2 * H) (4 * H) p
  have h4H : 1 ≤ 4 * H := by linarith
  obtain ⟨hp', hc', heval'⟩ := hcoeffchange p (fun _ => -2 * H) (4 * H) H (4 * H)
    hp hHpos.le h4H hcoeff
    (fun _ => by rw [abs_of_nonpos (by linarith)]; linarith)
    (by rw [abs_of_pos (by positivity)])
  have hp'deg : p'.totalDegree ≤ D := hp'
  have hp'coeff (b) : |p'.coeff b| ≤ L := (hc' b).trans hcoeffL
  have hf : Measurable f := by
    dsimp [f, quadraticPhysical, quadraticHidden]
    fun_prop
  have hpoint : ∀ᵐ ω ∂μ,
      (|a ω 1| ≤ L / 2 ∧ |cubicTest p' (z ω) (a ω 1)| ≤ Cₜ * H ^ 3 * E ∧
        baseGridCell (fun _ => 1 / 2) (ξ₀ / (4 * H))
          (baseGridTag (fun _ => 1 / 2) (ξ₀ / (4 * H)) (z ω)) ⊆
            Set.Icc (0 : Fin 2 → ℝ) 1) ∧ ∀ e, |f ω e| ≤ 3 * H := by
    filter_upwards [hgood] with ω hω
    rcases hω with ⟨hblock, hac, hbox, hfit⟩
    have hraw : ∀ e, |raw ω e| ≤ H := hbox (t ω) hblock
    have hfit' : ∀ s ∈ Set.Icc t₀ (t₀ + h),
        |a ω 2 + s * a ω 3 + s ^ 2 * a ω 4 -
          eval ![(s - t₀) / h, (a ω 0 + s * a ω 1 - z₀ 1) / h] p| ≤ E := by
      intro s hs
      have hv : (fun e => (quadraticBase (a ω) s e - z₀ e) / h) =
          ![(s - t₀) / h, (a ω 0 + s * a ω 1 - z₀ 1) / h] := by
        ext e
        fin_cases e <;> simp [quadraticBase, hz₀]
      simpa only [quadraticHidden, hv] using hfit s hs
    have ht01 : 0 ≤ t ω ∧ t ω ≤ 1 := ⟨ht₀.trans hblock.1, hblock.2.trans ht₁⟩
    have htab : |t ω| ≤ 1 := by rw [abs_of_nonneg ht01.1]; exact ht01.2
    refine ⟨⟨(hac 1).trans (by linarith), ?_,
      normalized_baseGridCell_subset_unit hHpos hξ₀ hξH (raw ω) hraw⟩, ?_⟩
    · have hz : normalizeBase H ![(t ω - t₀) / h,
          (a ω 0 + t ω * a ω 1 - z₀ 1) / h] = z ω := by
        congr 1
        ext e
        fin_cases e <;> simp [raw, quadraticBase, hz₀]
      simpa only [hz, p'] using htests p (a ω) t₀ (z₀ 1) h H E
        hp hh hHpos hE hfit' (t ω) hblock
    · have hprod (e : Fin 5) : |t ω * a ω e| ≤ H := by
        rw [abs_mul]
        exact (mul_le_mul htab (hac e) (abs_nonneg _) zero_le_one).trans_eq (one_mul H)
      have hsq : |t ω ^ 2 * a ω 4| ≤ H := by
        rw [abs_mul, abs_pow]
        exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) htab) (hac 4)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul H)
      intro e
      fin_cases e
      · exact htab.trans (by linarith)
      · exact (abs_add_le _ _).trans ((add_le_add (hac 0) (hprod 1)).trans (by linarith))
      · exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
          ((add_le_add (add_le_add (hac 2) (hprod 3)) hsq).trans (by linarith))
  have hdiam (ω ω' : Ω) (heq : gridTag ξᵥ (f ω) = gridTag ξᵥ (f ω')) :
      dist (z ω) (z ω') ≤ ξᵥ / (4 * H * h) := by
    have hd := Submission.Obl.k4_matching_endpoint_volume.dist_le_mesh_of_gridTag_eq hξᵥ heq
    have hbase (e : Fin 2) : |quadraticBase (a ω) (t ω) e -
        quadraticBase (a ω') (t ω') e| ≤ ξᵥ := by
      fin_cases e
      · exact (dist_le_pi_dist (f ω) (f ω') 0).trans hd
      · exact (dist_le_pi_dist (f ω) (f ω') 1).trans hd
    apply (dist_pi_le_iff (by positivity : 0 ≤ ξᵥ / (4 * H * h))).mpr
    intro e
    rw [Real.dist_eq]
    have he : z ω e - z ω' e =
        (quadraticBase (a ω) (t ω) e - quadraticBase (a ω') (t ω') e) / (4 * H * h) := by
      dsimp [z, normalizeBase, raw]
      field_simp
      ring
    rw [he, abs_div, abs_of_pos (by positivity : 0 < 4 * H * h)]
    exact div_le_div_of_nonneg_right (hbase e) (by positivity)
  have hgrid' (q : Fin 2 → ℤ) :
      μ {ω | baseGridTag (fun _ => 1 / 2) (ξ₀ / (4 * H)) (z ω) = q} ≤
        ENNReal.ofReal ((4 * H) ^ 2 * F) * ENNReal.ofReal ((ξ₀ / (4 * H)) ^ 2) := by
    have heq : {ω | baseGridTag (fun _ => 1 / 2) (ξ₀ / (4 * H)) (z ω) = q} =
        {ω | baseGridTag 0 ξ₀ (raw ω) = q} := by
      ext ω
      change _ = q ↔ _ = q
      rw [show baseGridTag (fun _ => 1 / 2) (ξ₀ / (4 * H)) (z ω) =
          baseGridTag 0 ξ₀ (raw ω) from baseGridTag_normalizeBase hHpos.ne' hξ₀.ne' _]
    rw [heq]
    apply (hgrid q).trans_eq
    rw [← ENNReal.ofReal_mul hF.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  obtain ⟨q, hq, hqc, happrox⟩ := hcore Ω μ π 3 f z (fun ω => a ω 1) p'
    (fun _ => 1 / 2) (ξ₀ / (4 * H)) ξᵥ δ L K ((4 * H) ^ 2 * F) M η
    (Cₜ * H ^ 3 * E) (ξᵥ / (4 * H * h)) (3 * H)
    hf hp'deg hp'coeff (by positivity) hξᵥ hξL hδ hξδ hL hLK hsep (by positivity)
    hM hη hη1 (by positivity) (by positivity) hμ hpoint hdiam hcond hcoarse hsmall hgrid' hmass
  obtain ⟨Q, hQ, hQcoeff, hQeval⟩ := hpull q z₀ H h L hq hH hh hh1
    (zero_le_one.trans hL) (fun b => (hqc b).trans (hp'coeff b)) hzbound
  refine ⟨Q, hQ, hQcoeff, ?_⟩
  filter_upwards [hgood] with ω hω
  intro s hs
  let u : Fin 2 → ℝ := fun e => (quadraticBase (a ω) s e - z₀ e) / h
  have hu : ∀ e, |u e| ≤ H := hω.2.2.1 s hs
  have hunit : normalizeBase H u ∈ Set.Icc (0 : Fin 2 → ℝ) 1 := by
    constructor <;> intro e
    · exact (by norm_num : (0 : ℝ) ≤ 1 / 4).trans (normalizeBase_margin hHpos u hu e).1
    · exact (normalizeBase_margin hHpos u hu e).2.trans (by norm_num)
  have hcomp := happrox (normalizeBase H u) hunit
  have heval : eval (normalizeBase H u) p' = eval u p := by
    rw [eval_affineBaseHom, normalizeBase_inverse hHpos.ne']
  rw [heval] at hcomp
  rw [hQeval]
  exact (abs_sub_le (quadraticHidden (a ω) s) (eval u p)
    (eval (normalizeBase H u) q)).trans (add_le_add (hω.2.2.2 s hs) hcomp)

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
