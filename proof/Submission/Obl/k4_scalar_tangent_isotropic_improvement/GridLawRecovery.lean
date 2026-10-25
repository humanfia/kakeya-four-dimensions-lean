import Submission.Obl.k4_scalar_tangent_isotropic_improvement.IncidenceRecovery
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridPartition

/-! Recovery directly from an original measure and its conditional grid ceilings. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open Set MeasureTheory
open Submission.Obl.k4_matching_endpoint_volume (gridTag)
open scoped BigOperators Classical

attribute [-instance] Nat.decidableForallFin Fintype.decidableForallFintype

/-- No finite state or palette choices are needed in the hypotheses: they are
extracted from the original bounded law, on a full-measure core. In particular,
every conditional ceiling retains its original grid-cell denominator. -/
theorem quadratic_recovery_from_grid_law (D : ℕ) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
      (π : Measure ℝ) [IsProbabilityMeasure π] (n : ℕ)
      (f : Ω → Fin n → ℝ) (z : Ω → Fin 2 → ℝ) (V : Ω → ℝ)
      (p : MvPolynomial (Fin 2) ℝ) (o : Fin 2 → ℝ)
      (ξ ξᵥ δ H K F M η E r B : ℝ),
      Measurable f → p.totalDegree ≤ D → (∀ a, |p.coeff a| ≤ H) →
      0 < ξ → 0 < ξᵥ → ξᵥ ≤ H / 2 → 0 < δ → ξᵥ ≤ δ →
      1 ≤ H → H ≤ K → K⁻¹ ≤ δ → 0 < F → 0 ≤ M →
      0 < η → η ≤ 1 → 0 ≤ E → 0 ≤ r → 0 < μ Set.univ →
      (∀ᵐ ω ∂μ, (|V ω| ≤ H / 2 ∧ |cubicTest p (z ω) (V ω)| ≤ E ∧
        baseGridCell o ξ (baseGridTag o ξ (z ω)) ⊆ Set.Icc (0 : Fin 2 → ℝ) 1) ∧
        ∀ i, |f ω i| ≤ B) →
      (∀ ω ω', gridTag ξᵥ (f ω) = gridTag ξᵥ (f ω') → dist (z ω) (z ω') ≤ r) →
      (∀ (q : Fin n → ℤ) (b : ℤ),
        μ {ω | gridTag ξᵥ (f ω) = q ∧ V ω ∈ scalarVelocityBin ξᵥ b} ≤
          ENNReal.ofReal H * μ {ω | gridTag ξᵥ (f ω) = q} * π (scalarVelocityBin ξᵥ b)) →
      (∀ b : ℤ, π (scalarVelocityBin δ b) ≤ ENNReal.ofReal M) →
      5 * M ≤ H⁻¹ / 8 →
      (∀ q : Fin 2 → ℤ, μ {ω | baseGridTag o ξ (z ω) = q} ≤
        ENNReal.ofReal F * ENNReal.ofReal (ξ ^ 2)) →
      F * η ≤ (H⁻¹ / 2) ^ 4 * (μ Set.univ).toReal →
      ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ a, |Q.coeff a| ≤ |p.coeff a|) ∧
        ∀ x ∈ Set.Icc (0 : Fin 2 → ℝ) 1,
          |MvPolynomial.eval x p - MvPolynomial.eval x Q| ≤
            C₀ * K ^ 18 * (16 * ((D : ℝ) + 1) / η) ^ (2 * D) *
              (E + C₁ * H ^ (2 * D + 4) * (ξ + r + ξᵥ)) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hcore⟩ := quadratic_recovery_of_incidence_cells D
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro Ω instΩ μ instμ π instπ n f z V p o ξ ξᵥ δ H K F M η E r B
    hf hp hcoeff hξ hξᵥ hξH hδ hξδ hH hHK hsep hF hM hη hη1 hE hr hμ
    hpoint hdiam hcond hcoarse hsmall hgrid hmass
  obtain ⟨G, S, hG, hGfull, hgood, hpres, hCells, hdisj, hpos, hsum, hdist⟩ :=
    exists_positive_grid_partition μ
      (fun ω => |V ω| ≤ H / 2 ∧ |cubicTest p (z ω) (V ω)| ≤ E ∧
        baseGridCell o ξ (baseGridTag o ξ (z ω)) ⊆ Set.Icc (0 : Fin 2 → ℝ) 1)
      f hf hξᵥ hpoint
  let Cells : (Fin n → ℤ) → Set Ω := fun q => G ∩ {ω | gridTag ξᵥ (f ω) = q}
  let m : (Fin n → ℤ) → ℝ := fun q => (μ (Cells q)).toReal
  let J : Finset ℤ := Finset.Icc ⌊(-H / 2) / ξᵥ⌋ ⌊(H / 2) / ξᵥ⌋
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hcenter (b : ↥J) : |ξᵥ * (b.val : ℝ)| ≤ H := by
    have hb := Finset.mem_Icc.mp b.property
    have hlo : ((⌊(-H / 2) / ξᵥ⌋ : ℤ) : ℝ) ≤ b.val := by exact_mod_cast hb.1
    have hhi : (b.val : ℝ) ≤ ((⌊(H / 2) / ξᵥ⌋ : ℤ) : ℝ) := by exact_mod_cast hb.2
    have hfloorlo := Int.lt_floor_add_one ((-H / 2) / ξᵥ)
    have hfloorhi := Int.floor_le ((H / 2) / ξᵥ)
    have hlo' : -H / 2 < (((⌊(-H / 2) / ξᵥ⌋ : ℤ) : ℝ) + 1) * ξᵥ :=
      (div_lt_iff₀ hξᵥ).mp hfloorlo
    have hhi' : (((⌊(H / 2) / ξᵥ⌋ : ℤ) : ℝ)) * ξᵥ ≤ H / 2 :=
      (le_div_iff₀ hξᵥ).mp hfloorhi
    have hblo := mul_le_mul_of_nonneg_right hlo hξᵥ.le
    have hbhi := mul_le_mul_of_nonneg_right hhi hξᵥ.le
    apply abs_le.mpr
    constructor <;> nlinarith
  have hvelbin (ω : Ω) (hω : ω ∈ G) : (⌊V ω / ξᵥ⌋ : ℤ) ∈ J := by
    have hv := abs_le.mp (hgood ω hω).1.1
    exact Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right (by linarith only [hv.1] : -H / 2 ≤ V ω) hξᵥ.le),
        Int.floor_mono (div_le_div_of_nonneg_right hv.2 hξᵥ.le)⟩
  have hcover (q : Fin n → ℤ) :
      μ (Cells q) ≤ ∑ b : ↥J, μ (Cells q ∩ V ⁻¹' scalarVelocityBin ξᵥ b.val) := by
    apply (measure_mono ?_).trans (measure_iUnion_fintype_le μ _)
    intro ω hω
    exact Set.mem_iUnion.mpr
      ⟨⟨⌊V ω / ξᵥ⌋, hvelbin ω hω.1⟩, hω, rfl⟩
  have hcond' (q : Fin n → ℤ) (b : ↥J) :
      μ (Cells q ∩ V ⁻¹' scalarVelocityBin ξᵥ b.val) ≤
        ENNReal.ofReal H * μ (Cells q) * π (scalarVelocityBin ξᵥ b.val) := by
    have heq : Cells q ∩ V ⁻¹' scalarVelocityBin ξᵥ b.val =
        G ∩ {ω | gridTag ξᵥ (f ω) = q ∧ V ω ∈ scalarVelocityBin ξᵥ b.val} := by
      ext ω
      simp only [Cells, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      tauto
    rw [heq, hpres, show μ (Cells q) = μ {ω | gridTag ξᵥ (f ω) = q} from hpres _]
    exact hcond q b.val
  have hmasspos : 0 < (∑ q ∈ S, m q) := by
    rw [show (∑ q ∈ S, m q) = (μ Set.univ).toReal from hsum]
    exact ENNReal.toReal_pos (ne_of_gt hμ) (measure_ne_top μ _)
  refine hcore Ω (Fin n → ℤ) ↥J μ π z V Cells S m Subtype.val p o
    ξ ξᵥ δ H K F M η E r hp hcoeff hξ hξᵥ hδ hξδ hH hHK hsep hF hM hη hη1 hE hr
    Subtype.val_injective hcenter (fun q => ENNReal.toReal_nonneg) hmasspos
    hCells hdisj (fun q hq => ?_) hpos (fun q hq => hcover q)
    (fun q hq => hcond' q) hcoarse hsmall ?_ ?_ ?_ hgrid ?_
  · exact le_of_eq (ENNReal.ofReal_toReal (measure_ne_top μ _))
  · intro q hq ω hω
    have h := (hgood ω hω.1).1
    exact ⟨h.1.trans (by linarith), h.2.1⟩
  · intro q hq ω hω ω' hω'
    exact hdiam ω ω' (hω.2.trans hω'.2.symm)
  · intro q hq ω hω
    exact (hgood ω hω.1).1.2.2
  · simpa only [show (∑ q ∈ S, m q) = (μ Set.univ).toReal from hsum] using hmass

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
