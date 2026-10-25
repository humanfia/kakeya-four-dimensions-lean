/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/FiniteStagePhysicalCore.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarScaleMass
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarScaleSupport
import Submission.Obl.k4_scalar_grid_parameter_preparation.PhysicalPreparationNumerics
import Submission.Obl.k4_scalar_grid_parameter_preparation.CommonScaleMasks

/-! One original-law physical core on a complete finite exponent grid. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped Classical BigOperators ENNReal

theorem exists_finite_stage_physical_core {X : Type*} [MeasurableSpace X] :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
    ∀ (G : Type*) [DecidableEq G] (N K d S : ℝ) (J : ℕ) (a : X → Fin 5 → ℝ),
      Measurable a → ∀ (ν : G → Measure X) (ρ : G → Measure (X × ℝ)) (π : G → Measure ℝ)
      (E₀ : G → Set (X × ℝ)),
      2 ≤ N → 1 ≤ K → 2 ≤ J → 0 < S →
      (∀ g, IsProbabilityMeasure (ν g) ∧ MeasurableSet (E₀ g) ∧
        ∀ p ∈ E₀ g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a p.1 e| ≤ K) →
      49766400 * K ^ 13 ≤ N ^ (1 / (J : ℝ) ^ 2) →
      12800000 * (J : ℝ) ^ 3 * K ^ 6 ≤ N ^ (S / J) →
      (∀ g c, π g (scalarVelocityBin (N ^ (-(1 / (J : ℝ)))) c) ≤
        ENNReal.ofReal (K * N ^ (-(S / J)))) →
      (∀ g, ∀ r ∈ positiveScaleGrid (J ^ 2) J, ∀ i j b c : ℤ,
        ρ g {p | (⌊p.2 / N ^ (-(10 * r))⌋ : ℤ) = i ∧
          (⌊scalarY (a p.1) p.2 / N ^ (-(10 * r))⌋ : ℤ) = j ∧
          (⌊scalarX (a p.1) p.2 / N ^ (-r)⌋ : ℤ) = b ∧
          a p.1 1 ∈ scalarVelocityBin (N ^ (-(1 / (J : ℝ)))) c} ≤
            ENNReal.ofReal (K * (N ^ (-(10 * r))) ^ 2 * N ^ (-d * r)) *
              π g (scalarVelocityBin (N ^ (-(1 / (J : ℝ)))) c)) →
      (∀ r ∈ positiveScaleGrid (J ^ 2) J, ∃ (n q : ℕ)
        (D : ScalarScalePackets X G a K (N ^ (-r)) n q),
        0 < q ∧ (q : ℝ) ≤ K * N ^ r ∧
        (∀ i, ENNReal.ofReal (N ^ (-d * r) / (K * (q : ℝ))) ≤ ν (D.world i) (D.labels i)) ∧
        ∀ g, ρ g (scalarScaleCovered D g)ᶜ = 0) →
      ∃ E : G → Set (X × ℝ),
        (∀ g, MeasurableSet (E g) ∧ E g ⊆ E₀ g ∧
          ρ g (E₀ g \ E g) ≤ ENNReal.ofReal (1 / (100 * K))) ∧
        ∀ g, ∀ r ∈ positiveScaleGrid (J ^ 2) J,
          (physicalScalarGridTag (N ^ (-r)) '' (scalarPacketPosition a '' E g)).Finite ∧
          ((physicalScalarGridTag (N ^ (-r)) '' (scalarPacketPosition a '' E g)).ncard : ℝ) ≤
            (A₀ * K ^ 7 * N ^ (1 / (J : ℝ))) * N ^ ((2 + d) * r) := by
  obtain ⟨Cm, hCm, hmass⟩ := exists_scalar_scale_core_mass_bound (X := X)
  obtain ⟨Cs, hCs, hsupport⟩ := exists_scalar_scale_core_support_bound (X := X)
  let A₀ := 720 * (Cm + Cs + 10)
  refine ⟨A₀, by dsimp [A₀]; linarith, ?_⟩
  intro G _ N K d S J a ha ν ρ π E₀ hN hK hJ hS hbase hFine hLoss hAngular hJoint hPackets
  have hNpos : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hN₀ : 0 ≤ N := by linarith
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hJpos : 0 < J := by omega
  have hJRpos : (0 : ℝ) < J := by exact_mod_cast hJpos
  let Γ := positiveScaleGrid (J ^ 2) J
  have hrange (r : Γ) : 1 / (J : ℝ) ^ 2 ≤ (r : ℝ) ∧ (r : ℝ) ≤ J := by
    have h := positiveScaleGrid_mem_bounds (pow_pos hJpos 2) r.property
    simpa only [Nat.cast_pow] using And.intro h.1 h.2.1
  have hrpos (r : Γ) : 0 < (r : ℝ) :=
    (by positivity : 0 < 1 / (J : ℝ) ^ 2).trans_le (hrange r).1
  have hdata (r : Γ) := hPackets r.val r.property
  choose n q D hq hqcap hfloor hcovered using hdata
  let β := N ^ (-(1 / (J : ℝ)))
  let M := (max Cm Cs * K ^ 2 + 1 + K) / β
  let H := A₀ * K ^ 7 * N ^ (1 / (J : ℝ))
  let P := ENNReal.ofReal (K * N ^ (-(S / J)))
  let ε := ENNReal.ofReal (1600 * (8 * K + 2) * (4 * K + 4) * K * K) * P
  have hβ : 0 < β := Real.rpow_pos_of_pos hNpos _
  have hβ₁ : β ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN₁
    (neg_nonpos.mpr (one_div_pos.mpr hJRpos).le)
  have hβinv : β⁻¹ = N ^ (1 / (J : ℝ)) := by dsimp [β]; rw [Real.rpow_neg hN₀, inv_inv]
  have hM : 0 < M := by dsimp [M]; positivity
  have hforecast : Cm * K ^ 2 + 1 + K ≤ M * β := by
    dsimp [M]
    rw [div_mul_cancel₀ _ hβ.ne']
    gcongr
    exact le_max_left _ _
  have hrate (r : Γ) : N ^ (-(r : ℝ)) ≤ K * (q r : ℝ)⁻¹ := by
    have hqr : (0 : ℝ) < q r := by exact_mod_cast hq r
    have hp : N ^ (-(r : ℝ)) * (q r : ℝ) ≤ K := by
      calc
        _ ≤ N ^ (-(r : ℝ)) * (K * N ^ (r : ℝ)) :=
          mul_le_mul_of_nonneg_left (hqcap r) (Real.rpow_nonneg hN₀ _)
        _ = K := by rw [mul_left_comm, ← Real.rpow_add hNpos]; simp
    simpa only [div_eq_mul_inv] using (le_div_iff₀ hqr).mpr hp
  have hfine (r : Γ) := scalar_fine_power_mesh_budget N K (q r : ℝ) r.val hN₁ hK
    (by exact_mod_cast hq r) (hrpos r) (hqcap r)
    (hFine.trans (Real.rpow_le_rpow_of_exponent_le hN₁ (hrange r).1))
  have hxi₁ (r : Γ) : N ^ (-(r : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN₁ (by linarith [hrpos r])
  have hmassOne (g : G) (r : Γ) :
      ρ g (E₀ g \ scalarScaleCore (D r) (E₀ g) M g) ≤ ε := by
    exact hmass G K (N ^ (-(r : ℝ))) (n r) (q r) a (D r) (ν g) (hbase g).1
      (ρ g) (E₀ g) g (π g) (N ^ (-(10 * (r : ℝ)))) β M K (N ^ (-d * (r : ℝ))) P
      hK (Real.rpow_pos_of_pos hNpos _) (hq r) (Real.rpow_pos_of_pos hNpos _)
      (hfine r).1 (hrate r) hM hβ hK₀ (Real.rpow_pos_of_pos hNpos _) hforecast
      ((hfine r).2.trans (hxi₁ r)) (hfine r).2 (hbase g).2.2
      (fun i hi => by simpa only [hi] using hfloor r i) (hcovered r g)
      (hJoint g r.val r.property) (hAngular g)
  have hcountOne (g : G) (r : Γ) :
      (physicalScalarGridTag (N ^ (-(r : ℝ))) ''
        (scalarPacketPosition a '' scalarScaleCore (D r) (E₀ g) M g)).Finite ∧
      ((physicalScalarGridTag (N ^ (-(r : ℝ))) ''
        (scalarPacketPosition a '' scalarScaleCore (D r) (E₀ g) M g)).ncard : ℝ) ≤
          H * N ^ ((2 + d) * (r : ℝ)) := by
    have hc := hsupport G K (N ^ (-(r : ℝ))) (n r) (q r) a (D r) (ν g) (hbase g).1
      (E₀ g) g M (N ^ (-d * (r : ℝ))) hK (Real.rpow_pos_of_pos hNpos _) (hq r)
      (hrate r) hM.le (Real.rpow_pos_of_pos hNpos _) (hbase g).2.2
      (fun i hi => by simpa only [hi] using hfloor r i)
    have hcost := scalar_scale_support_cost_le K Cm Cs β hK hCm hCs hβ hβ₁
    have hcost' : 4 * K ^ 3 * (8 * K + 2) * (4 * (Cs * K ^ 2 + (K + 1) * M + K) + 2) ≤ H := by
      apply hcost.trans_eq
      dsimp [H, A₀]
      rw [div_eq_mul_inv, hβinv]
    have hden : N ^ (-d * (r : ℝ)) * (N ^ (-(r : ℝ))) ^ 2 = N ^ (-((2 + d) * (r : ℝ))) := by
      rw [← Real.rpow_natCast (N ^ (-(r : ℝ))) 2, ← Real.rpow_mul hN₀, ← Real.rpow_add hNpos]
      congr 1
      norm_num
      ring
    refine ⟨hc.1, hc.2.trans ?_⟩
    apply (div_le_div_of_nonneg_right hcost' (by positivity : 0 ≤ N ^ (-d * (r : ℝ)) * (N ^ (-(r : ℝ))) ^ 2)).trans_eq
    rw [hden, div_eq_mul_inv, Real.rpow_neg hN₀, inv_inv]
  have hε : ε = ENNReal.ofReal ((1600 * (8 * K + 2) * (4 * K + 4) * K ^ 3) / N ^ (S / J)) := by
    dsimp [ε, P]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1600 * (8 * K + 2) * (4 * K + 4) * K * K),
      Real.rpow_neg hN₀, div_eq_mul_inv]
    congr 1
    ring
  have hsum : (∑ _r : Γ, ε) ≤ ENNReal.ofReal (1 / (100 * K)) := by
    have hcard : (Γ.card : ℝ) ≤ (J : ℝ) ^ 3 := by exact_mod_cast scalarStageGrid_card_le J
    have heq : (∑ _r : Γ, ε) = ENNReal.ofReal
        ((Γ.card : ℝ) * (1600 * (8 * K + 2) * (4 * K + 4) * K ^ 3) / N ^ (S / J)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe, hε]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg Γ.card)]
      congr 1
      ring
    rw [heq]
    apply ENNReal.ofReal_le_ofReal
    apply le_trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard (by positivity)) (Real.rpow_nonneg hN₀ _))
    exact scalar_finite_grid_exception_budget K (J : ℝ) (N ^ (S / J)) hK
      (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hNpos _) hLoss
  choose E hEm hEsub hEcore hEloss using fun g =>
    exists_common_finite_core (ρ g) (E₀ g) (hbase g).2.1
      (fun r : Γ => scalarScaleCore (D r) (E₀ g) M g)
      (fun r => measurableSet_scalarScaleCore ha (D r) (hbase g).2.1 M g)
      (fun _ => ε) (hmassOne g)
  refine ⟨E, fun g => ⟨hEm g, hEsub g, (hEloss g).trans hsum⟩, ?_⟩
  intro g r hr
  let s : Γ := ⟨r,hr⟩
  have hs : physicalScalarGridTag (N ^ (-r)) '' (scalarPacketPosition a '' E g) ⊆
      physicalScalarGridTag (N ^ (-r)) '' (scalarPacketPosition a '' scalarScaleCore (D s) (E₀ g) M g) :=
    Set.image_mono (Set.image_mono (hEcore g s))
  exact ⟨(hcountOne g s).1.subset hs,
    (Nat.cast_le.mpr (Set.ncard_le_ncard hs (hcountOne g s).1)).trans (hcountOne g s).2⟩

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
