/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/SequencePhysicalCore.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.FiniteStagePhysicalCore
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarPhysicalSequenceData
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth
import Submission.Obl.k4_tempered_grid_selection.SelectionMass

/-! A single subpower physical-support preparation on a slowly growing finite grid. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped Classical BigOperators ENNReal

theorem exists_scalar_physical_grid_preparation {X : Type*} [MeasurableSpace X]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (W : ℕ → ℕ) (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (ν : (k : ℕ) → Fin (W k) → Measure X)
    (ρ : (k : ℕ) → Fin (W k) → Measure (X × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ)
    (E₀ : (k : ℕ) → Fin (W k) → Set (X × ℝ)) (d S : ℝ) (hS : 0 < S)
    (hbase : ∀ k g, IsProbabilityMeasure (ν k g) ∧ MeasurableSet (E₀ k g) ∧
      ∀ p ∈ E₀ k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a p.1 e| ≤ K k)
    (hcaps : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ScalarOriginalCapsAt N K W ρ π a d S R k)
    (hpackets : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ScalarPacketSequenceAt N K W ν ρ a d R k) :
    ∃ (H : ℕ → ℝ) (M : ℕ → ℕ) (E : (k : ℕ) → Fin (W k) → Set (X × ℝ)),
      ((∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      (∀ k, 1 ≤ M k ∧ N k ^ (1 / (M k : ℝ)) ≤ H k) ∧
      (∀ k g, MeasurableSet (E k g) ∧ E k g ⊆ E₀ k g) ∧
      (∀ᶠ k in atTop, ∀ g, ρ k g (E₀ k g \ E k g) ≤ ENNReal.ofReal (1 / (100 * K k))) ∧
      (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ),
        R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) →
        (physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g)).Finite ∧
        ((physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g)).ncard : ℝ) ≤
          H k * N k ^ ((2 + d) * r)) ∧
      ∃ J : ℕ → ℕ, (∀ k, 2 ≤ J k ∧ M k = J k ^ 2) ∧ Tendsto J atTop atTop ∧
        ∀ᶠ k in atTop, (J k : ℝ) ^ 3 ≤ H k ∧
          ∀ g, ∀ r ∈ positiveScaleGrid (M k) (J k),
            (physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g)).Finite ∧
            ((physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g)).ncard : ℝ) ≤
              H k * N k ^ ((2 + d) * r) := by
  obtain ⟨A₀, hA₀, hstage⟩ := exists_finite_stage_physical_core (X := X)
  let stage : ℕ → ℕ := fun j => j + 2
  let Q : ℕ → ℕ → Prop := fun j k =>
    ScalarOriginalCapsAt N K W ρ π a d S (100 * (stage j : ℝ) ^ 2) k ∧
    ScalarPacketSequenceAt N K W ν ρ a d (100 * (stage j : ℝ) ^ 2) k ∧
    49766400 * K k ^ 13 ≤ N k ^ (1 / (stage j : ℝ) ^ 2) ∧
    12800000 * (stage j : ℝ) ^ 3 * K k ^ 6 ≤ N k ^ (S / stage j) ∧
    (stage j : ℝ) ^ 3 ≤ N k ^ (1 / (stage j : ℝ))
  have hN₁ (k) : 1 ≤ N k := by linarith [hN k]
  have hNpos (k) : 0 < N k := by linarith [hN k]
  have hQ (j : ℕ) : ∀ᶠ k in atTop, Q j k := by
    have hJ : (2 : ℝ) ≤ stage j := by dsimp [stage]; exact_mod_cast Nat.le_add_left 2 j
    have hJpos : (0 : ℝ) < stage j := by linarith
    have hR : 1 < 100 * (stage j : ℝ) ^ 2 := by nlinarith
    have hFine := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN₁ hNt hK.1 hK.2 13 (a := 0) (b := 1 / (stage j : ℝ) ^ 2)
      (by positivity) (A := 49766400) (by norm_num)
    have hLoss := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN₁ hNt hK.1 hK.2 6 (a := 0) (b := S / stage j)
      (by positivity) (A := 12800000 * (stage j : ℝ) ^ 3) (by positivity)
    have hCard := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN₁ hNt hK.1 hK.2 0 (a := 0) (b := 1 / (stage j : ℝ))
      (by positivity) (A := (stage j : ℝ) ^ 3) (by positivity)
    filter_upwards [hcaps _ hR, hpackets _ hR, hFine, hLoss, hCard] with k hc hp hf hl hj
    refine ⟨hc, hp, ?_, ?_, ?_⟩
    · simpa only [Real.rpow_zero, mul_one] using hf.le
    · simpa only [Real.rpow_zero, mul_one] using hl.le
    · simpa only [pow_zero, Real.rpow_zero, mul_one] using hj.le
  obtain ⟨m, hm, hmt, hmn, hdiag⟩ := Submission.Lib.K4ModelReduction.exists_slow_diagonal Q hQ
  let J : ℕ → ℕ := fun k => stage (m k)
  let M : ℕ → ℕ := fun k => J k ^ 2
  let Z : ℕ → ℝ := fun k => N k ^ (1 / (J k : ℝ))
  let H : ℕ → ℝ := fun k => A₀ * K k ^ 7 * Z k
  have hJ₂ (k) : 2 ≤ J k := by dsimp [J, stage]; omega
  have hJpos (k) : 0 < J k := by have h := hJ₂ k; omega
  have hJRpos (k) : (0 : ℝ) < J k := by exact_mod_cast hJpos k
  have hJt : Tendsto J atTop atTop := (tendsto_add_atTop_nat 2).comp hmt
  have hJRt : Tendsto (fun k => (J k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hJt
  have hZ₁ (k) : 1 ≤ Z k := Real.one_le_rpow (hN₁ k) (by positivity)
  have hZsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Z k ≤ N k ^ ε := by
    intro ε hε
    exact eventually_scale_rounding_loss_le N J hN₁ hJt hε
  have hpoly := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
    hN₁ hNt hK hA₀ 7
  have hH := Submission.Obl.k4_tempered_grid_selection.subpower_mul hNpos hpoly ⟨hZ₁,hZsub⟩
  have hZH (k) : Z k ≤ H k := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hpoly.1 k) (le_trans (by norm_num) (hZ₁ k))
  have hgood : ∀ᶠ k in atTop, Q (m k) k := hdiag.mono fun k hk => hk (m k) le_rfl
  have hexGood (k : ℕ) (hk : Q (m k) k) :
      ∃ E : Fin (W k) → Set (X × ℝ),
        (∀ g, MeasurableSet (E g) ∧ E g ⊆ E₀ k g ∧
          ρ k g (E₀ k g \ E g) ≤ ENNReal.ofReal (1 / (100 * K k))) ∧
        ∀ g, ∀ r ∈ positiveScaleGrid (J k ^ 2) (J k),
          (physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E g)).Finite ∧
          ((physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E g)).ncard : ℝ) ≤
            H k * N k ^ ((2 + d) * r) := by
    obtain ⟨hR, hb, hb', hrange⟩ := scalarStage_compact_bounds (hJ₂ k)
    have hc := hk.1
    have hp := hk.2.1
    change ScalarOriginalCapsAt N K W ρ π a d S (100 * (J k : ℝ) ^ 2) k at hc
    change ScalarPacketSequenceAt N K W ν ρ a d (100 * (J k : ℝ) ^ 2) k at hp
    apply hstage (Fin (W k)) (N k) (K k) d S (J k) a ha (ν k) (ρ k) (π k) (E₀ k)
      (hN k) (hK.1 k) (hJ₂ k) hS (hbase k) hk.2.2.1 hk.2.2.2.1
    · intro g c
      have h := (hc g (1 / (J k : ℝ)) (1 / (J k : ℝ)) (1 / (J k : ℝ))
        hb hb' hb hb' hb hb').1 c
      have he : -S * (1 / (J k : ℝ)) = -(S / J k) := by ring
      simpa only [he] using h
    · intro g r hr i j b c
      obtain ⟨hr₀,hr₁,h10₀,h10₁⟩ := hrange r hr
      have h := (hc g (10 * r) r (1 / (J k : ℝ)) h10₀ h10₁ hr₀ hr₁ hb hb').2 i j b c
      have he : N k ^ (-2 * (10 * r) - d * r) = (N k ^ (-(10 * r))) ^ 2 * N k ^ (-d * r) := by
        rw [← Real.rpow_natCast (N k ^ (-(10 * r))) 2, ← Real.rpow_mul (hNpos k).le,
          ← Real.rpow_add (hNpos k)]
        congr 1
        norm_num
        ring
      simpa only [he, mul_assoc] using h
    · intro r hr
      exact hp r (hrange r hr).1 (hrange r hr).2.1
  have hex (k : ℕ) : ∃ E : Fin (W k) → Set (X × ℝ),
      (∀ g, MeasurableSet (E g) ∧ E g ⊆ E₀ k g) ∧
      (Q (m k) k →
        (∀ g, ρ k g (E₀ k g \ E g) ≤ ENNReal.ofReal (1 / (100 * K k))) ∧
        ∀ g, ∀ r ∈ positiveScaleGrid (J k ^ 2) (J k),
          (physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E g)).Finite ∧
          ((physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E g)).ncard : ℝ) ≤
            H k * N k ^ ((2 + d) * r)) := by
    by_cases hk : Q (m k) k
    · obtain ⟨E, hE, hcount⟩ := hexGood k hk
      exact ⟨E, fun g => ⟨(hE g).1,(hE g).2.1⟩, fun _ => ⟨fun g => (hE g).2.2,hcount⟩⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨MeasurableSet.empty,Set.empty_subset _⟩, fun hc => False.elim (hk hc)⟩
  choose E hE hvalid using hex
  refine ⟨H, M, E, hH, ?_, hE, hgood.mono (fun k hk => (hvalid k hk).1), ?_, ?_⟩
  · intro k
    have hM : 1 ≤ M k := one_le_pow₀ (show 1 ≤ J k by have h := hJ₂ k; omega)
    refine ⟨hM, ?_⟩
    have hJJ : (J k : ℝ) ≤ (J k : ℝ) ^ 2 := by
      have hJ₁ : (1 : ℝ) ≤ J k := by exact_mod_cast (by have h := hJ₂ k; omega : 1 ≤ J k)
      nlinarith
    have hr : 1 / (M k : ℝ) ≤ 1 / (J k : ℝ) := by
      dsimp [M]
      rw [Nat.cast_pow]
      exact one_div_le_one_div_of_le (hJRpos k) hJJ
    calc
      _ ≤ Z k := Real.rpow_le_rpow_of_exponent_le (hN₁ k) hr
      _ ≤ H k := hZH k
  · intro R hR
    filter_upwards [hgood, hJRt.eventually_ge_atTop R] with k hk hJ
    intro g r hr hr' hgrid
    have hrpos : 0 < r := (inv_pos.mpr (by linarith : 0 < R)).trans_le hr
    have hmem : r ∈ positiveScaleGrid (J k ^ 2) (J k) :=
      mem_positiveScaleGrid_of_grid_scale (pow_pos (hJpos k) 2) hrpos (hr'.trans hJ) hgrid
    exact (hvalid k hk).2 g r hmem
  · refine ⟨J, fun k => ⟨hJ₂ k, rfl⟩, hJt, ?_⟩
    filter_upwards [hgood] with k hk
    exact ⟨hk.2.2.2.2.trans (hZH k), (hvalid k hk).2⟩

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
