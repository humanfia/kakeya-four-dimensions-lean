/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarTracePreparation.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.DurationTraceCore
import Submission.Obl.k4_scalar_grid_parameter_preparation.IncidenceFacts
import Submission.Obl.k4_scalar_grid_parameter_preparation.FiniteScaleGrid
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! Fixed-time original-prior preparation directly from the original sequence caps. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal

/-- Read the original two-coordinate grid cap as its two scalar equations. -/
theorem joint_vector_grid_cap_components {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) (T Y X V : Ω → ℝ) (π : Measure ℝ) (δ ζ ξ : ℝ) (C : ℝ≥0∞)
    (hcap : ∀ (q : Fin 2 → ℤ) (a c : ℤ),
      ρ {ω | (fun e : Fin 2 => (⌊(![T ω, Y ω] : Fin 2 → ℝ) e / δ⌋ : ℤ)) = q ∧
        (⌊X ω / ζ⌋ : ℤ) = a ∧ V ω ∈ scalarVelocityBin ξ c} ≤
        C * π (scalarVelocityBin ξ c)) :
    ∀ i j a c : ℤ, ρ {ω | (⌊T ω / δ⌋ : ℤ) = i ∧ (⌊Y ω / δ⌋ : ℤ) = j ∧
      (⌊X ω / ζ⌋ : ℤ) = a ∧ V ω ∈ scalarVelocityBin ξ c} ≤
        C * π (scalarVelocityBin ξ c) := by
  intro i j a c
  simpa only [funext_iff, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    and_assoc] using hcap ![i, j] a c

/-- One original-law mask supplies the fixed-time preparation ceiling for all
real scales in every compact range. The mask and its subpower loss are chosen
before that range. The palette and all world laws remain the original ones. -/
theorem exists_scalar_trace_preparation (N K : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (W : ℕ → ℕ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ) (d : ℝ)
    (hbase : ∀ k g, IsProbabilityMeasure (ν k g) ∧
      (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧
      ρ k g ≤ ENNReal.ofReal (K k) • (ν k g).prod volume ∧
      ρ k g {p | p.2 ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0)
    (hcaps : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
      R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → ∀ i j a c : ℤ,
      ρ k g {p | (⌊p.2 / N k ^ (-r)⌋ : ℤ) = i ∧
        (⌊(p.1.2 0 + p.2 * p.1.2 1) / N k ^ (-r)⌋ : ℤ) = j ∧
        (⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / N k ^ (-s)⌋ : ℤ) = a ∧
        p.1.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
          ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) *
            π k g (scalarVelocityBin (N k ^ (-b)) c)) :
    ∃ (H : ℕ → ℝ) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)),
      (∀ k, 1 ≤ H k ∧ 2 * K k ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      (∀ k g, MeasurableSet (E k g) ∧
        (∀ p ∈ E k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ K k) ∧
        ρ k g (E k g)ᶜ ≤ ENNReal.ofReal (3 / (100 * K k))) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
        R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
        ∀ (t : ℝ) (q a c : ℤ),
          ν k g {l | (l, t) ∈ E k g ∧ l.2 0 + t * l.2 1 ∈ scalarVelocityBin (N k ^ (-r)) q ∧
            l.2 2 + t * l.2 3 + t ^ 2 * l.2 4 ∈ scalarVelocityBin (N k ^ (-s)) a ∧
            l.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
              ENNReal.ofReal (H k * N k ^ (-r - d * s)) *
                π k g (scalarVelocityBin (N k ^ (-b)) c) := by
  let Q : ℕ → ℕ → Prop := fun j k => ∀ (g : Fin (W k)) (r s b : ℝ),
    ((j : ℝ) + 2)⁻¹ ≤ r → r ≤ (j : ℝ) + 2 →
    ((j : ℝ) + 2)⁻¹ ≤ s → s ≤ (j : ℝ) + 2 →
    ((j : ℝ) + 2)⁻¹ ≤ b → b ≤ (j : ℝ) + 2 → ∀ i l a c : ℤ,
      ρ k g {p | (⌊p.2 / N k ^ (-r)⌋ : ℤ) = i ∧
        (⌊(p.1.2 0 + p.2 * p.1.2 1) / N k ^ (-r)⌋ : ℤ) = l ∧
        (⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / N k ^ (-s)⌋ : ℤ) = a ∧
        p.1.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
          ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) *
            π k g (scalarVelocityBin (N k ^ (-b)) c)
  have hQ (j : ℕ) : ∀ᶠ k in atTop, Q j k :=
    hcaps ((j : ℝ) + 2) (by have hj := Nat.cast_nonneg (α := ℝ) j; linarith)
  obtain ⟨m, hm, hmt, hmn, hdiag⟩ := Submission.Lib.K4ModelReduction.exists_slow_diagonal Q hQ
  let u : ℕ → ℝ := fun k => (m k : ℝ) + 2
  let δ : ℕ → ℝ := fun k => N k ^ (-u k)
  let ε : ℕ → ℝ := fun k => 1 / (100 * K k)
  let H : ℕ → ℝ := fun k => 25600 * K k ^ 3
  have hNpos (k) : 0 < N k := by linarith [hN k]
  have hN1 (k) : 1 ≤ N k := by linarith [hN k]
  have hKpos (k) : 0 < K k := zero_lt_one.trans_le (hK.1 k)
  have hu2 (k) : 2 ≤ u k := by dsimp [u]; have hm := Nat.cast_nonneg (α := ℝ) (m k); linarith
  have hut : Tendsto u atTop atTop := by
    simpa only [u, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp ((tendsto_add_atTop_nat 2).comp hmt)
  have hδ (k) : 0 < δ k := Real.rpow_pos_of_pos (hNpos k) _
  have hδ1 (k) : δ k ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (hN1 k) (show -u k ≤ 0 by linarith [hu2 k])
  have hε (k) : 0 < ε k := one_div_pos.mpr (mul_pos (by norm_num) (hKpos k))
  letI (k : ℕ) (g : Fin (W k)) : IsProbabilityMeasure (ν k g) := (hbase k g).1
  letI (k : ℕ) (g : Fin (W k)) : IsFiniteMeasure (ρ k g) :=
    finite_original_incidence (ν k g) (ρ k g) (K k) 0 1 (hbase k g).2.2.1 (hbase k g).2.2.2
  let G : (k : ℕ) → Fin (W k) → ((ℕ × (Fin 5 → ℝ)) × ℝ) → ℝ≥0∞ :=
    fun k g => (ρ k g).rnDeriv ((ν k g).prod volume)
  have hG (k) (g : Fin (W k)) : Measurable (G k g) := Measure.measurable_rnDeriv _ _
  have hGeq (k) (g : Fin (W k)) : ((ν k g).prod volume).withDensity (G k g) = ρ k g :=
    Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le_smul (hbase k g).2.2.1)
  let E₀ : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
    fun k _ => {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ K k}
  have hE₀m (k) (g : Fin (W k)) : MeasurableSet (E₀ k g) := by
    apply (measurableSet_Icc.preimage measurable_snd).inter
    change MeasurableSet {p : (ℕ × (Fin 5 → ℝ)) × ℝ | ∀ e, |p.1.2 e| ≤ K k}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun e => measurableSet_le (by fun_prop) measurable_const
  have hsupport (k) (g : Fin (W k)) : ((ν k g).prod volume).withDensity (G k g) (E₀ k g)ᶜ = 0 := by
    rw [hGeq]
    have ht : ∀ᵐ p ∂ρ k g, p.2 ∈ Set.Icc (0 : ℝ) 1 := (ae_iff).mpr (hbase k g).2.2.2
    have hc := ae_original_incidence (ν k g) (ρ k g) (K k) (hbase k g).2.2.1 (hbase k g).2.1
    exact (ae_iff).mp (ht.and hc)
  choose E hEm hEsub hEloss hEtrace using fun k (g : Fin (W k)) =>
    exists_uniform_scalar_trace_core (ν k g) (G k g) (hG k g) Prod.snd measurable_snd
      (E₀ k g) (hE₀m k g) (hsupport k g) (K k) (δ k) (ε k) (hK.1 k) (hδ k) (hδ1 k) (hε k)
      (fun p hp => hp.2)
  refine ⟨H, E, ?_, ?_, ?_, ?_⟩
  · intro k
    have hp := one_le_pow₀ (hK.1 k) (n := 3)
    have hpK : K k ≤ K k ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ (hK.1 k) (show 1 ≤ 3 by norm_num)
    dsimp [H]
    constructor <;> nlinarith
  · intro η hη
    have hp := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN1 hNt hK.1 hK.2 3 (a := 0) (b := η) hη (A := 25600) (by norm_num)
    simpa only [Real.rpow_zero, mul_one, H] using hp.mono (fun k hk => hk.le)
  · intro k g
    refine ⟨hEm k g, fun p hp => hEsub k g hp, ?_⟩
    have hl := hEloss k g
    rw [hGeq, measure_univ, mul_one] at hl
    exact hl.trans_eq (by congr 1; dsimp [ε]; ring)
  · intro R hR
    have hRpos : 0 < R := zero_lt_one.trans hR
    have h5K := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN1 hNt hK.1 hK.2 1 (a := 0) (b := 2) (by norm_num) (A := 5) (by norm_num)
    filter_upwards [hdiag, hut.eventually_ge_atTop (R + 2), h5K] with k hk hu h5
    simp only [pow_one, Real.rpow_zero, mul_one] at h5
    have hcapk := hk (m k) le_rfl
    have hinv : (u k)⁻¹ ≤ R⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hRpos (by linarith : R ≤ u k)
    have hufloor : (u k)⁻¹ ≤ u k :=
      (inv_le_one_of_one_le₀ (by linarith [hu2 k] : 1 ≤ u k)).trans (by linarith [hu2 k])
    intro g r s b hr hr' hs hs' hb hb' t q a c
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have hδξ : δ k ≤ N k ^ (-r) :=
        Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
      have hsmall : 5 * K k * δ k ≤ N k ^ (-s) := by
        calc
          _ ≤ N k ^ (2 : ℝ) * N k ^ (-u k) :=
            mul_le_mul_of_nonneg_right h5.le (hδ k).le
          _ = N k ^ (2 - u k) := by rw [← Real.rpow_add (hNpos k), sub_eq_add_neg]
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
      have hcapfine : ∀ i j a' : ℤ,
          ((ν k g).prod volume).withDensity (G k g)
            {p | (⌊p.2 / δ k⌋ : ℤ) = i ∧ (⌊(p.1.2 0 + p.2 * p.1.2 1) / δ k⌋ : ℤ) = j ∧
              (⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / N k ^ (-s)⌋ : ℤ) = a' ∧
              p.1.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} ≤
                ENNReal.ofReal (K k * δ k ^ 2 * N k ^ (-d * s)) *
                  π k g (scalarVelocityBin (N k ^ (-b)) c) := by
        intro i j a'
        rw [hGeq]
        have h := hcapk g (u k) s b hufloor le_rfl (hinv.trans hs) (by linarith)
          (hinv.trans hb) (by linarith) i j a' c
        have he : N k ^ (-2 * u k - d * s) = δ k ^ 2 * N k ^ (-d * s) := by
          dsimp [δ]
          rw [← Real.rpow_natCast (N k ^ (-u k)) 2, ← Real.rpow_mul (hNpos k).le,
            ← Real.rpow_add (hNpos k)]
          congr 1
          ring
        simpa only [he, δ, mul_assoc] using h
      have hbnd := hEtrace k g t ht (N k ^ (-r)) (N k ^ (-s)) (K k) (N k ^ (-d * s))
        (scalarVelocityBin (N k ^ (-b)) c) (π k g (scalarVelocityBin (N k ^ (-b)) c)) q a
        hδξ (Real.rpow_pos_of_pos (hNpos k) _) hsmall (hKpos k).le
        (Real.rpow_nonneg (hNpos k).le _) (measurableSet_scalarVelocityBin _ _) hcapfine
      have he : 256 * K k * K k * N k ^ (-r) * N k ^ (-d * s) / ε k =
          H k * N k ^ (-r - d * s) := by
        dsimp [H, ε]
        rw [show -r - d * s = -r + (-d * s) by ring, Real.rpow_add (hNpos k)]
        field_simp
        ring
      simpa only [he] using hbnd
    · have he : {l | (l, t) ∈ E k g ∧
          l.2 0 + t * l.2 1 ∈ scalarVelocityBin (N k ^ (-r)) q ∧
          l.2 2 + t * l.2 3 + t ^ 2 * l.2 4 ∈ scalarVelocityBin (N k ^ (-s)) a ∧
          l.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} = ∅ := by
        apply Set.Subset.antisymm ?_ (Set.empty_subset _)
        intro l hl
        exact False.elim (ht (hEsub k g hl.1).1)
      rw [he, measure_empty]
      exact bot_le

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
