import Submission.Obl.k4_scalar_crop_profile_transport.Angular
import Submission.Obl.k4_scalar_crop_profile_transport.FiniteAngular
import Submission.Obl.k4_scalar_crop_profile_transport.WeightedUpper

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set Filter
open scoped ENNReal

local instance : SigmaFinite JointRef := by unfold JointRef BaseRef; infer_instance

/-- Joint densities and angular upper windows in every scalar crop world. -/
theorem joint_worlds_part (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hlim : Tendsto N atTop atTop)
    (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set Inc)
    (hsource : ∀ k, IsProbabilityMeasure (ν₀ k) ∧ MeasurableSet (E₀ k) ∧
      E₀ k ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (s V L u₀ α S U : ℝ) (F : ℝ → ℝ → ℝ)
    (hL : 0 ≤ L) (hLs : L ≤ s) (hu₀ : 0 ≤ u₀) (huV : u₀ + U ≤ V)
    (hgain : ∀ u : ℝ, 0 ≤ u → u ≤ U → F L u₀ + S * u ≤ F L (u₀ + u))
    (hhom : Homogeneous N s V (fun k => Selected (ν₀ k) (E₀ k)) F)
    (W : ℕ → ℕ) (ω p : (k : ℕ) → Fin (W k) → ℝ)
    (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ)
    (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc) (ρ : ℕ → ℝ)
    (hp : ∀ k γ, 0 < p k γ) (hlift : LiftFacts N u₀ W ν₀ E₀ ν E p z)
    (hω : ∀ k γ, ω k γ = p k γ / ρ k)
    (hpclass : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ γ,
      N k ^ (-α - ε) ≤ p k γ ∧ p k γ ≤ N k ^ (-α + ε))
    (hρsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (ρ k)⁻¹ ≤ N k ^ ε) :
    ∃ G : (k : ℕ) → Fin (W k) → ℝ → Joint → ENNReal,
      (∀ k γ u, 0 < u → u ≤ U → Measurable (G k γ u) ∧
        (Selected (ν k γ) (E k γ)).map (Aug (N k) L u) = JointRef.withDensity (G k γ u)) ∧
      (∀ u τ : ℝ, 0 < u → u ≤ U → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        (∑ γ, ENNReal.ofReal (ω k γ) * Selected (ν k γ) (E k γ)
          {q | ENNReal.ofReal (N k ^ (-(F L u₀ + u₀ - α) - S * u + τ)) <
            G k γ u (Aug (N k) L u q)}) ≤ ENNReal.ofReal (N k ^ (-c))) := by
  classical
  let μ₀ : ℕ → Measure Inc := fun k => Selected (ν₀ k) (E₀ k)
  let μ : (k : ℕ) → Fin (W k) → Measure Inc := fun k γ => Selected (ν k γ) (E k γ)
  have hfin (k : ℕ) : IsFiniteMeasure (μ₀ k) := by
    let : IsProbabilityMeasure (ν₀ k) := (hsource k).1
    exact selected_finite _ _ (hsource k).2.2
  have hmass (k : ℕ) : μ₀ k univ ≤ 1 := by
    let : IsProbabilityMeasure (ν₀ k) := (hsource k).1
    exact selected_mass_le_one _ _ (hsource k).2.2
  have hcropfin (k : ℕ) (γ : Fin (W k)) : IsFiniteMeasure (μ k γ) := by
    let : IsFiniteMeasure (μ₀ k) := hfin k
    rw [lift_map_eq (N k ^ (-u₀)) (p k γ) (hp k γ) (z k γ) (μ₀ k) (μ k γ)
      (hlift.2.2.2.1 k γ)]
    apply Measure.smul_finite
    simp only [ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt (hp k γ)
  obtain ⟨g₀, G₀, hg₀, hG₀, htyp₀, htypG₀⟩ := hhom
  have hGu (k : ℕ) (u : ℝ) (hu : 0 < u) (huU : u ≤ U) :=
    hG₀ k L (u₀ + u) hL hLs (by linarith) (by linarith)
  have hex : ∀ (k : ℕ) (γ : Fin (W k)) (u : ℝ), ∃ G : Joint → ENNReal,
      Measurable G ∧ (0 < u → u ≤ U → (μ k γ).map (Aug (N k) L u) = JointRef.withDensity G) := by
    intro k γ u
    by_cases hu : 0 < u ∧ u ≤ U
    · let : IsFiniteMeasure (μ k γ) := hcropfin k γ
      have hac := crop_joint_ac (by linarith [hN k]) (p k γ) (hp k γ) (z k γ)
        L u₀ u (μ₀ k) (μ k γ) (hlift.2.2.2.1 k γ) (G₀ k L (u₀ + u)) (hGu k u hu.1 hu.2).2
      exact ⟨((μ k γ).map (Aug (N k) L u)).rnDeriv JointRef,
        Measure.measurable_rnDeriv _ _, fun _ _ => (Measure.withDensity_rnDeriv_eq _ _ hac).symm⟩
    · exact ⟨0, measurable_const, fun h0 hU => (hu ⟨h0, hU⟩).elim⟩
  choose G hG hGlaw using hex
  refine ⟨G, fun k γ u hu huU => ⟨hG k γ u, hGlaw k γ u hu huU⟩, ?_⟩
  intro u τ hu huU hτ
  have hfinite (k : ℕ) (hi δ : ℝ) (hhi : 0 < hi) (hδ : 0 < δ) (_hδ₁ : δ ≤ 1) :
      (∑ γ, ENNReal.ofReal (p k γ) * μ k γ
        {q | ENNReal.ofReal ((N k ^ (-u₀) / p k γ) * hi / δ) < G k γ u (Aug (N k) L u q)}) ≤
      μ₀ k {q | ENNReal.ofReal hi < G₀ k L (u₀ + u) (Aug (N k) L (u₀ + u) q)} +
        ENNReal.ofReal (32 * δ) := by
    let : IsFiniteMeasure (μ₀ k) := hfin k
    have hNk : 0 < N k := by linarith [hN k]
    let a := N k ^ (-u₀)
    have ha : 0 < a := Real.rpow_pos_of_pos hNk _
    let t : Fin (W k) → Inc → ℤ := fun γ => cropBin a (N k ^ (-u)) (z k γ)
    let m : Fin (W k) → ℤ := fun γ => ⌊-((z k γ 1 : ℝ) / N k ^ (-u))⌋
    let R : Fin (W k) → ℤ → ℤ → Prop := fun γ i j => j = i + m γ ∨ j = i + (m γ + 1)
    have ht (γ : Fin (W k)) : Measurable (t γ) := by unfold t cropBin; fun_prop
    have hcomm (γ : Fin (W k)) (q : Inc) :
        Aug (N k) L u (CropInc a (z k γ) q) =
          (obsEquiv a ha.ne' (z k γ) (Obs (N k) L q), t γ q) :=
      aug_crop a ha.ne' (z k γ) (N k) L u q
    have hraw (γ : Fin (W k)) :
        ((μ₀ k).restrict (Cell a (z k γ) ×ˢ univ)).map (fun q => (Obs (N k) L q, t γ q)) =
          JointRef.withDensity (fun b => (ENNReal.ofReal (p k γ) / ENNReal.ofReal a) *
            G k γ u (obsEquiv a ha.ne' (z k γ) b.1, b.2)) :=
      raw_joint_density_law a (p k γ) ha (hp k γ) (z k γ) (N k) L u (μ₀ k) (μ k γ)
        (G k γ u) (hG k γ u) (hlift.2.2.2.1 k γ) (hGlaw k γ u hu huU)
    have hR (γ : Fin (W k)) : ∀ᵐ q ∂(μ₀ k).restrict (Cell a (z k γ) ×ˢ univ),
        R γ ⌊q.1.2 1 / N k ^ (-(u₀ + u))⌋ (t γ q) := by
      apply Eventually.of_forall
      intro q
      rcases cropAug_shift hNk L u₀ u (z k γ) q with h | h
      · left
        exact congrArg Prod.snd h
      · right
        exact congrArg Prod.snd h
    have hcard (γ : Fin (W k)) (j : ℤ) :
        ∑' i, @ite ENNReal (R γ i j) (Classical.propDecidable _) 1 0 ≤ 2 := by
      let B : Finset ℤ := {j - m γ, j - (m γ + 1)}
      have hb : ∀ i, R γ i j → i ∈ B := by
        intro i hi
        rcases hi with hi | hi
        · have hi' : i = j - m γ := by omega
          simp [B, hi']
        · have hi' : i = j - (m γ + 1) := by omega
          simp [B, hi']
      have hc : B.card ≤ 2 := by
        exact (Finset.card_insert_le _ _).trans (by simp)
      have hc' : (B.card : ENNReal) ≤ 2 := by exact_mod_cast hc
      exact (k4_scalar_grid_density_extension.tsum_ite_one_le_card (fun i => R γ i j) B hb).trans hc'
    exact finite_angular_from_raw (N k) L u₀ u hNk (μ₀ k) (hmass k) (W k) (p k) (z k)
      (μ k) (fun γ => G k γ u) (hp k) (fun γ => hG k γ u) (hlift.2.2.2.1 k)
      (hlift.2.2.1 k) t ht hcomm hraw (G₀ k L (u₀ + u)) (hGu k u hu huU).1
      (hGu k u hu huU).2 R hR hcard hi δ hδ
  have htyp : k4_native_grid_profile_extension.Profiles.HasTypicalDensity N μ₀
      (fun k q => G₀ k L (u₀ + u) (Aug (N k) L (u₀ + u) q)) (F L (u₀ + u)) :=
    fun ε hε => htypG₀ L (u₀ + u) ε hL hLs (by linarith) (by linarith) hε
  obtain ⟨c, hc, hbound⟩ := weighted_upper_of_finite_tail N hN hlim W p ω ρ μ₀ μ
    (fun k q => G₀ k L (u₀ + u) (Aug (N k) L (u₀ + u) q))
    (fun k γ q => G k γ u (Aug (N k) L u q)) u₀ α (F L (u₀ + u)) hω hpclass hρsub htyp hfinite τ hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound] with k hk
  refine (Finset.sum_le_sum fun γ _ => mul_le_mul' le_rfl (measure_mono ?_)).trans hk
  intro q hq
  change ENNReal.ofReal (N k ^ (-(F L (u₀ + u) + u₀ - α) + τ)) < G k γ u (Aug (N k) L u q)
  apply lt_of_le_of_lt _ hq
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le (by linarith [hN k])
  have h := hgain u hu.le huU
  linarith

end Submission.Obl.k4_scalar_crop_profile_transport
