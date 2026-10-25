-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.NonconcentratedFromStep.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.SymmetricSeed
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.BootstrapToOne
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.NonconcBudget
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.FiniteThin

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

/-- Proposition 8.5's counting conclusion from the uniform OSW improvement
step. The Frostman exponent is chosen before the line exponent `ζ`. -/
theorem nonconcentrated_dot_products_of_step {ε τ M : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) (hM : 1 ≤ M) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
      ∃ α δ₀ : ℝ, 0 < α ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (F G₁ G₂ : Finset Plane) (H : Finset Triple),
        ClosedFiniteFrostman δ (δ ^ (-ℓ)) F →
        ClosedFiniteFrostman δ (δ ^ (-ℓ)) G₁ →
        ClosedFiniteFrostman δ (δ ^ (-ℓ)) G₂ →
        IndexedLineFrostman δ (δ ^ (-ℓ)) ζ (fun b : G₁ => (b : Plane)) →
        IndexedLineFrostman δ (δ ^ (-ℓ)) ζ (fun x : G₂ => (x : Plane)) →
        (∀ b ∈ G₁, ∀ x ∈ G₂, 1 / 4 ≤ ‖b - x‖ ∧ ‖b - x‖ ≤ 8) →
        H ⊆ F ×ˢ (G₁ ×ˢ G₂) → H.Nonempty →
        δ ^ α * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ) ≤ (H.card : ℝ) →
        (∀ σ K c : ℝ, 1 / 4 ≤ σ → σ ≤ 1 - ε / 100 → 1 ≤ K → 0 < c → c < 1 / 10 →
          SymmetricThinTubes δ σ K c (fun b : G₁ => (b : Plane)) (fun x : G₂ => (x : Plane)) →
          SymmetricThinTubes δ (σ + τ) ((δ ^ (-ℓ) * K / c) ^ M) (4 * c)
            (fun b : G₁ => (b : Plane)) (fun x : G₂ => (x : Plane))) →
        CoverLower δ (DotSet (↑H : Set Triple)) (δ ^ (ε - 1)) := by
  classical
  obtain ⟨N, hreach, hrange⟩ := exists_bootstrap_depth (β := (1 / 4 : ℝ)) (t := 1 - ε / 100) hτ
  let L : ℝ := (2 * M) ^ N
  have hL : 1 ≤ L := one_le_pow₀ (by linarith)
  let ℓ := nonconcEll ε L
  have hℓ : 0 < ℓ := by
    dsimp [ℓ, nonconcEll]
    have hLp : 0 < L := zero_lt_one.trans_le hL
    positivity
  refine ⟨ℓ, hℓ, ?_⟩
  intro ζ hζ hζ1
  let α := nonconcAlpha ε L ζ
  have hα : 0 < α := (nonconc_parameter_bounds hε hL hζ hζ1).2.1
  obtain ⟨d₁, hd₁, hd₁1, hseed⟩ := exists_symmetric_quarter_thin_tubes hℓ hζ hζ1
    (show 0 < 2 * α by positivity)
  obtain ⟨d₂, hd₂, hbudget⟩ := exists_nonconc_scale_budget N hε hL hζ hζ1
  obtain ⟨d₃, hd₃, hdot⟩ := thin_dot_count_of_indexed_tubes (ε / 10) (by positivity)
  refine ⟨α, min d₁ (min d₂ d₃), hα, by positivity, ?_⟩
  intro δ hδ hsmall F G₁ G₂ H hF hG₁ hG₂ hL₁ hL₂ hsep hH hHne hdensity hstep
  have hs₁ := hsmall.trans (min_le_left _ _)
  have hs₂ := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs₃ := (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hb : NonconcScaleBudget δ ε ℓ α ζ L N := hbudget δ hδ hs₂
  obtain ⟨p, hp⟩ := hHne
  have hp' := Finset.mem_product.mp (hH hp)
  have hp'' := Finset.mem_product.mp hp'.2
  letI : Nonempty G₁ := ⟨⟨p.2.1, hp''.1⟩⟩
  letI : Nonempty G₂ := ⟨⟨p.2.2, hp''.2⟩⟩
  have hseed' := hseed δ hδ hs₁ G₁ G₂ (fun b : G₁ => (b : Plane)) (fun x : G₂ => (x : Plane))
    hG₁.indexed hG₂.indexed hL₁ hL₂ (fun b x => hsep b b.property x x.property)
  let K := 32 * δ ^ (-(ℓ + 6 * α / ζ))
  have hSK : SymmetricThinTubes δ (1 / 4) K (δ ^ (2 * α))
      (fun b : G₁ => (b : Plane)) (fun x : G₂ => (x : Plane)) := by
    simpa only [show 3 * (2 * α) / ζ = 6 * α / ζ by ring] using hseed'
  have hC : 1 ≤ δ ^ (-ℓ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hb.scale_le_one (by linarith)
  have hK : 1 ≤ K := by
    have hp : 1 ≤ δ ^ (-(ℓ + 6 * α / ζ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hb.scale_le_one (by
        have hpos : 0 ≤ ℓ + 6 * α / ζ := by positivity
        linarith)
    dsimp [K]
    linarith
  have hfull := thin_tube_bootstrap_to_one hδ hC hK (by positivity : 0 < δ ^ (2 * α))
    hτ hM (by positivity : 0 ≤ ε / 100) (by linarith : ε / 100 ≤ 1)
    hb.error_small hreach (fun n hn => (hrange n hn).le) hstep hSK
  have hfull' : SymmetricThinTubes δ 1 (δ ^ (-ε / 10)) ((4 : ℝ) ^ N * δ ^ (2 * α))
      (fun b : G₁ => (b : Plane)) (fun x : G₂ => (x : Plane)) :=
    hfull.mono_constant hδ.le (by simpa only [K, L, neg_div] using hb.constant_bound)
  have hKfinal : 1 ≤ δ ^ (-ε / 10) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hb.scale_le_one (by linarith)
  have hd : 0 < δ ^ α := by positivity
  have hdc : 0 < δ ^ α - (4 : ℝ) ^ N * δ ^ (2 * α) := by linarith [hb.error_density]
  have hF' := hF.mono_constant hδ.le hb.frostman_le
  have hcount := hdot δ (δ ^ (-ε / 10)) ((4 : ℝ) ^ N * δ ^ (2 * α)) (δ ^ α)
    F G₁ G₂ H hδ hs₃ hKfinal hdc hF' hH ⟨p, hp⟩ hsep hfull'.1 hdensity
  intro m cc hcov
  have hcg := hcount m cc hcov
  have hsquare : 0 < (δ ^ (-ε / 10)) ^ (2 : ℕ) := by positivity
  apply (mul_le_mul_iff_left₀ hsquare).mp
  calc δ ^ (ε - 1) * (δ ^ (-ε / 10)) ^ (2 : ℕ) ≤
        (δ ^ α / 2) ^ (4 : ℕ) * δ ^ (ε / 10 - 1) := hb.gain_bound
    _ ≤ (δ ^ α - (4 : ℝ) ^ N * δ ^ (2 * α)) ^ (4 : ℕ) * δ ^ (ε / 10 - 1) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith [hb.error_density]) 4) (by positivity)
    _ ≤ (δ ^ (-ε / 10)) ^ (2 : ℕ) * (m : ℝ) := hcg
    _ = (m : ℝ) * (δ ^ (-ε / 10)) ^ (2 : ℕ) := mul_comm _ _

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
