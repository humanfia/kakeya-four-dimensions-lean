import Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing.DepthStep
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing.Numerics

/-! One depth with the numerical choices of `Numerics`: a law of mass at least
`N^-ε₁ / 2` loses at most `N^-ε₁ / 4`, the native lists have at most `N^ε`
entries, and retained pairs compare within `N^ε a` on whole boxes. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem ofReal_sub_le_of_le_add {a b : ℝ} {x : ENNReal} (hb : 0 ≤ b) (hab : b ≤ a)
    (h : ENNReal.ofReal a ≤ x + ENNReal.ofReal b) : ENNReal.ofReal (a - b) ≤ x := by
  have heq : ENNReal.ofReal a = ENNReal.ofReal (a - b) + ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_add (by linarith) hb]
    congr 1
    ring
  rw [heq] at h
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h

/-- The original time blocks are not shorter than `N^-κs / K`. -/
theorem timeLength_lower {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hN : 0 < cfg.N k) (hK : 0 < cfg.K k) :
    cfg.N k ^ (-cfg.κ * s) / cfg.K k ≤ cfg.timeLength k s := by
  have hup := a.time_upper
  have h2 : (0 : ℝ) < 2 ^ cfg.T k s := by positivity
  rw [timeLength_eq]
  calc cfg.N k ^ (-cfg.κ * s) / cfg.K k = (cfg.K k * cfg.N k ^ (cfg.κ * s))⁻¹ := by
        rw [neg_mul, Real.rpow_neg hN.le]
        field_simp
    _ ≤ ((2 : ℝ) ^ cfg.T k s)⁻¹ := inv_anti₀ h2 hup

/-- One depth with the chosen numerics. -/
theorem numeric_step (h : cfg.Prepared) {η R₀ : ℝ} (HB : ComparisonBound cfg.d η R₀)
    {k : ℕ} {s M RE ε ε₁ : ℝ} (hs : 0 ≤ s) (hε₁ : 0 ≤ ε₁)
    (μm : Measure (α × ℝ)) [IsFiniteMeasure μm] (hμm : μm ≤ cfg.ρ k)
    (H : cfg.EndpointLevel k s M RE ε₁) (hcov : ∀ᵐ ω ∂μm, ∃ i, ω.1 ∈ H.A i)
    (na : cfg.NativeLevel k s)
    (hgood : ∀ᵐ p ∂cfg.μ k,
      p.1 ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)))
    (hphys : PhysicalCaps cfg k M (cfg.N k ^ (-(M + 1))))
    (hnum : DepthNumerics cfg k s M ε ε₁ η R₀)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-ε₁) / 2) ≤ μm univ) :
    ∃ ξ : Measure (α × ℝ), ξ ≤ μm ∧
      μm univ ≤ ξ univ + ENNReal.ofReal (cfg.N k ^ (-ε₁) / 4) ∧
      ∃ L : Fin H.count × ℕ → Finset (Fin (cfg.n k s) × ℤ × ℤ × ℤ),
        (∀ x, ((L x).card : ℝ) ≤ cfg.N k ^ ε) ∧
        ∀ᵐ ω ∂ξ, ∃ (hh : Fin H.count) (i : Fin (cfg.n k s)),
          ω.1 ∈ H.A hh ∧ ω.1 ∈ cfg.B k s i ∧ ω.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
          (∃ e ∈ L (hh, (cfg.j k s i : ℕ)), e.1 = i) ∧
          ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
          ∀ p ∈ Icc ((H.tag hh 1 : ℝ) * cfg.parameterWidth k s)
            (((H.tag hh 1 : ℝ) + 1) * cfg.parameterWidth k s),
          ∀ q ∈ Icc ((H.tag hh 2 : ℝ) * cfg.parameterWidth k s)
            (((H.tag hh 2 : ℝ) + 1) * cfg.parameterWidth k s),
            |cfg.nativeParameter k s i ((H.tag hh 0 : ℝ) * cfg.N k ^ (-M)) t p q -
              predictor (H.coeff hh) t p q| ≤ cfg.N k ^ ε * cfg.N k ^ (-s) := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hKp : 0 < cfg.K k := by linarith
  have hδ0 : 0 ≤ numδ cfg k s ε₁ := by unfold numδ; positivity
  -- The native table of this depth.
  have htime := timeLength_lower na.assignments hN hKp
  have htab : cfg.N k ^ (-M) ≤ cfg.timeLength k s * cfg.N k ^ (-cfg.κ * s) :=
    hnum.table.trans (mul_le_mul_of_nonneg_right htime (Real.rpow_pos_of_pos hN _).le)
  obtain ⟨S, hScover, hSocc, hSbudget⟩ := h.native_parameter_table na hs htab
  -- The comparison.
  have hmτ : 15360 * numE cfg k ε₁ * cfg.N k ^ (-M) ≤
      numδ cfg k s ε₁ * cfg.timeLength k s :=
    hnum.mesh_time.trans (mul_le_mul_of_nonneg_left htime hδ0)
  have hA₀1 : 1 ≤ numA₀ cfg k ε₁ := by
    unfold numA₀
    exact Real.one_le_rpow (by linarith [h.scale k]) (by linarith)
  have hA1 : 13720 ≤ 2000000 * numA₀ cfg k ε₁ * numE cfg k ε₁ := by
    have h11 := mul_le_mul hA₀1 hnum.E_one zero_le_one (by linarith)
    linarith
  have hBnn : 0 ≤ depthBudget cfg k s ε₁ (numδ cfg k s ε₁) := by
    unfold depthBudget hiddenWidth
    have := Real.rpow_pos_of_pos hN (-s)
    have := Real.rpow_pos_of_pos hN ε₁
    positivity
  have hA0inv : 0 ≤ (numA₀ cfg k ε₁)⁻¹ := inv_nonneg.mpr hnum.A₀_pos.le
  have hmass' : ENNReal.ofReal (numA₀ cfg k ε₁)⁻¹ *
      ENNReal.ofReal (depthBudget cfg k s ε₁ (numδ cfg k s ε₁)) < μm univ := by
    rw [← ENNReal.ofReal_mul hA0inv]
    refine lt_of_lt_of_le ?_ hmass
    exact (ENNReal.ofReal_lt_ofReal_iff (by
      have := Real.rpow_pos_of_pos hN (-ε₁); linarith)).mpr hnum.mass
  obtain ⟨ξ, hξ, hloss, L, hLcard, hae⟩ := depth_step h HB μm hμm H hcov na S
    hScover hSocc hSbudget hgood hphys (Real.rpow_pos_of_pos hN _) hnum.fit_le_one
    hnum.phys_le_fit hnum.phys_le_mesh hnum.mesh_le le_rfl hnum.vel_le_one
    hnum.width_le_one hnum.hidden_le_one hnum.fitE hnum.fitN hnum.E_one hnum.E_pow
    hnum.E_K hnum.A₀_pos hmτ hnum.mesh_width hnum.scale hA1 le_rfl hnum.gain hmass'
  refine ⟨ξ, hξ, ?_, L, fun x => (hLcard x).trans hnum.list, ?_⟩
  · apply hloss.trans
    apply add_le_add le_rfl
    have hl := hnum.loss
    have hpow : 0 ≤ 2000000 * numA₀ cfg k ε₁ * numE cfg k ε₁ *
        (numMst cfg k s ε / numδ cfg k s ε₁) ^ (-η) := by
      have := hnum.E_one
      have := hnum.A₀_pos
      have : 0 ≤ (numMst cfg k s ε / numδ cfg k s ε₁) ^ (-η) := by
        apply Real.rpow_nonneg
        unfold numMst numδ
        have := Real.rpow_pos_of_pos hN ε
        have := Real.rpow_pos_of_pos hN ε₁
        have := Real.rpow_pos_of_pos hN (-s)
        positivity
      positivity
    rw [← ENNReal.ofReal_add hA0inv hpow, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hl
  · filter_upwards [hae] with ω hω
    obtain ⟨hh, i, h1, h2, h3, h4, h5⟩ := hω
    refine ⟨hh, i, h1, h2, h3, h4, fun t ht p hp q hq => ?_⟩
    have := h5 t ht p hp q hq
    unfold numMst at this
    linarith

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing
