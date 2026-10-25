import Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing.Basics
import Submission.Obl.k4_subcritical_endpoint_native_pairing.NativeEntries
import Submission.Obl.k4_subcritical_endpoint_native_pairing.StaticCap
import Submission.Obl.k4_subcritical_endpoint_native_pairing.PositivePalette

/-! Comparison domains (velocity bin, parameter square, time block) and their
static caps. The caps are the original physical joint caps, transported to the
static parameters by `static_parameter_joint_cap`; empty palette bins carry no
original incidence mass at all. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

noncomputable section

/-- The comparison domain of an incidence. -/
def domainReader {α : Type} (b : α → Fin 6 → ℝ) (χ D : ℝ) (T : ℕ) (ω : α × ℝ) :
    ℤ × ℤ × ℤ × ℕ :=
  (⌊b ω.1 3 / χ⌋, ⌊b ω.1 0 / D⌋, ⌊b ω.1 1 / D⌋, timeBlock T ω.2)

theorem measurable_domainReader {α : Type} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (χ D : ℝ) (T : ℕ) : Measurable (domainReader b χ D T) := by
  have hc (e : Fin 6) : Measurable fun ω : α × ℝ => b ω.1 e :=
    (measurable_pi_apply e).comp (hb.comp measurable_fst)
  exact (Int.measurable_floor.comp ((hc 3).div_const χ)).prodMk
    ((Int.measurable_floor.comp ((hc 0).div_const D)).prodMk
      ((Int.measurable_floor.comp ((hc 1).div_const D)).prodMk
        ((measurable_timeBlock T).comp measurable_snd)))

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Static cap density of a velocity bin. An empty bin gets density one; it
carries no original incidence mass. -/
def domainDensity (cfg : Data α) (k : ℕ) (M : ℝ) (v : ℤ) : ℝ :=
  if cfg.velocityWeight k (cfg.N k ^ (-M)) v = 0 then 1
  else 4320 * cfg.K k * (2 * cfg.K k + 2) *
    (cfg.velocityWeight k (cfg.N k ^ (-M)) v).toReal

theorem domainDensity_pos (h : cfg.Prepared) (k : ℕ) (M : ℝ) (v : ℤ) :
    0 < domainDensity cfg k M v := by
  unfold domainDensity
  split_ifs with hw
  · exact one_pos
  · have hK : 1 ≤ cfg.K k := h.subpower.1 k
    have hK0 : 0 < cfg.K k := by linarith
    have hw' : 0 < (cfg.velocityWeight k (cfg.N k ^ (-M)) v).toReal :=
      ENNReal.toReal_pos hw (velocityWeight_ne_top h k _ v)
    positivity

theorem domainDensity_of_ne (k : ℕ) (M : ℝ) {v : ℤ}
    (hw : cfg.velocityWeight k (cfg.N k ^ (-M)) v ≠ 0) :
    domainDensity cfg k M v = 4320 * cfg.K k * (2 * cfg.K k + 2) *
      (cfg.velocityWeight k (cfg.N k ^ (-M)) v).toReal := by
  unfold domainDensity
  rw [if_neg hw]

/-- The physical joint caps at one base mesh, for every hidden width up to one. -/
def PhysicalCaps (cfg : Data α) (k : ℕ) (M δp : ℝ) : Prop :=
  ∀ w : ℝ, δp ≤ w → w ≤ 1 → ∀ (c : Fin 3 → ℤ) (a v : ℤ),
    cfg.μ k {p | (fun e => ⌊parameterPhysicalBase (cfg.b k) p e / δp⌋) = c ∧
      ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / w⌋ = a ∧
      ⌊cfg.b k p.1 3 / (cfg.N k ^ (-M))⌋ = v} ≤
      ENNReal.ofReal (cfg.K k * δp ^ 3 * w ^ cfg.d) *
        cfg.π k {v' | ⌊v' / (cfg.N k ^ (-M))⌋ = v}

/-- Every occupied velocity bin has a positive original palette weight. -/
theorem ae_velocityWeight_ne_zero (h : cfg.Prepared) {k : ℕ} {M δp : ℝ}
    (hphys : PhysicalCaps cfg k M δp) (hδp1 : δp ≤ 1) :
    ∀ᵐ p ∂cfg.μ k,
      cfg.velocityWeight k (cfg.N k ^ (-M)) ⌊cfg.b k p.1 3 / cfg.N k ^ (-M)⌋ ≠ 0 := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hχ : 0 < cfg.N k ^ (-M) := Real.rpow_pos_of_pos hN _
  have hae := ae_positive_palette_of_cell_caps (cfg.μ k)
    (fun p => ((fun e => ⌊parameterPhysicalBase (cfg.b k) p e / δp⌋),
      ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / 1⌋))
    (fun p => ⌊cfg.b k p.1 3 / cfg.N k ^ (-M)⌋)
    (fun v => cfg.π k {v' | ⌊v' / cfg.N k ^ (-M)⌋ = v})
    (ENNReal.ofReal (cfg.K k * δp ^ 3 * 1 ^ cfg.d))
    (fun c v => by
      apply (measure_mono _).trans (hphys 1 hδp1 le_rfl c.1 c.2 v)
      intro p hp
      exact ⟨congrArg Prod.fst hp.1, congrArg Prod.snd hp.1, hp.2⟩)
  filter_upwards [hae] with p hp
  rw [velocityWeight_eq k hχ]
  exact hp.ne'

/-- The static cap on one comparison domain, in the form required by the
comparison theorem. -/
theorem domain_cap (h : cfg.Prepared) {k : ℕ} {M D : ℝ} {T : ℕ}
    (μm : Measure (α × ℝ)) (hμm : μm ≤ cfg.μ k)
    (hgood : ∀ᵐ p ∂cfg.μ k,
      p.1 ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)))
    (hpos : ∀ᵐ p ∂cfg.μ k,
      cfg.velocityWeight k (cfg.N k ^ (-M)) ⌊cfg.b k p.1 3 / cfg.N k ^ (-M)⌋ ≠ 0)
    {δp δ δm : ℝ} (hphys : PhysicalCaps cfg k M δp)
    (hδp : 0 < δp) (hpδ : 3 * δp ≤ δ) (hpm : 3 * (2 * cfg.K k + 2) * δp ≤ δm)
    (hmH : δm ≤ 2 * cfg.K k + 2) (hχm : cfg.N k ^ (-M) ≤ δm) (hχ1 : cfg.N k ^ (-M) ≤ 1)
    (g : ℤ × ℤ × ℤ × ℕ) {σ' : ℝ} (hσ : δ ≤ σ') (hσ1 : σ' ≤ 1) (c : Fin 3 → ℤ) (j' : ℤ) :
    (μm.restrict {ω | domainReader (cfg.b k) (cfg.N k ^ (-M)) D T ω = g})
      {ω | (fun e => ⌊(![ω.2, cfg.b k ω.1 0, cfg.b k ω.1 1] : Fin 3 → ℝ) e / δm⌋) = c ∧
        ⌊(cfg.b k ω.1 2 + ω.2 * cfg.b k ω.1 5) / σ'⌋ = j'} ≤
      ENNReal.ofReal (domainDensity cfg k M g.1 * σ' ^ cfg.d * δm ^ 3) := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hχ : 0 < cfg.N k ^ (-M) := Real.rpow_pos_of_pos hN _
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hb := (h.basic k).1
  have hGm : MeasurableSet {ω | domainReader (cfg.b k) (cfg.N k ^ (-M)) D T ω = g} :=
    measurable_domainReader hb _ D T (measurableSet_singleton g)
  set G := {ω | domainReader (cfg.b k) (cfg.N k ^ (-M)) D T ω = g} with hGdef
  by_cases hw : cfg.velocityWeight k (cfg.N k ^ (-M)) g.1 = 0
  · -- An empty bin: the whole domain is null.
    have hG0 : cfg.μ k G = 0 := by
      have hz := ae_iff.mp hpos
      apply measure_mono_null _ hz
      intro ω hω
      simp only [mem_setOf_eq, not_not]
      have h1 : ⌊cfg.b k ω.1 3 / cfg.N k ^ (-M)⌋ = g.1 := congrArg Prod.fst hω
      rw [h1]
      exact hw
    calc (μm.restrict G) _ ≤ (μm.restrict G) univ := measure_mono (subset_univ _)
      _ = 0 := by
        rw [Measure.restrict_apply_univ]
        exact le_antisymm ((hμm G).trans hG0.le) bot_le
      _ ≤ _ := bot_le
  · by_cases hz : μm G = 0
    · calc (μm.restrict G) _ ≤ (μm.restrict G) univ := measure_mono (subset_univ _)
        _ = 0 := by rw [Measure.restrict_apply_univ]; exact hz
        _ ≤ _ := bot_le
    -- An occupied domain contains a good original trajectory.
    have hae : ∀ᵐ ω ∂μm.restrict G, ω ∈ G ∧
        ω.1 ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)) ∧
        ω.2 ∈ Icc (0 : ℝ) 1 := by
      filter_upwards [ae_restrict_mem hGm, ae_restrict_of_ae (ae_mono hμm hgood),
        ae_restrict_of_ae (ae_mono hμm (ae_unit_time h k))] with ω h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have hne : μm.restrict G ≠ 0 := by
      intro h0
      apply hz
      rw [← Measure.restrict_apply_univ, h0]
      simp
    haveI := ae_neBot.mpr hne
    obtain ⟨ω₀, hω₀G, hω₀g, -⟩ := hae.exists
    have hv0 : ⌊cfg.b k ω₀.1 3 / cfg.N k ^ (-M)⌋ = g.1 := congrArg Prod.fst hω₀G
    have hvc : |(g.1 : ℝ) * cfg.N k ^ (-M)| ≤ 2 * cfg.K k + 2 := by
      have h1 := abs_sub_floor_mul_le (w := cfg.b k ω₀.1 3) hχ
      rw [hv0] at h1
      have h2 := hω₀g.1 3
      calc |(g.1 : ℝ) * cfg.N k ^ (-M)|
          ≤ |cfg.b k ω₀.1 3| + |cfg.b k ω₀.1 3 - (g.1 : ℝ) * cfg.N k ^ (-M)| := by
            have := abs_sub_abs_le_abs_sub ((g.1 : ℝ) * cfg.N k ^ (-M)) (cfg.b k ω₀.1 3)
            rw [abs_sub_comm (cfg.b k ω₀.1 3)]
            linarith
        _ ≤ 2 * cfg.K k + 2 := by linarith
    have hδ : 0 < δ := by linarith
    have hσpos : 0 < σ' := by linarith
    have hδm : 0 < δm := hχ.trans_le hχm
    have hgood' : ∀ᵐ z ∂μm.restrict G, z.2 ∈ Icc (0 : ℝ) 1 ∧
        |cfg.b k z.1 0| ≤ 2 * cfg.K k + 2 ∧
        |cfg.b k z.1 3 - (g.1 : ℝ) * cfg.N k ^ (-M)| ≤ δm ∧
        |cfg.b k z.1 4 + cfg.b k z.1 0| ≤ δm ∧
        (fun z : α × ℝ => ⌊cfg.b k z.1 3 / cfg.N k ^ (-M)⌋) z = g.1 := by
      filter_upwards [hae] with z hz'
      obtain ⟨hzG, hzg, hzt⟩ := hz'
      have hv : ⌊cfg.b k z.1 3 / cfg.N k ^ (-M)⌋ = g.1 := congrArg Prod.fst hzG
      have h1 := abs_sub_floor_mul_le (w := cfg.b k z.1 3) hχ
      rw [hv] at h1
      refine ⟨hzt, by linarith [hzg.1 0], h1.trans hχm, hzg.2.trans hχm, hv⟩
    have hcap := static_parameter_joint_cap (cfg.μ k) (μm.restrict G)
      (Measure.restrict_le_self.trans hμm) (cfg.b k)
      (fun z : α × ℝ => ⌊cfg.b k z.1 3 / cfg.N k ^ (-M)⌋) g.1
      (cfg.π k {v' | ⌊v' / cfg.N k ^ (-M)⌋ = g.1})
      (δ := δp) (δm := δm) (w := σ') (H := 2 * cfg.K k + 2) (C := cfg.K k) (d := cfg.d)
      (vc := (g.1 : ℝ) * cfg.N k ^ (-M))
      hδp hδm hσpos (by linarith) (by linarith) hpm (by linarith) hmH hvc hgood'
      (fun c' j'' => hphys σ' (by linarith) hσ1 c' j'' g.1) c j'
    apply hcap.trans
    rw [domainDensity_of_ne k M hw]
    have hw' := velocityWeight_ne_top h k (cfg.N k ^ (-M)) g.1
    have hK0 : 0 < cfg.K k := by linarith
    calc ENNReal.ofReal (4320 * cfg.K k * (2 * cfg.K k + 2) * δm ^ 3 * σ' ^ cfg.d) *
          cfg.π k {v' | ⌊v' / cfg.N k ^ (-M)⌋ = g.1}
        = ENNReal.ofReal (4320 * cfg.K k * (2 * cfg.K k + 2) * δm ^ 3 * σ' ^ cfg.d) *
          cfg.velocityWeight k (cfg.N k ^ (-M)) g.1 := by rw [velocityWeight_eq k hχ]
      _ = ENNReal.ofReal (4320 * cfg.K k * (2 * cfg.K k + 2) * δm ^ 3 * σ' ^ cfg.d) *
          ENNReal.ofReal (cfg.velocityWeight k (cfg.N k ^ (-M)) g.1).toReal := by
          rw [ENNReal.ofReal_toReal hw']
      _ = ENNReal.ofReal (4320 * cfg.K k * (2 * cfg.K k + 2) * δm ^ 3 * σ' ^ cfg.d *
          (cfg.velocityWeight k (cfg.N k ^ (-M)) g.1).toReal) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := le_of_eq (by congr 1; ring)

/-- The endpoint floors, in real units. -/
theorem endpoint_reference_real (h : cfg.Prepared) {k : ℕ} {s M RE ζ : ℝ}
    (H : cfg.EndpointLevel k s M RE ζ) :
    (∑ i, cfg.parameterWidth k s ^ 2 * cfg.hiddenWidth k s ^ cfg.d *
      (cfg.velocityWeight k (cfg.N k ^ (-M)) (H.tag i 0)).toReal) ≤
        cfg.N k ^ ζ * cfg.K k := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hb := H.reference_budget hN
  have hρtop : cfg.ρ k univ ≠ ⊤ :=
    ((residual_mass_le h k).trans_lt ENNReal.ofReal_lt_top).ne
  have hR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hρtop) hb
  rw [ENNReal.toReal_sum (fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (velocityWeight_ne_top h k _ _))] at hR
  have hcoef : 0 ≤ cfg.parameterWidth k s ^ 2 * cfg.hiddenWidth k s ^ cfg.d := by
    unfold parameterWidth hiddenWidth
    positivity
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef] at hR
  rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hN _).le] at hR
  apply hR.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hN _).le
  have hρK := residual_mass_le h k
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hρK
  rwa [ENNReal.toReal_ofReal (by linarith)] at this

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing
