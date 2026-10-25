import Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing.DomainCaps
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing.Bound
import Submission.Obl.k4_subcritical_endpoint_native_pairing.NativeParameters

/-! One endpoint depth at one sample. The endpoint entries are (endpoint label,
time block); the native entries are the occupied original native parameter
cells. Both carry their full original floors as references, and the finite
comparison theorem with lists pairs them on a retained submeasure of the given
law. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The native parameter cell of an index, as a product. -/
def nativeCell {n : ℕ} (e : NativeParameterIndex n) : Fin n × ℤ × ℤ × ℤ :=
  (e.1, e.2.1, e.2.2 0, e.2.2 1)

theorem x_three (k : ℕ) (l : α) (t : ℝ) :
    (cfg.x k l t) 3 = cfg.b k l 2 + t * cfg.b k l 5 := rfl

theorem timeLength_eq (k : ℕ) (s : ℝ) :
    cfg.timeLength k s = ((2 : ℝ) ^ cfg.T k s)⁻¹ := rfl

theorem block_add_timeLength (k : ℕ) (s : ℝ) (J : ℕ) :
    (J : ℝ) / 2 ^ cfg.T k s + cfg.timeLength k s = ((J : ℝ) + 1) / 2 ^ cfg.T k s := by
  rw [timeLength_eq]
  field_simp

theorem I_eq_Icc (T : ℕ) (j : Fin (2 ^ T)) :
    I T j = Icc (((j : ℕ) : ℝ) / 2 ^ T) ((((j : ℕ) : ℝ) + 1) / 2 ^ T) := rfl

/-- One depth: the endpoint level is paired with original native entries on
a retained submeasure, with whole-box comparison and blockwise lists. -/
theorem depth_step (h : cfg.Prepared) {η R₀ : ℝ}
    (HB : ComparisonBound cfg.d η R₀) {k : ℕ} {s M RE ζ : ℝ}
    (μm : Measure (α × ℝ)) [IsFiniteMeasure μm] (hμm : μm ≤ cfg.ρ k)
    (H : cfg.EndpointLevel k s M RE ζ) (hcov : ∀ᵐ ω ∂μm, ∃ i, ω.1 ∈ H.A i)
    (na : cfg.NativeLevel k s)
    (S : Finset (NativeParameterIndex (cfg.n k s)))
    (hScover : ∀ i l, l ∈ cfg.B k s i →
        l ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)) →
        (⟨i, ⟨⌊cfg.b k l 3 / cfg.N k ^ (-M)⌋,
          ![⌊cfg.b k l 0 / cfg.parameterWidth k s⌋,
            ⌊cfg.b k l 1 / cfg.parameterWidth k s⌋]⟩⟩ :
              NativeParameterIndex (cfg.n k s)) ∈ S)
    (hSocc : ∀ e ∈ S, ∃ l ∈ cfg.B k s e.1,
        l ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)) ∧
        ⌊cfg.b k l 3 / cfg.N k ^ (-M)⌋ = e.2.1 ∧
        ![⌊cfg.b k l 0 / cfg.parameterWidth k s⌋,
          ⌊cfg.b k l 1 / cfg.parameterWidth k s⌋] = e.2.2)
    (hSbudget : (∑ e ∈ S, cfg.timeLength k s * cfg.parameterWidth k s ^ 2 *
        cfg.hiddenWidth k s ^ cfg.d *
          (cfg.velocityWeight k (cfg.N k ^ (-M)) e.2.1).toReal) ≤ 4096 * cfg.K k ^ 6)
    (hgood : ∀ᵐ p ∂cfg.μ k,
      p.1 ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)))
    {δp δ δm E A₀ A Mst : ℝ} (hphys : PhysicalCaps cfg k M δp)
    (hδp : 0 < δp) (hδ1 : δ ≤ 1) (hpδ : 3 * δp ≤ δ)
    (hpm : 3 * (2 * cfg.K k + 2) * δp ≤ δm) (hmH : δm ≤ 2 * cfg.K k + 2)
    (hχm : cfg.N k ^ (-M) ≤ δm) (hχ1 : cfg.N k ^ (-M) ≤ 1)
    (hD1 : cfg.parameterWidth k s ≤ 1) (ha1 : cfg.N k ^ (-s) ≤ 1)
    (hfitE : cfg.N k ^ ζ * cfg.hiddenWidth k s ≤ δ / 2)
    (hfitN : cfg.K k * cfg.N k ^ (-s) +
      36 * cfg.K k ^ 4 * (cfg.N k ^ (-M) + cfg.N k ^ (-M)) ≤ δ / 2)
    (hE1 : 1 ≤ E) (hEζ : cfg.N k ^ ζ ≤ E) (hE200 : 200 * cfg.K k ^ 4 ≤ E)
    (hA₀ : 0 < A₀)
    (hmτ : 15360 * E * δm ≤ δ * cfg.timeLength k s)
    (hmD : 15360 * E * δm ≤ δ * cfg.parameterWidth k s)
    (hMst : R₀ * δ ≤ Mst) (hA1 : 13720 ≤ A) (hA2 : 2000000 * A₀ * E ≤ A)
    (hA : A ≤ (Mst / δ) ^ η)
    (hmass : ENNReal.ofReal A₀⁻¹ * ENNReal.ofReal (depthBudget cfg k s ζ δ) < μm univ) :
    ∃ ξ : Measure (α × ℝ), ξ ≤ μm ∧
      μm univ ≤ ξ univ + (ENNReal.ofReal A₀⁻¹ + ENNReal.ofReal (A * (Mst / δ) ^ (-η))) *
        ENNReal.ofReal (depthBudget cfg k s ζ δ) ∧
      ∃ L : Fin H.count × ℕ → Finset (Fin (cfg.n k s) × ℤ × ℤ × ℤ),
        (∀ x, ((L x).card : ℝ) ≤ 2000000 * A₀ * E * ((5120 * Mst) / δ) ^ cfg.d) ∧
        ∀ᵐ ω ∂ξ, ∃ (hh : Fin H.count) (i : Fin (cfg.n k s)),
          ω.1 ∈ H.A hh ∧ ω.1 ∈ cfg.B k s i ∧ ω.2 ∈ I (cfg.T k s) (cfg.j k s i) ∧
          (∃ e ∈ L (hh, (cfg.j k s i : ℕ)), e.1 = i) ∧
          ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
          ∀ p ∈ Icc ((H.tag hh 1 : ℝ) * cfg.parameterWidth k s)
            (((H.tag hh 1 : ℝ) + 1) * cfg.parameterWidth k s),
          ∀ q ∈ Icc ((H.tag hh 2 : ℝ) * cfg.parameterWidth k s)
            (((H.tag hh 2 : ℝ) + 1) * cfg.parameterWidth k s),
            |cfg.nativeParameter k s i ((H.tag hh 0 : ℝ) * cfg.N k ^ (-M)) t p q -
              predictor (H.coeff hh) t p q| ≤ 10 * Mst := by
  classical
  -- Constants of this sample.
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hb : Measurable (cfg.b k) := (h.basic k).1
  set χ := cfg.N k ^ (-M) with hχdef
  set D := cfg.parameterWidth k s with hDdef
  set T := cfg.T k s with hTdef
  set τ := cfg.timeLength k s with hτdef
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN _
  have hD : 0 < D := Real.rpow_pos_of_pos hN _
  have hτ : 0 < τ := by rw [hτdef, timeLength_eq]; positivity
  have ha : 0 < cfg.hiddenWidth k s := Real.rpow_pos_of_pos hN _
  have hδ : 0 < δ := by linarith
  have hδm : 0 < δm := hχ.trans_le hχm
  have hμρ : μm ≤ cfg.μ k := hμm.trans (h.basic k).2.2.2.2.1
  have hpos := ae_velocityWeight_ne_zero h hphys (by nlinarith)
  -- Almost sure facts of the retained law.
  have hpos' := ae_mono hμρ hpos
  have hgood' := ae_mono hμρ hgood
  have hunit' := ae_mono hμρ (ae_unit_time h k)
  have hdy' := ae_mono hμρ (ae_not_dyadic h k T)
  have hcovN := ae_mono hμρ na.assignments.covers
  -- The comparison data.
  let reader : α × ℝ → ℤ × ℤ × ℤ × ℕ := domainReader (cfg.b k) χ D T
  have hreader : Measurable reader := measurable_domainReader hb χ D T
  let domain₁ : Fin H.count × ℕ → ℤ × ℤ × ℤ × ℕ := fun x =>
    (H.tag x.1 0, H.tag x.1 1, H.tag x.1 2, x.2)
  let domain₂ : Fin (cfg.n k s) × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℕ := fun e =>
    (e.2.1, e.2.2.1, e.2.2.2, (cfg.j k s e.1 : ℕ))
  let s₁ : Finset (Fin H.count × ℕ) :=
    (Finset.univ ×ˢ Finset.range (2 ^ T)).filter
      (fun x => cfg.velocityWeight k χ (H.tag x.1 0) ≠ 0)
  let s₂ : Finset (Fin (cfg.n k s) × ℤ × ℤ × ℤ) :=
    (S.image nativeCell).filter (fun e => cfg.velocityWeight k χ e.2.1 ≠ 0)
  let Good := goodOriginalLines (cfg.b k) (2 * cfg.K k) χ
  let E₁ : Fin H.count × ℕ → Set (α × ℝ) := fun x =>
    {ω | ω.1 ∈ H.A x.1 ∧ ω.2 ∈ Icc (0 : ℝ) 1 ∧ reader ω = domain₁ x}
  let E₂ : Fin (cfg.n k s) × ℤ × ℤ × ℤ → Set (α × ℝ) := fun e =>
    {ω | ω.1 ∈ cfg.B k s e.1 ∧ ω.2 ∈ I T (cfg.j k s e.1) ∧ ω.1 ∈ Good ∧
      reader ω = domain₂ e}
  let h₂ : Fin (cfg.n k s) × ℤ × ℤ × ℤ → Fin 6 → ℝ := fun e =>
    Match3.nativeParam (na.L e.1) ((e.2.1 : ℝ) * χ)
  let t₀ : ℤ × ℤ × ℤ × ℕ → ℝ := fun g => (g.2.2.2 : ℝ) / 2 ^ T
  let p₀ : ℤ × ℤ × ℤ × ℕ → ℝ := fun g => (g.2.1 : ℝ) * D
  let q₀ : ℤ × ℤ × ℤ × ℕ → ℝ := fun g => (g.2.2.1 : ℝ) * D
  let V : ℤ × ℤ × ℤ × ℕ → ℝ := fun g => domainDensity cfg k M g.1
  have hGood : MeasurableSet Good := measurableSet_goodOriginalLines hb _ _
  have hB : ∀ i, MeasurableSet (cfg.B k s i) := na.fitted_measurable
  have hE₁m : ∀ x, MeasurableSet (E₁ x) := fun x =>
    ((H.measurable x.1).preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter
        (hreader (measurableSet_singleton _)))
  have hE₂m : ∀ e, MeasurableSet (E₂ e) := fun e =>
    ((hB e.1).preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter
        ((hGood.preimage measurable_fst).inter (hreader (measurableSet_singleton _))))
  -- Coordinates of the trajectory at its incidence time.
  have hT : Measurable (fun ω : α × ℝ => ω.2) := measurable_snd
  have hP : Measurable (fun ω : α × ℝ => cfg.b k ω.1 0) :=
    (measurable_pi_apply 0).comp (hb.comp measurable_fst)
  have hQ : Measurable (fun ω : α × ℝ => cfg.b k ω.1 1) :=
    (measurable_pi_apply 1).comp (hb.comp measurable_fst)
  -- Inclusions in the domains.
  have hsub₁ : ∀ x ∈ s₁, E₁ x ⊆ {ω | reader ω = domain₁ x} := fun x _ ω hω => hω.2.2
  have hsub₂ : ∀ e ∈ s₂, E₂ e ⊆ {ω | reader ω = domain₂ e} := fun e _ ω hω => hω.2.2.2
  -- Uniqueness of the entries at a point.
  have huniq₁ : ∀ᵐ ω ∂μm, ∀ x ∈ s₁, ∀ y ∈ s₁, ω ∈ E₁ x → ω ∈ E₁ y → x = y := by
    refine Filter.Eventually.of_forall (fun ω x _ y _ hx hy => ?_)
    have h1 : x.1 = y.1 := by
      by_contra hne
      exact Set.disjoint_left.mp (H.disjoint hne) hx.1 hy.1
    have h2 : x.2 = y.2 := by
      have := hx.2.2.symm.trans hy.2.2
      exact congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.2.2.2) this
    exact Prod.ext h1 h2
  have huniq₂ : ∀ᵐ ω ∂μm, ∀ e ∈ s₂, ∀ e' ∈ s₂, ω ∈ E₂ e → ω ∈ E₂ e' → e = e' := by
    refine Filter.Eventually.of_forall (fun ω e _ e' _ he he' => ?_)
    have hd := he.2.2.2.symm.trans he'.2.2.2
    have hj : (cfg.j k s e.1 : ℕ) = (cfg.j k s e'.1 : ℕ) :=
      congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.2.2.2) hd
    have h1 : e.1 = e'.1 := by
      by_contra hne
      exact Set.disjoint_left.mp (na.assignments.disjoint e.1 e'.1 hne (Fin.ext hj))
        (na.assignments.fitted_subset e.1 he.1) (na.assignments.fitted_subset e'.1 he'.1)
    have h2 : e.2.1 = e'.2.1 := congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.1) hd
    have h3 : e.2.2.1 = e'.2.2.1 := congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.2.1) hd
    have h4 : e.2.2.2 = e'.2.2.2 := congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.2.2.1) hd
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  -- Coverage by both entry families.
  have hcover₁ : ∀ᵐ ω ∂μm, ∃ x ∈ s₁, ω ∈ E₁ x := by
    filter_upwards [hcov, hunit', hpos'] with ω hω hu hp
    obtain ⟨hh, hA⟩ := hω
    have hbins := H.bins hh ω.1 hA
    refine ⟨(hh, timeBlock T ω.2), ?_, hA, hu, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (timeBlock_lt T ω.2)⟩, ?_⟩
      rw [← hbins.1]
      exact hp
    · show (⌊cfg.b k ω.1 3 / χ⌋, ⌊cfg.b k ω.1 0 / D⌋, ⌊cfg.b k ω.1 1 / D⌋,
        timeBlock T ω.2) = (H.tag hh 0, H.tag hh 1, H.tag hh 2, timeBlock T ω.2)
      rw [hbins.1, hbins.2.1, hbins.2.2]
  have hcover₂ : ∀ᵐ ω ∂μm, ∃ e ∈ s₂, ω ∈ E₂ e := by
    filter_upwards [hcovN, hgood', hpos', hdy'] with ω hω hg hp hdω
    obtain ⟨i, hBi, hIi⟩ := hω
    have hblock : timeBlock T ω.2 = (cfg.j k s i : ℕ) :=
      timeBlock_eq_of_mem (cfg.j k s i).isLt hIi hdω
    have hmem := hScover i ω.1 hBi hg
    refine ⟨(i, ⌊cfg.b k ω.1 3 / χ⌋, ⌊cfg.b k ω.1 0 / D⌋, ⌊cfg.b k ω.1 1 / D⌋), ?_,
      hBi, hIi, hg, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, hmem, rfl⟩, hp⟩
    · show (⌊cfg.b k ω.1 3 / χ⌋, ⌊cfg.b k ω.1 0 / D⌋, ⌊cfg.b k ω.1 1 / D⌋,
        timeBlock T ω.2) = (⌊cfg.b k ω.1 3 / χ⌋, ⌊cfg.b k ω.1 0 / D⌋,
          ⌊cfg.b k ω.1 1 / D⌋, (cfg.j k s i : ℕ))
      rw [hblock]
  -- Box membership on each domain.
  have hbox : ∀ g, ∀ᵐ ω ∂μm.restrict {ω | reader ω = g},
      ω.2 ∈ Icc (t₀ g) (t₀ g + τ) ∧ cfg.b k ω.1 0 ∈ Icc (p₀ g) (p₀ g + D) ∧
        cfg.b k ω.1 1 ∈ Icc (q₀ g) (q₀ g + D) := by
    intro g
    filter_upwards [ae_restrict_mem (hreader (measurableSet_singleton g)),
      ae_restrict_of_ae hunit'] with ω hω hu
    have hr : reader ω = g := hω
    have hJ : timeBlock T ω.2 = g.2.2.2 := congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.2.2.2) hr
    have hp : ⌊cfg.b k ω.1 0 / D⌋ = g.2.1 := congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.2.1) hr
    have hq : ⌊cfg.b k ω.1 1 / D⌋ = g.2.2.1 :=
      congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.2.2.1) hr
    refine ⟨?_, ?_, ?_⟩
    · have hm := mem_timeBlock (T := T) hu
      rw [hJ] at hm
      show ω.2 ∈ Icc ((g.2.2.2 : ℝ) / 2 ^ T) ((g.2.2.2 : ℝ) / 2 ^ T + τ)
      rw [hτdef, block_add_timeLength]
      exact hm
    · have hm := mem_Icc_floor_mul (w := cfg.b k ω.1 0) hD
      rw [hp] at hm
      exact ⟨hm.1, by linarith [hm.2]⟩
    · have hm := mem_Icc_floor_mul (w := cfg.b k ω.1 1) hD
      rw [hq] at hm
      exact ⟨hm.1, by linarith [hm.2]⟩
  -- Fits of both entry families.
  have hfit₁ : ∀ x ∈ s₁, ∀ ω ∈ E₁ x,
      |(cfg.b k ω.1 2 + ω.2 * cfg.b k ω.1 5) -
        parameterPredictor (H.coeff x.1) ω.2 (cfg.b k ω.1 0) (cfg.b k ω.1 1)| ≤ δ / 2 := by
    intro x _ ω hω
    have hf := H.fit x.1 ω.1 hω.1 ω.2 hω.2.1
    exact hf.trans hfitE
  have hfit₂ : ∀ e ∈ s₂, ∀ ω ∈ E₂ e,
      |(cfg.b k ω.1 2 + ω.2 * cfg.b k ω.1 5) -
        parameterPredictor (h₂ e) ω.2 (cfg.b k ω.1 0) (cfg.b k ω.1 1)| ≤ δ / 2 := by
    intro e _ ω hω
    have hv : ⌊cfg.b k ω.1 3 / χ⌋ = e.2.1 :=
      congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.1) hω.2.2.2
    have hvel : |cfg.b k ω.1 3 - (e.2.1 : ℝ) * χ| ≤ χ := by
      have := abs_sub_floor_mul_le (w := cfg.b k ω.1 3) hχ
      rwa [hv] at this
    have hf := na.parameter_fit e.1 hω.1 hω.2.1 hvel hω.2.2.1.2
    rw [na.nativeParameter_eq] at hf
    exact hf.trans hfitN
  -- Norms on whole domains.
  have hnorm₁ : ∀ x ∈ s₁, ∀ t ∈ Icc (t₀ (domain₁ x)) (t₀ (domain₁ x) + τ),
      ∀ p ∈ Icc (p₀ (domain₁ x)) (p₀ (domain₁ x) + D),
      ∀ q ∈ Icc (q₀ (domain₁ x)) (q₀ (domain₁ x) + D),
        |parameterPredictor (H.coeff x.1) t p q| ≤ E := by
    intro x hx t ht p hp q hq
    have hx2 : x.2 < 2 ^ T := by
      have := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
      exact Finset.mem_range.mp this
    have htJ : t ∈ Icc ((x.2 : ℝ) / 2 ^ T) (((x.2 : ℝ) + 1) / 2 ^ T) := by
      have h' := ht
      change t ∈ Icc ((x.2 : ℝ) / 2 ^ T) ((x.2 : ℝ) / 2 ^ T + τ) at h'
      rwa [hτdef, block_add_timeLength] at h'
    have hpow : (0 : ℝ) < 2 ^ T := by positivity
    have ht01 : t ∈ Icc (0 : ℝ) 1 := by
      refine ⟨le_trans (by positivity) htJ.1, htJ.2.trans ?_⟩
      rw [div_le_one hpow]
      have : ((x.2 : ℕ) : ℝ) + 1 ≤ ((2 ^ T : ℕ) : ℝ) := by exact_mod_cast hx2
      simpa using this
    have hp' : p ∈ Icc ((H.tag x.1 1 : ℝ) * D) (((H.tag x.1 1 : ℝ) + 1) * D) :=
      ⟨hp.1, by have := hp.2; change p ≤ (H.tag x.1 1 : ℝ) * D + D at this; linarith⟩
    have hq' : q ∈ Icc ((H.tag x.1 2 : ℝ) * D) (((H.tag x.1 2 : ℝ) + 1) * D) :=
      ⟨hq.1, by have := hq.2; change q ≤ (H.tag x.1 2 : ℝ) * D + D at this; linarith⟩
    exact (H.norm_bound x.1 t ht01 p hp' q hq').trans hEζ
  have hnorm₂ : ∀ e ∈ s₂, ∀ t ∈ Icc (t₀ (domain₂ e)) (t₀ (domain₂ e) + τ),
      ∀ p ∈ Icc (p₀ (domain₂ e)) (p₀ (domain₂ e) + D),
      ∀ q ∈ Icc (q₀ (domain₂ e)) (q₀ (domain₂ e) + D),
        |parameterPredictor (h₂ e) t p q| ≤ E := by
    intro e he t ht p hp q hq
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
    obtain ⟨l, hl, hlg, hl3, hlsq⟩ := hSocc e₀ he₀
    have hl0 : ⌊cfg.b k l 0 / D⌋ = e₀.2.2 0 := by
      have := congrFun hlsq 0; simpa using this
    have hl1 : ⌊cfg.b k l 1 / D⌋ = e₀.2.2 1 := by
      have := congrFun hlsq 1; simpa using this
    have hocc : ∃ l ∈ cfg.B k s e₀.1,
        (∀ e, |cfg.b k l e| ≤ 2 * cfg.K k) ∧
        |cfg.b k l 3 - (e₀.2.1 : ℝ) * χ| ≤ χ ∧ |cfg.b k l 4 + cfg.b k l 0| ≤ χ ∧
        cfg.b k l 0 ∈ Icc ((e₀.2.2 0 : ℝ) * D) ((e₀.2.2 0 : ℝ) * D + D) ∧
        cfg.b k l 1 ∈ Icc ((e₀.2.2 1 : ℝ) * D) ((e₀.2.2 1 : ℝ) * D + D) := by
      refine ⟨l, hl, hlg.1, ?_, hlg.2, ?_, ?_⟩
      · have := abs_sub_floor_mul_le (w := cfg.b k l 3) hχ
        rwa [hl3] at this
      · have hm := mem_Icc_floor_mul (w := cfg.b k l 0) hD
        rw [hl0] at hm
        exact ⟨hm.1, by linarith [hm.2]⟩
      · have hm := mem_Icc_floor_mul (w := cfg.b k l 1) hD
        rw [hl1] at hm
        exact ⟨hm.1, by linarith [hm.2]⟩
    have hnb := na.parameter_square_norm h e₀.1 hχ1 hD.le hD1 ha1 hocc
    have htI : t ∈ I T (cfg.j k s e₀.1) := by
      rw [I_eq_Icc]
      have h' := ht
      change t ∈ Icc (((cfg.j k s e₀.1 : ℕ) : ℝ) / 2 ^ T)
        (((cfg.j k s e₀.1 : ℕ) : ℝ) / 2 ^ T + τ) at h'
      rwa [hτdef, block_add_timeLength] at h'
    have hval := hnb t htI p hp q hq
    change |parameterPredictor (Match3.nativeParam (na.L e₀.1) ((e₀.2.1 : ℝ) * χ)) t p q| ≤ E
    rw [← na.nativeParameter_eq]
    exact hval.trans hE200
  -- Static caps on the domains.
  have hcap : ∀ g σ, δ ≤ σ → σ ≤ 1 → ∀ (c : Fin 3 → ℤ) (j : ℤ),
      (μm.restrict {ω | reader ω = g})
        {ω | (fun e => ⌊(![ω.2, cfg.b k ω.1 0, cfg.b k ω.1 1] : Fin 3 → ℝ) e / δm⌋) = c ∧
          ⌊(cfg.b k ω.1 2 + ω.2 * cfg.b k ω.1 5) / σ⌋ = j} ≤
          ENNReal.ofReal (V g * σ ^ cfg.d * δm ^ 3) := by
    intro g σ hσ hσ1 c j
    exact domain_cap h μm hμρ hgood hpos hphys hδp hpδ hpm hmH hχm hχ1 g hσ hσ1 c j
  -- The reference budget.
  have hbudget : ((∑ x ∈ s₁, ENNReal.ofReal (τ * D ^ 2 * V (domain₁ x) * δ ^ cfg.d)) +
      (∑ e ∈ s₂, ENNReal.ofReal (τ * D ^ 2 * V (domain₂ e) * δ ^ cfg.d))) ≤
        ENNReal.ofReal (depthBudget cfg k s ζ δ) := by
    set a := cfg.hiddenWidth k s with hadef
    set c₀ := 4320 * cfg.K k * (2 * cfg.K k + 2) * (δ / a) ^ cfg.d with hc₀def
    have hc₀ : 0 ≤ c₀ := by positivity
    have hδd : δ ^ cfg.d = (δ / a) ^ cfg.d * a ^ cfg.d := by
      rw [Real.div_rpow hδ.le ha.le]
      field_simp
    let f : Fin H.count → ℝ := fun hh =>
      c₀ * (D ^ 2 * a ^ cfg.d * (cfg.velocityWeight k χ (H.tag hh 0)).toReal)
    have hf : ∀ hh, 0 ≤ f hh := fun hh => by positivity
    have hterm₁ : ∀ x ∈ s₁, ENNReal.ofReal (τ * D ^ 2 * V (domain₁ x) * δ ^ cfg.d) =
        ENNReal.ofReal (τ * f x.1) := by
      intro x hx
      have hw := (Finset.mem_filter.mp hx).2
      change ENNReal.ofReal (τ * D ^ 2 * domainDensity cfg k M (H.tag x.1 0) * δ ^ cfg.d) = _
      rw [domainDensity_of_ne k M hw, hδd]
      congr 1
      simp only [f, hc₀def]
      ring
    have hsum₁ : (∑ x ∈ s₁, ENNReal.ofReal (τ * D ^ 2 * V (domain₁ x) * δ ^ cfg.d)) ≤
        ENNReal.ofReal (c₀ * (cfg.N k ^ ζ * cfg.K k)) := by
      rw [Finset.sum_congr rfl hterm₁]
      calc _ ≤ ∑ x ∈ Finset.univ ×ˢ Finset.range (2 ^ T), ENNReal.ofReal (τ * f x.1) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = ∑ hh : Fin H.count, ENNReal.ofReal (f hh) := by
            rw [Finset.sum_product]
            refine Finset.sum_congr rfl (fun hh _ => ?_)
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hτdef, timeLength_eq, hTdef]
            push_cast
            field_simp
        _ = ENNReal.ofReal (∑ hh, f hh) :=
            (ENNReal.ofReal_sum_of_nonneg (fun hh _ => hf hh)).symm
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            simp only [f]
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (endpoint_reference_real h H) hc₀
    let g₂ : NativeParameterIndex (cfg.n k s) → ℝ := fun e =>
      c₀ * (τ * D ^ 2 * a ^ cfg.d * (cfg.velocityWeight k χ e.2.1).toReal)
    have hg₂ : ∀ e, 0 ≤ g₂ e := fun e => by positivity
    have hterm₂ : ∀ e ∈ s₂, ENNReal.ofReal (τ * D ^ 2 * V (domain₂ e) * δ ^ cfg.d) =
        ENNReal.ofReal (c₀ * (τ * D ^ 2 * a ^ cfg.d *
          (cfg.velocityWeight k χ e.2.1).toReal)) := by
      intro e he
      have hw := (Finset.mem_filter.mp he).2
      change ENNReal.ofReal (τ * D ^ 2 * domainDensity cfg k M e.2.1 * δ ^ cfg.d) = _
      rw [domainDensity_of_ne k M hw, hδd]
      congr 1
      simp only [hc₀def]
      ring
    have hsum₂ : (∑ e ∈ s₂, ENNReal.ofReal (τ * D ^ 2 * V (domain₂ e) * δ ^ cfg.d)) ≤
        ENNReal.ofReal (c₀ * (4096 * cfg.K k ^ 6)) := by
      rw [Finset.sum_congr rfl hterm₂]
      calc _ ≤ ∑ e ∈ S.image nativeCell, ENNReal.ofReal (c₀ * (τ * D ^ 2 * a ^ cfg.d *
              (cfg.velocityWeight k χ e.2.1).toReal)) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ ≤ ∑ e ∈ S, ENNReal.ofReal (g₂ e) :=
            Finset.sum_image_le_of_nonneg (fun _ _ => zero_le)
        _ = ENNReal.ofReal (∑ e ∈ S, g₂ e) :=
            (ENNReal.ofReal_sum_of_nonneg (fun e _ => hg₂ e)).symm
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            simp only [g₂]
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left hSbudget hc₀
    calc _ ≤ ENNReal.ofReal (c₀ * (cfg.N k ^ ζ * cfg.K k)) +
          ENNReal.ofReal (c₀ * (4096 * cfg.K k ^ 6)) := add_le_add hsum₁ hsum₂
      _ = ENNReal.ofReal (depthBudget cfg k s ζ δ) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          simp only [depthBudget, hc₀def, hadef]
          ring
  obtain ⟨ξ, hξ, hloss, L, hLsub, hLcard, hgoodξ⟩ :=
    HB (α × ℝ) (ℤ × ℤ × ℤ × ℕ) (Fin H.count × ℕ) (Fin (cfg.n k s) × ℤ × ℤ × ℤ)
      μm s₁ s₂ E₁ E₂ domain₁ domain₂ reader
      (fun ω => ω.2) (fun ω => cfg.b k ω.1 0) (fun ω => cfg.b k ω.1 1)
      (fun ω => cfg.b k ω.1 2 + ω.2 * cfg.b k ω.1 5)
      (fun x => H.coeff x.1) h₂ t₀ p₀ q₀ V τ D δ δm E A₀ A Mst
      (ENNReal.ofReal (depthBudget cfg k s ζ δ))
      hreader hT hP hQ hE₁m hE₂m hsub₁ hsub₂ huniq₁ huniq₂ hcover₁ hcover₂
      hτ hD hδ hδ1 hδm (fun g => domainDensity_pos h k M g.1) hE1 hA₀ hmτ hmD
      hMst hA1 hA2 hA hbox hfit₁ hfit₂ hnorm₁ hnorm₂ hcap hbudget hmass
  refine ⟨ξ, hξ, hloss, L, hLcard, ?_⟩
  filter_upwards [hgoodξ] with ω hω
  obtain ⟨x, hx, e, he, hωx, hωe, hdx, hde, hel, hcmp⟩ := hω
  have hJ : x.2 = (cfg.j k s e.1 : ℕ) := by
    have := hdx.trans hde.symm
    exact congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.2.2.2) this
  have hv : e.2.1 = H.tag x.1 0 := by
    have := hde.trans hdx.symm
    exact congrArg (fun g : ℤ × ℤ × ℤ × ℕ => g.1) this
  refine ⟨x.1, e.1, hωx.1, hωe.1, hωe.2.1, ⟨e, ?_, rfl⟩, ?_⟩
  · have hx' : x = (x.1, (cfg.j k s e.1 : ℕ)) := Prod.ext rfl hJ
    rw [← hx']
    exact hel
  · intro t ht p hp q hq
    have hpow : (0 : ℝ) < 2 ^ T := by positivity
    have hrt : t₀ (reader ω) = ((cfg.j k s e.1 : ℕ) : ℝ) / 2 ^ T := by
      show ((reader ω).2.2.2 : ℝ) / 2 ^ T = _
      rw [← hde]
    have hrp : p₀ (reader ω) = (H.tag x.1 1 : ℝ) * D := by
      show ((reader ω).2.1 : ℝ) * D = _
      rw [← hdx]
    have hrq : q₀ (reader ω) = (H.tag x.1 2 : ℝ) * D := by
      show ((reader ω).2.2.1 : ℝ) * D = _
      rw [← hdx]
    have htI := ht
    rw [I_eq_Icc] at htI
    have hτJ : (((cfg.j k s e.1 : ℕ) : ℝ) + 1) / 2 ^ T =
        ((cfg.j k s e.1 : ℕ) : ℝ) / 2 ^ T + τ := (block_add_timeLength k s _).symm
    have h1 : |t - (t₀ (reader ω) + τ / 2)| ≤ 4 * τ := by
      rw [hrt, abs_le]
      constructor <;> linarith [htI.1, htI.2]
    have h2 : |p - (p₀ (reader ω) + D / 2)| ≤ 4 * D := by
      have hp2 : ((H.tag x.1 1 : ℝ) + 1) * D = (H.tag x.1 1 : ℝ) * D + D := by ring
      rw [hrp, abs_le]
      constructor <;> linarith [hp.1, hp.2]
    have h3 : |q - (q₀ (reader ω) + D / 2)| ≤ 4 * D := by
      have hq2 : ((H.tag x.1 2 : ℝ) + 1) * D = (H.tag x.1 2 : ℝ) * D + D := by ring
      rw [hrq, abs_le]
      constructor <;> linarith [hq.1, hq.2]
    have hc := (hcmp t p q h1 h2 h3).le
    change |parameterPredictor (H.coeff x.1) t p q -
      parameterPredictor (Match3.nativeParam (na.L e.1) ((e.2.1 : ℝ) * χ)) t p q| ≤ 10 * Mst at hc
    rw [← na.nativeParameter_eq, hv, abs_sub_comm] at hc
    exact hc

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing
