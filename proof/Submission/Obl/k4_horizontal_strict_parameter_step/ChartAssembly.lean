import Submission.Obl.k4_horizontal_strict_parameter_step.ChartPreparation
import Submission.Obl.k4_horizontal_strict_parameter_step.ChartPriorMass
import Submission.Obl.k4_horizontal_strict_parameter_step.ComparedLayer

/-!
# From a compared layer to a raw chart family (the chart half of the strict step)

The old labels whose current mass is at least half the average density (x0852's
`heavy_original_chart_priors`) carry dense prior mass. Each is prepared by `chart_prepared`
under its fixed conditional prior; its row and support count come unchanged from the compared
layer. The old floors bound the numerator budget by the total current mass.
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter

noncomputable section

/-- The conditional prior of a chart with positive original mass is a probability measure. -/
theorem RawChart.prior_isProbability {α : Type} [MeasurableSpace α] (C : RawChart α)
    {ν : Measure α} [IsFiniteMeasure ν] (hA0 : ν C.A ≠ 0) : IsProbabilityMeasure (C.prior ν) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [RawChart.prior, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hA0 (measure_ne_top ν C.A)

/-- The chart half of the strict step at one sample. -/
theorem rawChartFamily_of_compared {N : ℕ → ℝ} {d e₀ : ℝ} {α : Type} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] {μ ρ : Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {k : ℕ} [IsFiniteMeasure (π k)]
    {K δ ξ D a ζ m : ℝ}
    (L : ComparedLayer N d e₀ π b k ρ δ D a ζ)
    (hb : Measurable (b k)) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hN : 1 ≤ N k) (hδ : 0 < δ) (hK : 1 ≤ K) (hKδ : K ≤ N k ^ δ)
    (hloss : 806400 * N k ^ (6 * δ) ≤ N k ^ ξ)
    (hD : 0 < D) (hD1 : D ≤ 1) (ha : 0 < a) (hζ1 : ζ ≤ 1) (hm : 0 < m)
    (hm8 : 8 * N k ^ δ * m ≤ ζ) (hmD : (K + 2) * m ≤ D * ζ) (hχD : N k ^ (-e₀) ≤ D * ζ)
    (hma : m ≤ 2 * a * ζ) (ha1 : 2 * a ≤ 1)
    (hround : 2 * N k ^ δ * m + (6 * N k ^ δ / D) * (N k ^ (-e₀) + (K + 2) * m) ≤
      2 * a * ζ)
    (hμ : μ ≤ ENNReal.ofReal K • ν.prod volume) (hρ : ρ ≤ μ)
    (hμt : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hgood : ∀ᵐ p ∂μ, |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀) ∧ |b k p.1 0| ≤ K ∧
      |b k p.1 3| ≤ K)
    (hcap : MeshCapAt μ (π k) (b k) d K (N k ^ (-e₀)) m) :
    Nonempty (RawChartFamily α ν ρ (π k) (b k) d (N k) ξ (N k ^ (-e₀)) D a ζ) := by
  classical
  obtain ⟨hmeas, hdisj, hlab, hsuppH⟩ := L.layer
  set M : ℝ := N k ^ δ with hMdef
  have hNpos : 0 < N k := by linarith
  have hM1 : 1 ≤ M := Real.one_le_rpow hN hδ.le
  have hM0 : 0 < M := by linarith
  have hK0 : 0 < K := by linarith
  have hχ : 0 < N k ^ (-e₀) := Real.rpow_pos_of_pos hNpos _
  -- numerical consequences of the loss condition
  have hM6 : M ^ 6 = N k ^ (6 * δ) := by
    rw [hMdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num [mul_comm]
  have hMpow : M ≤ M ^ 6 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 6 := pow_le_pow_right₀ hM1 (by norm_num)
  have hξbig : 806400 * M ^ 6 ≤ N k ^ ξ := by rw [hM6]; exact hloss
  have hKM : K ≤ M := hKδ
  have hNξpos : 0 < N k ^ ξ := Real.rpow_pos_of_pos hNpos _
  have hM2 : M ^ 2 ≤ M ^ 6 := pow_le_pow_right₀ hM1 (by norm_num)
  have hMsq : 0 ≤ M ^ 2 := by positivity
  have hb1 : 8 * K * M ≤ N k ^ ξ := by nlinarith
  have hb2 : 2 * M ≤ N k ^ ξ := by nlinarith
  have hb3 : K * M ≤ N k ^ ξ := by nlinarith
  have hb4 : 4 * M ≤ N k ^ ξ := by nlinarith
  have hb5 : 201600 * K ^ 3 * M / ((M⁻¹) / 2) ^ 2 ≤ N k ^ ξ := by
    have heq : 201600 * K ^ 3 * M / ((M⁻¹) / 2) ^ 2 = 806400 * K ^ 3 * M ^ 3 := by
      field_simp
      ring
    rw [heq]
    have hK3 : K ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ hK0.le hKM 3
    have hM33 : M ^ 3 * M ^ 3 = M ^ 6 := by ring
    calc 806400 * K ^ 3 * M ^ 3 ≤ 806400 * M ^ 3 * M ^ 3 := by gcongr
      _ = 806400 * M ^ 6 := by ring
      _ ≤ N k ^ ξ := hξbig
  have hNnegδ : N k ^ (-δ) = M⁻¹ := by rw [hMdef, Real.rpow_neg hNpos.le]
  have hNnegξ : N k ^ (-ξ) = (N k ^ ξ)⁻¹ := Real.rpow_neg hNpos.le _
  -- the dense current law
  have hσμ : L.σ ≤ μ := L.σ_le.trans (L.ρH_le.trans hρ)
  have hμuniv : μ univ ≤ ENNReal.ofReal K := by
    have h1 : μ univ = μ (univ ×ˢ Icc (0 : ℝ) 1) := by
      rw [← measure_inter_add_sdiff univ (MeasurableSet.univ.prod measurableSet_Icc)]
      rw [univ_inter, sdiff_eq, univ_inter, hμt, add_zero]
    rw [h1]
    refine (hμ _).trans ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, Real.volume_Icc]
    simp
  haveI : IsFiniteMeasure μ := ⟨hμuniv.trans_lt ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure L.σ := ⟨((hσμ univ).trans hμuniv).trans_lt ENNReal.ofReal_lt_top⟩
  have hσK : L.σ ≤ ENNReal.ofReal K • ν.prod volume := hσμ.trans hμ
  have hcover : ∀ᵐ p ∂L.σ, ∃ i, p ∈ L.A i ×ˢ Icc (0 : ℝ) 1 := by
    have h1 : ∀ᵐ p ∂L.σ, ∃ i, p.1 ∈ L.A i := by
      rw [ae_iff]
      have : {a : α × ℝ | ¬∃ i, a.1 ∈ L.A i} = {p | ∃ i, p.1 ∈ L.A i}ᶜ := rfl
      rw [this]
      exact le_antisymm ((L.σ_le _).trans hsuppH.le) bot_le
    have h2 : ∀ᵐ p ∂L.σ, p ∈ univ ×ˢ Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      exact le_antisymm ((hσμ _).trans hμt.le) bot_le
    filter_upwards [h1, h2] with p hp1 hp2
    obtain ⟨i, hi⟩ := hp1
    exact ⟨i, hi, hp2.2⟩
  have hdisj' : Pairwise (fun i j => Disjoint (L.A i) (L.A j)) := fun i j hij => hdisj i j hij
  set δ' : ℝ := M⁻¹ / 2 with hδ'def
  have hδ' : 0 < δ' := by positivity
  obtain ⟨F, hF, hFmass⟩ := heavy_original_chart_priors ν L.σ L.A hmeas hdisj' hcover
    hK0.le hδ'.le hσK
  -- each heavy chart is prepared
  have hfloorK : ∀ i, ENNReal.ofReal (D ^ 2 * a ^ d / M) *
      π k (Ico ((L.q i 0 : ℝ) * N k ^ (-e₀)) (((L.q i 0 : ℝ) + 1) * N k ^ (-e₀))) ≤
        ENNReal.ofReal K * ν (L.A i) := by
    intro i
    refine (hlab i).2.2.2.trans ((L.ρH_le.trans hρ _).trans ((hμ _).trans ?_))
    rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, Real.volume_Icc]
    simp
  have hprep : ∀ i ∈ F, ∃ E' : Set (α × ℝ), MeasurableSet E' ∧ E' ⊆ L.E i ∧
      ENNReal.ofReal (δ' / (4 * K)) ≤
        (((⟨L.A i, L.q i, L.h i, L.F i, L.E i⟩ : RawChart α).prior ν).prod volume) E' ∧
      (ENNReal.ofReal (δ' / 2) * ν (L.A i)) •
        (((⟨L.A i, L.q i, L.h i, L.F i, L.E i⟩ : RawChart α).prior ν).prod volume).restrict E' ≤
        L.σ.restrict (L.A i ×ˢ Icc (0 : ℝ) 1) ∧
      ∀ t r w : ℝ, ζ ≤ r → r ≤ 1 → ζ ≤ w → w ≤ 1 → ∀ (z : Fin 2 → ℤ) (j : ℤ),
        ((⟨L.A i, L.q i, L.h i, L.F i, L.E i⟩ : RawChart α).prior ν)
          {l | (l, t) ∈ E' ∧
            ⌊FirstJet.xbar ((⟨L.A i, L.q i, L.h i, L.F i, L.E i⟩ : RawChart α).β (b k) a D)
              ((⟨L.A i, L.q i, L.h i, L.F i, L.E i⟩ : RawChart α).γ (b k) a D) l t / w⌋ = j ∧
            ⌊(⟨L.A i, L.q i, L.h i, L.F i, L.E i⟩ : RawChart α).y (b k) a D l 0 / r⌋ = z 0 ∧
            ⌊(⟨L.A i, L.q i, L.h i, L.F i, L.E i⟩ : RawChart α).y (b k) a D l 1 / r⌋ = z 1} ≤
          ENNReal.ofReal ((201600 * K ^ 3 * M / δ' ^ 2) * r ^ 2 * w ^ d) := by
    intro i hi
    obtain ⟨hpos, hheavy⟩ := hF i hi
    exact chart_prepared (μ := μ) (π := π k) (⟨L.A i, L.q i, L.h i, L.F i, L.E i⟩ : RawChart α)
      hb hd hd1 hK hM1 hD hD1 ha hm hχ hζ1 hδ' hm8 hmD hχD hma ha1 hround hσμ hμ
      (hmeas i) hpos.ne' hgood (hlab i).1 (hlab i).2.1 (hlab i).2.2.1 hcap (hfloorK i)
      (L.measurableSet_E i) (L.E_sub i) (L.conull i) hheavy
  choose E' hE'meas hE'sub hE'mass hE'lower hE'mix using hprep
  have hMξ : M ≤ N k ^ ξ := by nlinarith
  have hone : (1 : ℝ) ≤ N k ^ ξ := by nlinarith
  -- enumerate the heavy charts
  set e : Fin F.card → Fin L.n := fun j => (F.equivFin.symm j).1 with he
  have hemem : ∀ j, e j ∈ F := fun j => (F.equivFin.symm j).2
  have heinj : Function.Injective e := fun j₁ j₂ h =>
    F.equivFin.symm.injective (Subtype.ext h)
  have hsumF : ∀ g : Fin L.n → ENNReal, ∑ j, g (e j) = ∑ i ∈ F, g i := by
    intro g
    rw [← Finset.sum_coe_sort F g]
    exact F.equivFin.symm.sum_comp (fun x => g x.1)
  let chart : Fin F.card → RawChart α := fun j =>
    ⟨L.A (e j), L.q (e j), L.h (e j), L.F (e j), E' (e j) (hemem j)⟩
  refine ⟨⟨F.card, chart, ?_, ?_, ?_, ?_⟩⟩
  · intro j
    have hi : e j ∈ F := hemem j
    obtain ⟨hpos, -⟩ := hF (e j) hi
    obtain ⟨hgrid, hnorm, hfit, -⟩ := hlab (e j)
    have hbounds := RawChart.coords_bounds (chart j) (b := b k) ha hD hM0.le
      (fun l hl => ⟨(hgrid l hl).2.1, (hgrid l hl).2.2⟩) hfit
    have hlow : ENNReal.ofReal (N k ^ (-ξ)) ≤ ENNReal.ofReal (δ' / 2) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hNnegξ, hδ'def]
      rw [inv_le_comm₀ hNξpos (by positivity)]
      field_simp
      linarith
    refine
      { measurable_A := hmeas (e j)
        prior_pos := hpos
        probability := RawChart.prior_isProbability (chart j) hpos.ne'
        grid := hgrid
        norm := fun t ht p hp q hq => (hnorm t ht p hp q hq).trans hMξ
        fit := fun l hl t ht => (hfit l hl t ht).trans (mul_le_mul_of_nonneg_right hMξ ha.le)
        labeled := (hE'sub (e j) hi).trans (L.E_sub (e j))
        lower := ?_
        data := ?_ }
    · calc (ENNReal.ofReal (N k ^ (-ξ)) * ν (L.A (e j))) •
            (((chart j).prior ν).prod volume).restrict (E' (e j) hi)
          ≤ (ENNReal.ofReal (δ' / 2) * ν (L.A (e j))) •
            (((chart j).prior ν).prod volume).restrict (E' (e j) hi) := by
            gcongr
        _ ≤ L.σ.restrict (L.A (e j) ×ˢ Icc (0 : ℝ) 1) := hE'lower (e j) hi
        _ ≤ ρ.restrict (L.A (e j) ×ˢ Icc (0 : ℝ) 1) :=
            Measure.restrict_mono le_rfl (L.σ_le.trans L.ρH_le)
    · refine
        { measurable_y := (RawChart.measurable_coords (chart j) hb (hmeas (e j)) a D).1
          measurable_β := (RawChart.measurable_coords (chart j) hb (hmeas (e j)) a D).2.1
          measurable_γ := (RawChart.measurable_coords (chart j) hb (hmeas (e j)) a D).2.2
          measurable_F := L.measurable_F (e j)
          measurableSet_E := hE'meas (e j) hi
          subset_E := fun p hp => ⟨trivial, (L.E_sub (e j) (hE'sub (e j) hi hp)).2⟩
          bound_y := fun l c => ((hbounds l).1 c).trans hone
          bound_β := fun l => (hbounds l).2.1.trans hMξ
          bound_γ := fun l => (hbounds l).2.2.trans hb2
          bound_F := fun t c => (L.bound_F (e j) t c).trans hMξ
          mass := ?_
          mixedCap := ?_
          support := ?_ }
      · refine le_trans ?_ (hE'mass (e j) hi)
        apply ENNReal.ofReal_le_ofReal
        rw [hδ'def, inv_le_comm₀ hNξpos (by positivity)]
        field_simp
        linarith
      · intro t r w hr hr1 hw hw1 z i₀
        refine (hE'mix (e j) hi t r w hr hr1 hw hw1 z i₀).trans ?_
        apply ENNReal.ofReal_le_ofReal
        have hζ0 : 0 < ζ := by
          by_contra hcon
          push Not at hcon
          have : D * ζ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD.le hcon
          linarith
        have hr0 : 0 ≤ r := hζ0.le.trans hr
        have hw0 : 0 ≤ w := hζ0.le.trans hw
        have hb5' : 201600 * K ^ 3 * M / δ' ^ 2 ≤ N k ^ ξ := by rw [hδ'def]; exact hb5
        gcongr
      · intro t w hw hw1
        obtain ⟨C, hC, hmem⟩ := L.support (e j) t w hw hw1
        refine ⟨C, hC.trans ?_, fun l hl => hmem l (hE'sub (e j) hi hl)⟩
        have hζ0 : 0 < ζ := by
          by_contra hcon
          push Not at hcon
          have : D * ζ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD.le hcon
          linarith
        have hw0 : 0 < w := hζ0.trans_le hw
        exact mul_le_mul_of_nonneg_right hMξ (Real.rpow_nonneg hw0.le _)
  · intro j₁ j₂ hj
    exact hdisj (e j₁) (e j₂) (heinj.ne hj)
  · -- dense prior
    change ENNReal.ofReal (N k ^ (-ξ)) ≤ ∑ j, ν (L.A (e j))
    rw [hsumF (fun i => ν (L.A i))]
    have hσreal : M⁻¹ ≤ L.σ.real univ := by
      have h := L.σ_mass
      rw [hNnegδ] at h
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp h
    have hsum_nonneg : 0 ≤ ∑ i ∈ F, ν.real (L.A i) :=
      Finset.sum_nonneg (fun i _ => measureReal_nonneg)
    have hreal : (N k ^ ξ)⁻¹ ≤ ∑ i ∈ F, ν.real (L.A i) := by
      set S := ∑ i ∈ F, ν.real (L.A i) with hSdef
      have h1 : M⁻¹ / 2 ≤ K * S := by
        have := hFmass
        rw [hδ'def] at this
        linarith
      have h2 : 1 ≤ 2 * K * M * S := by
        have e1 : 2 * M * (M⁻¹ / 2) = 1 := by field_simp
        have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * M)
        calc (1 : ℝ) = 2 * M * (M⁻¹ / 2) := e1.symm
          _ ≤ 2 * M * (K * S) := h3
          _ = 2 * K * M * S := by ring
      have hS0 : 0 ≤ S := hsum_nonneg
      rw [inv_eq_one_div, div_le_iff₀ hNξpos]
      calc (1 : ℝ) ≤ 2 * K * M * S := h2
        _ ≤ N k ^ ξ * S := mul_le_mul_of_nonneg_right (by linarith) hS0
        _ = S * N k ^ ξ := mul_comm _ _
    rw [hNnegξ]
    calc ENNReal.ofReal (N k ^ ξ)⁻¹ ≤ ENNReal.ofReal (∑ i ∈ F, ν.real (L.A i)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ∑ i ∈ F, ν (L.A i) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · -- numerator budget
    change (∑ j, ENNReal.ofReal (D ^ 2 * a ^ d) *
      π k (Ico ((L.q (e j) 0 : ℝ) * N k ^ (-e₀)) (((L.q (e j) 0 : ℝ) + 1) * N k ^ (-e₀)))) ≤
        ENNReal.ofReal (N k ^ ξ)
    rw [hsumF (fun i => ENNReal.ofReal (D ^ 2 * a ^ d) *
      π k (Ico ((L.q i 0 : ℝ) * N k ^ (-e₀)) (((L.q i 0 : ℝ) + 1) * N k ^ (-e₀))))]
    have hterm : ∀ i ∈ F, ENNReal.ofReal (D ^ 2 * a ^ d) *
        π k (Ico ((L.q i 0 : ℝ) * N k ^ (-e₀)) (((L.q i 0 : ℝ) + 1) * N k ^ (-e₀))) ≤
        ENNReal.ofReal M * L.ρH (L.A i ×ˢ Icc (0 : ℝ) 1) := by
      intro i _
      have hfl := (hlab i).2.2.2
      have heq : ENNReal.ofReal (D ^ 2 * a ^ d) =
          ENNReal.ofReal M * ENNReal.ofReal (D ^ 2 * a ^ d / M) := by
        rw [← ENNReal.ofReal_mul hM0.le]
        congr 1
        field_simp
      rw [heq, mul_assoc]
      gcongr
    have hdisjF : (F : Set (Fin L.n)).PairwiseDisjoint (fun i => L.A i ×ˢ Icc (0 : ℝ) 1) := by
      intro i _ j _ hij
      exact Disjoint.set_prod_left (hdisj i j hij) _ _
    calc (∑ i ∈ F, ENNReal.ofReal (D ^ 2 * a ^ d) *
          π k (Ico ((L.q i 0 : ℝ) * N k ^ (-e₀)) (((L.q i 0 : ℝ) + 1) * N k ^ (-e₀))))
        ≤ ∑ i ∈ F, ENNReal.ofReal M * L.ρH (L.A i ×ˢ Icc (0 : ℝ) 1) :=
          Finset.sum_le_sum hterm
      _ = ENNReal.ofReal M * L.ρH (⋃ i ∈ F, L.A i ×ˢ Icc (0 : ℝ) 1) := by
          rw [← Finset.mul_sum, measure_biUnion_finset hdisjF
            (fun i _ => (hmeas i).prod measurableSet_Icc)]
      _ ≤ ENNReal.ofReal M * μ univ :=
          mul_le_mul_right ((measure_mono (subset_univ _)).trans ((L.ρH_le.trans hρ) univ)) _
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal (M * K) := (ENNReal.ofReal_mul hM0.le).symm
      _ ≤ ENNReal.ofReal (N k ^ ξ) := by
          apply ENNReal.ofReal_le_ofReal
          linarith

end

end Submission.Obl.k4_horizontal_strict_parameter_step
