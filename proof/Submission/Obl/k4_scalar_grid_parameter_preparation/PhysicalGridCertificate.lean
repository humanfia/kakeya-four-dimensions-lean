/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarPhysicalPreparation.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.SequencePhysicalCore
import Submission.Obl.k4_scalar_grid_parameter_preparation.SequencePartitionFloors
import Submission.Obl.k4_scalar_grid_parameter_preparation.InheritedPhysicalCounts

/-! Physical support and hereditary counts, retaining the registered finite-grid stage.
This strengthens ScalarPhysicalPreparation by preserving the finite-grid information
already present in its construction. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal

theorem exists_scalar_physical_preparation_on_grid {X : Type*} [MeasurableSpace X]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (W : ℕ → ℕ) (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (ν : (k : ℕ) → Fin (W k) → Measure X)
    (ρ : (k : ℕ) → Fin (W k) → Measure (X × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ)
    (E₀ : (k : ℕ) → Fin (W k) → Set (X × ℝ)) (d S : ℝ) (hS : 0 < S)
    (hbase : ∀ k g, IsProbabilityMeasure (ν k g) ∧ MeasurableSet (E₀ k g) ∧
      ∀ p ∈ E₀ k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a p.1 e| ≤ K k)
    (hfinite : ∀ k g, IsFiniteMeasure (ρ k g))
    (hcaps : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ScalarOriginalCapsAt N K W ρ π a d S R k)
    (hpure : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g r, R⁻¹ ≤ r → r ≤ R → ∀ q,
      ρ k g {p | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a p) = q} ≤
        ENNReal.ofReal (K k * N k ^ (-((2 + d) * r))))
    (hpackets : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ScalarPacketSequenceAt N K W ν ρ a d R k) :
    ∃ (H : ℕ → ℝ) (M : ℕ → ℕ) (E : (k : ℕ) → Fin (W k) → Set (X × ℝ)),
      ((∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      (∀ k, 1 ≤ M k ∧ N k ^ (1 / (M k : ℝ)) ≤ H k) ∧
      (∀ k g, MeasurableSet (E k g) ∧ E k g ⊆ E₀ k g) ∧
      (∀ᶠ k in atTop, ∀ g, ρ k g (E₀ k g \ E k g) ≤ ENNReal.ofReal (2 / (100 * K k))) ∧
      (∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ),
        R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) →
        (physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g)).Finite ∧
        ((physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g)).ncard : ℝ) ≤
          H k * N k ^ ((2 + d) * r) ∧
        (∀ p ∈ E k g, ENNReal.ofReal (N k ^ (-((2 + d) * r)) / H k) ≤
          ρ k g (E k g ∩ {p' | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a p') =
            physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a p)})) ∧
        ∀ r₀ : ℝ, R⁻¹ ≤ r₀ → r₀ ≤ r → (∃ m : ℕ, r₀ = (m : ℝ) / (M k : ℝ)) →
          ∀ (Z : Set (X × ℝ)), Z ⊆ E k g → ∀ q₀ : Fin 3 → ℤ,
            {q : Fin 3 → ℤ | (ρ k g).restrict Z {p |
              physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a p) = q ∧
              physicalScalarGridTag (N k ^ (-r₀)) (scalarPacketPosition a p) = q₀} ≠ 0}.Finite ∧
            ({q : Fin 3 → ℤ | (ρ k g).restrict Z {p |
              physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a p) = q ∧
              physicalScalarGridTag (N k ^ (-r₀)) (scalarPacketPosition a p) = q₀} ≠ 0}.ncard : ℝ) ≤
                H k * N k ^ ((2 + d) * (r - r₀))) ∧
      ∃ J : ℕ → ℕ, (∀ k, 2 ≤ J k ∧ M k = J k ^ 2) ∧ Tendsto J atTop atTop ∧
        ∀ᶠ k in atTop, ((positiveScaleGrid (M k) (J k)).card : ℝ) ≤ H k ∧
          ∀ g, ∀ r ∈ positiveScaleGrid (M k) (J k),
            (physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g)).Finite ∧
            ((physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g)).ncard : ℝ) ≤
              H k * N k ^ ((2 + d) * r) ∧
            ∀ p ∈ E k g, ENNReal.ofReal (N k ^ (-((2 + d) * r)) / H k) ≤
              ρ k g (E k g ∩ {p' | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a p') =
                physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a p)}) := by
  letI (k : ℕ) (g : Fin (W k)) : IsFiniteMeasure (ρ k g) := hfinite k g
  have hN₁ (k) : 1 ≤ N k := by linarith [hN k]
  have hNpos (k) : 0 < N k := by linarith [hN k]
  obtain ⟨H₀,M,A,hH₀,hM,hA,hAloss,hAcount,J,hJM,hJt,hstage⟩ :=
    exists_scalar_physical_grid_preparation N K hN hNt hK W a ha ν ρ π E₀ d S hS hbase hcaps hpackets
  let Γ : ℕ → Finset ℝ := fun k => positiveScaleGrid (M k) (J k)
  let code : ℕ → ℝ → X × ℝ → Fin 3 → ℤ :=
    fun k r p => physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a p)
  have hcode (k r) : Measurable (code k r) := by
    apply Measurable.of_eval
    intro i
    dsimp only [code,physicalScalarGridTag]
    have hm := measurable_scalarPacketPosition ha
    fun_prop
  have hstage' : ∀ᶠ k in atTop, ((Γ k).card : ℝ) ≤ H₀ k ∧
      ∀ g, ∀ r ∈ Γ k, (code k r '' A k g).Finite ∧
        ((code k r '' A k g).ncard : ℝ) ≤ H₀ k * N k ^ ((2 + d) * r) := by
    filter_upwards [hstage] with k hk
    refine ⟨?_,?_⟩
    · have hc : ((Γ k).card : ℝ) ≤ (J k : ℝ) ^ 3 := by
        dsimp [Γ]
        rw [(hJM k).2]
        exact_mod_cast scalarStageGrid_card_le (J k)
      exact hc.trans hk.1
    · intro g r hr
      simpa only [Set.image_image] using hk.2 g r hr
  obtain ⟨P,E,hP,hE,hfloor⟩ := exists_sequence_partition_floors N K H₀ hN hNt hK hH₀ W ρ A
    (fun k g => ⟨(hA k g).1,measure_ne_top (ρ k g) (A k g)⟩) Γ code
    (fun k r c => measurableSet_eq_fun (hcode k r) measurable_const) d hstage'
  let C : ℕ → ℝ := fun k => K k * (27 * P k)
  have hC := Submission.Obl.k4_tempered_grid_selection.subpower_mul hNpos hK
    (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
      hN₁ hNt hP (by norm_num : (1 : ℝ) ≤ 27) 1)
  have hC' : Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower N C := by
    simpa only [Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower,
      Submission.Obl.k4_tempered_grid_selection.Subpower,C,pow_one] using hC
  let H : ℕ → ℝ := fun k => max (H₀ k) (max (P k) (C k))
  have hH := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hH₀
    (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hP hC')
  have hH₀H (k) : H₀ k ≤ H k := le_max_left _ _
  have hPH (k) : P k ≤ H k := (le_max_left _ _).trans (le_max_right _ _)
  have hCH (k) : 27 * K k * P k ≤ H k := by
    calc
      _ = C k := by dsimp [C]; ring
      _ ≤ _ := (le_max_right _ _).trans (le_max_right _ _)
  have hPpos (k) : 0 < P k := zero_lt_one.trans_le (hP.1 k)
  have hJRt : Tendsto (fun k => (J k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hJt
  refine ⟨H,M,E,hH,fun k => ⟨(hM k).1,(hM k).2.trans (hH₀H k)⟩,
    fun k g => ⟨(hE k g).1,(hE k g).2.trans (hA k g).2⟩,?_,?_,?_⟩
  · filter_upwards [hAloss,hfloor] with k hk hf
    intro g
    have hcover : E₀ k g \ E k g ⊆ (E₀ k g \ A k g) ∪ (A k g \ E k g) := by
      intro p hp
      by_cases ha : p ∈ A k g
      · exact Or.inr ⟨ha,hp.2⟩
      · exact Or.inl ⟨hp.1,ha⟩
    calc
      _ ≤ ρ k g (E₀ k g \ A k g) + ρ k g (A k g \ E k g) :=
        (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (1 / (100 * K k)) + ENNReal.ofReal (1 / (100 * K k)) :=
        add_le_add (hk g) (hf g).1
      _ = _ := by
        have hε : 0 ≤ 1 / (100 * K k) := div_nonneg (by norm_num)
          (mul_nonneg (by norm_num) (zero_le_one.trans (hK.1 k)))
        rw [← ENNReal.ofReal_add hε hε]
        congr 1
        ring
  · intro R hR
    filter_upwards [hAcount R hR,hfloor,hpure R hR,hJRt.eventually_ge_atTop R] with k hc hf hp hJ
    intro g r hr hr' hgrid
    have hrpos : 0 < r := (inv_pos.mpr (by linarith : 0 < R)).trans_le hr
    have hmem : r ∈ Γ k := mem_positiveScaleGrid_of_grid_scale
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (hM k).1) hrpos (hr'.trans hJ) hgrid
    have hcount := hc g r hr hr' hgrid
    have himage : physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' E k g) ⊆
        physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition a '' A k g) :=
      Set.image_mono (Set.image_mono (hE k g).2)
    have hfin := hcount.1.subset himage
    have hmass := (hf g).2 r hmem
    refine ⟨hfin,?_,?_,?_⟩
    · exact (Nat.cast_le.mpr (Set.ncard_le_ncard himage hcount.1)).trans
        (hcount.2.trans (mul_le_mul_of_nonneg_right (hH₀H k) (Real.rpow_nonneg (hNpos k).le _)))
    · intro p hpoint
      exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
        (Real.rpow_nonneg (hNpos k).le _) (hPpos k) (hPH k))).trans (hmass p hpoint)
    · intro r₀ hr₀ hr₀' hgrid₀ Z hZ q₀
      have hh := inherited_physical_power_count (ρ k g) (scalarPacketPosition a)
        (measurable_scalarPacketPosition ha) (E k g) Z (hE k g).1 hZ
        (N k) (K k) (P k) d r r₀ (hN₁ k) (zero_le_one.trans (hK.1 k)) (hPpos k)
        hr₀' hfin hmass (hp g r₀ hr₀ (hr₀'.trans hr')) q₀
      exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_right (hCH k) (Real.rpow_nonneg (hNpos k).le _))⟩

  · refine ⟨J,hJM,hJt,?_⟩
    filter_upwards [hstage',hfloor] with k hs hf
    refine ⟨hs.1.trans (hH₀H k),?_⟩
    intro g r hr
    have hc := hs.2 g r hr
    have hsub : code k r '' E k g ⊆ code k r '' A k g := Set.image_mono (hE k g).2
    have hfin := hc.1.subset hsub
    have hcard : ((code k r '' E k g).ncard : ℝ) ≤ H k * N k ^ ((2 + d) * r) :=
      (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hc.1)).trans
        (hc.2.trans (mul_le_mul_of_nonneg_right (hH₀H k) (Real.rpow_nonneg (hNpos k).le _)))
    refine ⟨?_,?_,?_⟩
    · simpa only [code,Set.image_image] using hfin
    · simpa only [code,Set.image_image] using hcard
    · intro p hp
      exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
        (Real.rpow_nonneg (hNpos k).le _) (hPpos k) (hPH k))).trans ((hf g).2 r hr p hp)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
