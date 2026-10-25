import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.GoodFloor

/-!
# The measures of the synthetic model

The model lines are `emb ω`; their recorded coefficients are `sbS l = (b₀, b₁, hid, β u₃, 0, 0)`.
The prior is `P.map emb`, the incidence law is the product with time restricted to the good set
and pushed to lines, and the palette is the law of the slope `β u₃`. The good set carries at
least half of the unit time interval at every time (`good_mass`). Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

namespace Synth

variable (S : Synth)

/-- The recorded coefficients of a model line. -/
def sbS (l : ℕ × (Fin 6 → ℝ)) : Fin 6 → ℝ :=
  ![l.2 0, l.2 1, hid S.e S.e₁ S.G l.1 (l.2 2), S.β * l.2 3, 0, 0]

theorem measurable_sbS : Measurable S.sbS := by
  have hh : Measurable (fun l : ℕ × (Fin 6 → ℝ) => hid S.e S.e₁ S.G l.1 (l.2 2)) :=
    (measurable_hid S.e S.e₁ S.G).comp (measurable_fst.prodMk
      ((measurable_pi_apply 2).comp measurable_snd))
  refine measurable_pi_iff.mpr fun j => ?_
  fin_cases j
  · exact ((measurable_pi_apply 0).comp measurable_snd :
      Measurable fun l : ℕ × (Fin 6 → ℝ) => l.2 0)
  · exact ((measurable_pi_apply 1).comp measurable_snd :
      Measurable fun l : ℕ × (Fin 6 → ℝ) => l.2 1)
  · exact hh
  · exact ((measurable_const_mul _).comp ((measurable_pi_apply 3).comp measurable_snd) :
      Measurable fun l : ℕ × (Fin 6 → ℝ) => S.β * l.2 3)
  · exact measurable_const
  · exact measurable_const

theorem M_pos : 0 < S.M := by unfold M; positivity

scoped instance P_prob : IsProbabilityMeasure (P S.M) := P_isProb S.M S.M_pos

/-- The model prior. -/
def nu : Measure (ℕ × (Fin 6 → ℝ)) := (P S.M).map emb

scoped instance nu_prob : IsProbabilityMeasure S.nu := by
  unfold nu; infer_instance

/-- The model incidence law. -/
def mu : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  (((P S.M).prod (volume : Measure ℝ)).restrict S.Good).map (Prod.map emb id)

/-- The model palette. -/
def pal : Measure ℝ := U.map (fun u => S.β * u)

scoped instance pal_prob : IsProbabilityMeasure S.pal := by
  unfold pal; infer_instance

theorem pal_apply {V : Set ℝ} (hV : MeasurableSet V) : S.pal V = U {u | S.β * u ∈ V} := by
  rw [pal, Measure.map_apply (measurable_const_mul _) hV]
  rfl

theorem measurable_embid : Measurable (Prod.map emb (id : ℝ → ℝ)) :=
  measurable_emb.prodMap measurable_id

theorem prod_map_emb :
    ((P S.M).prod (volume : Measure ℝ)).map (Prod.map emb id) = S.nu.prod volume := by
  rw [nu, ← Measure.map_prod_map _ _ measurable_emb measurable_id, Measure.map_id]

theorem mu_le : S.mu ≤ S.nu.prod volume := by
  rw [← S.prod_map_emb, mu]
  exact Measure.map_mono Measure.restrict_le_self measurable_embid

theorem mu_apply {E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE : MeasurableSet E) :
    S.mu E = ((P S.M).prod (volume : Measure ℝ)) (S.Good ∩ Prod.map emb id ⁻¹' E) := by
  rw [mu, Measure.map_apply measurable_embid hE,
    Measure.restrict_apply (measurable_embid hE), inter_comm]

theorem measurable_τ (d : ℕ) : Measurable (S.τ d) := by
  unfold τ blk
  exact ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
    (Nat.measurable_floor.comp (measurable_id.mul_const _))).div_const _

theorem measurable_X (d : ℕ) : Measurable (S.X d) := by
  unfold X
  exact (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))).add
    (((S.measurable_τ d).comp measurable_snd).mul
      ((measurable_const_mul _).comp
        (measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))))

theorem measurable_cellOf (d : ℕ) : Measurable (S.cellOf d) := by
  unfold Grid.cellOf
  exact Nat.measurable_floor.comp ((measurable_id.sub_const _).div_const _)

theorem measurableSet_Good : MeasurableSet S.Good := by
  have h1 : MeasurableSet {p : Ω × ℝ | ∀ d ≤ S.D, S.β ≤ S.X d p ∧
      S.valid d (S.cellOf d (S.X d p))} := by
    have : {p : Ω × ℝ | ∀ d ≤ S.D, S.β ≤ S.X d p ∧ S.valid d (S.cellOf d (S.X d p))} =
        ⋂ d ∈ Finset.range (S.D + 1), ({p | S.β ≤ S.X d p} ∩
          (S.cellOf d ∘ S.X d) ⁻¹' {c | S.valid d c}) := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_inter_iff, mem_preimage,
        Function.comp_apply]
      constructor
      · intro h d hd; exact h d (by omega)
      · intro h d hd; exact h d (by omega)
    rw [this]
    refine Finset.measurableSet_biInter _ fun d _ => ?_
    exact (measurableSet_le measurable_const (S.measurable_X d)).inter
      (((S.measurable_cellOf d).comp (S.measurable_X d)) (MeasurableSet.of_discrete))
  unfold Good
  refine (measurable_snd measurableSet_Ico).inter ?_
  refine (((measurable_fst.comp measurable_fst).comp measurable_fst)
    (MeasurableSet.of_discrete : MeasurableSet {i : ℕ | i < S.M})).inter ?_
  refine (((measurable_snd.comp measurable_fst).comp measurable_fst) measurableSet_Icc).inter ?_
  refine (((measurable_snd.comp (measurable_fst.comp measurable_snd)).comp measurable_fst)
    measurableSet_Icc).inter ?_
  refine (((measurable_snd.comp measurable_snd).comp measurable_fst) measurableSet_Ico).inter ?_
  exact h1

/-- A measurable property of all good incidences holds `mu`-almost everywhere. -/
theorem ae_mu_of_good {Q : (ℕ × (Fin 6 → ℝ)) × ℝ → Prop} (hQ : MeasurableSet {x | Q x})
    (h : ∀ p ∈ S.Good, Q (emb p.1, p.2)) : ∀ᵐ x ∂S.mu, Q x := by
  rw [mu, ae_map_iff measurable_embid.aemeasurable hQ]
  exact ae_restrict_of_forall_mem S.measurableSet_Good fun p hp => h p hp

/-- The prior of a label. -/
theorem nu_sA (d : ℕ) (L : S.Label d) (hm : MeasurableSet (S.sA d L)) :
    S.nu (S.sA d L) = P S.M (emb ⁻¹' S.sA d L) := by
  rw [nu, Measure.map_apply measurable_emb hm]

/-- The root margin: a position at most `β` to the right of a uniform point misses
`[β, 1-β)` with probability at most `2β`. -/
theorem U_root_fail (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ S.β) :
    U {b | b + c ∉ Ico S.β (1 - S.β)} ≤ ENNReal.ofReal (2 * S.β) := by
  have hβ := S.β_pos
  have hβ2 := S.β_le_half
  have hsub : {b | b + c ∉ Ico S.β (1 - S.β)} ∩ Icc 0 1 ⊆
      Icc 0 1 \ Ico (S.β - c) (1 - S.β - c) := by
    rintro b ⟨hb, hb'⟩
    refine ⟨hb', fun h => hb ⟨by linarith [h.1], by linarith [h.2]⟩⟩
  have hIco : Ico (S.β - c) (1 - S.β - c) ⊆ Icc 0 1 := fun b hb =>
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
  calc U {b | b + c ∉ Ico S.β (1 - S.β)}
      = volume ({b | b + c ∉ Ico S.β (1 - S.β)} ∩ Icc 0 1) := by
        rw [Measure.restrict_apply' measurableSet_Icc]
    _ ≤ volume (Icc 0 1 \ Ico (S.β - c) (1 - S.β - c)) := measure_mono hsub
    _ = volume (Icc (0 : ℝ) 1) - volume (Ico (S.β - c) (1 - S.β - c)) :=
        measure_sdiff hIco measurableSet_Ico.nullMeasurableSet (by simp)
    _ = ENNReal.ofReal (2 * S.β) := by
        rw [Real.volume_Icc, Real.volume_Ico, ← ENNReal.ofReal_sub _ (by linarith)]
        congr 1; ring

/-- The global margin of level `d`. -/
theorem UU_fail_le (d : ℕ) (τ' : ℝ) :
    (U.prod U) {p : ℝ × ℝ | (Int.fract ((p.1 + τ' * (S.β * p.2) - S.β) / S.q d) <
        S.β + 1 / S.r d ∨ 1 - (2 * S.β + 1 / S.r d) ≤
          Int.fract ((p.1 + τ' * (S.β * p.2) - S.β) / S.q d)) ∧ p.2 ∈ Icc (0 : ℝ) 1} ≤
      ENNReal.ofReal (20 * S.β) := by
  have hβ := S.β_pos
  have hq := S.q_pos d
  have hr := S.inv_r_le d
  have hrp : (0 : ℝ) < S.r d := by exact_mod_cast S.r_pos d
  set N := 2 ^ S.T d with hN
  have hNq : (N : ℝ) * S.q d = 1 := by
    unfold Grid.q; rw [hN]; push_cast; field_simp
  have hq1 : S.q d ≤ 1 := by
    unfold Grid.q; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hm : Measurable (fun p : ℝ × ℝ => (p.1 + τ' * (S.β * p.2) - S.β) / S.q d) := by fun_prop
  have hmeas : MeasurableSet {p : ℝ × ℝ | (Int.fract ((p.1 + τ' * (S.β * p.2) - S.β) / S.q d) <
        S.β + 1 / S.r d ∨ 1 - (2 * S.β + 1 / S.r d) ≤
          Int.fract ((p.1 + τ' * (S.β * p.2) - S.β) / S.q d)) ∧ p.2 ∈ Icc (0 : ℝ) 1} :=
    ((measurableSet_lt (measurable_fract.comp hm) measurable_const).union
      (measurableSet_le measurable_const (measurable_fract.comp hm))).inter
      (measurable_snd measurableSet_Icc)
  calc _ ≤ ENNReal.ofReal (((N + 1 : ℕ) + 2) * (((S.β + 1 / S.r d) + (2 * S.β + 1 / S.r d)) *
        S.q d)) * U (Icc 0 1) := by
        refine UU_apply_le _ hmeas _ (Icc 0 1) ?_ ?_ measurableSet_Icc
        · intro u hu
          have hsec : {b | (b, u) ∈ {p : ℝ × ℝ | (Int.fract ((p.1 + τ' * (S.β * p.2) - S.β) /
              S.q d) < S.β + 1 / S.r d ∨ 1 - (2 * S.β + 1 / S.r d) ≤
                Int.fract ((p.1 + τ' * (S.β * p.2) - S.β) / S.q d)) ∧
                p.2 ∈ Icc (0 : ℝ) 1}} ∩ Icc 0 1 ⊆
              {b ∈ Ico 0 (0 + ((N + 1 : ℕ) : ℝ) * S.q d) |
                Int.fract ((b + (τ' * (S.β * u) - S.β)) / S.q d) < S.β + 1 / S.r d ∨
                1 - (2 * S.β + 1 / S.r d) ≤ Int.fract ((b + (τ' * (S.β * u) - S.β)) / S.q d)} := by
            rintro b ⟨⟨hb, -⟩, hb'⟩
            refine ⟨⟨hb'.1, ?_⟩, ?_⟩
            · push_cast; nlinarith [hb'.2]
            · convert hb using 3 <;> ring_nf
          calc U _ = volume (_ ∩ Icc 0 1) := Measure.restrict_apply' measurableSet_Icc
            _ ≤ _ := measure_mono hsec
            _ ≤ _ := vol_fract_bad_le _ _ 0 hq _ _ _ (by positivity) (by positivity)
        · intro u hu
          ext b
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          exact fun _ h => hu h
    _ = ENNReal.ofReal (((N + 1 : ℕ) + 2) * (((S.β + 1 / S.r d) + (2 * S.β + 1 / S.r d)) *
        S.q d)) := by simp [U]
    _ ≤ ENNReal.ofReal (20 * S.β) := by
        apply ENNReal.ofReal_le_ofReal
        push_cast
        have h3 : (S.β + 1 / S.r d) + (2 * S.β + 1 / S.r d) ≤ 5 * S.β := by linarith
        have h4 : ((N : ℝ) + 1 + 2) * S.q d ≤ 4 := by nlinarith
        have h5 : 0 ≤ (S.β + 1 / (S.r d : ℝ)) + (2 * S.β + 1 / S.r d) := by positivity
        nlinarith

/-- **Good mass.** At every time of `[0,1)`, at least half of the samples are good. -/
theorem good_mass (hBD : 64 * (S.D + 1) ≤ 2 ^ S.B) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (1 / 2 : ENNReal) ≤ P S.M {ω | (ω, t) ∈ S.Good} := by
  have hβ := S.β_pos
  have : IsProbabilityMeasure (idx S.M) := idx_isProb S.M S.M_pos
  set Gt := {ω : Ω | (ω, t) ∈ S.Good}
  have hGt : MeasurableSet Gt :=
    (measurable_id.prodMk measurable_const) S.measurableSet_Good
  set Sc : Set Ω := {ω | ¬ ω.1.1 < S.M} ∪ {ω | ω.1.2 ∉ Icc (0 : ℝ) 1} ∪
    {ω | ω.2.1.2 ∉ Icc (0 : ℝ) 1} ∪ {ω | ω.2.2 ∉ Ico (0 : ℝ) 1}
  set RF : Set Ω := {ω | S.X 0 (ω, t) ∉ Ico S.β (1 - S.β) ∧ ω.2.1.2 ∈ Icc (0 : ℝ) 1}
  set FG : ℕ → Set Ω := fun d => {ω | S.FailF d (ω, t) ∧ ω.2.1.2 ∈ Icc (0 : ℝ) 1}
  have hcov : Gtᶜ ⊆ Sc ∪ RF ∪ ⋃ d ∈ Finset.range S.D, FG d := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop, not_or, not_exists,
      not_and, Sc, RF, FG, mem_ofPred_eq, not_not] at hc
    obtain ⟨⟨⟨⟨⟨hi, hu2⟩, hu3⟩, hb1⟩, hroot⟩, hfail⟩ := hc
    apply hω
    have hX0 : S.X 0 (ω, t) ∈ Ico S.β (1 - S.β) := by
      by_contra h; exact hroot h hu3
    have hval0 : S.valid 0 (S.cellOf 0 (S.X 0 (ω, t))) := by
      show S.cellOf 0 (S.X 0 (ω, t)) < S.N₀
      unfold Grid.cellOf
      have hq := S.q_pos 0
      rw [Nat.floor_lt (div_nonneg (by linarith [hX0.1]) hq.le), div_lt_iff₀ hq, S.N₀_q]
      linarith [hX0.2]
    refine ⟨ht, hi, hu2, hu3, hb1, fun d hd => ?_⟩
    have := S.levels_gt 0 ht.1 hu3 ⟨hX0.1, hval0⟩ d
      (fun d'' _ h2 hF => hfail d'' (by omega) hF hu3)
    simpa using this
  -- the null support failures
  have hSc : P S.M Sc = 0 := by
    have h1 : P S.M {ω | ¬ ω.1.1 < S.M} = 0 := by
      refine le_antisymm ?_ bot_le
      calc P S.M {ω | ¬ ω.1.1 < S.M}
          ≤ ((idx S.M).prod U) ({i | ¬ i < S.M} ×ˢ univ) * ((U.prod U) univ * U univ) :=
            P_mono_prod S.M (fun ω hω => ⟨⟨hω, trivial⟩, trivial, trivial⟩)
        _ = 0 := by
            rw [Measure.prod_prod, idx_apply]
            have : {i : ℕ | ¬ i < S.M} ∩ Iio S.M = ∅ := by
              rw [Set.eq_empty_iff_forall_notMem]
              rintro i ⟨h1, h2⟩
              exact h1 h2
            rw [this]; simp
    have h2 : P S.M {ω | ω.1.2 ∉ Icc (0 : ℝ) 1} = 0 := by
      refine le_antisymm ?_ bot_le
      calc P S.M {ω | ω.1.2 ∉ Icc (0 : ℝ) 1}
          ≤ ((idx S.M).prod U) (univ ×ˢ (Icc 0 1)ᶜ) * ((U.prod U) univ * U univ) :=
            P_mono_prod S.M (fun ω hω => ⟨⟨trivial, hω⟩, trivial, trivial⟩)
        _ = 0 := by rw [Measure.prod_prod]; simp [U]
    have h3 : P S.M {ω | ω.2.1.2 ∉ Icc (0 : ℝ) 1} = 0 := by
      refine le_antisymm ?_ bot_le
      calc P S.M {ω | ω.2.1.2 ∉ Icc (0 : ℝ) 1}
          ≤ ((idx S.M).prod U) univ * ((U.prod U) (univ ×ˢ (Icc 0 1)ᶜ) * U univ) :=
            P_mono_prod S.M (fun ω hω => ⟨trivial, ⟨trivial, hω⟩, trivial⟩)
        _ = 0 := by rw [Measure.prod_prod]; simp [U]
    have h4 : P S.M {ω | ω.2.2 ∉ Ico (0 : ℝ) 1} = 0 := by
      refine le_antisymm ?_ bot_le
      calc P S.M {ω | ω.2.2 ∉ Ico (0 : ℝ) 1}
          ≤ ((idx S.M).prod U) univ * ((U.prod U) univ * U (Ico 0 1)ᶜ) :=
            P_mono_prod S.M (fun ω hω => ⟨trivial, trivial, hω⟩)
        _ = 0 := by
            have : U (Ico (0 : ℝ) 1)ᶜ = 0 := by
              rw [Measure.restrict_apply' measurableSet_Icc]
              refine measure_mono_null (t := {1}) ?_ (by simp)
              rintro x ⟨hx1, hx2⟩
              simp only [mem_compl_iff, mem_Ico, not_and, not_lt] at hx1
              simp only [mem_singleton_iff]
              exact le_antisymm hx2.2 (hx1 hx2.1)
            rw [this]; simp
    exact measure_union_null (measure_union_null (measure_union_null h1 h2) h3) h4
  have hRF : P S.M RF ≤ ENNReal.ofReal (2 * S.β) := by
    have hτ := S.τ_le 0 ht
    calc P S.M RF
        ≤ ((idx S.M).prod U) univ * ((U.prod U) {p : ℝ × ℝ | p.1 + S.τ 0 t * (S.β * p.2) ∉
            Ico S.β (1 - S.β) ∧ p.2 ∈ Icc (0 : ℝ) 1} * U univ) :=
          P_mono_prod S.M (fun ω hω => ⟨trivial, hω, trivial⟩)
      _ ≤ 1 * (ENNReal.ofReal (2 * S.β) * 1) := by
          gcongr
          · simp [U]
          · calc _ ≤ ENNReal.ofReal (2 * S.β) * U (Icc 0 1) := by
                  refine UU_apply_le _ ?_ _ (Icc 0 1) ?_ ?_ measurableSet_Icc
                  · exact (((measurable_fst.add (measurable_const.mul
                      ((measurable_const_mul _).comp measurable_snd)))
                      measurableSet_Ico).compl).inter (measurable_snd measurableSet_Icc)
                  · intro u hu
                    have hc0 : 0 ≤ S.τ 0 t * (S.β * u) :=
                      mul_nonneg hτ.1 (mul_nonneg hβ.le hu.1)
                    have hc : S.τ 0 t * (S.β * u) ≤ S.β := by
                      have : S.β * u ≤ S.β := by nlinarith [hu.2]
                      nlinarith [hτ.2]
                    refine le_trans (measure_mono ?_) (S.U_root_fail _ hc0 hc)
                    intro b hb; exact hb.1
                  · intro u hu; ext b; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false,
                      not_and]; exact fun _ h => hu h
              _ = ENNReal.ofReal (2 * S.β) := by simp [U]
          · simp [U]
      _ = ENNReal.ofReal (2 * S.β) := by simp
  have hFG : ∀ d, P S.M (FG d) ≤ ENNReal.ofReal (20 * S.β) := by
    intro d
    calc P S.M (FG d)
        ≤ ((idx S.M).prod U) univ * ((U.prod U) {p : ℝ × ℝ | (Int.fract ((p.1 + S.τ d t *
            (S.β * p.2) - S.β) / S.q d) < S.β + 1 / S.r d ∨ 1 - (2 * S.β + 1 / S.r d) ≤
              Int.fract ((p.1 + S.τ d t * (S.β * p.2) - S.β) / S.q d)) ∧
              p.2 ∈ Icc (0 : ℝ) 1} * U univ) := by
          refine P_mono_prod S.M (fun ω hω => ⟨trivial, ⟨?_, hω.2⟩, trivial⟩)
          obtain ⟨hF, -⟩ := hω
          unfold FailF X at hF
          rcases hF with h | h
          · left; exact h
          · right; linarith
      _ ≤ 1 * (ENNReal.ofReal (20 * S.β) * 1) := by
          gcongr
          · simp [U]
          · exact S.UU_fail_le d _
          · simp [U]
      _ = ENNReal.ofReal (20 * S.β) := by simp
  have hcompl : P S.M Gtᶜ ≤ 1 / 2 := by
    calc P S.M Gtᶜ ≤ P S.M (Sc ∪ RF ∪ ⋃ d ∈ Finset.range S.D, FG d) := measure_mono hcov
      _ ≤ P S.M (Sc ∪ RF) + P S.M (⋃ d ∈ Finset.range S.D, FG d) := measure_union_le _ _
      _ ≤ (P S.M Sc + P S.M RF) + ∑ d ∈ Finset.range S.D, P S.M (FG d) := by
          gcongr
          · exact measure_union_le _ _
          · exact measure_biUnion_finset_le _ _
      _ ≤ (0 + ENNReal.ofReal (2 * S.β)) +
            ∑ _d ∈ Finset.range S.D, ENNReal.ofReal (20 * S.β) := by
          rw [hSc]; gcongr with d hd; exact hFG d
      _ = ENNReal.ofReal ((2 + 20 * S.D) * S.β) := by
          rw [zero_add, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (1 / 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hB : (64 : ℝ) * (S.D + 1) ≤ 2 ^ S.B := by exact_mod_cast hBD
          have hβe : S.β = 1 / 2 ^ S.B := rfl
          rw [hβe, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
      _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have hsum := measure_add_measure_compl (μ := P S.M) hGt
  rw [measure_univ] at hsum
  calc (1 / 2 : ENNReal) = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
    _ ≤ 1 - P S.M Gtᶜ := tsub_le_tsub_left hcompl _
    _ = P S.M Gt := by
        rw [← hsum, ENNReal.add_sub_cancel_right (measure_ne_top _ _)]

/-- The good incidences have mass at least one half. -/
theorem mu_univ (hBD : 64 * (S.D + 1) ≤ 2 ^ S.B) : (1 / 2 : ENNReal) ≤ S.mu univ := by
  rw [S.mu_apply MeasurableSet.univ, preimage_univ, inter_univ,
    Measure.prod_apply_symm S.measurableSet_Good]
  calc (1 / 2 : ENNReal) = ∫⁻ _t in Ico (0 : ℝ) 1, (1 / 2 : ENNReal) := by simp
    _ ≤ ∫⁻ t in Ico (0 : ℝ) 1, P S.M ((fun ω => (ω, t)) ⁻¹' S.Good) :=
        setLIntegral_mono' measurableSet_Ico fun t ht => S.good_mass hBD ht
    _ ≤ ∫⁻ t, P S.M ((fun ω => (ω, t)) ⁻¹' S.Good) := setLIntegral_le_lintegral _ _

end Synth

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
