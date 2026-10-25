import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.ModelDefs

/-!
# Masses of the labels of the synthetic model

A label is measurable, its incidences over its block keep at least half of its prior times the
block length, the slope bins inside a label carry at most the prior times the block length
times the palette mass, almost every incidence lies in a label of every level, and the labels
of a finer level sit inside labels of a coarser one. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

namespace Synth

variable (S : Synth)

theorem measurableSet_sA (d : ℕ) (L : S.Label d) : MeasurableSet (S.sA d L) := by
  have h0 : Measurable (fun l : ℕ × (Fin 6 → ℝ) => l.2 0) :=
    (measurable_pi_apply 0).comp measurable_snd
  have h1 : Measurable (fun l : ℕ × (Fin 6 → ℝ) => l.2 1) :=
    (measurable_pi_apply 1).comp measurable_snd
  have h2 : Measurable (fun l : ℕ × (Fin 6 → ℝ) => l.2 2) :=
    (measurable_pi_apply 2).comp measurable_snd
  have h3 : Measurable (fun l : ℕ × (Fin 6 → ℝ) => l.2 3) :=
    (measurable_pi_apply 3).comp measurable_snd
  have hi : MeasurableSet {l : ℕ × (Fin 6 → ℝ) | l.1 < S.M ∧
      pre S.e₁ S.G (S.Gh d) l.1 = (L.2.2.2 : ℕ)} :=
    measurable_fst (MeasurableSet.of_discrete : MeasurableSet {i : ℕ | i < S.M ∧
      pre S.e₁ S.G (S.Gh d) i = (L.2.2.2 : ℕ)})
  exact ((h0.add (measurable_const.mul ((measurable_const_mul _).comp h3))) measurableSet_Ico).inter
    ((h3 measurableSet_Icc).inter ((h1 measurableSet_Ico).inter ((h2 measurableSet_Icc).inter hi)))

theorem nu_sA_eq (d : ℕ) (hd : d ≤ S.D) (L : S.Label d) :
    S.nu (S.sA d L) =
      ((idx S.M).prod U) (S.Aidx d L) * (ENNReal.ofReal (S.q d) * U (S.Ax2 d L)) := by
  rw [S.nu_sA d L (S.measurableSet_sA d L), S.P_sA d hd L]

theorem volume_blockI (T : ℕ) (j : Fin (2 ^ T)) :
    volume (blockI T j) = ENNReal.ofReal (1 / 2 ^ T) := by
  rw [blockI, Real.volume_Icc]
  congr 1
  field_simp
  ring

/-- **Label floor.** -/
theorem floor_label (hBD : 30 * (S.D + 1) ≤ 2 ^ S.B) (d : ℕ) (hd : d ≤ S.D) (L : S.Label d) :
    (1 / 2 : ENNReal) * S.nu (S.sA d L) * ENNReal.ofReal (1 / 2 ^ S.T d) ≤
      S.mu (S.sA d L ×ˢ blockI (S.T d) L.1) := by
  have hm := S.measurableSet_sA d L
  have hE : MeasurableSet (S.sA d L ×ˢ blockI (S.T d) L.1) := hm.prod measurableSet_Icc
  rw [S.mu_apply hE, S.nu_sA d L hm]
  have hE' : MeasurableSet (S.Good ∩ Prod.map emb id ⁻¹' (S.sA d L ×ˢ blockI (S.T d) L.1)) :=
    S.measurableSet_Good.inter (measurable_embid hE)
  rw [Measure.prod_apply_symm hE']
  set I := Ico (((L.1 : ℕ) : ℝ) / 2 ^ S.T d) ((((L.1 : ℕ) : ℝ) + 1) / 2 ^ S.T d) with hI
  have hvol : volume I = ENNReal.ofReal (1 / 2 ^ S.T d) := by
    rw [hI, Real.volume_Ico]
    congr 1
    field_simp
    ring
  calc (1 / 2 : ENNReal) * P S.M (emb ⁻¹' S.sA d L) * ENNReal.ofReal (1 / 2 ^ S.T d)
      = ∫⁻ t, I.indicator (fun _ => (1 / 2 : ENNReal) * P S.M (emb ⁻¹' S.sA d L)) t := by
        rw [lintegral_indicator_const measurableSet_Ico, hvol]
    _ ≤ ∫⁻ t, P S.M ((fun ω => (ω, t)) ⁻¹'
          (S.Good ∩ Prod.map emb id ⁻¹' (S.sA d L ×ˢ blockI (S.T d) L.1))) := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ I
        · rw [indicator_of_mem ht]
          have hp : (0 : ℝ) < 2 ^ S.T d := by positivity
          have ht01 : t ∈ Ico (0 : ℝ) 1 := by
            refine ⟨le_trans (by positivity) ht.1, lt_of_lt_of_le ht.2 ?_⟩
            rw [div_le_one hp]
            exact_mod_cast L.1.2
          have hblk : S.blk d t = L.1 := S.blk_eq_of_mem ht
          refine le_trans (S.good_floor hBD d hd L ht01 hblk) (measure_mono ?_)
          rintro ω ⟨hg, hA⟩
          exact ⟨hg, hA, Ico_subset_Icc_self ht⟩
        · rw [indicator_of_notMem ht]
          exact bot_le

/-- **Label cap.** -/
theorem cap_label (d : ℕ) (hd : d ≤ S.D) (L : S.Label d) {V : Set ℝ} (hV : MeasurableSet V) :
    S.mu {x | x.1 ∈ S.sA d L ∧ x.2 ∈ blockI (S.T d) L.1 ∧ S.β * x.1.2 3 ∈ V} ≤
      ENNReal.ofReal (1 / 2 ^ S.T d) * S.nu (S.sA d L) * S.pal V := by
  have hm := S.measurableSet_sA d L
  have hW : MeasurableSet {l : ℕ × (Fin 6 → ℝ) | S.β * l.2 3 ∈ V} :=
    ((measurable_const_mul _).comp ((measurable_pi_apply 3).comp measurable_snd)) hV
  have hA' : MeasurableSet (S.sA d L ∩ {l | S.β * l.2 3 ∈ V}) := hm.inter hW
  have hnu : S.nu (S.sA d L ∩ {l | S.β * l.2 3 ∈ V}) ≤ S.nu (S.sA d L) * S.pal V := by
    rw [S.nu_sA_eq d hd L, nu, Measure.map_apply measurable_emb hA', S.pal_apply hV]
    have hsub : emb ⁻¹' (S.sA d L ∩ {l | S.β * l.2 3 ∈ V}) ⊆ S.Aidx d L ×ˢ
        ({p : ℝ × ℝ | p.1 + ((L.1 : ℕ) : ℝ) / 2 ^ S.T d * S.β * p.2 ∈
          Ico (S.cpos d L.2.1.1) (S.cpos d L.2.1.1 + S.q d) ∧ S.β * p.2 ∈ V} ×ˢ
          S.Ax2 d L) := by
      intro ω hω
      obtain ⟨hA, hV'⟩ := hω
      have h := (S.emb_preimage_sA d L ▸ hA : ω ∈ S.Aidx d L ×ˢ (S.Apos d L ×ˢ S.Ax2 d L))
      exact ⟨h.1, ⟨h.2.1.1, hV'⟩, h.2.2⟩
    refine (P_mono_prod S.M hsub).trans ?_
    have hsh := UU_shear_le (((L.1 : ℕ) : ℝ) / 2 ^ S.T d) S.β
      (measurableSet_Ico (a := S.cpos d L.2.1.1) (b := S.cpos d L.2.1.1 + S.q d)) hV
    rw [Real.volume_Ico, add_sub_cancel_left] at hsh
    calc ((idx S.M).prod U) (S.Aidx d L) * ((U.prod U) {p : ℝ × ℝ | p.1 +
            ((L.1 : ℕ) : ℝ) / 2 ^ S.T d * S.β * p.2 ∈
            Ico (S.cpos d L.2.1.1) (S.cpos d L.2.1.1 + S.q d) ∧ S.β * p.2 ∈ V} *
            U (S.Ax2 d L))
        ≤ ((idx S.M).prod U) (S.Aidx d L) *
            ((ENNReal.ofReal (S.q d) * U {u | S.β * u ∈ V}) * U (S.Ax2 d L)) := by
          gcongr
      _ = ((idx S.M).prod U) (S.Aidx d L) * (ENNReal.ofReal (S.q d) * U (S.Ax2 d L)) *
            U {u | S.β * u ∈ V} := by ring
  calc S.mu {x | x.1 ∈ S.sA d L ∧ x.2 ∈ blockI (S.T d) L.1 ∧ S.β * x.1.2 3 ∈ V}
      ≤ S.mu ((S.sA d L ∩ {l | S.β * l.2 3 ∈ V}) ×ˢ blockI (S.T d) L.1) :=
        measure_mono fun x hx => ⟨⟨hx.1, hx.2.2⟩, hx.2.1⟩
    _ ≤ (S.nu.prod volume) ((S.sA d L ∩ {l | S.β * l.2 3 ∈ V}) ×ˢ blockI (S.T d) L.1) :=
        S.mu_le _
    _ = S.nu (S.sA d L ∩ {l | S.β * l.2 3 ∈ V}) * volume (blockI (S.T d) L.1) :=
        Measure.prod_prod _ _
    _ ≤ S.nu (S.sA d L) * S.pal V * ENNReal.ofReal (1 / 2 ^ S.T d) := by
        rw [volume_blockI]
        gcongr
    _ = ENNReal.ofReal (1 / 2 ^ S.T d) * S.nu (S.sA d L) * S.pal V := by ring

/-- **Coverage.** -/
theorem cover_label (d : ℕ) (hd : d ≤ S.D) :
    ∀ᵐ x ∂S.mu, ∃ L : S.Label d, x.1 ∈ S.sA d L ∧ x.2 ∈ blockI (S.T d) L.1 := by
  have hQ : MeasurableSet {x : (ℕ × (Fin 6 → ℝ)) × ℝ |
      ∃ L : S.Label d, x.1 ∈ S.sA d L ∧ x.2 ∈ blockI (S.T d) L.1} := by
    have : {x : (ℕ × (Fin 6 → ℝ)) × ℝ | ∃ L : S.Label d, x.1 ∈ S.sA d L ∧
        x.2 ∈ blockI (S.T d) L.1} = ⋃ L : S.Label d, S.sA d L ×ˢ blockI (S.T d) L.1 := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_prod]
    rw [this]
    exact MeasurableSet.iUnion fun L => (S.measurableSet_sA d L).prod measurableSet_Icc
  exact S.ae_mu_of_good hQ fun q hq => S.good_cover hq hd

/-- **Nesting.** -/
theorem anc_exists {d d' : ℕ} (h : d ≤ d') (hd' : d' ≤ S.D) (L : S.Label d') :
    ∃ L' : S.Label d, S.sA d' L ⊆ S.sA d L' ∧ blockI (S.T d') L.1 ⊆ blockI (S.T d) L'.1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨S.anc d k hd' L, S.sA_anc d k hd' L⟩

end Synth

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
