import Submission.Obl.k4_horizontal_coefficient_count.LMCluster

/-!
# The light-mass estimate at one index and one depth

See `LMCluster.lean` for the argument.  `group_light_le` is the estimate for one
group; `light_mass_le` sums it over the finitely many groups of bounded
labels.
-/

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Covered incidences in unit time. -/
def DepthData.incSet (H : DepthData α) : Set (α × ℝ) :=
  {p | ∃ i, p.1 ∈ H.B i ∧ p.2 ∈ tblock H.q (H.j i)} ∩ (univ ×ˢ Icc (0 : ℝ) 1)

namespace DepthData.Hyp

variable {H : DepthData α}

theorem measurableSet_incSet (hH : H.Hyp) : MeasurableSet H.incSet := by
  have : {p : α × ℝ | ∃ i, p.1 ∈ H.B i ∧ p.2 ∈ tblock H.q (H.j i)} =
      ⋃ i, H.B i ×ˢ tblock H.q (H.j i) := by
    ext p; simp [mem_prod]
  unfold DepthData.incSet
  rw [this]
  exact (MeasurableSet.iUnion fun i => (hH.hB i).prod measurableSet_Icc).inter
    (MeasurableSet.univ.prod measurableSet_Icc)

theorem μ_incSet_compl (hH : H.Hyp) : H.μ H.incSetᶜ = 0 := by
  unfold DepthData.incSet
  rw [compl_inter]
  apply measure_union_null
  · have : {p : α × ℝ | ∃ i, p.1 ∈ H.B i ∧ p.2 ∈ tblock H.q (H.j i)}ᶜ =
        {p | ¬ ∃ i, p.1 ∈ H.B i ∧ p.2 ∈ tblock H.q (H.j i)} := by
      ext p; simp
    rw [this]
    exact hH.hcov
  · exact hH.hμsupp

end DepthData.Hyp

theorem group_light_le (H : DepthData α) (hH : H.Hyp) (G : Set α) (hG : MeasurableSet G)
    (hGg : G ⊆ goodSet H.b H.K H.χ) (g : ℤ × ℤ × ℤ) {Csupp Λ σ θ Z : ℝ}
    (hsupp : H.SupportCount Csupp) (hclust : ClusterOracle H.a H.d Λ σ)
    (hΛs : Csupp ≤ Λ) (hΛK : 2574 * H.K ^ 4 ≤ Λ) (hZσ : 1 < Z * σ) (hθ : 0 < θ)
    (hZ : 0 < Z) :
    H.ρ ((lmLight H.ρ H.π H.b H.χ H.a H.d Z G ∩ groupSet H.b H.χ H.a g) ×ˢ univ) ≤
      ENNReal.ofReal (H.a ^ 2 / (Λ * θ)) * H.π {x | ⌊x / H.χ⌋ = g.1} +
        ENNReal.ofReal (H.K * θ) * H.ν (groupSet H.b H.χ H.a g) := by
  classical
  have := hH.hν
  have := hH.hπ
  have hK := hH.hK
  have hK0 : 0 ≤ H.K := by linarith
  have ha := hH.ha0
  have hΛ : 0 < Λ := by
    have : 0 < H.K ^ 4 := by positivity
    linarith
  have hσ : 0 < σ := by
    by_contra h
    push_neg at h
    nlinarith
  set bin : Set ℝ := {x : ℝ | ⌊x / H.χ⌋ = g.1} with hbin
  set Gg := groupSet H.b H.χ H.a g with hGgdef
  have hGgm : MeasurableSet Gg := measurableSet_groupSet hH.hb _ _ g
  set Light := lmLight H.ρ H.π H.b H.χ H.a H.d Z G with hLight
  have hLm : MeasurableSet Light := measurableSet_lmLight _ _ hH.hb _ _ _ _ hG
  set Inc := H.incSet with hInc
  have hIncm : MeasurableSet Inc := hH.measurableSet_incSet
  set φ : α → ℝ≥0∞ := fun l => volume (Prod.mk l ⁻¹' Inc) with hφ
  have hφm : Measurable φ := measurable_measure_prodMk_left hIncm
  set Gθ := {l | ENNReal.ofReal θ ≤ φ l} with hGθ
  have hGθm : MeasurableSet Gθ := measurableSet_le measurable_const hφm
  set Λg := Light ∩ Gg ∩ Gθ with hΛg
  have hΛgm : MeasurableSet Λg := (hLm.inter hGgm).inter hGθm
  have hρμ : ∀ s, H.ρ s ≤ H.μ s := fun s => hH.hρμ s
  have hLG : Light ⊆ G := fun l hl => hl.1
  have hΛgG : Λg ×ˢ (univ : Set ℝ) ⊆ (G ∩ Gg) ×ˢ univ :=
    prod_mono (fun l hl => ⟨hLG hl.1.1, hl.1.2⟩) subset_rfl
  have hGGg : G ∩ Gg ⊆ Gg ∩ goodSet H.b H.K H.χ := fun l hl => ⟨hl.2, hGg hl.1⟩
  -- labels with little incidence time
  have hstepB : H.ρ ((Gg \ Gθ) ×ˢ univ) ≤ ENNReal.ofReal (H.K * θ) * H.ν Gg := by
    have hSm : MeasurableSet (Gg \ Gθ) := hGgm.diff hGθm
    have hm2 : MeasurableSet (((Gg \ Gθ) ×ˢ univ) ∩ Inc) :=
      (hSm.prod MeasurableSet.univ).inter hIncm
    calc H.ρ ((Gg \ Gθ) ×ˢ univ) ≤ H.μ ((Gg \ Gθ) ×ˢ univ) := hρμ _
      _ ≤ H.μ ((((Gg \ Gθ) ×ˢ univ) ∩ Inc) ∪ Incᶜ) := by
          apply measure_mono
          intro p hp
          by_cases h : p ∈ Inc
          · exact Or.inl ⟨hp, h⟩
          · exact Or.inr h
      _ ≤ H.μ (((Gg \ Gθ) ×ˢ univ) ∩ Inc) + H.μ Incᶜ := measure_union_le _ _
      _ = H.μ (((Gg \ Gθ) ×ˢ univ) ∩ Inc) := by rw [hH.μ_incSet_compl, add_zero]
      _ ≤ ENNReal.ofReal H.K * (H.ν.prod volume) (((Gg \ Gθ) ×ˢ univ) ∩ Inc) := by
          have := hH.hμν (((Gg \ Gθ) ×ˢ univ) ∩ Inc)
          simpa only [Measure.smul_apply, smul_eq_mul] using this
      _ = ENNReal.ofReal H.K *
            ∫⁻ l, volume (Prod.mk l ⁻¹' (((Gg \ Gθ) ×ˢ univ) ∩ Inc)) ∂H.ν := by
          rw [Measure.prod_apply hm2]
      _ ≤ ENNReal.ofReal H.K *
            ∫⁻ l, (Gg \ Gθ).indicator (fun _ => ENNReal.ofReal θ) l ∂H.ν := by
          gcongr with l
          by_cases hl : l ∈ Gg \ Gθ
          · rw [indicator_of_mem hl]
            have hpre : Prod.mk l ⁻¹' (((Gg \ Gθ) ×ˢ univ) ∩ Inc) = Prod.mk l ⁻¹' Inc := by
              ext t
              simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true]
              exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩
            rw [hpre]
            have h2 := hl.2
            simp only [hGθ, mem_setOf_eq, not_le] at h2
            exact h2.le
          · rw [indicator_of_notMem hl]
            have hpre : Prod.mk l ⁻¹' (((Gg \ Gθ) ×ˢ univ) ∩ Inc) = ∅ := by
              ext t
              simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true,
                mem_empty_iff_false, iff_false, not_and]
              exact fun h => absurd h hl
            rw [hpre, measure_empty]
      _ = ENNReal.ofReal H.K * (ENNReal.ofReal θ * H.ν (Gg \ Gθ)) := by
          rw [lintegral_indicator_const hSm]
      _ ≤ ENNReal.ofReal (H.K * θ) * H.ν Gg := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hK0]
          gcongr
          exact diff_subset
  -- the light part with long incidence time
  have hstepD : H.ρ (Λg ×ˢ univ) ≤ ENNReal.ofReal (H.a ^ 2 / (Λ * θ)) * H.π bin := by
    by_cases hπ0 : H.π bin = 0
    · have h1 : H.μ ((G ∩ Gg) ×ˢ univ) = 0 := by
        have := group_total_cap H hH g (G ∩ Gg) hGGg
        rw [← hbin, hπ0, mul_zero] at this
        exact le_antisymm this bot_le
      calc H.ρ (Λg ×ˢ univ) ≤ H.μ (Λg ×ˢ univ) := hρμ _
        _ ≤ H.μ ((G ∩ Gg) ×ˢ univ) := measure_mono hΛgG
        _ = 0 := h1
        _ ≤ _ := bot_le
    by_contra hlt
    push_neg at hlt
    set W : ℝ≥0∞ := ENNReal.ofReal (H.a ^ 2) * H.π bin with hW
    have hW0 : W ≠ 0 := by
      rw [hW]
      refine mul_ne_zero ?_ hπ0
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hWtop : W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have hWcancel : ∀ x : ℝ≥0∞, W⁻¹ * (x * W) = x := by
      intro x
      rw [mul_comm x W, ← mul_assoc, ENNReal.inv_mul_cancel hW0 hWtop, one_mul]
    set lam := H.ρ.fst with hlam
    have hlam_apply : ∀ s, MeasurableSet s → lam s = H.ρ (s ×ˢ univ) := by
      intro s hs
      rw [hlam, Measure.fst_apply hs, Set.prod_univ]
    set ν' : Measure α := W⁻¹ • lam.restrict Λg with hν'
    have hν'_apply : ∀ s, ν' s = W⁻¹ * lam (s ∩ Λg) := by
      intro s
      rw [hν', Measure.smul_apply, Measure.restrict_apply' hΛgm, smul_eq_mul]
    -- the coefficient map
    set f : α → EuclideanSpace ℝ (Fin 3) := fun l =>
      if l ∈ goodSet H.b H.K H.χ then !₂[H.b l 2, H.b l 5, 0] else 0 with hf
    have hfm : Measurable f := by
      apply Measurable.ite (measurableSet_goodSet hH.hb _ _)
      · have h2 : Measurable fun l => H.b l 2 := (measurable_pi_apply 2).comp hH.hb
        have h5 : Measurable fun l => H.b l 5 := (measurable_pi_apply 5).comp hH.hb
        fun_prop
      · exact measurable_const
    have hf_good : ∀ l ∈ goodSet H.b H.K H.χ,
        f l 0 = H.b l 2 ∧ f l 1 = H.b l 5 ∧ f l 2 = 0 := by
      intro l hl
      simp [hf, hl]
    -- the incidences
    set E' := (Λg ×ˢ univ) ∩ Inc with hE'
    have hE'm : MeasurableSet E' := (hΛgm.prod MeasurableSet.univ).inter hIncm
    obtain ⟨F, hFcard, hF⟩ := hsupp g
    have hΛg_le : lam Λg ≤ ENNReal.ofReal (2574 * H.K ^ 4) * W := by
      rw [hlam_apply _ hΛgm]
      calc H.ρ (Λg ×ˢ univ) ≤ H.μ (Λg ×ˢ univ) := hρμ _
        _ ≤ H.μ ((G ∩ Gg) ×ˢ univ) := measure_mono hΛgG
        _ ≤ ENNReal.ofReal (2574 * H.K ^ 4 * H.a ^ 2) * H.π bin :=
            group_total_cap H hH g (G ∩ Gg) hGGg
        _ = ENNReal.ofReal (2574 * H.K ^ 4) * W := by
            rw [hW, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have hν'univ : ν' univ ≤ ENNReal.ofReal (2574 * H.K ^ 4) := by
      rw [hν'_apply, univ_inter]
      calc W⁻¹ * lam Λg ≤ W⁻¹ * (ENNReal.ofReal (2574 * H.K ^ 4) * W) := by gcongr
        _ = ENNReal.ofReal (2574 * H.K ^ 4) := hWcancel _
    obtain ⟨qq, hqq⟩ := hclust α ν' f E' F hfm hE'm
      (by
        rintro p ⟨-, -, hp⟩
        exact hp)
      (by
        intro l
        by_cases hl : l ∈ goodSet H.b H.K H.χ
        · have hfl : f l = !₂[H.b l 2, H.b l 5, 0] := by simp [hf, hl]
          rw [hfl, EuclideanSpace.norm_eq]
          obtain ⟨-, -, h2, h25⟩ := hl
          have hb5 : |H.b l 5| ≤ 2 * H.K := by
            have : H.b l 5 = (H.b l 2 + H.b l 5) - H.b l 2 := by ring
            rw [this]
            linarith [abs_sub (H.b l 2 + H.b l 5) (H.b l 2)]
          rw [Real.sqrt_le_left hΛ.le]
          simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
          simp
          have h2' : H.b l 2 ^ 2 ≤ H.K ^ 2 := by
            have := sq_abs (H.b l 2) ▸ (pow_le_pow_left₀ (abs_nonneg _) h2 2)
            exact this
          have h5' : H.b l 5 ^ 2 ≤ (2 * H.K) ^ 2 := by
            have := sq_abs (H.b l 5) ▸ (pow_le_pow_left₀ (abs_nonneg _) hb5 2)
            exact this
          have hK4 : H.K ≤ H.K ^ 4 := le_self_pow₀ hK (by norm_num)
          have h3K : 3 * H.K ≤ Λ := by nlinarith
          have : 5 * H.K ^ 2 ≤ Λ ^ 2 := by nlinarith
          nlinarith
        · have hfl : f l = 0 := by simp [hf, hl]
          rw [hfl, norm_zero]
          exact hΛ.le)
      (hν'univ.trans (ENNReal.ofReal_le_ofReal hΛK))
      (by
        rw [Measure.prod_apply hE'm]
        have hgm : Measurable fun l => volume (Prod.mk l ⁻¹' E') :=
          measurable_measure_prodMk_left hE'm
        rw [hν', lintegral_smul_measure, smul_eq_mul]
        have h1 : ENNReal.ofReal θ * lam Λg ≤ ∫⁻ l in Λg, volume (Prod.mk l ⁻¹' E') ∂lam := by
          rw [← setLIntegral_const]
          apply setLIntegral_mono hgm
          intro l hl
          have hpre : Prod.mk l ⁻¹' E' = Prod.mk l ⁻¹' Inc := by
            ext t
            simp only [hE', mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true]
            exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩
          rw [hpre]
          exact hl.2
        have h2 : ENNReal.ofReal θ * (ENNReal.ofReal (H.a ^ 2 / (Λ * θ)) * H.π bin) =
            ENNReal.ofReal Λ⁻¹ * W := by
          rw [hW, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hθ.le,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
        calc ENNReal.ofReal Λ⁻¹ = W⁻¹ * (ENNReal.ofReal Λ⁻¹ * W) := (hWcancel _).symm
          _ = W⁻¹ * (ENNReal.ofReal θ * (ENNReal.ofReal (H.a ^ 2 / (Λ * θ)) * H.π bin)) := by
              rw [h2]
          _ ≤ W⁻¹ * (ENNReal.ofReal θ * lam Λg) := by
              rw [hlam_apply _ hΛgm]
              gcongr
          _ ≤ W⁻¹ * ∫⁻ l in Λg, volume (Prod.mk l ⁻¹' E') ∂lam := by gcongr)
      (hFcard.trans (mul_le_mul_of_nonneg_right hΛs (Real.rpow_nonneg ha.le _)))
      (by
        rintro l t ⟨⟨hl, -⟩, hinc, -, ht⟩
        have hlgood : l ∈ goodSet H.b H.K H.χ := hGg (hLG hl.1.1)
        obtain ⟨h0, h1, h2⟩ := hf_good l hlgood
        have := hF l ⟨hl.1.2, hlgood⟩ t ht hinc
        rw [h0, h1, h2]
        simpa [X3] using this)
      (by
        intro c r hr
        rw [hν'_apply]
        by_cases hr1 : 1 ≤ r
        · calc W⁻¹ * lam ({l | f l ∈ Metric.ball c r} ∩ Λg) ≤ W⁻¹ * lam Λg := by
                gcongr
                exact inter_subset_right
            _ = ν' univ := by rw [hν'_apply, univ_inter]
            _ ≤ ENNReal.ofReal (2574 * H.K ^ 4) := hν'univ
            _ ≤ ENNReal.ofReal (Λ * r ^ H.d) := by
                apply ENNReal.ofReal_le_ofReal
                have : 1 ≤ r ^ H.d := Real.one_le_rpow hr1 hH.hd0
                nlinarith
        · push_neg at hr1
          set Sc := {l | l ∈ groupSet H.b H.χ H.a g ∩ goodSet H.b H.K H.χ ∧
            |H.b l 2 - c 0| < r ∧ |H.b l 5 - c 1| < r} with hSc
          have hScm : MeasurableSet Sc := by
            have h2 : Measurable fun l => H.b l 2 := (measurable_pi_apply 2).comp hH.hb
            have h5 : Measurable fun l => H.b l 5 := (measurable_pi_apply 5).comp hH.hb
            refine ((hGgm.inter (measurableSet_goodSet hH.hb _ _))).inter
              ((measurableSet_lt (f := fun l => |H.b l 2 - c 0|) (by fun_prop)
                measurable_const).inter
              (measurableSet_lt (f := fun l => |H.b l 5 - c 1|) (by fun_prop)
                measurable_const))
          have hsub : {l | f l ∈ Metric.ball c r} ∩ Λg ⊆ Sc := by
            rintro l ⟨hlb, hl⟩
            have hlgood : l ∈ goodSet H.b H.K H.χ := hGg (hLG hl.1.1)
            obtain ⟨h0, h1, -⟩ := hf_good l hlgood
            have hd : ‖f l - c‖ < r := by
              have := hlb
              simp only [mem_setOf_eq, Metric.mem_ball, dist_eq_norm] at this
              exact this
            refine ⟨⟨hl.1.2, hlgood⟩, ?_, ?_⟩
            · have := (abs_apply_le_norm3 (f l - c) 0).trans_lt hd
              simpa [h0] using this
            · have := (abs_apply_le_norm3 (f l - c) 1).trans_lt hd
              simpa [h1] using this
          calc W⁻¹ * lam ({l | f l ∈ Metric.ball c r} ∩ Λg) ≤ W⁻¹ * lam Sc := by
                gcongr
            _ = W⁻¹ * H.ρ (Sc ×ˢ univ) := by rw [hlam_apply _ hScm]
            _ ≤ W⁻¹ * H.μ (Sc ×ˢ univ) := mul_le_mul' le_rfl (hρμ _)
            _ ≤ W⁻¹ * (ENNReal.ofReal (2574 * H.K ^ 4 * H.a ^ 2 * r ^ H.d) * H.π bin) := by
                gcongr
                exact group_box_cap H hH g (c 0) (c 1) r hr hr1.le
            _ = ENNReal.ofReal (2574 * H.K ^ 4 * r ^ H.d) := by
                have : ENNReal.ofReal (2574 * H.K ^ 4 * H.a ^ 2 * r ^ H.d) * H.π bin =
                    ENNReal.ofReal (2574 * H.K ^ 4 * r ^ H.d) * W := by
                  rw [hW, ← mul_assoc, ← ENNReal.ofReal_mul
                    (mul_nonneg (by positivity) (Real.rpow_nonneg (ha.le.trans hr) _))]
                  congr 2
                  ring
                rw [this, hWcancel]
            _ ≤ ENNReal.ofReal (Λ * r ^ H.d) := by
                apply ENNReal.ofReal_le_ofReal
                have : 0 ≤ r ^ H.d := Real.rpow_nonneg (ha.le.trans hr) _
                nlinarith)
    -- the clustered bin is light: contradiction
    rw [hν'_apply] at hqq
    set Q := {l | (∀ i : Fin 3, ⌊f l i / H.a⌋ = qq i) ∧
      ENNReal.ofReal σ ≤ volume {t | (l, t) ∈ E'}} with hQ
    have hpos : 0 < H.a ^ H.d * σ := mul_pos (Real.rpow_pos_of_pos ha _) hσ
    rcases (Q ∩ Λg).eq_empty_or_nonempty with h0 | ⟨l1, hl1⟩
    · rw [h0, measure_empty, mul_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hqq
      linarith
    have hl1Λ : l1 ∈ Λg := hl1.2
    have hl1good : l1 ∈ goodSet H.b H.K H.χ := hGg (hLG hl1Λ.1.1)
    set cs := lmCode H.χ H.a (H.b l1) with hcs
    have hsub : Q ∩ Λg ⊆ lmCell H.b H.χ H.a G cs := by
      rintro l ⟨hlQ, hlΛ⟩
      have hlgood : l ∈ goodSet H.b H.K H.χ := hGg (hLG hlΛ.1.1)
      refine ⟨hLG hlΛ.1.1, ?_⟩
      have hg := hlΛ.1.2
      have hg1 := hl1Λ.1.2
      obtain ⟨a0, a1, -⟩ := hf_good l hlgood
      obtain ⟨b0, b1, -⟩ := hf_good l1 hl1good
      have e2 : ⌊H.b l 2 / H.a⌋ = ⌊H.b l1 2 / H.a⌋ := by
        have := hlQ.1 0
        have h' := hl1.1.1 0
        rw [a0] at this
        rw [b0] at h'
        rw [this, h']
      have e5 : ⌊H.b l 5 / H.a⌋ = ⌊H.b l1 5 / H.a⌋ := by
        have := hlQ.1 1
        have h' := hl1.1.1 1
        rw [a1] at this
        rw [b1] at h'
        rw [this, h']
      simp only [mem_setOf_eq, hcs]
      funext i
      fin_cases i
      · simp only [lmCode]; exact hg.1.trans hg1.1.symm
      · simp only [lmCode]; exact hg.2.1.trans hg1.2.1.symm
      · simp only [lmCode]; exact hg.2.2.trans hg1.2.2.symm
      · simpa [lmCode] using e2
      · simpa [lmCode] using e5
    have hlight1 : H.ρ (lmCell H.b H.χ H.a G cs ×ˢ univ) <
        lmWeight H.π H.χ H.a H.d Z cs := hl1Λ.1.1.2
    have hcs0 : cs 0 = g.1 := by
      simp only [hcs, lmCode]
      exact hl1Λ.1.2.1
    have hwt : lmWeight H.π H.χ H.a H.d Z cs = ENNReal.ofReal (H.a ^ H.d / Z) * W := by
      rw [lmWeight, hcs0, ← bin_eq_Ico hH.hχ0, hW, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring
    have hcellm : MeasurableSet (lmCell H.b H.χ H.a G cs) :=
      measurableSet_lmCell hH.hb _ _ hG cs
    have hle : W⁻¹ * lam (Q ∩ Λg) ≤ ENNReal.ofReal (H.a ^ H.d / Z) := by
      calc W⁻¹ * lam (Q ∩ Λg) ≤ W⁻¹ * lam (lmCell H.b H.χ H.a G cs) := by gcongr
        _ = W⁻¹ * H.ρ (lmCell H.b H.χ H.a G cs ×ˢ univ) := by rw [hlam_apply _ hcellm]
        _ ≤ W⁻¹ * (ENNReal.ofReal (H.a ^ H.d / Z) * W) := by
            gcongr
            rw [← hwt]
            exact hlight1.le
        _ = ENNReal.ofReal (H.a ^ H.d / Z) := hWcancel _
    have h3 := hqq.trans hle
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    have hpow : 0 < H.a ^ H.d := Real.rpow_pos_of_pos ha _
    have : H.a ^ H.d * σ * Z ≤ H.a ^ H.d := by
      have := mul_le_mul_of_nonneg_right h3 hZ.le
      rwa [div_mul_cancel₀ _ hZ.ne'] at this
    nlinarith
  -- conclusion
  calc H.ρ ((Light ∩ Gg) ×ˢ univ) ≤ H.ρ ((Λg ×ˢ univ) ∪ ((Gg \ Gθ) ×ˢ univ)) := by
        apply measure_mono
        rintro ⟨l, t⟩ ⟨⟨hl1, hl2⟩, -⟩
        by_cases h : l ∈ Gθ
        · exact Or.inl ⟨⟨⟨hl1, hl2⟩, h⟩, trivial⟩
        · exact Or.inr ⟨⟨hl2, h⟩, trivial⟩
    _ ≤ H.ρ (Λg ×ˢ univ) + H.ρ ((Gg \ Gθ) ×ˢ univ) := measure_union_le _ _
    _ ≤ _ := add_le_add hstepD hstepB

/-- Number of parameter bins of bounded labels. -/
theorem card_Icc_floor_le {K w : ℝ} (hw : 0 < w) (hK : 0 ≤ K) :
    ((Finset.Icc ⌊-K / w⌋ ⌊K / w⌋).card : ℝ) ≤ 2 * K / w + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le (K / w)
  have h2 := Int.lt_floor_add_one (-K / w)
  have hle : ⌊-K / w⌋ ≤ ⌊K / w⌋ + 1 := by
    have : -K / w ≤ K / w := div_le_div_of_nonneg_right (by linarith) hw.le
    have := Int.floor_mono this
    omega
  have : ((⌊K / w⌋ + 1 - ⌊-K / w⌋).toNat : ℝ) = ((⌊K / w⌋ + 1 - ⌊-K / w⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [this]
  push_cast
  have e1 : -K / w = -(K / w) := by ring
  have e2 : 2 * K / w = 2 * (K / w) := by ring
  rw [e2]
  linarith

theorem floor_mem_Icc_of_abs_le {x K w : ℝ} (hw : 0 < w) (hx : |x| ≤ K) :
    ⌊x / w⌋ ∈ Finset.Icc ⌊-K / w⌋ ⌊K / w⌋ := by
  rw [abs_le] at hx
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hx.1 hw.le),
    Int.floor_mono (div_le_div_of_nonneg_right hx.2 hw.le)⟩

/-- The light-mass estimate at one index and one depth. -/
theorem light_mass_le (H : DepthData α) (hH : H.Hyp) (G : Set α) (hG : MeasurableSet G)
    (hGg : G ⊆ goodSet H.b H.K H.χ) {Csupp Λ σ θ Z : ℝ}
    (hsupp : H.SupportCount Csupp) (hclust : ClusterOracle H.a H.d Λ σ)
    (hΛs : Csupp ≤ Λ) (hΛK : 2574 * H.K ^ 4 ≤ Λ) (hZσ : 1 < Z * σ) (hθ : 0 < θ)
    (hZ : 0 < Z) :
    H.ρ (lmLight H.ρ H.π H.b H.χ H.a H.d Z G ×ˢ univ) ≤
      ENNReal.ofReal (16 * H.K ^ 2 / (Λ * θ) + H.K * θ) := by
  classical
  have := hH.hν
  have := hH.hπ
  have hK := hH.hK
  have hK0 : 0 ≤ H.K := by linarith
  have ha := hH.ha0
  have hχ := hH.hχ0
  have hΛ : 0 < Λ := by
    have : 0 < H.K ^ 4 := by positivity
    linarith
  set I0 := Finset.Icc ⌊-H.K / H.χ⌋ ⌊H.K / H.χ⌋ with hI0
  set I1 := Finset.Icc ⌊-H.K / H.a⌋ ⌊H.K / H.a⌋ with hI1
  set Γ := I0 ×ˢ (I1 ×ˢ I1) with hΓ
  set Light := lmLight H.ρ H.π H.b H.χ H.a H.d Z G with hLight
  have hcover : Light ×ˢ (univ : Set ℝ) ⊆
      ⋃ g ∈ Γ, (Light ∩ groupSet H.b H.χ H.a g) ×ˢ univ := by
    rintro ⟨l, t⟩ ⟨hl, -⟩
    obtain ⟨hsum, -, -, -⟩ := hGg hl.1
    have h0 : |H.b l 0| ≤ H.K := by
      linarith [abs_nonneg (H.b l 1), abs_nonneg (H.b l 3), abs_nonneg (H.b l 4)]
    have h1 : |H.b l 1| ≤ H.K := by
      linarith [abs_nonneg (H.b l 0), abs_nonneg (H.b l 3), abs_nonneg (H.b l 4)]
    have h3 : |H.b l 3| ≤ H.K := by
      linarith [abs_nonneg (H.b l 0), abs_nonneg (H.b l 1), abs_nonneg (H.b l 4)]
    simp only [mem_iUnion]
    refine ⟨(⌊H.b l 3 / H.χ⌋, ⌊H.b l 0 / H.a⌋, ⌊H.b l 1 / H.a⌋), ?_,
      ⟨⟨hl, rfl, rfl, rfl⟩, trivial⟩⟩
    rw [hΓ, Finset.mem_product, Finset.mem_product]
    exact ⟨floor_mem_Icc_of_abs_le hχ h3, floor_mem_Icc_of_abs_le ha h0,
      floor_mem_Icc_of_abs_le ha h1⟩
  have hsumν : ∑ g ∈ Γ, H.ν (groupSet H.b H.χ H.a g) ≤ 1 := by
    rw [← measure_biUnion_finset]
    · exact prob_le_one
    · intro g _ g' _ hne
      rw [Function.onFun, Set.disjoint_left]
      rintro l ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
      exact hne (Prod.ext (h1.symm.trans h1') (Prod.ext (h2.symm.trans h2') (h3.symm.trans h3')))
    · intro g _
      exact measurableSet_groupSet hH.hb _ _ g
  have hsumπ : ∑ g ∈ Γ, H.π {x | ⌊x / H.χ⌋ = g.1} ≤ ((I1.card : ℝ≥0∞)) ^ 2 := by
    rw [hΓ, Finset.sum_product]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    have hb : ∑ d0 ∈ I0, H.π {x | ⌊x / H.χ⌋ = d0} ≤ 1 := by
      rw [← measure_biUnion_finset]
      · exact prob_le_one
      · intro d _ d' _ hne
        rw [Function.onFun, Set.disjoint_left]
        intro x h h'
        exact hne (h.symm.trans h')
      · intro d _
        exact (Int.measurable_floor.comp (measurable_id.div_const _)) (measurableSet_singleton _)
    calc ((I1 ×ˢ I1).card : ℝ≥0∞) * ∑ d0 ∈ I0, H.π {x | ⌊x / H.χ⌋ = d0}
        ≤ ((I1 ×ˢ I1).card : ℝ≥0∞) * 1 := by gcongr
      _ = (I1.card : ℝ≥0∞) ^ 2 := by rw [Finset.card_product, mul_one]; push_cast; ring
  have hcard : (I1.card : ℝ) ≤ 2 * H.K / H.a + 2 := card_Icc_floor_le ha hK0
  calc H.ρ (Light ×ˢ univ)
      ≤ H.ρ (⋃ g ∈ Γ, (Light ∩ groupSet H.b H.χ H.a g) ×ˢ univ) := measure_mono hcover
    _ ≤ ∑ g ∈ Γ, H.ρ ((Light ∩ groupSet H.b H.χ H.a g) ×ˢ univ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ g ∈ Γ, (ENNReal.ofReal (H.a ^ 2 / (Λ * θ)) * H.π {x | ⌊x / H.χ⌋ = g.1} +
          ENNReal.ofReal (H.K * θ) * H.ν (groupSet H.b H.χ H.a g)) := by
        apply Finset.sum_le_sum
        intro g _
        exact group_light_le H hH G hG hGg g hsupp hclust hΛs hΛK hZσ hθ hZ
    _ = ENNReal.ofReal (H.a ^ 2 / (Λ * θ)) * ∑ g ∈ Γ, H.π {x | ⌊x / H.χ⌋ = g.1} +
          ENNReal.ofReal (H.K * θ) * ∑ g ∈ Γ, H.ν (groupSet H.b H.χ H.a g) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ENNReal.ofReal (H.a ^ 2 / (Λ * θ)) * (I1.card : ℝ≥0∞) ^ 2 +
          ENNReal.ofReal (H.K * θ) * 1 := by gcongr
    _ ≤ ENNReal.ofReal (16 * H.K ^ 2 / (Λ * θ)) + ENNReal.ofReal (H.K * θ) := by
        rw [mul_one]
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hc0 : (0 : ℝ) ≤ I1.card := Nat.cast_nonneg _
        have h2 : (I1.card : ℝ) ^ 2 ≤ (2 * H.K / H.a + 2) ^ 2 := by gcongr
        have h3 : H.a ^ 2 * (2 * H.K / H.a + 2) ^ 2 ≤ 16 * H.K ^ 2 := by
          have : H.a * (2 * H.K / H.a + 2) = 2 * H.K + 2 * H.a := by field_simp
          have ha1 := hH.a_le_one
          nlinarith
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        nlinarith
    _ = ENNReal.ofReal (16 * H.K ^ 2 / (Λ * θ) + H.K * θ) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]

end

end Submission.Obl.k4_horizontal_coefficient_count
