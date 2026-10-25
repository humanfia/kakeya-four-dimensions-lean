/- Adapted from this LOT tree o255, session x0901, commit25b5b5db,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/ListGlue2.lean.
   The original-assignment estimate is replaced by the accepted o253 budget. -/
import Submission.Obl.k4_narrow_projected_row_parents.ListedParents
import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.GlobalHorizontalCaps
import Submission.Obl.k4_narrow_projected_row_parents.WitnessExponent

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Velocity lists at depth `r`: frequently, a retained set of mass at least `1/M` on which
the zoomed transverse velocity of each parent takes at most `M` bins of width `N^(-e)` per
zoomed horizontal cell and velocity bin of mesh `N^(-aξ)`. -/
def VelocityLists (cfg : Model α) (r aξ e : ℝ) : Prop :=
  ∃ M : ℕ → ℝ, (∀ k, 1 ≤ M k) ∧ Model.Subpow cfg.N M ∧
    ∃ᶠ k in atTop, ∃ Gl : Set (α × ℝ), MeasurableSet Gl ∧
      ENNReal.ofReal (M k)⁻¹ ≤ cfg.ρ k Gl ∧
      ∀ Q : Fin (cfg.n k r), ∃ L : (Fin 2 → ℤ) → ℤ → Finset ℤ,
        (∀ c w, ((L c w).card : ℝ) ≤ M k) ∧
        ∀ z ∈ Gl, z ∈ (Model.prepared cfg).B k r Q ×ˢ (Model.prepared cfg).block k r Q →
          ⌊(parentZoom (Model.parameters cfg) (Model.prepared cfg) k r Q).coeff
              (cfg.b k z.1) 4 / cfg.N k ^ (-e)⌋ ∈
            L (hcell (parentZoom (Model.parameters cfg) (Model.prepared cfg) k r Q)
                (cfg.N k ^ (-aξ)) (cfg.b k z.1) z.2) ⌊cfg.b k z.1 3 / cfg.N k ^ (-aξ)⌋

/-- Joint caps at depth `r`: eventually, outside a set of mass `N^(-c₀)`, every parent has
the horizontal joint cell cap `M ξ² π(bin) q_r ν(A_Q)` at mesh `ξ = N^(-aξ)`. -/
def JointCaps (cfg : Model α) (r aξ : ℝ) : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ M : ℕ → ℝ, (∀ k, 1 ≤ M k) ∧ Model.Subpow cfg.N M ∧
    ∀ᶠ k in atTop, ∃ Gc : Set (α × ℝ), MeasurableSet Gc ∧
      cfg.ρ k Gcᶜ ≤ ENNReal.ofReal (cfg.N k ^ (-c₀)) ∧
      ∀ (Q : Fin (cfg.n k r)) (c : Fin 2 → ℤ) (v₀ : ℤ),
        cfg.ρ k {z | z ∈ Gc ∧
            z ∈ (Model.prepared cfg).B k r Q ×ˢ (Model.prepared cfg).block k r Q ∧
            hcell (parentZoom (Model.parameters cfg) (Model.prepared cfg) k r Q)
              (cfg.N k ^ (-aξ)) (cfg.b k z.1) z.2 = c ∧
            ⌊cfg.b k z.1 3 / cfg.N k ^ (-aξ)⌋ = v₀} ≤
          ENNReal.ofReal (M k * (cfg.N k ^ (-aξ)) ^ 2) *
            cfg.π k (Ico ((v₀ : ℝ) * cfg.N k ^ (-aξ)) (((v₀ : ℝ) + 1) * cfg.N k ^ (-aξ))) *
            (ENNReal.ofReal ((Model.prepared cfg).q k r) * cfg.ν k (cfg.A k r Q))

/-- Listed parents along the original sequence. -/
def ListedParents (cfg : Model α) (r aξ e : ℝ) : Prop :=
  ∃ M : ℕ → ℝ, (∀ k, 1 ≤ M k) ∧ Model.Subpow cfg.N M ∧
    ∃ᶠ k in atTop, Nonempty (ParentLists (Model.parameters cfg) (Model.prepared cfg) k r
      (cfg.N k ^ (-aξ)) (cfg.N k ^ (-e)) (M k))


/-- **Listed parents from velocity lists and joint caps.** A parent heavy for the
retained set carries the lists and the caps. -/
theorem listedParents_of_lists_caps (cfg : Model α) (hv : Model.Valid cfg) {r aξ e : ℝ}
    (hr : 0 < r) (hrU : r ≤ cfg.U) (hvl : VelocityLists cfg r aξ e)
    (hjc : JointCaps cfg r aξ) : ListedParents cfg r aξ e := by
  classical
  obtain ⟨M₁, hM₁, hM₁sub, hfreq⟩ := hvl
  obtain ⟨c₀, hc₀, M₂, hM₂, hM₂sub, hjev⟩ := hjc
  have hp := Model.parameters_valid hv
  have ha := Model.prepared_valid hv
  have hK1 : ∀ k, 1 ≤ cfg.K k := hv.subpower.1
  have hNlim := hv.scale_limit
  set R : ℝ := r⁻¹ + cfg.U + 2 with hR
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hU0 := hv.depth_pos
  have hR1 : 1 < R := by linarith
  have hRr : R⁻¹ ≤ r := by
    rw [inv_le_comm₀ (by linarith) hr]; linarith
  let M : ℕ → ℝ := fun k => 4 * M₁ k * cfg.K k ^ 2 + M₂ k + cfg.K k
  have hMge : ∀ k, 4 * M₁ k * cfg.K k ^ 2 ≤ M k ∧ M₁ k ≤ M k ∧ M₂ k ≤ M k ∧ cfg.K k ≤ M k := by
    intro k
    have h1 := hM₁ k; have h2 := hM₂ k; have h3 := hK1 k
    have h4 : M₁ k ≤ 4 * M₁ k * cfg.K k ^ 2 := by
      have hK2 : 1 ≤ cfg.K k ^ 2 := one_le_pow₀ h3
      nlinarith [mul_le_mul_of_nonneg_left hK2 (by linarith : (0 : ℝ) ≤ M₁ k)]
    have h5 : 0 ≤ 4 * M₁ k * cfg.K k ^ 2 := by positivity
    refine ⟨by simp only [M]; linarith, by simp only [M]; linarith, by simp only [M]; linarith,
      by simp only [M]; linarith⟩
  refine ⟨M, fun k => (hK1 k).trans (hMge k).2.2.2, ?_, ?_⟩
  · intro ε hε
    have hε4 : 0 < ε / 4 := by positivity
    filter_upwards [hM₁sub _ hε4, hM₂sub _ hε4, hv.subpower.2 _ hε4,
      ((tendsto_rpow_atTop hε4).comp hNlim).eventually_ge_atTop 6] with k h1 h2 h3 h6
    simp only [Function.comp_apply] at h6
    have hN0 : 0 < cfg.N k := by linarith [hv.scale k]
    have hX : 1 ≤ cfg.N k ^ (ε / 4) := by linarith
    have hpow : cfg.N k ^ ε = cfg.N k ^ (ε / 4) * cfg.N k ^ (ε / 4) * cfg.N k ^ (ε / 4) *
        cfg.N k ^ (ε / 4) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
    have hK0 : 0 ≤ cfg.K k := by linarith [hK1 k]
    have hM10 : 0 ≤ M₁ k := by linarith [hM₁ k]
    simp only [M]
    rw [hpow]
    set X := cfg.N k ^ (ε / 4)
    have hK2 : cfg.K k ^ 2 ≤ X ^ 2 := by gcongr
    have h4 : 4 * M₁ k * cfg.K k ^ 2 ≤ 4 * X * X ^ 2 := by gcongr
    have hX3 : 1 ≤ X ^ 3 := one_le_pow₀ hX
    have hX6 : 6 * X ^ 3 ≤ X * X * X * X := by
      have : X * X * X * X = X ^ 3 * X := by ring
      rw [this]; nlinarith
    have hXX : X ≤ X ^ 3 := le_self_pow₀ hX (by norm_num)
    have : 4 * X * X ^ 2 = 4 * X ^ 3 := by ring
    linarith
  · have hsmall : ∀ᶠ k in atTop, 2 * M₁ k * cfg.N k ^ (-c₀) ≤ 1 := by
      filter_upwards [hM₁sub _ (half_pos hc₀),
        ((tendsto_rpow_atTop (half_pos hc₀)).comp hNlim).eventually_ge_atTop 2] with k h1 h2
      simp only [Function.comp_apply] at h2
      have hN0 : 0 < cfg.N k := by linarith [hv.scale k]
      have hsplit : cfg.N k ^ (-c₀) * cfg.N k ^ (c₀ / 2) * cfg.N k ^ (c₀ / 2) = 1 := by
        rw [mul_assoc, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf; simp
      have hpos : 0 < cfg.N k ^ (-c₀) := Real.rpow_pos_of_pos hN0 _
      nlinarith [mul_le_mul_of_nonneg_left h1 hpos.le, mul_le_mul_of_nonneg_left h2 hpos.le]
    refine (hfreq.and_eventually ((hjev.and (ha.2.2.1 R hR1)).and hsmall)).mono ?_
    rintro k ⟨⟨Gl, hGlm, hGlmass, hlists⟩, ⟨⟨Gc, hGcm, hGcmass, hcap⟩, hatall⟩, hsm⟩
    have hat := hatall r hRr hrU
    obtain ⟨hbm, hνp, hπp, hμK, hρμ, -⟩ := hv.basic k
    have hN0 : 0 < cfg.N k := by linarith [hv.scale k]
    have hK0 : 0 < cfg.K k := by linarith [hK1 k]
    have hM10 : 0 < M₁ k := by linarith [hM₁ k]
    -- the good velocity set
    set Good : Set (α × ℝ) := {z | |cfg.b k z.1 3| ≤ cfg.K k} with hGood
    have hGoodm : MeasurableSet Good :=
      measurableSet_le ((((measurable_pi_apply 3).comp hbm).comp measurable_fst).abs)
        measurable_const
    have hGoodnull : cfg.ρ k Goodᶜ = 0 := by
      have hae : ∀ᵐ z ∂cfg.μ k, |cfg.b k z.1 3| ≤ cfg.K k := by
        have := hνp
        have hprod : ∀ᵐ z : α × ℝ ∂(cfg.ν k).prod volume,
            |cfg.b k z.1 0| + |cfg.b k z.1 1| + |cfg.b k z.1 3| + |cfg.b k z.1 4| ≤ cfg.K k :=
          (Measure.quasiMeasurePreserving_fst (μ := cfg.ν k) (ν := (volume : Measure ℝ))).ae
            (hv.basic k).2.2.2.2.2.2.2.2.1
        have hmu := (Measure.absolutelyContinuous_of_le_smul hμK).ae_le hprod
        filter_upwards [hmu] with z hz
        have := abs_nonneg (cfg.b k z.1 0)
        have := abs_nonneg (cfg.b k z.1 1)
        have := abs_nonneg (cfg.b k z.1 4)
        linarith
      have h0 : cfg.μ k Goodᶜ = 0 := by
        have := ae_iff.mp hae
        simpa [Good, compl_ofPred] using this
      exact nonpos_iff_eq_zero.mp ((hρμ _).trans h0.le)
    set G : Set (α × ℝ) := Gl ∩ Gc ∩ Good with hG
    have hGm : MeasurableSet G := (hGlm.inter hGcm).inter hGoodm
    -- the retained mass
    have hGmass : ENNReal.ofReal (2 * M₁ k)⁻¹ ≤ cfg.ρ k G := by
      have hsub : Gl ⊆ G ∪ Gcᶜ ∪ Goodᶜ := by
        intro z hz
        by_cases h1 : z ∈ Gc
        · by_cases h2 : z ∈ Good
          · left; left; exact ⟨⟨hz, h1⟩, h2⟩
          · right; exact h2
        · left; right; exact h1
      have h1 : cfg.ρ k Gl ≤ cfg.ρ k G + ENNReal.ofReal (cfg.N k ^ (-c₀)) := by
        calc cfg.ρ k Gl ≤ cfg.ρ k (G ∪ Gcᶜ ∪ Goodᶜ) := measure_mono hsub
          _ ≤ cfg.ρ k G + cfg.ρ k Gcᶜ + cfg.ρ k Goodᶜ :=
              (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
          _ ≤ cfg.ρ k G + ENNReal.ofReal (cfg.N k ^ (-c₀)) + 0 := by
              rw [hGoodnull]; gcongr
          _ = _ := add_zero _
      have h2 : ENNReal.ofReal (cfg.N k ^ (-c₀)) ≤ ENNReal.ofReal (2 * M₁ k)⁻¹ := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_inv_comm₀ (Real.rpow_pos_of_pos hN0 _) (by positivity)]
        rw [Real.rpow_neg hN0.le, inv_inv]
        have hpos : 0 < cfg.N k ^ c₀ := Real.rpow_pos_of_pos hN0 _
        have : cfg.N k ^ (-c₀) * cfg.N k ^ c₀ = 1 := by
          rw [← Real.rpow_add hN0]; simp
        rw [Real.rpow_neg hN0.le] at hsm this
        nlinarith [inv_mul_cancel₀ hpos.ne']
      have h3 : ENNReal.ofReal (M₁ k)⁻¹ = ENNReal.ofReal (2 * M₁ k)⁻¹ +
          ENNReal.ofReal (2 * M₁ k)⁻¹ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; field_simp; ring
      have h4 := hGlmass.trans h1
      rw [h3] at h4
      have hfin : ENNReal.ofReal (2 * M₁ k)⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
      calc ENNReal.ofReal (2 * M₁ k)⁻¹
          = ENNReal.ofReal (2 * M₁ k)⁻¹ + ENNReal.ofReal (2 * M₁ k)⁻¹ -
              ENNReal.ofReal (2 * M₁ k)⁻¹ := (ENNReal.add_sub_cancel_right hfin).symm
        _ ≤ cfg.ρ k G + ENNReal.ofReal (cfg.N k ^ (-c₀)) - ENNReal.ofReal (2 * M₁ k)⁻¹ :=
            tsub_le_tsub_right h4 _
        _ ≤ cfg.ρ k G + ENNReal.ofReal (2 * M₁ k)⁻¹ - ENNReal.ofReal (2 * M₁ k)⁻¹ := by
            gcongr
        _ = cfg.ρ k G := ENNReal.add_sub_cancel_right hfin
    -- the parents cover the retained set
    obtain ⟨-, -, hmeas, -, hlab, hcov, -⟩ := hat
    set S : Fin (cfg.n k r) → Set (α × ℝ) := fun Q =>
      (Model.prepared cfg).B k r Q ×ˢ (Model.prepared cfg).block k r Q with hS
    have hsumG : cfg.ρ k G ≤ ∑ Q, cfg.ρ k (G ∩ S Q) := by
      have hnull : cfg.ρ k (G \ ⋃ Q, S Q) = 0 := by
        have h0 : (Model.prepared cfg).mu k {z | ¬ ∃ Q, z.1 ∈ (Model.prepared cfg).B k r Q ∧
            z.2 ∈ (Model.prepared cfg).block k r Q} = 0 := ae_iff.mp hcov
        refine nonpos_iff_eq_zero.mp ((hρμ _).trans (le_of_le_of_eq (measure_mono ?_) h0))
        rintro z ⟨-, hz⟩ ⟨Q, h1, h2⟩
        exact hz (mem_iUnion.mpr ⟨Q, h1, h2⟩)
      calc cfg.ρ k G ≤ cfg.ρ k (⋃ Q, (G ∩ S Q)) + cfg.ρ k (G \ ⋃ Q, S Q) := by
            rw [← inter_iUnion]
            exact measure_le_inter_add_sdiff _ _ _
        _ = cfg.ρ k (⋃ Q, (G ∩ S Q)) := by rw [hnull, add_zero]
        _ ≤ ∑ Q, cfg.ρ k (G ∩ S Q) := measure_iUnion_fintype_le _ _
    have hsumA : ∑ Q, ENNReal.ofReal ((Model.prepared cfg).q k r) * cfg.ν k (cfg.A k r Q) ≤
        ENNReal.ofReal (cfg.K k) * ENNReal.ofReal (cfg.K k) := by
      apply (NativeCaps.reference_weight_sum_le_one (Model.parameters cfg)
        (Model.prepared cfg) ha.1 (hatall r hRr hrU)).trans
      have hKK : 1 ≤ cfg.K k * cfg.K k := by nlinarith [hK1 k]
      simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul hK0.le] using
        ENNReal.ofReal_le_ofReal hKK
    -- a heavy parent
    set c : ℝ≥0∞ := ENNReal.ofReal (4 * M₁ k * cfg.K k ^ 2)⁻¹ with hc
    obtain ⟨Q, hQ⟩ : ∃ Q, c * (ENNReal.ofReal ((Model.prepared cfg).q k r) *
        cfg.ν k (cfg.A k r Q)) < cfg.ρ k (G ∩ S Q) := by
      by_contra hcon
      push Not at hcon
      have h1 : ∑ Q, cfg.ρ k (G ∩ S Q) ≤ c * (ENNReal.ofReal (cfg.K k) * ENNReal.ofReal (cfg.K k)) :=
        calc ∑ Q, cfg.ρ k (G ∩ S Q)
            ≤ ∑ Q, c * (ENNReal.ofReal ((Model.prepared cfg).q k r) * cfg.ν k (cfg.A k r Q)) :=
              Finset.sum_le_sum fun Q _ => hcon Q
          _ = c * ∑ Q, ENNReal.ofReal ((Model.prepared cfg).q k r) * cfg.ν k (cfg.A k r Q) := by
              rw [Finset.mul_sum]
          _ ≤ c * (ENNReal.ofReal (cfg.K k) * ENNReal.ofReal (cfg.K k)) := by gcongr
      have h2 : c * (ENNReal.ofReal (cfg.K k) * ENNReal.ofReal (cfg.K k)) =
          ENNReal.ofReal (4 * M₁ k)⁻¹ := by
        rw [hc, ← ENNReal.ofReal_mul hK0.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
      have h3 : ENNReal.ofReal (4 * M₁ k)⁻¹ < ENNReal.ofReal (2 * M₁ k)⁻¹ := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        apply inv_strictAnti₀ (by positivity); linarith
      have := (hGmass.trans hsumG).trans (h1.trans h2.le)
      exact absurd (lt_of_le_of_lt this h3) (lt_irrefl _)
    -- the listed parent
    obtain ⟨L, hLcard, hLmem⟩ := hlists Q
    obtain ⟨hνlo, -, -, -, -, hbox, -⟩ := hlab Q
    have hq0 : 0 < (Model.prepared cfg).q k r := q_pos _ k r
    have hg0 : 0 < narrow (Model.parameters cfg) k r := narrow_pos _ hp k r
    have ht₀ := blockStart_mem (cfg.T k r) (cfg.j k r Q)
    have hMk := hMge k
    refine ⟨{ Q := Q
              W := G ∩ S Q
              measurable_W := hGm.inter ((hmeas Q).2.1.prod measurableSet_Icc)
              W_sub := inter_subset_right
              measurable_A := (hmeas Q).1
              B_sub_A := (hmeas Q).2.2
              prior_ne := ?_
              mass := ?_
              pos_bound := ?_
              vel_bound := ?_
              yv_bound := ?_
              L := L
              L_card := fun c w => (hLcard c w).trans hMk.2.1
              L_mem := fun z hz => hLmem z hz.1.1.1 hz.2
              joint_cap := ?_ }⟩
    · refine (lt_of_lt_of_le ?_ hνlo).ne'
      rw [ENNReal.ofReal_pos]
      have hw : 0 < width (Model.parameters cfg) k r := Real.rpow_pos_of_pos hN0 _
      positivity
    · refine le_trans ?_ hQ.le
      rw [hc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
      rw [div_eq_mul_inv, mul_comm]
      gcongr
      exact hMk.1
    · intro z hz
      have hl : z.1 ∈ (Model.prepared cfg).A k r Q := (hmeas Q).2.2 hz.2.1
      have h1 := (hbox z.1 hl _ ht₀).1
      rw [Zoom.coeff_zero]
      simp only [parentZoom]
      rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
      simp only [PreparedModel.x, Submission.Lib.K4ContactNormalization.point,
        Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      have h1' : |cfg.b k z.1 0 + blockStart (cfg.T k r) (cfg.j k r Q) * cfg.b k z.1 3 -
          (cfg.c k r Q 0 + blockStart (cfg.T k r) (cfg.j k r Q) * cfg.c k r Q 1)| ≤
          cfg.K k * (Model.prepared cfg).q k r := by
        have : cfg.b k z.1 0 + blockStart (cfg.T k r) (cfg.j k r Q) * cfg.b k z.1 3 -
            (cfg.c k r Q 0 + blockStart (cfg.T k r) (cfg.j k r Q) * cfg.c k r Q 1) =
            cfg.b k z.1 0 + blockStart (cfg.T k r) (cfg.j k r Q) * cfg.b k z.1 3 -
              cfg.c k r Q 0 - blockStart (cfg.T k r) (cfg.j k r Q) * cfg.c k r Q 1 := by ring
        rw [this]; exact h1
      exact h1'.trans (by gcongr; exact hMk.2.2.2)
    · intro z hz
      exact hz.1.2.trans hMk.2.2.2
    · intro z hz
      have hl : z.1 ∈ (Model.prepared cfg).A k r Q := (hmeas Q).2.2 hz.2.1
      have h3 := (hbox z.1 hl _ ht₀).2.2
      rw [Zoom.coeff_four]
      simp only [parentZoom]
      rw [abs_div, abs_mul, abs_of_pos hq0, abs_of_pos (mul_pos hq0 hg0),
        div_le_iff₀ (mul_pos hq0 hg0)]
      calc (Model.prepared cfg).q k r * |cfg.b k z.1 4 - cfg.c k r Q 3 - cfg.c k r Q 4 * cfg.b k z.1 3|
          ≤ (Model.prepared cfg).q k r * (cfg.K k * narrow (Model.parameters cfg) k r) := by
            gcongr; exact h3
        _ ≤ M k * ((Model.prepared cfg).q k r * narrow (Model.parameters cfg) k r) := by
            rw [show (Model.prepared cfg).q k r * (cfg.K k * narrow (Model.parameters cfg) k r) =
              cfg.K k * ((Model.prepared cfg).q k r * narrow (Model.parameters cfg) k r) by ring]
            gcongr; exact hMk.2.2.2
    · intro c v₀
      refine le_trans (measure_mono ?_) ((hcap Q c v₀).trans ?_)
      · rintro z ⟨⟨⟨⟨-, hzc⟩, -⟩, hzS⟩, hcell, hbin⟩
        exact ⟨hzc, hzS, hcell, hbin⟩
      · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal ?_) zero_le) zero_le
        gcongr
        exact hMk.2.2.1


/-- The prepared-model assumptions already supply the required joint caps. -/
theorem jointCaps_of_valid (cfg : Model α) (hv : Model.Valid cfg)
    {r aξ : ℝ} (hr : 0 < r) (hrU : r ≤ cfg.U) (hξ : 0 < aξ) :
    JointCaps cfg r aξ := by
  have hp := Model.parameters_valid hv
  have ha := Model.prepared_valid hv
  refine ⟨r / 2, by positivity, fun k => NativeCaps.horizontalParentConstant (cfg.K k),
    fun k => (NativeCaps.horizontalParentConstant_polynomial (hv.subpower.1 k)).1,
    NativeCaps.horizontalParentConstant_subpow (Model.parameters cfg) hp, ?_⟩
  filter_upwards [NativeCaps.eventually_global_horizontal_caps (Model.parameters cfg) hp
    (Model.prepared cfg) ha hr hrU hξ] with k hk
  obtain ⟨Bad, hBad, hsmall, hcap⟩ := hk
  obtain ⟨-, -, -, -, hρμ, -⟩ := hv.basic k
  refine ⟨Badᶜ, hBad.compl, ?_, ?_⟩
  · simpa only [compl_compl, neg_div, Model.parameters] using (hρμ Bad).trans hsmall
  · intro Q c j
    apply le_trans (measure_mono ?_) (hcap Q c j)
    rintro z ⟨hzBad, hzParent, hcell, hbin⟩
    exact ⟨hzParent, hzBad, hcell, hbin⟩

/-- A true depth with room for the deep labels converts listed parents to rows. -/
theorem rowParents_of_listedParents (hRow : Row) (cfg : Model α) (hv : Model.Valid cfg)
    {r aξ e : ℝ} (hr : 0 < r) (he : 0 < e) (heξ : e < aξ)
    (hroom : r + aξ / cfg.κ + e / cfg.ℓ < cfg.U)
    (h : ListedParents cfg r aξ e) : RowParents cfg r := by
  obtain ⟨M, hM, hMsub, hfreq⟩ := h
  obtain ⟨r', hrr', hr'U, hmajor, hminor⟩ :=
    exists_deeper_true_depth hv.rate_pos hv.transverse_pos he (he.trans heξ) hroom
  exact rowParents_of_parentLists hRow cfg hv hr hrr' hr'U.le he heξ hmajor hminor
    M hM hMsub hfreq

/-- Global transverse-velocity lists suffice for the row-parent conclusion. -/
theorem rowParents_of_velocityLists (hRow : Row) (cfg : Model α) (hv : Model.Valid cfg)
    {r aξ e : ℝ} (hr : 0 < r) (he : 0 < e) (heξ : e < aξ)
    (hroom : r + aξ / cfg.κ + e / cfg.ℓ < cfg.U)
    (h : VelocityLists cfg r aξ e) : RowParents cfg r := by
  have hrU : r < cfg.U := by
    have := div_pos (he.trans heξ) hv.rate_pos
    have := div_pos he hv.transverse_pos
    linarith
  exact rowParents_of_listedParents hRow cfg hv hr he heξ hroom
    (listedParents_of_lists_caps cfg hv hr hrU.le h
      (jointCaps_of_valid cfg hv hr hrU.le (he.trans heξ)))

end

end Submission.Obl.k4_narrow_projected_row_parents
