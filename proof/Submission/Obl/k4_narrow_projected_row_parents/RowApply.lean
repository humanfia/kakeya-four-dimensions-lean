/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/RowApply.lean.
   Earlier provenance comments in the source are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.RowParent
import Submission.Obl.k4_narrow_projected_row_parents.ZoomLaw
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom
import Submission.Obl.k4_narrow_projected_row_parents.Model

/-!
# Applying Row inside a parent

A *row-ready parent* at one index is a true parent `Q`, a retained set `W` of
its incidences with mass at least `q ν(A_Q) / M`, and a row field `T` on `W`
that predicts the zoomed transverse velocity to `M E`, has at most `M` bins of
width `E` per zoomed horizontal cell of width `ξ`, and obeys the joint
horizontal-cell/velocity-bin cap.  This is the paper's verification of the
hypotheses of the row fit in the normalized parent chart (Proposition 8.5).

`rowParent_of_rowReady` applies the frozen Row hypothesis to the zoomed law
`zoomLaw ρ W t₀ q (q ν(A_Q))`, with the conditioned prior and the original
palette, and returns a row parent whose dense set is the pullback of the Row
event.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers Submission.Obl.k4_general_parent_projected_layers.PreparedModel Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Zoomed horizontal position `(τ, Z(τ))` of a trajectory at zoomed time `τ`. -/
def hpos (Z : Zoom) (b : Fin 6 → ℝ) (τ : ℝ) : Fin 2 → ℝ :=
  ![τ, Z.coeff b 0 + τ * b 3]

/-- Zoomed horizontal cell of an incidence at original time `t`. -/
def hcell (Z : Zoom) (ξ : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 2 → ℤ :=
  fun i => ⌊hpos Z b ((t - Z.t₀) / Z.q) i / ξ⌋

/-- A parent at depth `r` and index `k` ready for the row fit. -/
structure RowReady (p : Parameters) (a : PreparedModel α) (k : ℕ) (r ξ E M : ℝ) where
  /-- the parent label -/
  Q : Fin (a.n k r)
  /-- retained incidences -/
  W : Set (α × ℝ)
  measurable_W : MeasurableSet W
  W_sub : W ⊆ a.B k r Q ×ˢ a.block k r Q
  measurable_A : MeasurableSet (a.A k r Q)
  B_sub_A : a.B k r Q ⊆ a.A k r Q
  prior_ne : a.nu k (a.A k r Q) ≠ 0
  mass : ENNReal.ofReal (a.q k r / M) * a.nu k (a.A k r Q) ≤ a.rho k W
  pos_bound : ∀ z ∈ W, |(parentZoom p a k r Q).coeff (a.b k z.1) 0| ≤ M
  vel_bound : ∀ z ∈ W, |a.b k z.1 3| ≤ M
  /-- the row field -/
  T : α × ℝ → Fin 2 → ℝ
  measurable_T : Measurable T
  T_bound : ∀ z ∈ W, ∀ i, |T z i| ≤ M
  T_predict : ∀ z ∈ W,
    |T z 0 + a.b k z.1 3 * T z 1 - (parentZoom p a k r Q).coeff (a.b k z.1) 4| ≤ M * E
  /-- row-bin lists per zoomed horizontal cell -/
  F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)
  F_card : ∀ c, ((F c).card : ℝ) ≤ M
  T_list : ∀ z ∈ W,
    (fun i => ⌊T z i / E⌋) ∈ F (hcell (parentZoom p a k r Q) ξ (a.b k z.1) z.2)
  joint_cap : ∀ (c : Fin 2 → ℤ) (v₀ : ℤ),
    a.rho k {z | z ∈ W ∧ hcell (parentZoom p a k r Q) ξ (a.b k z.1) z.2 = c ∧
        ⌊a.b k z.1 3 / ξ⌋ = v₀} ≤
      ENNReal.ofReal (M * ξ ^ 2) * a.pi k (Ico ((v₀ : ℝ) * ξ) (((v₀ : ℝ) + 1) * ξ)) *
        (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r Q))

/-- Clamp to `[-M, M]`. -/
def clampM (M x : ℝ) : ℝ := max (-M) (min M x)

theorem clampM_of_abs_le {M x : ℝ} (h : |x| ≤ M) : clampM M x = x := by
  unfold clampM
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

theorem abs_clampM_le {M x : ℝ} (hM : 0 ≤ M) : |clampM M x| ≤ M := by
  unfold clampM
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem measurable_clampM (M : ℝ) : Measurable (clampM M) := by
  unfold clampM
  fun_prop

theorem zoom_untime {t₀ q t : ℝ} (hq : q ≠ 0) : t₀ + q * ((t - t₀) / q) = t := by
  field_simp
  ring

theorem measurable_coeff_comp (Z : Zoom) {b : α → Fin 6 → ℝ} (hb : Measurable b) (i : Fin 6) :
    Measurable (fun l => Z.coeff (b l) i) := by
  have h : ∀ j : Fin 6, Measurable (fun l => b l j) := fun j => (measurable_pi_apply j).comp hb
  fin_cases i <;> simp only [Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff] <;> fun_prop

/-- Row instance: clamped zoomed major intercept. -/
def rowB (Z : Zoom) (M : ℝ) (b : α → Fin 6 → ℝ) : α → ℝ := fun l => clampM M (Z.coeff (b l) 0)

/-- Row instance: clamped major velocity. -/
def rowV (M : ℝ) (b : α → Fin 6 → ℝ) : α → ℝ := fun l => clampM M (b l 3)

/-- Row instance: zoomed transverse velocity. -/
def rowH (Z : Zoom) (b : α → Fin 6 → ℝ) : α → ℝ := fun l => Z.coeff (b l) 4

/-- Row instance: the clamped row field at zoomed time. -/
def rowT (Z : Zoom) (M : ℝ) (T : α × ℝ → Fin 2 → ℝ) : α × ℝ → Fin 2 → ℝ :=
  fun w i => clampM M (T (w.1, Z.t₀ + Z.q * w.2) i)

theorem measurable_rowCell {b' v' : α → ℝ} (hb : Measurable b') (hv : Measurable v') (ξ : ℝ) :
    Measurable (fun w : α × ℝ => fun i : Fin 2 =>
      ⌊(![w.2, b' w.1 + w.2 * v' w.1] : Fin 2 → ℝ) i / ξ⌋) := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact (measurable_snd.div_const ξ).floor
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact (((hb.comp measurable_fst).add (measurable_snd.mul (hv.comp measurable_fst))).div_const
      ξ).floor

/-- **Row in a parent.** One application of the frozen Row hypothesis, in the
zoomed chart of a row-ready parent, gives a row parent. `η` and `N₀` depend
only on the palette exponent `S`, the mesh exponent `aξ` and the Row loss `ε`. -/
theorem rowParent_of_rowReady_at (hRow : Row) {S aξ ε : ℝ} (hS : 0 < S) (haξ : 0 < aξ)
    (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
    ∀ (p : Parameters) (a : PreparedModel α) (k : ℕ) (r E M : ℝ),
      N₀ ≤ p.N k → 1 ≤ M → 2 * M ≤ p.N k ^ η → p.K k ≤ p.N k ^ η →
      p.N k ^ (-aξ) ≤ E → E ≤ 1 →
      Measurable (a.b k) → IsProbabilityMeasure (a.nu k) → IsProbabilityMeasure (a.pi k) →
      a.mu k ≤ ENNReal.ofReal (p.K k) • (a.nu k).prod volume → a.rho k ≤ a.mu k →
      (∀ x r' : ℝ, p.N k ^ (-aξ) ≤ r' → r' ≤ 1 →
        a.pi k (Icc (x - r') (x + r')) ≤ ENNReal.ofReal (p.N k ^ η * r' ^ S)) →
      RowReady p a k r (p.N k ^ (-aξ)) E M →
      Nonempty (RowParent p a k r ((M + p.N k ^ ε * (1 + M)) * E) (max M (p.N k ^ ε))) := by
  obtain ⟨η, hη, N₀, hN₀, hrow⟩ := hRow S aξ ε hS haξ hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro p a k r E M hNk hM1 hM2 hKη hξE hE1 hbm hνp hπp hμ hρμ hπ R
  obtain ⟨Z, hZ⟩ : ∃ Z : Zoom, Z = parentZoom p a k r R.Q := ⟨_, rfl⟩
  have hpos_b : ∀ z ∈ R.W, |Z.coeff (a.b k z.1) 0| ≤ M := by
    intro z hz; rw [hZ]; exact R.pos_bound z hz
  have hpred : ∀ z ∈ R.W,
      |R.T z 0 + a.b k z.1 3 * R.T z 1 - Z.coeff (a.b k z.1) 4| ≤ M * E := by
    intro z hz; rw [hZ]; exact R.T_predict z hz
  have hlist : ∀ z ∈ R.W,
      (fun i => ⌊R.T z i / E⌋) ∈ R.F (hcell Z (p.N k ^ (-aξ)) (a.b k z.1) z.2) := by
    intro z hz; rw [hZ]; exact R.T_list z hz
  have hjoint : ∀ (c : Fin 2 → ℤ) (v₀ : ℤ),
      a.rho k {z | z ∈ R.W ∧ hcell Z (p.N k ^ (-aξ)) (a.b k z.1) z.2 = c ∧
        ⌊a.b k z.1 3 / p.N k ^ (-aξ)⌋ = v₀} ≤
      ENNReal.ofReal (M * (p.N k ^ (-aξ)) ^ 2) *
        a.pi k (Ico ((v₀ : ℝ) * p.N k ^ (-aξ)) (((v₀ : ℝ) + 1) * p.N k ^ (-aξ))) *
        (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r R.Q)) := by
    intro c v₀; rw [hZ]; exact R.joint_cap c v₀
  have hZq : Z.q = a.q k r := by rw [hZ]; rfl
  have hZt : Z.t₀ = blockStart (a.T k r) (a.j k r R.Q) := by rw [hZ]; rfl
  have hN2 : 2 ≤ p.N k := le_trans hN₀ hNk
  have hNpos : 0 < p.N k := by linarith
  have hq : 0 < a.q k r := q_pos a k r
  have hqZ : 0 < Z.q := hZq ▸ hq
  have hqne : Z.q ≠ 0 := hqZ.ne'
  have hMη : M ≤ p.N k ^ η := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hνA_top : a.nu k (a.A k r R.Q) ≠ ⊤ := measure_ne_top _ _
  have hWt0 : ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q) ≠ 0 :=
    mul_ne_zero (by simp [hqZ]) R.prior_ne
  have hWtt : ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνA_top
  -- facts on `W`
  have hW_b' : ∀ z ∈ R.W, rowB Z M (a.b k) z.1 = Z.coeff (a.b k z.1) 0 := fun z hz =>
    clampM_of_abs_le (hpos_b z hz)
  have hW_v' : ∀ z ∈ R.W, rowV M (a.b k) z.1 = a.b k z.1 3 := fun z hz =>
    clampM_of_abs_le (R.vel_bound z hz)
  have hW_T' : ∀ z ∈ R.W, rowT Z M R.T (zoomTime Z.t₀ Z.q z) = R.T z := by
    intro z hz
    funext i
    simp only [rowT, zoomTime]
    rw [zoom_untime hqne]
    exact clampM_of_abs_le (R.T_bound z hz i)
  have hWA : R.W ⊆ a.A k r R.Q ×ˢ univ := by
    intro z hz
    exact ⟨R.B_sub_A (R.W_sub hz).1, mem_univ _⟩
  have hWblock : R.W ⊆ univ ×ˢ Icc Z.t₀ (Z.t₀ + Z.q) := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    have h2 := (R.W_sub hz).2
    simp only [block] at h2
    rw [interval_eq] at h2
    rw [hZt, hZq]
    exact h2
  have hrowk := hrow (p.N k) hNk α (condPrior (a.nu k) (a.A k r R.Q))
    (zoomLaw (a.rho k) R.W Z.t₀ Z.q (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q)))
    (rowB Z M (a.b k)) (rowV M (a.b k)) (rowH Z (a.b k)) (rowT Z M R.T) (a.pi k) E R.F
  beta_reduce at hrowk
  -- measurability
  have hcoeff : ∀ i : Fin 6, Measurable (fun l => Z.coeff (a.b k l) i) :=
    measurable_coeff_comp Z hbm
  have h1 : Measurable (rowB Z M (a.b k)) := (measurable_clampM M).comp (hcoeff 0)
  have h2 : Measurable (rowV M (a.b k)) :=
    (measurable_clampM M).comp ((measurable_pi_apply 3).comp hbm)
  have h3 : Measurable (rowH Z (a.b k)) := hcoeff 4
  have hmapT : Measurable (fun w : α × ℝ => (w.1, Z.t₀ + Z.q * w.2)) := by fun_prop
  have h4 : Measurable (rowT Z M R.T) := by
    refine measurable_pi_iff.mpr fun i => ?_
    exact (measurable_clampM M).comp ((measurable_pi_apply i).comp (R.measurable_T.comp hmapT))
  have h5 : IsProbabilityMeasure (condPrior (a.nu k) (a.A k r R.Q)) :=
    condPrior_isProbability _ _ R.prior_ne hνA_top
  have h9 : ∀ l, |rowB Z M (a.b k) l| + |rowV M (a.b k) l| ≤ p.N k ^ η := by
    intro l
    have := abs_clampM_le (x := Z.coeff (a.b k l) 0) hM0
    have := abs_clampM_le (x := a.b k l 3) hM0
    simp only [rowB, rowV]
    linarith
  have h10 : zoomLaw (a.rho k) R.W Z.t₀ Z.q (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q)) ≤
      ENNReal.ofReal (p.N k ^ η) • (condPrior (a.nu k) (a.A k r R.Q)).prod volume := by
    have hρK : a.rho k ≤ ENNReal.ofReal (p.K k) • (a.nu k).prod volume := hρμ.trans hμ
    refine (zoomLaw_le hρK R.measurable_A R.measurable_W hWA hqZ).trans ?_
    exact IsOrderedSMul.smul_le_smul_right _ _ (ENNReal.ofReal_le_ofReal hKη) _
  have h11 : zoomLaw (a.rho k) R.W Z.t₀ Z.q (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))
      (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    zoomLaw_compl_unit _ R.measurable_W hqZ _ hWblock
  have h12 : ENNReal.ofReal (p.N k ^ (-η)) ≤
      zoomLaw (a.rho k) R.W Z.t₀ Z.q (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q)) univ := by
    rw [zoomLaw_univ _ R.measurable_W]
    have hmass := R.mass
    rw [← hZq] at hmass
    have hsplit : ENNReal.ofReal (Z.q / M) * a.nu k (a.A k r R.Q) =
        ENNReal.ofReal M⁻¹ * (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q)) := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul hqZ.le]
      ring
    rw [hsplit] at hmass
    calc ENNReal.ofReal (p.N k ^ (-η)) ≤ ENNReal.ofReal M⁻¹ := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.rpow_neg hNpos.le]
          exact inv_anti₀ (by linarith) hMη
      _ = (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))⁻¹ *
            (ENNReal.ofReal M⁻¹ * (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))) := by
          rw [mul_comm (ENNReal.ofReal M⁻¹), ← mul_assoc, ENNReal.inv_mul_cancel hWt0 hWtt,
            one_mul]
      _ ≤ _ := by gcongr
  have hcellm := measurable_rowCell h1 h2 (p.N k ^ (-aξ))
  have hW_cell : ∀ z ∈ R.W, (fun i => ⌊(![(zoomTime Z.t₀ Z.q z).2,
      rowB Z M (a.b k) (zoomTime Z.t₀ Z.q z).1 +
        (zoomTime Z.t₀ Z.q z).2 * rowV M (a.b k) (zoomTime Z.t₀ Z.q z).1] : Fin 2 → ℝ) i /
          p.N k ^ (-aξ)⌋) = hcell Z (p.N k ^ (-aξ)) (a.b k z.1) z.2 := by
    intro z hz
    funext i
    simp only [zoomTime, hcell, hpos]
    rw [hW_b' z hz, hW_v' z hz]
  have h14 : ∀ (p₀ : Fin 2 → ℤ) (j : ℤ),
      zoomLaw (a.rho k) R.W Z.t₀ Z.q (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))
        {w | (fun i => ⌊(![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] : Fin 2 → ℝ) i /
            p.N k ^ (-aξ)⌋) = p₀ ∧ ⌊rowV M (a.b k) w.1 / p.N k ^ (-aξ)⌋ = j} ≤
      ENNReal.ofReal (p.N k ^ η * (p.N k ^ (-aξ)) ^ 2) *
        a.pi k (Ico ((j : ℝ) * p.N k ^ (-aξ)) (((j : ℝ) + 1) * p.N k ^ (-aξ))) := by
    intro p₀ j
    have hmeas : MeasurableSet {w : α × ℝ | (fun i => ⌊(![w.2, rowB Z M (a.b k) w.1 +
        w.2 * rowV M (a.b k) w.1] : Fin 2 → ℝ) i / p.N k ^ (-aξ)⌋) = p₀ ∧
          ⌊rowV M (a.b k) w.1 / p.N k ^ (-aξ)⌋ = j} := by
      refine MeasurableSet.inter (hcellm (measurableSet_singleton p₀)) ?_
      exact ((h2.comp measurable_fst).div_const _).floor (measurableSet_singleton j)
    rw [zoomLaw_apply _ R.measurable_W _ _ _ hmeas]
    have hsub : R.W ∩ zoomTime Z.t₀ Z.q ⁻¹' {w : α × ℝ | (fun i => ⌊(![w.2,
        rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] : Fin 2 → ℝ) i / p.N k ^ (-aξ)⌋) = p₀ ∧
          ⌊rowV M (a.b k) w.1 / p.N k ^ (-aξ)⌋ = j} ⊆
        {z | z ∈ R.W ∧ hcell Z (p.N k ^ (-aξ)) (a.b k z.1) z.2 = p₀ ∧
          ⌊a.b k z.1 3 / p.N k ^ (-aξ)⌋ = j} := by
      rintro z ⟨hzW, hz1, hz2⟩
      refine ⟨hzW, ?_, ?_⟩
      · rw [← hW_cell z hzW]; exact hz1
      · have : (zoomTime Z.t₀ Z.q z).1 = z.1 := rfl
        rw [this, hW_v' z hzW] at hz2
        exact hz2
    have hcap := (measure_mono hsub).trans (hjoint p₀ j)
    rw [← hZq] at hcap
    calc (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))⁻¹ * a.rho k (R.W ∩ zoomTime Z.t₀ Z.q ⁻¹'
          {w : α × ℝ | (fun i => ⌊(![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
            Fin 2 → ℝ) i / p.N k ^ (-aξ)⌋) = p₀ ∧
              ⌊rowV M (a.b k) w.1 / p.N k ^ (-aξ)⌋ = j})
        ≤ (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))⁻¹ *
            (ENNReal.ofReal (M * (p.N k ^ (-aξ)) ^ 2) *
              a.pi k (Ico ((j : ℝ) * p.N k ^ (-aξ)) (((j : ℝ) + 1) * p.N k ^ (-aξ))) *
              (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))) := by gcongr
      _ = ENNReal.ofReal (M * (p.N k ^ (-aξ)) ^ 2) *
              a.pi k (Ico ((j : ℝ) * p.N k ^ (-aξ)) (((j : ℝ) + 1) * p.N k ^ (-aξ))) := by
          rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hWt0 hWtt, mul_one]
      _ ≤ _ := by
          gcongr
  have h15 : ∀ p₀ : Fin 2 → ℤ, ((R.F p₀).card : ℝ) ≤ p.N k ^ η :=
    fun p₀ => (R.F_card p₀).trans hMη
  have hE0 : 0 ≤ E := le_trans (Real.rpow_nonneg hNpos.le _) hξE
  have h16 : ∀ᵐ w ∂zoomLaw (a.rho k) R.W Z.t₀ Z.q (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q)),
      (∀ j : Fin 2, |rowT Z M R.T w j| ≤ p.N k ^ η) ∧
      ((fun j => ⌊rowT Z M R.T w j / E⌋) ∈ R.F (fun i => ⌊(![w.2, rowB Z M (a.b k) w.1 +
          w.2 * rowV M (a.b k) w.1] : Fin 2 → ℝ) i / p.N k ^ (-aξ)⌋)) ∧
      |rowT Z M R.T w 0 + rowV M (a.b k) w.1 * rowT Z M R.T w 1 - rowH Z (a.b k) w.1| ≤
        p.N k ^ η * E := by
    have hTm : ∀ j : Fin 2, Measurable (fun w => rowT Z M R.T w j) :=
      fun j => (measurable_pi_apply j).comp h4
    have hfloorT : Measurable (fun w : α × ℝ => fun j : Fin 2 => ⌊rowT Z M R.T w j / E⌋) :=
      measurable_pi_iff.mpr fun j => ((hTm j).div_const E).floor
    have hmP : MeasurableSet {w : α × ℝ | (∀ j : Fin 2, |rowT Z M R.T w j| ≤ p.N k ^ η) ∧
        ((fun j => ⌊rowT Z M R.T w j / E⌋) ∈ R.F (fun i => ⌊(![w.2, rowB Z M (a.b k) w.1 +
          w.2 * rowV M (a.b k) w.1] : Fin 2 → ℝ) i / p.N k ^ (-aξ)⌋)) ∧
        |rowT Z M R.T w 0 + rowV M (a.b k) w.1 * rowT Z M R.T w 1 - rowH Z (a.b k) w.1| ≤
          p.N k ^ η * E} := by
      have hA : MeasurableSet {w : α × ℝ | ∀ j : Fin 2, |rowT Z M R.T w j| ≤ p.N k ^ η} := by
        have : {w : α × ℝ | ∀ j : Fin 2, |rowT Z M R.T w j| ≤ p.N k ^ η} =
            ⋂ j : Fin 2, {w | |rowT Z M R.T w j| ≤ p.N k ^ η} := by
          ext w; simp
        rw [this]
        exact MeasurableSet.iInter fun j => measurableSet_le (hTm j).abs measurable_const
      have hB : MeasurableSet {w : α × ℝ | (fun j => ⌊rowT Z M R.T w j / E⌋) ∈
          R.F (fun i => ⌊(![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
            Fin 2 → ℝ) i / p.N k ^ (-aξ)⌋)} := by
        have hpair : Measurable (fun w : α × ℝ => ((fun j : Fin 2 => ⌊rowT Z M R.T w j / E⌋),
            (fun i : Fin 2 => ⌊(![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
              Fin 2 → ℝ) i / p.N k ^ (-aξ)⌋))) := hfloorT.prodMk hcellm
        exact hpair
          (Set.to_countable {pr : (Fin 2 → ℤ) × (Fin 2 → ℤ) | pr.1 ∈ R.F pr.2}).measurableSet
      have hC : MeasurableSet {w : α × ℝ | |rowT Z M R.T w 0 + rowV M (a.b k) w.1 *
          rowT Z M R.T w 1 - rowH Z (a.b k) w.1| ≤ p.N k ^ η * E} := by
        refine measurableSet_le ?_ measurable_const
        exact (((hTm 0).add ((h2.comp measurable_fst).mul (hTm 1))).sub
          (h3.comp measurable_fst)).abs
      exact hA.inter (hB.inter hC)
    refine ae_zoomLaw (a.rho k) R.measurable_W Z.t₀ Z.q _ hmP
      (Filter.Eventually.of_forall fun z hz => ?_)
    have hT := hW_T' z hz
    have h1z : (zoomTime Z.t₀ Z.q z).1 = z.1 := rfl
    refine ⟨fun j => ?_, ?_, ?_⟩
    · rw [hT]; exact (R.T_bound z hz j).trans hMη
    · rw [hT, hW_cell z hz]; exact hlist z hz
    · rw [hT, h1z, hW_v' z hz]
      simp only [rowH]
      exact (hpred z hz).trans (mul_le_mul_of_nonneg_right hMη hE0)
  obtain ⟨B, ℓ, hBℓ, hmassRow⟩ :=
    hrowk h1 h2 h3 h4 h5 hπp hξE hE1 h9 h10 h11 h12 hπ h14 h15 h16
  have hTm : ∀ j : Fin 2, Measurable (fun w => rowT Z M R.T w j) :=
    fun j => (measurable_pi_apply j).comp h4
  have hEvm : MeasurableSet {w : α × ℝ |
      |rowT Z M R.T w 0 - B 0 + ℓ * (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
        Fin 2 → ℝ) 1| ≤ p.N k ^ ε * E ∧
      |rowT Z M R.T w 1 - B 1 - ℓ * (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
        Fin 2 → ℝ) 0| ≤ p.N k ^ ε * E} := by
    have hz1 : Measurable (fun w : α × ℝ =>
        (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] : Fin 2 → ℝ) 1) := by
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact (h1.comp measurable_fst).add (measurable_snd.mul (h2.comp measurable_fst))
    have hz0 : Measurable (fun w : α × ℝ =>
        (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] : Fin 2 → ℝ) 0) := by
      simp only [Fin.isValue, Matrix.cons_val_zero]
      exact measurable_snd
    have hA : MeasurableSet {w : α × ℝ |
        |rowT Z M R.T w 0 - B 0 + ℓ * (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
          Fin 2 → ℝ) 1| ≤ p.N k ^ ε * E} :=
      measurableSet_le (((hTm 0).sub_const _).add (hz1.const_mul ℓ)).abs measurable_const
    have hB : MeasurableSet {w : α × ℝ |
        |rowT Z M R.T w 1 - B 1 - ℓ * (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
          Fin 2 → ℝ) 0| ≤ p.N k ^ ε * E} :=
      measurableSet_le (((hTm 1).sub_const _).sub (hz0.const_mul ℓ)).abs measurable_const
    exact hA.inter hB
  rw [zoomLaw_apply _ R.measurable_W _ _ _ hEvm] at hmassRow
  have hGm : MeasurableSet (R.W ∩ zoomTime Z.t₀ Z.q ⁻¹' {w : α × ℝ |
      |rowT Z M R.T w 0 - B 0 + ℓ * (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
        Fin 2 → ℝ) 1| ≤ p.N k ^ ε * E ∧
      |rowT Z M R.T w 1 - B 1 - ℓ * (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
        Fin 2 → ℝ) 0| ≤ p.N k ^ ε * E}) :=
    R.measurable_W.inter (measurable_zoomTime Z.t₀ Z.q hEvm)
  have hNε : 0 < p.N k ^ ε := Real.rpow_pos_of_pos hNpos ε
  have hM'pos : 0 < max M (p.N k ^ ε) := lt_of_lt_of_le hNε (le_max_right _ _)
  refine ⟨{
    Q := R.Q
    B := B
    lam := ℓ
    G := _
    measurable_G := hGm
    G_sub := fun z hz => R.W_sub hz.1
    mass := ?_
    B_le := ?_
    lam_le := ?_
    row := ?_ }⟩
  · -- the mass of the pulled-back Row event
    have hρG : ENNReal.ofReal (p.N k ^ (-ε)) * (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q)) ≤
        a.rho k (R.W ∩ zoomTime Z.t₀ Z.q ⁻¹' {w : α × ℝ |
          |rowT Z M R.T w 0 - B 0 + ℓ * (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
            Fin 2 → ℝ) 1| ≤ p.N k ^ ε * E ∧
          |rowT Z M R.T w 1 - B 1 - ℓ * (![w.2, rowB Z M (a.b k) w.1 + w.2 * rowV M (a.b k) w.1] :
            Fin 2 → ℝ) 0| ≤ p.N k ^ ε * E}) := by
      calc ENNReal.ofReal (p.N k ^ (-ε)) * (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))
          ≤ (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q))⁻¹ * a.rho k _ *
              (ENNReal.ofReal Z.q * a.nu k (a.A k r R.Q)) := by gcongr
        _ = _ := by
            rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hWt0 hWtt, one_mul]
    refine le_trans ?_ hρG
    rw [← hZq, ← mul_assoc]
    gcongr
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le _)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hNpos.le, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hNε (le_max_right _ _)) hqZ.le
  · have := abs_nonneg ℓ
    exact le_trans (by linarith) (le_max_right _ _)
  · have := abs_nonneg (B 0)
    have := abs_nonneg (B 1)
    exact le_trans (by linarith) (le_max_right _ _)
  · rintro z ⟨hzW, hz1, hz2⟩
    have hT := hW_T' z hzW
    have h1z : (zoomTime Z.t₀ Z.q z).1 = z.1 := rfl
    rw [hT, h1z, hW_b' z hzW, hW_v' z hzW] at hz1 hz2
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, zoomTime] at hz1 hz2
    rw [← hZ]
    have he := hpred z hzW
    have hb3 := R.vel_bound z hzW
    set τ := (z.2 - Z.t₀) / Z.q
    have key : Z.coeff (a.b k z.1) 4 - B 0 - B 1 * a.b k z.1 3 + ℓ * Z.coeff (a.b k z.1) 0 =
        (R.T z 0 - B 0 + ℓ * (Z.coeff (a.b k z.1) 0 + τ * a.b k z.1 3)) +
        a.b k z.1 3 * (R.T z 1 - B 1 - ℓ * τ) -
        (R.T z 0 + a.b k z.1 3 * R.T z 1 - Z.coeff (a.b k z.1) 4) := by ring
    rw [key]
    have hw : |a.b k z.1 3 * (R.T z 1 - B 1 - ℓ * τ)| ≤ M * (p.N k ^ ε * E) := by
      rw [abs_mul]
      exact mul_le_mul hb3 hz2 (abs_nonneg _) hM0
    calc |(R.T z 0 - B 0 + ℓ * (Z.coeff (a.b k z.1) 0 + τ * a.b k z.1 3)) +
          a.b k z.1 3 * (R.T z 1 - B 1 - ℓ * τ) -
          (R.T z 0 + a.b k z.1 3 * R.T z 1 - Z.coeff (a.b k z.1) 4)|
        ≤ |R.T z 0 - B 0 + ℓ * (Z.coeff (a.b k z.1) 0 + τ * a.b k z.1 3)| +
          |a.b k z.1 3 * (R.T z 1 - B 1 - ℓ * τ)| +
          |R.T z 0 + a.b k z.1 3 * R.T z 1 - Z.coeff (a.b k z.1) 4| := by
          have := abs_sub (R.T z 0 - B 0 + ℓ * (Z.coeff (a.b k z.1) 0 + τ * a.b k z.1 3) +
            a.b k z.1 3 * (R.T z 1 - B 1 - ℓ * τ))
            (R.T z 0 + a.b k z.1 3 * R.T z 1 - Z.coeff (a.b k z.1) 4)
          have := abs_add_le (R.T z 0 - B 0 + ℓ * (Z.coeff (a.b k z.1) 0 + τ * a.b k z.1 3))
            (a.b k z.1 3 * (R.T z 1 - B 1 - ℓ * τ))
          linarith
      _ ≤ p.N k ^ ε * E + M * (p.N k ^ ε * E) + M * E := by linarith
      _ = (M + p.N k ^ ε * (1 + M)) * E := by ring

end

end Submission.Obl.k4_narrow_projected_row_parents
