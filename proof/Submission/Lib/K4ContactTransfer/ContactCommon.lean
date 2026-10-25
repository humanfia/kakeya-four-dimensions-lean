import Mathlib
import Submission.Lib.K4ContactTransfer.ContactInstance

/-!
# Basic hypotheses of the zoomed contact instance

For one input index: the conditioned prior is a probability measure, the zoomed
law is dominated by the original constant times the conditioned prior and
Lebesgue measure, lives in unit time, keeps a dense part of the retained
contact set after pruning, and the normalized trajectory coefficients are
bounded on the parent assignment.
-/

namespace Submission.Lib.K4ContactTransfer

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace PreparedModel

variable {p : Parameters} {a : PreparedModel α} {R : ℝ} {k : ℕ} {s : ℝ}

theorem AtlasAt.transverse_box (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) {l : α}
    (hl : l ∈ a.A k s i) {t : ℝ} (ht : t ∈ a.block k s i) :
    |(a.b k l 1 + t * a.b k l 4) - a.c k s i 2 - t * a.c k s i 3 -
        a.c k s i 4 * (a.b k l 0 + t * a.b k l 3)| ≤ p.K k * a.q k s * narrow p k s := by
  have := (((h.2.2.2.2.1 i).2.2.2.2.2.1 l hl t ht).2.1)
  simpa [PreparedModel.x, Submission.Lib.K4ContactNormalization.point] using this

theorem AtlasAt.strip (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) {l : α}
    (hl : l ∈ a.A k s i) :
    |a.b k l 4 - a.c k s i 3 - a.c k s i 4 * a.b k l 3| ≤ p.K k * narrow p k s := by
  have ht := blockStart_mem (a.T k s) (a.j k s i)
  exact ((h.2.2.2.2.1 i).2.2.2.2.2.1 l hl _ ht).2.2

theorem AtlasAt.prior_upper (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    a.nu k (a.A k s i) ≤
      ENNReal.ofReal (p.K k * width p k s ^ p.d * a.q k s ^ 2 * narrow p k s) :=
  (h.2.2.2.2.1 i).2.1

theorem AtlasAt.floor (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    ENNReal.ofReal (a.q k s / p.K k) * a.nu k (a.A k s i) ≤
      a.mu k (a.B k s i ×ˢ a.block k s i) :=
  (h.2.2.2.2.1 i).2.2.1

theorem AtlasAt.measurable_B (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    MeasurableSet (a.B k s i) := (h.2.2.1 i).2.1

/-- The parent prior is positive. -/
theorem AtlasAt.prior_pos (hp : p.Valid) (h : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    a.nu k (a.A k s i) ≠ 0 := by
  have hK : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hp.2.2.1.1 k)
  apply (lt_of_lt_of_le _ (h.prior_lower i)).ne'
  apply ENNReal.ofReal_pos.mpr
  have := width_pos p hp k s
  have := narrow_pos p hp k s
  have := q_pos a k s
  positivity

end PreparedModel

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

theorem Z_t₀ : I.Z.t₀ = blockStart (a.T I.k r) (a.j I.k r I.Q) := rfl
theorem Z_q : I.Z.q = a.q I.k r := rfl
theorem Z_w : I.Z.w = a.q I.k r * narrow p I.k r := rfl
theorem Z_a : I.Z.a = width p I.k r := rfl

theorem block_eq : a.block I.k r I.Q = Icc I.Z.t₀ (I.Z.t₀ + I.Z.q) :=
  interval_eq _ _

theorem keep_subset : I.keep ⊆ I.G := sdiff_subset

/-- Prior of the zoomed instance. -/
theorem condPrior_prob (hp : p.Valid) {R : ℝ} (hatr : a.AtlasAt p R I.k r)
    [IsProbabilityMeasure (a.nu I.k)] :
    IsProbabilityMeasure (condPrior (a.nu I.k) (a.A I.k r I.Q)) :=
  condPrior_isProbability _ _ (hatr.prior_pos hp I.Q) (measure_ne_top _ _)

/-- The tower boxes are measurable. -/
theorem measurable_towerBox {R : ℝ} (hats : ∀ j, a.AtlasAt p R I.k (I.depth j)) (x : I.Label) :
    MeasurableSet (towerBox x) :=
  ((hats x.1).measurable_B _).prod measurableSet_Icc

theorem measurable_keep {R : ℝ} (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) : MeasurableSet I.keep :=
  measurableSet_towerKeep _ hGm _ _ _ _ (I.measurable_towerBox hats)

/-- Domination of the zoomed law. -/
theorem zoom_dom (hcommon : a.Common p) {R : ℝ} (hatr : a.AtlasAt p R I.k r)
    (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) (hGsub : I.G ⊆ a.B I.k r I.Q ×ˢ a.block I.k r I.Q) :
    zoomLaw (a.mu I.k) I.keep I.Z.t₀ I.Z.q I.W ≤
      ENNReal.ofReal (p.K I.k) • (condPrior (a.nu I.k) (a.A I.k r I.Q)).prod volume := by
  have := hcommon.prob I.k
  apply zoomLaw_le (hcommon.dom I.k) (hatr.measurable_A I.Q) (I.measurable_keep hats hGm)
  · intro z hz
    exact ⟨hatr.B_sub_A I.Q (hGsub (I.keep_subset hz)).1, mem_univ _⟩
  · exact q_pos a I.k r

/-- The zoomed law lives in unit time. -/
theorem zoom_support {R : ℝ} (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) (hGsub : I.G ⊆ a.B I.k r I.Q ×ˢ a.block I.k r I.Q)
    (μ₀ : Measure (α × ℝ)) :
    zoomLaw μ₀ I.keep I.Z.t₀ I.Z.q I.W (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  apply zoomLaw_compl_unit μ₀ (I.measurable_keep hats hGm) (q_pos a I.k r)
  intro z hz
  have h2 := (hGsub (I.keep_subset hz)).2
  rw [I.block_eq] at h2
  exact ⟨mem_univ _, h2⟩

/-- The zoomed residual keeps a fixed fraction of the parent weight. -/
theorem zoom_rho_mass (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r)
    (hats : ∀ j, a.AtlasAt p R I.k (I.depth j))
    (hGm : MeasurableSet I.G) {MG : ℝ} (hMG : 0 < MG)
    (hmass : ENNReal.ofReal (a.q I.k r / MG) * a.nu I.k (a.A I.k r I.Q) ≤ a.rho I.k I.G)
    (hθ0 : 0 ≤ I.θ) (hθ : 4 * I.θ ≤ 1 / MG) :
    ENNReal.ofReal (1 / (2 * MG)) ≤
      zoomLaw (a.rho I.k) I.keep I.Z.t₀ I.Z.q I.W univ := by
  classical
  have := hcommon.prob I.k
  have hkeep := I.measurable_keep hats hGm
  rw [zoomLaw_univ _ hkeep]
  -- removed mass is small
  have hrem : a.mu I.k (I.G ∩ I.removed) ≤ ENNReal.ofReal (2 * I.θ) * I.W :=
    tower_removed_le (μ := a.mu I.k) (G := I.G) (lv := I.lv) (X := I.box) (w := I.wt)
      hθ0 I.W (M := I.M) (fun x => x.1.2) (tower_root_budget hats)
  have hρG : a.rho I.k I.G ≤ a.rho I.k I.keep + a.mu I.k (I.G ∩ I.removed) := by
    calc a.rho I.k I.G ≤ a.rho I.k I.keep + a.rho I.k (I.G ∩ I.removed) := by
          calc a.rho I.k I.G ≤ a.rho I.k (I.keep ∪ (I.G ∩ I.removed)) := by
                apply measure_mono
                intro z hz
                by_cases hr : z ∈ I.removed
                · exact Or.inr ⟨hz, hr⟩
                · exact Or.inl ⟨hz, hr⟩
            _ ≤ _ := measure_union_le _ _
      _ ≤ _ := by gcongr; exact hcommon.rho_le I.k
  have hW0 : I.W ≠ 0 := mul_ne_zero (by simp [q_pos a I.k r]) (hatr.prior_pos hp I.Q)
  have hWt : I.W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hq := q_pos a I.k r
  have hmass' : ENNReal.ofReal (1 / MG) * I.W ≤ a.rho I.k I.G := by
    refine le_trans (le_of_eq ?_) hmass
    simp only [ZoomInput.W]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  have hrem' := hrem
  have hsum : ENNReal.ofReal (1 / (2 * MG)) * I.W + ENNReal.ofReal (2 * I.θ) * I.W ≤
      ENNReal.ofReal (1 / MG) * I.W := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
    have : 1 / (2 * MG) = (1 / MG) / 2 := by field_simp
    rw [this]
    linarith
  have hkeepmass : ENNReal.ofReal (1 / (2 * MG)) * I.W ≤ a.rho I.k I.keep := by
    have h1 : ENNReal.ofReal (1 / (2 * MG)) * I.W + ENNReal.ofReal (2 * I.θ) * I.W ≤
        a.rho I.k I.keep + ENNReal.ofReal (2 * I.θ) * I.W :=
      (hsum.trans hmass').trans (hρG.trans (by gcongr))
    exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWt)).mp h1
  calc ENNReal.ofReal (1 / (2 * MG))
      = I.W⁻¹ * (ENNReal.ofReal (1 / (2 * MG)) * I.W) := by
        rw [mul_comm (ENNReal.ofReal _) I.W, ← mul_assoc, ENNReal.inv_mul_cancel hW0 hWt,
          one_mul]
    _ ≤ I.W⁻¹ * a.rho I.k I.keep := by gcongr

/-- Normalized trajectory coefficients are bounded on the parent assignment. -/
theorem zoom_coeff_bound (hp : p.Valid) (hcommon : a.Common p) {R : ℝ}
    (hatr : a.AtlasAt p R I.k r) {M₁ : ℝ} (hBle : |I.B 0| + |I.B 1| ≤ M₁)
    (hlam : |I.lam⁻¹| ≤ M₁) :
    ∀ᵐ l ∂condPrior (a.nu I.k) (a.A I.k r I.Q),
      |Zoom.nCoeff I.Z I.B I.lam (a.b I.k l) 0| + |Zoom.nCoeff I.Z I.B I.lam (a.b I.k l) 1| +
        |Zoom.nCoeff I.Z I.B I.lam (a.b I.k l) 3| + |Zoom.nCoeff I.Z I.B I.lam (a.b I.k l) 4| ≤
      2 * p.K I.k + M₁ * (2 * p.K I.k + M₁ + 2 * M₁ * p.K I.k) := by
  have hν := (hcommon I.k).2.2.2.2.2.2.2.2.1
  have hK0 : 0 ≤ p.K I.k := le_trans zero_le_one (hp.2.2.1.1 I.k)
  have hM₁ : 0 ≤ M₁ := le_trans (abs_nonneg _) hlam
  unfold condPrior
  apply Measure.ae_smul_measure
  rw [ae_restrict_iff' (hatr.measurable_A I.Q)]
  filter_upwards [hν] with l hl hlA
  set b := a.b I.k l
  have hb3 : |b 3| ≤ p.K I.k := by
    linarith [abs_nonneg (b 0), abs_nonneg (b 1), abs_nonneg (b 4)]
  have ht₀ : I.Z.t₀ ∈ a.block I.k r I.Q := blockStart_mem _ _
  have hq := q_pos a I.k r
  have hg := narrow_pos p hp I.k r
  -- the three zoomed coordinates
  have hZq : I.Z.q = a.q I.k r := rfl
  have hZw : I.Z.w = a.q I.k r * narrow p I.k r := rfl
  have hZt : I.Z.t₀ = blockStart (a.T I.k r) (a.j I.k r I.Q) := rfl
  have hZz : I.Z.z₀ = a.c I.k r I.Q 0 + blockStart (a.T I.k r) (a.j I.k r I.Q) * a.c I.k r I.Q 1 :=
    rfl
  have hZ2 : I.Z.c₂ = a.c I.k r I.Q 2 := rfl
  have hZ3 : I.Z.c₃ = a.c I.k r I.Q 3 := rfl
  have hZ4 : I.Z.c₄ = a.c I.k r I.Q 4 := rfl
  have h0 : |I.Z.coeff b 0| ≤ p.K I.k := by
    have := hatr.major_box I.Q hlA ht₀
    rw [Zoom.coeff_zero, abs_div, hZq, abs_of_pos hq, div_le_iff₀ hq, hZz, ← hZt]
    calc |b 0 + I.Z.t₀ * b 3 - (a.c I.k r I.Q 0 + I.Z.t₀ * a.c I.k r I.Q 1)|
        = |a.b I.k l 0 + I.Z.t₀ * a.b I.k l 3 - a.c I.k r I.Q 0 - I.Z.t₀ * a.c I.k r I.Q 1| := by
          simp only [b]; ring_nf
      _ ≤ p.K I.k * a.q I.k r := this
  have h1 : |I.Z.coeff b 1| ≤ p.K I.k := by
    have := hatr.transverse_box I.Q hlA ht₀
    rw [Zoom.coeff_one, abs_div, hZw, abs_of_pos (mul_pos hq hg), div_le_iff₀ (mul_pos hq hg),
      hZ2, hZ3, hZ4]
    calc |b 1 - a.c I.k r I.Q 2 - a.c I.k r I.Q 4 * b 0 +
          I.Z.t₀ * (b 4 - a.c I.k r I.Q 3 - a.c I.k r I.Q 4 * b 3)|
        = |(a.b I.k l 1 + I.Z.t₀ * a.b I.k l 4) - a.c I.k r I.Q 2 -
            I.Z.t₀ * a.c I.k r I.Q 3 -
            a.c I.k r I.Q 4 * (a.b I.k l 0 + I.Z.t₀ * a.b I.k l 3)| := by simp only [b]; ring_nf
      _ ≤ p.K I.k * a.q I.k r * narrow p I.k r := this
      _ = p.K I.k * (a.q I.k r * narrow p I.k r) := by ring
  have h4 : |I.Z.coeff b 4| ≤ p.K I.k := by
    have := hatr.strip I.Q hlA
    rw [Zoom.coeff_four, hZq, hZw, hZ3, hZ4]
    have e : a.q I.k r * (b 4 - a.c I.k r I.Q 3 - a.c I.k r I.Q 4 * b 3) /
        (a.q I.k r * narrow p I.k r) = (b 4 - a.c I.k r I.Q 3 - a.c I.k r I.Q 4 * b 3) /
          narrow p I.k r := by field_simp
    rw [e, abs_div, abs_of_pos hg, div_le_iff₀ hg]
    exact this
  -- the row normalization
  simp only [Zoom.nCoeff, Submission.Lib.K4ContactNormalization.skewCoeff, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.isValue, Zoom.coeff_three]
  have hB0 := abs_nonneg (I.B 0)
  have hB1 := abs_nonneg (I.B 1)
  have e1 : |(I.Z.coeff b 1 - I.B 1 * I.Z.coeff b 0) / I.lam| ≤ M₁ * (p.K I.k + M₁ * p.K I.k) := by
    rw [div_eq_mul_inv, abs_mul, mul_comm]
    apply mul_le_mul hlam _ (abs_nonneg _) hM₁
    calc |I.Z.coeff b 1 - I.B 1 * I.Z.coeff b 0| ≤ |I.Z.coeff b 1| + |I.B 1 * I.Z.coeff b 0| :=
          abs_sub _ _
      _ ≤ p.K I.k + M₁ * p.K I.k := by
          rw [abs_mul]
          have : |I.B 1| ≤ M₁ := by linarith
          nlinarith [abs_nonneg (I.Z.coeff b 0)]
  have e4 : |(I.Z.coeff b 4 - I.B 0 - I.B 1 * b 3) / I.lam| ≤
      M₁ * (p.K I.k + M₁ + M₁ * p.K I.k) := by
    rw [div_eq_mul_inv, abs_mul, mul_comm]
    apply mul_le_mul hlam _ (abs_nonneg _) hM₁
    calc |I.Z.coeff b 4 - I.B 0 - I.B 1 * b 3| ≤ |I.Z.coeff b 4| + |I.B 0| + |I.B 1 * b 3| := by
          calc |I.Z.coeff b 4 - I.B 0 - I.B 1 * b 3| ≤ |I.Z.coeff b 4 - I.B 0| + |I.B 1 * b 3| :=
                abs_sub _ _
            _ ≤ |I.Z.coeff b 4| + |I.B 0| + |I.B 1 * b 3| := by gcongr; exact abs_sub _ _
      _ ≤ p.K I.k + M₁ + M₁ * p.K I.k := by
          rw [abs_mul]
          have h1' : |I.B 1| ≤ M₁ := by linarith
          have h0' : |I.B 0| ≤ M₁ := by linarith
          nlinarith [abs_nonneg (b 3)]
  nlinarith [abs_nonneg (I.Z.coeff b 0)]

end ZoomInput

end

end Submission.Lib.K4ContactTransfer
