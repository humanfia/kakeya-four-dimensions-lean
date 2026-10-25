/- Adapted within this LOT tree from o218/x0764, commit a57aabc6806d303a53728cab0d5e6ea27469d825,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/ScalarCell.lean. -/
import Submission.Obl.k4_horizontal_wide_interval_return.Interface
import Submission.Obl.k4_horizontal_wide_interval_return.BlockRescale
import Submission.Obl.k4_horizontal_wide_interval_return.CellFrame
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

set_option linter.unusedVariables false

/-!
# Scalar mesh projection inside a true cell

The last step of the wide-interval proposition (paper `prop:wide-interval`, "Scalar support
after subtraction"): inside a true label with block `[t₀, t₀ + q]`, after subtracting the
transverse correction, apply scalar mesh projection in normalized `(z_t, z_Z)` with `c = 1`
(masses divided by `q ν(A)`), terminal width `N^-v` and the angular cap.  The output is one
quadratic `P(z_t, z_Z)` predicting the normalized signal to `N^ε N^-v` on WHOLE assigned
trajectories over the WHOLE block, with original mass `N^(-dv - 2ε) q ν(A)`.

The wrapper `scalar_candidate_of_mesh` of accepted o177 (`ScalarAdmissible`) does the scalar
application; this file transports its hypotheses and conclusion through the block rescaling
of `Wide/BlockRescale.lean` and the trajectory coefficients of `Wide/CellFrame.lean`.
Rate-free.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- The frozen scalar premise of o218 is o177's `ScalarMeshProjection`, verbatim. -/
theorem scalar_iff_meshProjection : Scalar ↔ ScalarMeshProjection := Iff.rfl

/-- Positions of a trajectory `t ↦ (t, b₀ + t b₃, b₁ + t b₄, b₂ + t b₅)`. -/
def lineZ (b : Fin 6 → ℝ) (t : ℝ) : ℝ := b 0 + t * b 3
def lineY (b : Fin 6 → ℝ) (t : ℝ) : ℝ := b 1 + t * b 4
def lineX (b : Fin 6 → ℝ) (t : ℝ) : ℝ := b 2 + t * b 5

namespace CellFrame

variable (F : CellFrame)

/-- The normalized `(z_t, z_Z)` cell of mesh `σ` of a trajectory at time `t`. -/
noncomputable def cellCode (σ : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 2 → ℤ :=
  ![⌊F.zt t / σ⌋, ⌊F.zZ t (lineZ b t) / σ⌋]

/-- The scalar signal of a trajectory at time `t`. -/
noncomputable def cellSig (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  F.sig t (lineZ b t) (lineY b t) (lineX b t)

/-- Scalar coefficients of the cell: the trajectory's `lineCoeffs` on `Bs`, zero elsewhere. -/
noncomputable def cellCoeffs {α : Type*} (Bs : Set α) (b : α → Fin 6 → ℝ) (l : α) :
    Fin 5 → ℝ :=
  Bs.indicator (fun l => F.lineCoeffs (b l)) l

variable {F}

theorem t₀_add_zt (hq : F.q ≠ 0) (t : ℝ) : F.t₀ + F.q * F.zt t = t := by
  unfold zt; field_simp; ring

theorem scalarY_lineCoeffs (hq : F.q ≠ 0) (b : Fin 6 → ℝ) (t : ℝ) :
    scalarY (F.lineCoeffs b) (F.zt t) = F.zZ t (lineZ b t) := by
  have h := lineCoeffs_y hq b (F.zt t)
  rw [t₀_add_zt hq] at h
  simp only [scalarY, lineZ]
  rw [h]

theorem scalarX_lineCoeffs (hq : F.q ≠ 0) (hg : F.g ≠ 0) (ha : F.a ≠ 0) (b : Fin 6 → ℝ)
    (t : ℝ) : scalarX (F.lineCoeffs b) (F.zt t) = F.cellSig b t := by
  have h := lineCoeffs_x hq hg ha b (F.zt t)
  rw [t₀_add_zt hq] at h
  simp only [scalarX, cellSig, lineZ, lineY, lineX]
  rw [h]

theorem scalarCell_lineCoeffs (hq : F.q ≠ 0) (σ : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    scalarCell (F.lineCoeffs b) (F.zt t) σ = F.cellCode σ b t := by
  simp only [scalarCell, cellCode, scalarY_lineCoeffs hq]

theorem continuous_lineCoeffs : Continuous F.lineCoeffs := by
  refine continuous_pi fun i => ?_
  fin_cases i <;>
    simp only [lineCoeffs, y₀, y₁, u₀, u₁, r₀, r₁, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val] <;> fun_prop

theorem measurable_cellCoeffs {α : Type*} [MeasurableSpace α] {Bs : Set α}
    (hBs : MeasurableSet Bs) {b : α → Fin 6 → ℝ} (hb : Measurable b) :
    Measurable (F.cellCoeffs Bs b) :=
  (continuous_lineCoeffs.measurable.comp hb).indicator hBs

end CellFrame


theorem measurable_scalarCell {α : Type*} [MeasurableSpace α] {b : α → Fin 5 → ℝ}
    (hb : Measurable b) (σ : ℝ) :
    Measurable fun p : α × ℝ => scalarCell (b p.1) p.2 σ := by
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · simp only [scalarCell, Fin.zero_eta, Matrix.cons_val_zero]
    exact (measurable_snd.div_const σ).floor
  · simp only [scalarCell, Fin.mk_one, Matrix.cons_val_one]
    have h0 : Measurable fun p : α × ℝ => b p.1 0 :=
      (measurable_pi_apply 0).comp (hb.comp measurable_fst)
    have h1 : Measurable fun p : α × ℝ => b p.1 1 :=
      (measurable_pi_apply 1).comp (hb.comp measurable_fst)
    exact (((h0.add (measurable_snd.mul h1))).div_const σ).floor

theorem measurable_scalarX {α : Type*} [MeasurableSpace α] {b : α → Fin 5 → ℝ}
    (hb : Measurable b) : Measurable fun p : α × ℝ => scalarX (b p.1) p.2 := by
  have hc : ∀ i, Measurable fun p : α × ℝ => b p.1 i := fun i =>
    (measurable_pi_apply i).comp (hb.comp measurable_fst)
  simp only [scalarX]
  exact ((hc 2).add (measurable_snd.mul (hc 3))).add ((measurable_snd.pow_const 2).mul (hc 4))

/-- **Scalar mesh projection inside a true cell.** -/
theorem scalar_cell_candidate (hScalar : Scalar) {d v m S U ε : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hv : 0 < v) (hvm : v < m) (hS : 0 < S) (hU : 0 < U) (hUm : U < m) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (lam : Measure (α × ℝ))
      (b : α → Fin 6 → ℝ) (A Bs : Set α) (F : CellFrame),
      Measurable b → MeasurableSet A → MeasurableSet Bs → Bs ⊆ A →
      IsProbabilityMeasure ν → ν A ≠ 0 → 0 < F.q → 0 < F.g → 0 < F.a →
      lam ≤ ENNReal.ofReal (N ^ η) • ν.prod volume →
      (∀ᵐ p ∂lam, p.1 ∈ Bs ∧ p.2 ∈ Icc F.t₀ (F.t₀ + F.q)) →
      ENNReal.ofReal (N ^ (-η)) * (ENNReal.ofReal F.q * ν A) ≤ lam univ →
      (∀ l ∈ Bs, ∀ i, |F.lineCoeffs (b l) i| ≤ N ^ η) →
      (∀ (r : ℝ) (q₀ : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ v →
        lam {p | F.cellCode (N ^ (-m)) (b p.1) p.2 = q₀ ∧
          ⌊F.cellSig (b p.1) p.2 / N ^ (-r)⌋ = j} ≤
          ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-r)) ^ d) *
            (ENNReal.ofReal F.q * ν A)) →
      (∃ Fs : Finset ((Fin 2 → ℤ) × ℤ),
        (Fs.card : ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ η * (N ^ (-v)) ^ (-d) ∧
        ∀ᵐ p ∂lam, (F.cellCode (N ^ (-m)) (b p.1) p.2,
          ⌊F.cellSig (b p.1) p.2 / N ^ (-v)⌋) ∈ Fs) →
      (∀ (r : ℝ) (q₀ : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U →
        lam {p | F.cellCode (N ^ (-m)) (b p.1) p.2 = q₀ ∧
          ⌊F.cellSig (b p.1) p.2 / N ^ (-v)⌋ = j ∧ ⌊F.y₁ (b p.1) / N ^ (-r)⌋ = k} ≤
          ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-v)) ^ d * N ^ (-S * r)) *
            (ENNReal.ofReal F.q * ν A)) →
      ∃ G : ScalarCandidate N v m ε,
        ENNReal.ofReal (scalarCandidateFloor N 1 d v ε) * (ENNReal.ofReal F.q * ν A) ≤
          lam {p | p.1 ∈ Bs ∧ p.2 ∈ Icc F.t₀ (F.t₀ + F.q) ∧ ∀ z ∈ Icc (0 : ℝ) 1,
            |F.cellSig (b p.1) (F.t₀ + F.q * z) -
              MvPolynomial.eval ![z, F.zZ (F.t₀ + F.q * z) (lineZ (b p.1) (F.t₀ + F.q * z))]
                G.P| ≤ N ^ ε * N ^ (-v)} := by
  obtain ⟨η, hη, N₀, hN₀, hmain⟩ :=
    scalar_candidate_of_mesh (scalar_iff_meshProjection.mp hScalar) hd hd1 hv hvm one_pos hS hU
      hUm hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν lam b A Bs F hb hA hBs hBA hν hνA hq hg ha hdom hsupp hmass hcoef hcap
    hsupport hang
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hq0 : F.q ≠ 0 := hq.ne'
  have hg0 : F.g ≠ 0 := hg.ne'
  have ha0 : F.a ≠ 0 := ha.ne'
  have hνtop : ν A ≠ ⊤ := measure_ne_top ν A
  set W : ℝ≥0∞ := ENNReal.ofReal F.q * ν A with hWdef
  have hW0 : W ≠ 0 := mul_ne_zero (by simpa using hq) hνA
  have hWtop : W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνtop
  set ν' : Measure α := (ν A)⁻¹ • ν.restrict A with hν'def
  set μ' : Measure (α × ℝ) := W⁻¹ • lam.map (blockRescale F.t₀ F.q) with hμ'def
  set b' : α → Fin 5 → ℝ := F.cellCoeffs Bs b with hb'def
  have hmeasR := measurable_blockRescale (α := α) F.t₀ F.q
  have hb' : Measurable b' := CellFrame.measurable_cellCoeffs hBs hb
  have htrans : ∀ T : Set (α × ℝ), MeasurableSet T →
      μ' T = W⁻¹ * lam (blockRescale F.t₀ F.q ⁻¹' T) := by
    intro T hT
    simp only [μ', Measure.smul_apply, smul_eq_mul, Measure.map_apply hmeasR hT]
  have hsuppA : ∀ᵐ p ∂lam, p.1 ∈ A := hsupp.mono fun p hp => hBA hp.1
  -- on the support, the scalar data of `b'` are the cell data of `b`
  have hcellEq : ∀ p : α × ℝ, p.1 ∈ Bs →
      scalarCell (b' p.1) (F.zt p.2) (N ^ (-m)) = F.cellCode (N ^ (-m)) (b p.1) p.2 ∧
      scalarX (b' p.1) (F.zt p.2) = F.cellSig (b p.1) p.2 ∧
      b' p.1 1 = F.y₁ (b p.1) := by
    intro p hp
    have hbp : b' p.1 = F.lineCoeffs (b p.1) := by
      simp only [b', CellFrame.cellCoeffs, Set.indicator_of_mem hp]
    refine ⟨?_, ?_, ?_⟩
    · rw [hbp]; exact CellFrame.scalarCell_lineCoeffs hq0 _ _ _
    · rw [hbp]; exact CellFrame.scalarX_lineCoeffs hq0 hg0 ha0 _ _
    · rw [hbp]; simp [CellFrame.lineCoeffs]
  have hbr : ∀ p : α × ℝ, blockRescale F.t₀ F.q p = (p.1, F.zt p.2) := fun p => rfl
  -- admissibility of the rescaled cell law
  have hadm : ScalarAdmissible N η d v m 1 S U 1 ν' b' μ' := by
    refine ⟨hb', isProbabilityMeasure_cond ν hνA hνtop, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · exact normalized_blockRescale_le ν hA hνA hνtop F.t₀ F.q hq lam _ hdom hsuppA
    · rw [htrans _ (MeasurableSet.univ.prod measurableSet_Icc).compl]
      have h0 : lam (blockRescale F.t₀ F.q ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) = 0 := by
        refine measure_eq_zero_iff_ae_notMem.mpr ?_
        filter_upwards [hsupp] with p hp
        simp only [mem_preimage, hbr, mem_compl_iff, mem_prod, mem_univ, true_and, not_not,
          mem_Icc, CellFrame.zt]
        exact ⟨div_nonneg (by linarith [hp.2.1]) hq.le,
          (div_le_one hq).mpr (by linarith [hp.2.2])⟩
      rw [h0, mul_zero]
    · intro l i
      by_cases hl : l ∈ Bs
      · simp only [b', CellFrame.cellCoeffs, Set.indicator_of_mem hl]; exact hcoef l hl i
      · simp only [b', CellFrame.cellCoeffs, Set.indicator_of_notMem hl, Pi.zero_apply, abs_zero]
        exact (Real.rpow_pos_of_pos hNpos _).le
    · rw [Real.rpow_neg_one]; exact inv_le_one_of_one_le₀ hN1
    · rw [Real.rpow_one]; exact hN1
    · intro r q₀ j hr hrv
      have hmeasE : MeasurableSet {p : α × ℝ | scalarCell (b' p.1) p.2 (N ^ (-m)) = q₀ ∧
          ⌊scalarX (b' p.1) p.2 / N ^ (-r)⌋ = j} :=
        ((measurable_scalarCell hb' _) (measurableSet_singleton q₀)).inter
          (((measurable_scalarX hb').div_const _).floor (measurableSet_singleton j))
      rw [htrans _ hmeasE]
      have hle : lam (blockRescale F.t₀ F.q ⁻¹' {p : α × ℝ |
            scalarCell (b' p.1) p.2 (N ^ (-m)) = q₀ ∧
            ⌊scalarX (b' p.1) p.2 / N ^ (-r)⌋ = j}) ≤
          lam {p | F.cellCode (N ^ (-m)) (b p.1) p.2 = q₀ ∧
            ⌊F.cellSig (b p.1) p.2 / N ^ (-r)⌋ = j} := by
        apply measure_mono_ae
        filter_upwards [hsupp] with p hp hmem
        obtain ⟨h1, h2, -⟩ := hcellEq p hp.1
        simp only [mem_preimage, hbr, mem_ofPred_eq] at hmem
        rw [h1, h2] at hmem
        exact hmem
      calc W⁻¹ * lam (blockRescale F.t₀ F.q ⁻¹' _)
          ≤ W⁻¹ * (ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-r)) ^ d) * W) :=
            mul_le_mul' le_rfl (hle.trans (hcap r q₀ j hr hrv))
        _ = ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * 1 * (N ^ (-r)) ^ d) := by
            rw [mul_comm (ENNReal.ofReal _) W, ← mul_assoc, ENNReal.inv_mul_cancel hW0 hWtop,
              one_mul, mul_one]
    · obtain ⟨Fs, hFs, hFsae⟩ := hsupport
      refine ⟨Fs, by simpa using hFs, ?_⟩
      have hmeasG : MeasurableSet {p : α × ℝ | (scalarCell (b' p.1) p.2 (N ^ (-m)),
          ⌊scalarX (b' p.1) p.2 / N ^ (-v)⌋) ∈ Fs} :=
        ((measurable_scalarCell hb' _).prodMk
          ((measurable_scalarX hb').div_const _).floor) (Fs.finite_toSet.measurableSet)
      rw [ae_iff]
      change μ' {p : α × ℝ | (scalarCell (b' p.1) p.2 (N ^ (-m)),
          ⌊scalarX (b' p.1) p.2 / N ^ (-v)⌋) ∈ Fs}ᶜ = 0
      rw [htrans _ hmeasG.compl]
      have h0 : lam (blockRescale F.t₀ F.q ⁻¹' {p : α × ℝ | (scalarCell (b' p.1) p.2 (N ^ (-m)),
          ⌊scalarX (b' p.1) p.2 / N ^ (-v)⌋) ∈ Fs}ᶜ) = 0 := by
        refine measure_eq_zero_iff_ae_notMem.mpr ?_
        filter_upwards [hsupp, hFsae] with p hp hpF
        obtain ⟨h1, h2, -⟩ := hcellEq p hp.1
        simp only [mem_preimage, hbr, mem_compl_iff, mem_ofPred_eq, not_not]
        rw [h1, h2]
        exact hpF
      rw [h0, mul_zero]
    · intro r q₀ j k hr hrU
      have hb1 : Measurable fun p : α × ℝ => b' p.1 1 :=
        (measurable_pi_apply 1).comp (hb'.comp measurable_fst)
      have hmeasE : MeasurableSet {p : α × ℝ | scalarCell (b' p.1) p.2 (N ^ (-m)) = q₀ ∧
          ⌊scalarX (b' p.1) p.2 / N ^ (-v)⌋ = j ∧ ⌊b' p.1 1 / N ^ (-r)⌋ = k} :=
        ((measurable_scalarCell hb' _) (measurableSet_singleton q₀)).inter
          ((((measurable_scalarX hb').div_const _).floor (measurableSet_singleton j)).inter
            ((hb1.div_const _).floor (measurableSet_singleton k)))
      rw [htrans _ hmeasE]
      have hle : lam (blockRescale F.t₀ F.q ⁻¹' {p : α × ℝ |
            scalarCell (b' p.1) p.2 (N ^ (-m)) = q₀ ∧
            ⌊scalarX (b' p.1) p.2 / N ^ (-v)⌋ = j ∧ ⌊b' p.1 1 / N ^ (-r)⌋ = k}) ≤
          lam {p | F.cellCode (N ^ (-m)) (b p.1) p.2 = q₀ ∧
            ⌊F.cellSig (b p.1) p.2 / N ^ (-v)⌋ = j ∧ ⌊F.y₁ (b p.1) / N ^ (-r)⌋ = k} := by
        apply measure_mono_ae
        filter_upwards [hsupp] with p hp hmem
        obtain ⟨h1, h2, h3⟩ := hcellEq p hp.1
        simp only [mem_preimage, hbr, mem_ofPred_eq] at hmem
        rw [h1, h2, h3] at hmem
        exact hmem
      calc W⁻¹ * lam (blockRescale F.t₀ F.q ⁻¹' _)
          ≤ W⁻¹ * (ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-v)) ^ d * N ^ (-S * r)) *
              W) := mul_le_mul' le_rfl (hle.trans (hang r q₀ j k hr hrU))
        _ = ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * 1 * (N ^ (-v)) ^ d * N ^ (-S * r)) := by
            rw [mul_comm (ENNReal.ofReal _) W, ← mul_assoc, ENNReal.inv_mul_cancel hW0 hWtop,
              one_mul, mul_one]
  -- the rescaled law is dense
  have hmass' : ENNReal.ofReal (N ^ (-η)) ≤ μ' univ := by
    rw [htrans _ MeasurableSet.univ, preimage_univ]
    calc ENNReal.ofReal (N ^ (-η)) = W⁻¹ * (ENNReal.ofReal (N ^ (-η)) * W) := by
          rw [mul_comm (ENNReal.ofReal _) W, ← mul_assoc, ENNReal.inv_mul_cancel hW0 hWtop,
            one_mul]
      _ ≤ W⁻¹ * lam univ := mul_le_mul' le_rfl hmass
  obtain ⟨G, hG⟩ := hmain N hN α ν' μ' b' 1 hadm hmass'
  refine ⟨G, ?_⟩
  rw [htrans _ (G.measurable_fit hb')] at hG
  have hle : lam (blockRescale F.t₀ F.q ⁻¹' G.fit b') ≤
      lam {p | p.1 ∈ Bs ∧ p.2 ∈ Icc F.t₀ (F.t₀ + F.q) ∧ ∀ z ∈ Icc (0 : ℝ) 1,
        |F.cellSig (b p.1) (F.t₀ + F.q * z) -
          MvPolynomial.eval ![z, F.zZ (F.t₀ + F.q * z) (lineZ (b p.1) (F.t₀ + F.q * z))]
            G.P| ≤ N ^ ε * N ^ (-v)} := by
    apply measure_mono_ae
    filter_upwards [hsupp] with p hp hmem
    refine ⟨hp.1, hp.2, ?_⟩
    intro z hz
    simp only [mem_preimage, hbr, ScalarCandidate.fit, mem_prod, scalarFit, mem_ofPred_eq]
      at hmem
    have hfit := hmem.1 z hz
    have hbp : b' p.1 = F.lineCoeffs (b p.1) := by
      simp only [b', CellFrame.cellCoeffs, Set.indicator_of_mem hp.1]
    rw [hbp] at hfit
    have hx := CellFrame.scalarX_lineCoeffs hq0 hg0 ha0 (b p.1) (F.t₀ + F.q * z)
    have hy := CellFrame.scalarY_lineCoeffs hq0 (b p.1) (F.t₀ + F.q * z)
    rw [CellFrame.zt_line hq0] at hx hy
    rw [hx, hy] at hfit
    exact hfit
  calc ENNReal.ofReal (scalarCandidateFloor N 1 d v ε) * W
      ≤ (W⁻¹ * lam (blockRescale F.t₀ F.q ⁻¹' G.fit b')) * W := mul_le_mul' hG le_rfl
    _ = lam (blockRescale F.t₀ F.q ⁻¹' G.fit b') := by
        rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hW0 hWtop, one_mul]
    _ ≤ _ := hle

end Submission.Obl.k4_horizontal_wide_interval_return
