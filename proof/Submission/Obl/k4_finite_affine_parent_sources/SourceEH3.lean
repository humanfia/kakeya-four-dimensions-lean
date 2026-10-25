-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceEH
import Submission.Obl.k4_finite_affine_parent_sources.NativeFits

/-!
# True labels `EH3` of a source stage

Pieces of `EH3` for `SourceData.stage`: disjointness inside a relative block, the incidence
floor from a floor of the prepared set on the old label, coverage of the prepared incidences,
the fits of the normalized old tests and their hidden-derivative floor.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Model labels of one relative block are disjoint. -/
theorem stage_disjoint (unit : ℝ)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i i' : Fin (p.activeCount D.Hm (D.depth s)))
    (hne : i ≠ i') (hj : (D.stage Nk L unit ν B).j s i = (D.stage Nk L unit ν B).j s i') :
    Disjoint ((D.stage Nk L unit ν B).A s i) ((D.stage Nk L unit ν B).A s i') := by
  have hbin := D.old_bin_eq_of_relBin hp hSo s hs i i' hj
  have hne' : D.old s i ≠ D.old s i' := fun h => hne ((p.activeLabel D.Hm (D.depth s)).injective h)
  have hlev : p.lev (D.old s i) = p.lev (D.old s i') := by
    rw [D.old_level s i, D.old_level s i']
  have hw : p.world (D.old s i) = p.world (D.old s i') := by
    rw [(D.old_world s i).1, (D.old_world s i').1]
  exact hp.assignment_disjoint _ _ hne' hlev hw hbin

/-- The model preimage of a label rectangle is the old label rectangle. -/
theorem tnorm_preimage_label
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i : Fin (p.activeCount D.Hm (D.depth s))) :
    tnorm D.t₀ D.q₀ ⁻¹' (p.assigned (D.old s i) ×ˢ IS (D.relT s) (D.relBin s i)) =
      p.packet (D.old s i) := by
  ext z
  simp only [mem_preimage, tnorm, mem_prod, PathData.packet]
  rw [D.old_relBin_mem hp hSo s hs i z.2]

/-- **Incidence floor.** A floor `τ` of the prepared set on the old packet gives the model
floor with any `K ≥ τ⁻¹`. -/
theorem stage_incidence_floor (unit : ℝ) {τ : ℝ} (hτ : 0 < τ) (hKτ : τ⁻¹ ≤ D.K)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i : Fin (p.activeCount D.Hm (D.depth s)))
    (hfloor : ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
      ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i))) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(D.relT s : ℤ)) / D.K) *
        (D.stage Nk L unit ν B).ν ((D.stage Nk L unit ν B).A s i) ≤
      (D.stage Nk L unit ν B).μ
        ((D.stage Nk L unit ν B).B s i ×ˢ IS (D.relT s) (D.relBin s i)) := by
  have hc := hp.chart (D.old s i)
  have hAm : MeasurableSet (p.assigned (D.old s i)) := hc.2.2.2.2.2.2.1
  have hsubA := D.old_assigned_subset hp hSo s hs i
  have hT := (D.old_bin_div hp hSo s hs i).1
  -- model sides
  have hrect : MeasurableSet (p.assigned (D.old s i) ×ˢ IS (D.relT s) (D.relBin s i)) :=
    hAm.prod measurableSet_Icc
  show ENNReal.ofReal ((2 : ℝ) ^ (-(D.relT s : ℤ)) / D.K) *
      nuE (ν D.w₀) (p.assigned D.parent) (p.assigned (D.old s i)) ≤
    muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S
      (p.assigned (D.old s i) ×ˢ IS (D.relT s) (D.relBin s i))
  rw [muE_apply _ _ _ _ _ hrect, D.tnorm_preimage_label hp hSo s hs i]
  rw [nuE, Measure.smul_apply, Measure.restrict_apply hAm, Set.inter_eq_left.mpr hsubA,
    smul_eq_mul]
  -- the old packet mass
  have hpk : ((ν D.w₀).prod volume) (p.packet (D.old s i)) =
      ν D.w₀ (p.assigned (D.old s i)) * ENNReal.ofReal (((2 : ℝ) ^ p.T (D.depth s))⁻¹) := by
    rw [PathData.packet, Measure.prod_prod, Real.volume_Icc, D.old_level s i]
    congr 2
    rw [← sub_div]; ring
  have hcount : D.S ∩ p.counted (D.old s i) ⊆ p.packet (D.old s i) ∩ D.S := by
    intro z hz
    exact ⟨⟨(hp.counted_support _ z hz.2).2.1, (hp.counted_support _ z hz.2).2.2.1⟩, hz.1⟩
  have hge : ENNReal.ofReal τ * (ν D.w₀ (p.assigned (D.old s i)) *
      ENNReal.ofReal (((2 : ℝ) ^ p.T (D.depth s))⁻¹)) ≤
      ((ν D.w₀).prod volume) (p.packet (D.old s i) ∩ D.S) :=
    (hpk ▸ hfloor).trans (measure_mono hcount)
  refine le_trans ?_ (mul_le_mul_right hge _)
  -- arithmetic: q_rel / K * (ν A / ν A₀) ≤ (q₀ ν A₀)⁻¹ * τ * ν A * q_old
  have hq₀ := D.q₀_pos
  have hK0 : 0 < D.K := lt_of_lt_of_le (inv_pos.mpr hτ) hKτ
  have hrel : (2 : ℝ) ^ (-(D.relT s : ℤ)) = ((2 : ℝ) ^ p.T (D.depth s))⁻¹ / D.q₀ := by
    simp only [relT, q₀, zpow_neg, zpow_natCast]
    rw [div_inv_eq_mul, pow_sub₀ (2 : ℝ) two_ne_zero hT, mul_inv, inv_inv]
  rw [hrel]
  set a := ν D.w₀ (p.assigned (D.old s i))
  set a₀ := ν D.w₀ (p.assigned D.parent)
  set qo := ((2 : ℝ) ^ p.T (D.depth s))⁻¹
  have hqo : 0 < qo := by positivity
  have hle : ENNReal.ofReal (qo / D.q₀ / D.K) ≤
      ENNReal.ofReal D.q₀⁻¹ * ENNReal.ofReal τ * ENNReal.ofReal qo := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 / D.K ≤ τ := by
      rw [one_div]; exact (inv_le_comm₀ hK0 hτ).mpr hKτ
    calc qo / D.q₀ / D.K = D.q₀⁻¹ * qo * (1 / D.K) := by ring
      _ ≤ D.q₀⁻¹ * qo * τ := by gcongr
      _ = _ := by ring
  have hinv : (ENNReal.ofReal D.q₀ * a₀)⁻¹ = ENNReal.ofReal D.q₀⁻¹ * a₀⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (by simp [hq₀])) (Or.inl ENNReal.ofReal_ne_top),
      ENNReal.ofReal_inv_of_pos hq₀]
  rw [hinv]
  calc ENNReal.ofReal (qo / D.q₀ / D.K) * (a₀⁻¹ * a)
      ≤ (ENNReal.ofReal D.q₀⁻¹ * ENNReal.ofReal τ * ENNReal.ofReal qo) * (a₀⁻¹ * a) := by
        gcongr
    _ = ENNReal.ofReal D.q₀⁻¹ * a₀⁻¹ * (ENNReal.ofReal τ * (a * ENNReal.ofReal qo)) := by ring

omit hp in
/-- The model residual family lies in the terminal incidences. -/
theorem Hm_terminal (hterm : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀) :
    ∀ w, D.Hm w ⊆ TerminalInc W p.C m p.lev p.world p.counted w := by
  intro w
  by_cases hw : w = D.w₀
  · subst hw
    simpa only [Hm, worldOnly, ite_true] using hterm
  · simp only [Hm, worldOnly, hw, ite_false]
    exact empty_subset _

/-- **Coverage.** Prepared incidences lie in model labels at every interior depth. -/
theorem stage_cover (unit : ℝ) (hSm : MeasurableSet D.S)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hterm : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀)
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (hsm : D.depth s < m) :
    ∀ᵐ z ∂(D.stage Nk L unit ν B).μ, ∃ i,
      z.1 ∈ (D.stage Nk L unit ν B).B s i ∧ z.2 ∈ IS (D.relT s) (D.relBin s i) := by
  show ∀ᵐ z ∂(muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S), _
  refine ae_muE_of_forall _ _ _ _ D.q₀_pos.ne' hSm fun z hz => ?_
  have hzH : z ∈ D.Hm D.w₀ := by simpa only [Hm, worldOnly, ite_true] using hz
  obtain ⟨b, -, hzb⟩ := hp.active_labels_cover D.Hm D.w₀ (D.Hm_terminal hterm) (D.depth s) hsm hzH
  have hsup := hp.counted_support _ z hzb
  refine ⟨b, hsup.2.1, ?_⟩
  exact (D.old_relBin_mem hp hSo s hs b z.2).mp hsup.2.2.1

/-- **Fits.** The normalized old tests fit their model labels at any thickness that dominates
the old thickness ratio. -/
theorem stage_fit (unit : ℝ) (hBw : 0 < B D.w₀)
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (i : Fin (p.activeCount D.Hm (D.depth s))) (K a : ℝ)
    (hvalue : p.κ * (δ Nk (p.r (D.depth s)) / δ Nk (p.r D.i₀)) ≤ K * a)
    (hκK : p.κ ≤ K)
    (hcurv : p.κ / (δ Nk (p.r (D.depth s)) / δ Nk (p.r D.i₀)) ≤ K / a) :
    ∀ l ∈ (D.stage Nk L unit ν B).B s i,
      fitS (D.stage Nk L unit ν B).b K a ((D.stage Nk L unit ν B).F s i) l
        (IS (D.relT s) (D.relBin s i)) := by
  intro l hl
  have hc := hp.chart (D.old s i)
  have hδ : ∀ r, 0 < δ Nk r := fun r => by
    show 0 < (2 : ℝ) ^ (-(⌊r * Real.log Nk / Real.log 2⌋ : ℤ))
    positivity
  have hD : IsUnit (D.frame Nk B).F.D.det := by
    rw [D.frame_F]
    show IsUnit D.D₀.det
    rw [hD₀]
    exact isUnit_iff_ne_zero.mpr (MajorFrame.det_ne_zero (hp.chart D.parent).1)
  have hw : p.world (D.old s i) = D.w₀ := (D.old_world s i).1
  have hfit : Fits p.κ (δ Nk (p.r (D.depth s))) (B D.w₀) (p.test (D.old s i)) l
      (Icc ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))
        (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))) := by
    intro t ht
    obtain ⟨-, -, htube⟩ := hc.2.2.2.2.2.2.2.2.2.1 l hl
    obtain ⟨-, h2, h3, h4⟩ := htube t ht
    rw [D.old_level s i] at h2 h4
    rw [hw] at h3 h4
    exact ⟨h2, h3, h4⟩
  have hI : ∀ t ∈ IS (D.relT s) (D.relBin s i), (D.frame Nk B).F.t₀ + (D.frame Nk B).F.q * t ∈
      Icc ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))
        (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (D.old s i))) := by
    intro t ht
    rw [D.frame_F]
    apply (D.old_relBin_mem hp hSo s hs i _).mpr
    have hq := D.q₀_pos
    have : (D.t₀ + D.q₀ * t - D.t₀) / D.q₀ = t := by field_simp; ring
    rw [this]; exact ht
  have h := PFrame.fitS_normTest (D.frame Nk B) D.q₀_pos.ne' hD hBw (hδ _) (hδ _) rfl
    (p.test (D.old s i)) l _ _ hI hfit
  exact fitS_of_thickness_comparison _ l _ _ hvalue hκK hcurv h

/-- **Hidden-derivative floor** on the model labels. -/
theorem stage_deriv_floor (unit : ℝ) (hBw : 0 < B D.w₀)
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) (hSm : MeasurableSet D.S)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hterm : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀)
    (hend : ∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
      z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))
    (hKκ : p.κ ≤ D.K)
    (s : ℝ) (hs : D.i₀ ≤ D.depth s) (hsm : D.depth s ≤ m - 1)
    (i : Fin (p.activeCount D.Hm (D.depth s))) :
    ∀ᵐ z ∂(D.stage Nk L unit ν B).μ, z.1 ∈ (D.stage Nk L unit ν B).B s i →
      z.2 ∈ IS (D.relT s) (D.relBin s i) →
      (D.stage Nk L unit ν B).K⁻¹ ≤ |eval (exS (D.stage Nk L unit ν B).b z.1 z.2)
        (pderiv 3 ((D.stage Nk L unit ν B).F s i))| := by
  show ∀ᵐ z ∂(muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S), _
  refine ae_muE_of_forall _ _ _ _ D.q₀_pos.ne' hSm fun z hz hzA hzI => ?_
  have hδ : 0 < δ Nk (p.r D.i₀) := by
    show 0 < (2 : ℝ) ^ (-(⌊p.r D.i₀ * Real.log Nk / Real.log 2⌋ : ℤ))
    positivity
  have hD : IsUnit (D.frame Nk B).F.D.det := by
    rw [D.frame_F]
    show IsUnit D.D₀.det
    rw [hD₀]
    exact isUnit_iff_ne_zero.mpr (MajorFrame.det_ne_zero (hp.chart D.parent).1)
  -- the original time lies in the open old block
  have hzI' : z.2 ∈ Icc ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))
      (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (D.old s i))) :=
    (D.old_relBin_mem hp hSo s hs i z.2).mpr hzI
  have hzo : z.2 ∈ Ioo ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))
      (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (D.old s i))) :=
    ⟨lt_of_le_of_ne hzI'.1 (hend z hz (D.old s i)).1.symm,
      lt_of_le_of_ne hzI'.2 (hend z hz (D.old s i)).2⟩
  -- the terminal label of `z` descends from the model label
  obtain ⟨bt, hbt, hbtw, hzbt⟩ := hterm hz
  have hlev : p.lev (D.old s i) ≤ p.lev bt := by rw [D.old_level s i, hbt]; exact hsm
  have hw : p.world bt = p.world (D.old s i) := by rw [hbtw, (D.old_world s i).1]
  have hanc := hp.ancestor_eq_of_interior hlev hw hzbt hzA hzo
  have hzc : z ∈ p.counted (D.old s i) := by
    have h := (hp.ancestor bt (p.lev (D.old s i)) hlev).2.2 hzbt
    rwa [hanc] at h
  have hder := (hp.counted_support _ z hzc).2.2.2
  rw [(D.old_world s i).1] at hder
  have hq := D.q₀_pos
  have htime : (D.frame Nk B).F.t₀ + (D.frame Nk B).F.q * ((z.2 - D.t₀) / D.q₀) = z.2 := by
    rw [D.frame_F]; field_simp; ring
  have h := PFrame.normTest_derivative_lower (D.frame Nk B) D.q₀_pos.ne' hD hBw hδ rfl
    (p.test (D.old s i)) z.1 ((z.2 - D.t₀) / D.q₀) (by rw [htime]; exact hder)
  have hK0 : 0 < p.κ := lt_of_lt_of_le one_pos hp.one_le_slack
  calc (D.stage Nk L unit ν B).K⁻¹ = D.K⁻¹ := rfl
    _ ≤ p.κ⁻¹ := inv_anti₀ hK0 hKκ
    _ ≤ _ := h

/-- **`EH3` of the source stage at range `R`.** The time-length bounds, the prior floors, the
tracking coefficients, the thickness comparison and the per-label velocity caps are
hypotheses; the rest is proved above. -/
theorem eh3_stage (unit : ℝ) (d₁ κ₁ ℓ' R : ℝ) {τ : ℝ} (hτ : 0 < τ) (hKτ : τ⁻¹ ≤ D.K)
    (hKκ : p.κ ≤ D.K) (hBw : 0 < B D.w₀)
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) (hSm : MeasurableSet D.S)
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hterm : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀)
    (hend : ∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
      z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))
    (hdepth : ∀ s : ℝ, R⁻¹ ≤ s → s ≤ 1 → D.i₀ ≤ D.depth s ∧ D.depth s ≤ m - 1 ∧ D.depth s < m)
    (htime : ∀ s : ℝ, R⁻¹ ≤ s → s ≤ 1 →
      (Nk ^ (unit * L)) ^ (κ₁ * s) / D.K ≤ (2 : ℝ) ^ D.relT s ∧
      (2 : ℝ) ^ D.relT s ≤ D.K * (Nk ^ (unit * L)) ^ (κ₁ * s))
    (hthick : ∀ s : ℝ, R⁻¹ ≤ s → s ≤ 1 →
      p.κ * (δ Nk (p.r (D.depth s)) / δ Nk (p.r D.i₀)) ≤ D.K * (Nk ^ (unit * L)) ^ (-s) ∧
      p.κ / (δ Nk (p.r (D.depth s)) / δ Nk (p.r D.i₀)) ≤ D.K / (Nk ^ (unit * L)) ^ (-s))
    (hlabel : ∀ s : ℝ, R⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
      ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
        ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i)) ∧
      ENNReal.ofReal (((Nk ^ (unit * L)) ^ (-s)) ^ d₁ * ((2 : ℝ) ^ (-(D.relT s : ℤ))) ^ 2 *
          (Nk ^ (unit * L)) ^ (-ℓ' * s) / D.K) ≤
        (D.stage Nk L unit ν B).ν (p.assigned (D.old s i)) ∧
      (D.stage Nk L unit ν B).ν (p.assigned (D.old s i)) ≤
        ENNReal.ofReal (D.K * ((Nk ^ (unit * L)) ^ (-s)) ^ d₁ *
          ((2 : ℝ) ^ (-(D.relT s : ℤ))) ^ 2 * (Nk ^ (unit * L)) ^ (-ℓ' * s)) ∧
      (∀ e, |D.c s i e| ≤ D.K) ∧
      (∀ l ∈ p.assigned (D.old s i), ∀ t ∈ IS (D.relT s) (D.relBin s i),
        |(exS (D.stage Nk L unit ν B).b l t) 1 - D.c s i 0 - t * D.c s i 1| ≤
          D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) ∧
        |(exS (D.stage Nk L unit ν B).b l t) 2 - D.c s i 2 - t * D.c s i 3 -
            D.c s i 4 * (exS (D.stage Nk L unit ν B).b l t) 1| ≤
          D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) * (Nk ^ (unit * L)) ^ (-ℓ' * s) ∧
        |(D.stage Nk L unit ν B).b l 4 - D.c s i 3 - D.c s i 4 * (D.stage Nk L unit ν B).b l 3| ≤
          D.K * (Nk ^ (unit * L)) ^ (-ℓ' * s)))
    (hvel : ∀ s : ℝ, R⁻¹ ≤ s → s ≤ 1 → ∀ (i : Fin (p.activeCount D.Hm (D.depth s)))
      (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
      (D.stage Nk L unit ν B).μ {z | z.1 ∈ p.assigned (D.old s i) ∧
          z.2 ∈ IS (D.relT s) (D.relBin s i) ∧
          ⌊(D.stage Nk L unit ν B).b z.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} ≤
        ENNReal.ofReal (D.K * (2 : ℝ) ^ (-(D.relT s : ℤ))) *
          (D.stage Nk L unit ν B).ν (p.assigned (D.old s i)) *
          D.π {w : ℝ | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}) :
    EH3 d₁ κ₁ ℓ' 1 1 (D.stage Nk L unit ν B) R := by
  intro s hs1 hs2
  obtain ⟨hi₀, hsm', hsm⟩ := hdepth s hs1 hs2
  obtain ⟨hT1, hT2⟩ := htime s hs1 hs2
  obtain ⟨hv, hcu⟩ := hthick s hs1 hs2
  refine ⟨hT1, hT2, fun i => ⟨(hp.chart (D.old s i)).2.2.2.2.2.2.1,
    (hp.chart (D.old s i)).2.2.2.2.2.2.1, le_rfl⟩,
    fun i i' hne hj => D.stage_disjoint hp unit hSo s hi₀ i i' hne hj, fun i => ?_,
    D.stage_cover hp unit hSm hSo hterm s hi₀ hsm, fun i v v₀ hv1 hv2 => hvel s hs1 hs2 i v v₀ hv1 hv2⟩
  obtain ⟨hfl, hlo, hup, hc, htrack⟩ := hlabel s hs1 hs2 i
  refine ⟨hlo, hup, D.stage_incidence_floor hp unit hτ hKτ hSo s hi₀ i hfl, hc, ?_,
    fun l hl t ht => htrack l hl t ht,
    D.stage_fit hp unit hBw hD₀ hSo s hi₀ i _ _ hv hKκ hcu,
    D.stage_deriv_floor hp unit hBw hD₀ hSm hSo hterm hend hKκ s hi₀ hsm' i,
    fun h => absurd h (by decide)⟩
  · exact ((D.frame Nk B).totalDegree_normTest_le _ _).trans (hp.chart (D.old s i)).2.2.2.2.1

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
