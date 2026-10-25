-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.MaskedParentPalette
import Submission.Obl.k4_finite_affine_parent_sources.FinitePlanarPalette
import Submission.Obl.k4_finite_affine_parent_sources.PaletteDepthMenu
import Submission.Obl.k4_finite_affine_parent_sources.SourcePaletteGeometry
import Submission.Obl.k4_finite_affine_parent_sources.PathBaseLocalization
import Submission.Obl.k4_finite_affine_parent_sources.NativeVelocityCoordinates
import Submission.Obl.k4_finite_affine_parent_sources.MajorPaletteGeometry
import Submission.Obl.k4_finite_affine_parent_sources.SourceWindow
import Submission.Lib.K4ExactProblemOps.Coarsening

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Lib.K4AngularCharge
open Submission.Obl.k4_compatible_pair_frame_preparation.Construction
open scoped ENNReal

noncomputable section

/-- The original planar velocity mesh is fixed before the parent is chosen. -/
def sourcePaletteMesh (n : ℕ) (Nk unit L : ℝ) : ℝ :=
  (Nk ^ (unit * L)) ^ (-((n : ℝ) + 2))

/-- One common blur pays the major-row readout for every full parent. -/
def sourcePaletteBlur (n : ℕ) (Nk unit L β : ℝ) : ℝ :=
  4 * (Nk ^ (unit * L)) ^ β * sourcePaletteMesh n Nk unit L

/-- An explicit bound for the parent palette's angular coefficient. -/
def sourcePaletteConstant (Nk κ τa τd eS eP ma : ℝ) : ℝ :=
  10000 * κ ^ 2 * Nk ^ (τa + τd + eS + eP + ma)

theorem log_sourcePaletteMesh (n : ℕ) (Nk unit L : ℝ) (hNk : 0 < Nk) :
    Real.log (sourcePaletteMesh n Nk unit L) =
      -((n : ℝ) + 2) * (unit * L) * Real.log Nk := by
  rw [sourcePaletteMesh, Real.log_rpow (Real.rpow_pos_of_pos hNk _) _, Real.log_rpow hNk]
  ring

/-- The code alphabet has the original velocity size plus a fixed native
power, independently of the chosen parent and the original format budget. -/
theorem log_sourcePaletteMesh_ratio (n : ℕ) (Nk unit L Rv : ℝ)
    (hNk : 0 < Nk) (hRv : 0 < Rv) :
    Real.log (2 * Rv / sourcePaletteMesh n Nk unit L) =
      Real.log (2 * Rv) + ((n : ℝ) + 2) * (unit * L) * Real.log Nk := by
  have hfine : 0 < sourcePaletteMesh n Nk unit L := by
    unfold sourcePaletteMesh
    positivity
  rw [Real.log_div (by positivity) hfine.ne', log_sourcePaletteMesh n Nk unit L hNk]
  ring

private def paletteParentData {W : ℕ} (p : PathData W) (b₀ : Fin p.C) : SourceData p where
  parent := b₀
  D₀ := MajorFrame.frame (p.frame b₀)
  K := 1
  π := 0
  S := ∅
  depth := fun _ => 0
  c := fun _ _ _ => 0

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The actual parent palette, from the original terminal density and
angular/share masks. Later restrictions use the unchanged original planar
bins and reference probabilities; no finite code is exposed to the caller. -/
theorem PathData.Valid.source_parent_palette
    (n : ℕ) (unit β S ma τd τa eS eP Rv : ℝ)
    (hNk : 1 ≤ Nk) (hL : 0 < L) (hu : 0 < unit) (hNt : 8 ≤ Nk ^ (unit * L))
    (hℓ : 0 ≤ ℓ) (hS : 0 ≤ S) (hS1 : S ≤ 1) (hβ : β ≤ 1) (hma : 0 ≤ ma)
    (hunit : unit * ((n : ℝ) + 2) ≤ ℓ / 8) (hδ : 2 * δ₀ ≤ unit)
    (b₀ : Fin p.C) (hband : 1 / 8 ≤ sg (p.lev b₀))
    (hfull : (((2 : ℝ) ^ p.T (p.lev b₀))⁻¹) / Nk ^ (unit * L * β) ≤ r₁ (p.frame b₀))
    (μ : Measure Incidence) [IsFiniteMeasure μ]
    (g : Observation → ENNReal) (hg : Measurable g)
    (hmap : μ.map (obs (B (p.world b₀)) (δ Nk L)) =
      (volume.prod Measure.count).withDensity g)
    (G : ℝ → Observation × (Fin 2 → ℤ) → ENNReal) (Qa : Finset ℝ)
    (hG : ∀ r ∈ Qa, Measurable (G r))
    (hmapG : ∀ r ∈ Qa,
      μ.map (fun z => (obs (B (p.world b₀)) (δ Nk L) z,
        worldBin (δ Nk r) (p.world b₀, z))) =
          ((volume.prod Measure.count).prod Measure.count).withDensity (G r))
    (hmenu : ∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n →
      ∃ r ∈ Qa, unit * L * v - ma ≤ r ∧ r ≤ unit * L * v)
    (R : Set Incidence) (hRm : MeasurableSet R) (hR0 : μ R ≠ 0)
    (hRF : R ⊆ p.counted b₀)
    (hshare : ∀ z ∈ R, ENNReal.ofReal (Nk ^ (-eS)) ≤
      labelShare μ (obs (B (p.world b₀)) (δ Nk L)) (p.counted b₀) z)
    (hlower : ∀ z ∈ R, ENNReal.ofReal (Nk ^ (-f L - τd)) ≤
      g (obs (B (p.world b₀)) (δ Nk L) z))
    (hangular : ∀ r ∈ Qa, ∀ z ∈ R,
      G r (obs (B (p.world b₀)) (δ Nk L) z,
        worldBin (δ Nk r) (p.world b₀, z)) ≤
          ENNReal.ofReal (Nk ^ (-f L - S * r + τa)))
    (hfloor : ENNReal.ofReal (Nk ^ (-eP)) * μ (p.counted b₀) ≤ μ R)
    (hRv : 0 ≤ Rv)
    (hvel : ∀ᵐ z ∂μ, ∀ e : Fin 2, |worldVel (p.world b₀, z) e| ≤ Rv) :
    ∃ π : Measure ℝ, IsProbabilityMeasure π ∧
      0 < sourcePaletteMesh n Nk unit L ∧ 0 < sourcePaletteBlur n Nk unit L β ∧
      2 * sourcePaletteBlur n Nk unit L β ≤ (Nk ^ (unit * L)) ^ (-(n : ℝ)) ∧
      (∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ a : ℤ,
        π {w | ⌊w / (Nk ^ (unit * L)) ^ (-v)⌋ = a} ≤
          ENNReal.ofReal (sourcePaletteConstant Nk p.κ τa τd eS eP ma *
            (Nk ^ (unit * L)) ^ (-S * v))) ∧
      (∀ a c : ℝ, 2 * sourcePaletteBlur n Nk unit L β ≤ c - a →
        nuE μ R ((fun z => (labelFrame p b₀ (B (p.world b₀))
          (δ Nk (p.r (p.lev b₀)))).eb z.1 3) ⁻¹'
            Icc (a - sourcePaletteBlur n Nk unit L β / 2)
              (c + sourcePaletteBlur n Nk unit L β / 2)) ≤ 4 * π (Ico a c)) ∧
      (∀ (ρ : Measure Incidence), ρ ≤ nuE μ R → ∀ (P : Set Incidence) (C : ENNReal)
        (width : ℝ), 2 * sourcePaletteBlur n Nk unit L β ≤ width →
        (∀ z : Fin 2 → ℤ,
          ρ (P ∩ {x | worldBin (sourcePaletteMesh n Nk unit L) (p.world b₀, x) = z}) ≤
            C * nuE μ R {x | worldBin (sourcePaletteMesh n Nk unit L) (p.world b₀, x) = z}) →
        ∀ e : ℤ,
          ρ (P ∩ {z | ⌊(labelFrame p b₀ (B (p.world b₀))
            (δ Nk (p.r (p.lev b₀)))).eb z.1 3 / width⌋ = e}) ≤
              4 * C * π {w | ⌊w / width⌋ = e}) := by
  classical
  let D := paletteParentData p b₀
  let Φ := labelFrame p b₀ (B (p.world b₀)) (δ Nk (p.r (p.lev b₀)))
  let Haxis := Nk ^ (unit * L * β)
  let fine := sourcePaletteMesh n Nk unit L
  let blur := sourcePaletteBlur n Nk unit L β
  let nv : Incidence → Fin 2 → ℝ := fun z => ![Φ.eb z.1 3, Φ.eb z.1 4]
  let M : Matrix (Fin 2) (Fin 2) ℝ := Φ.F.q⁻¹ • Φ.F.D
  let offset := Φ.F.u
  have hNk0 : 0 < Nk := lt_of_lt_of_le zero_lt_one hNk
  have hκ : 1 ≤ p.κ := hp.one_le_slack
  have hκ0 : 0 ≤ p.κ := zero_le_one.trans hκ
  have hq : 0 < Φ.F.q := labelFrame_q_pos hp b₀ _ _
  have hD : IsUnit Φ.F.D.det := labelFrame_det hp b₀ _ _
  have hHaxis : 0 < Haxis := by dsimp [Haxis]; positivity
  have hHnative : Haxis = (Nk ^ (unit * L)) ^ β := by
    dsimp [Haxis]
    rw [← Real.rpow_mul hNk0.le]
  obtain ⟨hfine, hblur, hsmall⟩ := palette_blur_budget n hNt hβ
  change 0 < fine at hfine
  change 0 < blur at hblur
  change 2 * blur ≤ (Nk ^ (unit * L)) ^ (-(n : ℝ)) at hsmall
  have hrow : |Φ.F.q| * (|Φ.F.D⁻¹ 0 0| + |Φ.F.D⁻¹ 0 1|) ≤ 2 * Haxis := by
    change |(((2 : ℝ) ^ p.T (p.lev b₀))⁻¹)| *
      (|(MajorFrame.frame (p.frame b₀))⁻¹ 0 0| +
        |(MajorFrame.frame (p.frame b₀))⁻¹ 0 1|) ≤ _
    apply MajorFrame.inverse_major_row_budget (hp.chart b₀).1 (by positivity)
    simpa only [mul_comm] using (div_le_iff₀ hHaxis).mp hfull
  have hmajor (e : Fin 2) : |M e 0| ≤ 6 * p.κ := by
    change |((((2 : ℝ) ^ p.T (p.lev b₀))⁻¹)⁻¹ •
      MajorFrame.frame (p.frame b₀)) e 0| ≤ _
    exact MajorFrame.major_velocity_column_le (hp.chart b₀).1 (by positivity)
      (hp.major_upper b₀ (6 * p.κ) (by linarith)) e
  have hminor (v : ℝ) (_hv : (n : ℝ)⁻¹ ≤ v) (hvn : v ≤ n) (e : Fin 2) :
      |M e 1| ≤ (Nk ^ (unit * L)) ^ (-v) := by
    have hgap := palette_parent_exponent_gap_of_small_error ℓ unit β (sg (p.lev b₀)) δ₀ v n
      hℓ hu.le hβ hband hunit hδ hvn
    exact SourceData.parent_palette_minor_column D hp hNk hL.le unit β Haxis v hHaxis rfl rfl
      hfull hgap e
  have hcoord : ∀ z ∈ p.counted b₀, ∀ e,
      v z.1 e = offset e + ∑ i, M e i * nv z i := by
    intro z _ e
    have hh := Φ.original_velocity_coordinates hq.ne' hD z.1 e
    simpa only [offset, M, nv, v, k4_quadratic_finite_greedy_cover.v,
      Submission.Lib.K4XInterface.gv, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
      using hh
  have hbound : ∀ z ∈ p.counted b₀, |nv z 1| ≤ 6 * p.κ := by
    intro z hz
    have hn := labelFrame_native_velocity hp b₀ (B (p.world b₀))
      (δ Nk (p.r (p.lev b₀))) z.1 (hp.counted_support b₀ z hz).2.1
    have hc := PiLp.norm_apply_le (gv (0, Φ.eb z.1)) (1 : Fin 2)
    have habs : |nv z 1| ≤ ‖gv (0, Φ.eb z.1)‖ := by
      simpa only [nv, Submission.Lib.K4XInterface.gv, PiLp.toLp_apply,
        Matrix.cons_val_one, Matrix.head_cons, Real.norm_eq_abs] using hc
    exact habs.trans hn
  have hnv : Measurable (fun z => nv z 0) := by
    change Measurable (fun z : Incidence => Φ.eb z.1 3)
    exact ((measurable_pi_apply 3).comp Φ.measurable_eb).comp measurable_fst
  let ref := nuE μ R
  letI : IsProbabilityMeasure ref := nuE_isProb μ R hR0 (measure_ne_top _ _)
  have hvelRef : ∀ᵐ z ∂ref, ∀ e : Fin 2, |worldVel (p.world b₀, z) e| ≤ Rv := by
    exact Measure.ae_smul_measure (ae_restrict_of_ae hvel) _
  have hworldVel : Measurable (fun z : Incidence => worldVel (p.world b₀, z)) :=
    measurable_worldVel.comp (measurable_const.prodMk measurable_id)
  obtain ⟨U, hU, hcode⟩ := exists_planar_palette_code ref
    (fun z => worldVel (p.world b₀, z)) hworldVel hRv hfine hvelRef
  let center := fun c : PlanarPaletteCodes Rv fine =>
    Φ.majorVelocityCenter fine (fun e => (c e : ℤ))
  have hclose : ∀ᵐ z ∂ref, |nv z 0 - center (U z)| ≤ blur / 2 := by
    have hh := Φ.planar_palette_center_close ref Prod.fst
      (fun z => worldVel (p.world b₀, z))
      (fun _ e => by fin_cases e <;> rfl) hfine hrow U hcode
    filter_upwards [hh] with z hz
    apply hz.trans_eq
    dsimp [blur, sourcePaletteBlur, fine]
    rw [← hHnative]
    ring
  let depth (v : ℝ) : ℝ :=
    if hv : (n : ℝ)⁻¹ ≤ v ∧ v ≤ n then (hmenu v hv.1 hv.2).choose else 0
  have hdep (v : ℝ) (hv : (n : ℝ)⁻¹ ≤ v) (hvn : v ≤ n) :
      depth v ∈ Qa ∧ unit * L * v - ma ≤ depth v ∧ depth v ≤ unit * L * v := by
    dsimp only [depth]
    rw [dif_pos ⟨hv, hvn⟩]
    exact (hmenu v hv hvn).choose_spec
  have hbudget : 6 * ((6 * (6 * p.κ) + 2) ^ 2 * Nk ^ (τa + τd + eS + eP)) *
      Nk ^ (S * ma) ≤ sourcePaletteConstant Nk p.κ τa τd eS eP ma :=
    palette_parent_budget hNk hκ hS1 hma
  obtain ⟨π, hπ, hpal, henlarge, hread⟩ :=
    ReferencePalette.exists_masked_parent_palette μ (obs (B (p.world b₀)) (δ Nk L))
      (Submission.Lib.K4ExactProblemOps.measurable_obs _ _) (fun z => v z.1)
      (volume.prod Measure.count) g hg hmap (fun v => G (depth v))
      (p.counted b₀) R (hp.counted_measurable b₀) hR0 U hU center nv hnv offset M n Nk unit L S
      (sourcePaletteConstant Nk p.κ τa τd eS eP ma) (6 * p.κ) ma blur (f L) τa τd eS eP
      depth (fun v => δ Nk (depth v)) hNk (by linarith) hS (by positivity)
      hblur hsmall hclose hfloor hmajor hcoord hbound hbudget
      (fun v hv hvn => (hdep v hv hvn).2.1)
      (fun v hv hvn => ⟨gδ_pos _ _,
        native_velocity_width_le_original hNk (hdep v hv hvn).2.2⟩) hminor
      (fun v _ _ => (measurable_worldBin (W := W) (δ Nk (depth v))).comp
        (show Measurable (fun z : Incidence => (p.world b₀, z)) from
          measurable_const.prodMk measurable_id))
      (fun v hv hvn => hG _ (hdep v hv hvn).1)
      (fun v hv hvn => hmapG _ (hdep v hv hvn).1) (by
        intro v hv hvn z hz
        exact ⟨⟨hRF hz, hshare z hz⟩,
          hangular _ (hdep v hv hvn).1 z hz, hlower z hz⟩)
  refine ⟨π, hπ, hfine, hblur, hsmall, hpal, henlarge, ?_⟩
  intro ρ hρ P C width hw hcap e
  apply hread ρ hρ P C width hw _ e
  intro c
  change ρ (P ∩ U ⁻¹' {c}) ≤ C * ref (U ⁻¹' {c})
  have hbaseFiber : ∀ᵐ z ∂ref, U z = c ↔
      worldBin fine (p.world b₀, z) = (fun j => (c j : ℤ)) :=
    planar_palette_fiber_ae ref (fun z => worldVel (p.world b₀, z)) U hcode c
  have hcurrentFiber := (Measure.absolutelyContinuous_of_le hρ).ae_le hbaseFiber
  have heqρ : ρ (P ∩ U ⁻¹' {c}) =
      ρ (P ∩ {z | worldBin fine (p.world b₀, z) = (fun j => (c j : ℤ))}) := by
    apply measure_congr
    filter_upwards [hcurrentFiber] with z hz
    exact propext (and_congr Iff.rfl hz)
  have heqRef : ref (U ⁻¹' {c}) =
      ref {z | worldBin fine (p.world b₀, z) = (fun j => (c j : ℤ))} := by
    apply measure_congr
    filter_upwards [hbaseFiber] with z hz
    exact propext hz
  rw [heqρ, heqRef]
  exact hcap (fun j => (c j : ℤ))

end Path

end
end Submission.Obl.k4_finite_affine_parent_sources
