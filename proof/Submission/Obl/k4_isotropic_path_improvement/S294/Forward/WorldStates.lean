-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.WorldStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.FrontStates

/-!
# Breadth and palette of the virtual states, for the original world measure

`Forward/FrontStates.lean` gives the per-end-history breadth and palette in the coarse law of an
active packet `a`; `Forward/CoarseTransfer.lean` turns ratios of that coarse law into ratios of
the original world measure `(ν_{γ a}) ⊗ dt`. Inside the likelihood cut `F.U a` the residual and
coarse-support restrictions are automatic, so the statements are about the world sections of
`F.U a ∩ {history at stop = e}` only.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294

namespace Forward

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open Submission.Lib.K4VelocityStrips
open scoped ENNReal

noncomputable section

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a₁ A : ℝ} {θ : ENNReal}

/-- The standing finiteness and positivity facts used to transfer the coarse law of an active
packet to the original world measure. -/
structure TransferData (Q : PreparedAngularPath d k p m H u τ) (F : PaletteFamily Q i stop a₁ A θ)
    (a : Fin p.C) : Prop where
  active : F.active a
  measurable_F : ∀ b, MeasurableSet (p.F b)
  finite_world : ∀ w, ((d.ν k w).prod volume) (Q.residual w) ≠ ⊤
  measurable_residual : ∀ w, MeasurableSet (Q.residual w)

namespace TransferData

variable {F : PaletteFamily Q i stop a₁ A θ} {a : Fin p.C}

theorem measurableSet_coarse (h : TransferData Q F a) :
    MeasurableSet (Q.coarseSupport (p.lev a) (F.code a)) :=
  (measurableSet_labelledSupport _ h.measurable_residual).inter
    (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F h.measurable_F _)
      measurable_const)

theorem coarse_world (h : TransferData Q F a) :
    ∀ z ∈ Q.coarseSupport (p.lev a) (F.code a), z.1 = p.γ a :=
  fun z hz => (F.packet a h.active z hz).1

theorem sum_ne_top (h : TransferData Q F a) :
    (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w)) ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro w _
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h.finite_world w)

theorem coarse_mass_ne_top (h : TransferData Q F a) :
    ((d.ν k (p.γ a)).prod volume)
      (Q.residual (p.γ a) ∩ worldSection (p.γ a) (Q.coarseSupport (p.lev a) (F.code a))) ≠ ⊤ :=
  ne_top_of_le_ne_top (h.finite_world _) (measure_mono inter_subset_left)

theorem coarse_mass_ne_zero (h : TransferData Q F a) :
    ((d.ν k (p.γ a)).prod volume)
      (Q.residual (p.γ a) ∩ worldSection (p.γ a) (Q.coarseSupport (p.lev a) (F.code a))) ≠ 0 := by
  intro h0
  apply F.coarse_positive a h.active
  rw [PreparedAngularPath.law, preparedResidualLaw_single _ _ _ (p.γ a) h.measurableSet_coarse
    h.coarse_world, h0, mul_zero, ENNReal.zero_div]

/-- Inside the likelihood cut, the residual and coarse-support restrictions are automatic. -/
theorem inter_eq_of_subset_U (h : TransferData Q F a)
    {D : Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ))} (hD : D ⊆ F.U a) :
    Q.residual (p.γ a) ∩ worldSection (p.γ a) (Q.coarseSupport (p.lev a) (F.code a)) ∩
        worldSection (p.γ a) D = worldSection (p.γ a) D := by
  apply inter_eq_right.mpr
  intro x hx
  have hC : ((p.γ a, x) : Fin (d.W k) × _) ∈ Q.coarseSupport (p.lev a) (F.code a) :=
    F.subset_coarse a h.active (hD hx)
  exact ⟨hC.1, hC⟩

end TransferData

/-- Per-state breadth for the original world measure. -/
theorem world_breadth (F : PaletteFamily Q i stop a₁ A θ) {a : Fin p.C} (h : TransferData Q F a)
    {r fraction : ℝ} (hfr : 0 ≤ fraction) {e : ℕ} (he : e ∈ goodEnd F r fraction a)
    (n : StripSpace) (hn : ‖n‖ = 1) (β : ℝ) :
    ((d.ν k (p.γ a)).prod volume) (worldSection (p.γ a)
        {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a ∧
          p.normalizedVelocity a z.2 ∈ affineStrip n β r}) ≤
      ENNReal.ofReal (8 * fraction) * ((d.ν k (p.γ a)).prod volume) (worldSection (p.γ a)
        {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a}) := by
  have hhist := measurable_finitePacketHistory p.lev p.γ p.F h.measurable_F stop
  have hU := F.measurable_U a h.active
  have hV : Measurable (fun z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
      p.normalizedVelocity a z.2) := (p.measurable_normalizedVelocity a).comp measurable_snd
  have hstrip : MeasurableSet (affineStrip n β r) := by
    have : affineStrip n β r = (fun x : StripSpace => inner ℝ x n - β) ⁻¹' Metric.closedBall 0 r := by
      ext x; simp [affineStrip]
    rw [this]
    exact (Metric.isClosed_closedBall.preimage
      ((continuous_id.inner continuous_const).sub continuous_const)).measurableSet
  have hD₂ : MeasurableSet {z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) |
      finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a} :=
    (measurableSet_eq_fun hhist measurable_const).inter hU
  have hD₁ : MeasurableSet {z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) |
      finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a ∧
        p.normalizedVelocity a z.2 ∈ affineStrip n β r} :=
    (measurableSet_eq_fun hhist measurable_const).inter (hU.inter (hV hstrip))
  have hb := coarse_breadth F h.measurable_F hfr a he n hn β
  have ht := world_ratio_of_cond_ratio_real (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
    (p.γ a) (F.weight_positive a h.active) h.sum_ne_top h.measurableSet_coarse h.coarse_world
    h.coarse_mass_ne_top h.coarse_mass_ne_zero hD₁ hD₂ (by positivity) hb
  rw [h.inter_eq_of_subset_U (fun z hz => hz.2.1), h.inter_eq_of_subset_U (fun z hz => hz.2)] at ht
  exact ht

/-- Per-state palette for the original world measure, with ONE palette: the normalized
velocity-bin law of the coarse law of `a`. -/
theorem world_palette (F : PaletteFamily Q i stop a₁ A θ) {a : Fin p.C} (h : TransferData Q F a)
    (hA : 0 ≤ A) {r fraction : ℝ} {e : ℕ} (he : e ∈ goodEnd F r fraction a) (q : ℤ × ℤ) :
    ((d.ν k (p.γ a)).prod volume) (worldSection (p.γ a)
        {z | z ∈ F.U a ∧ finitePacketHistory p.lev p.γ p.F stop z = e ∧
          p.labelledNormalizedPalette a a₁ z = q}) ≤
      ENNReal.ofReal (8 * A * (Q.coarseLaw (p.lev a) (F.code a)).real
          {z | p.labelledNormalizedPalette a a₁ z = q}) *
        ((d.ν k (p.γ a)).prod volume) (worldSection (p.γ a)
          {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a}) := by
  have hhist := measurable_finitePacketHistory p.lev p.γ p.F h.measurable_F stop
  have hU := F.measurable_U a h.active
  have hpal : Measurable (p.labelledNormalizedPalette a a₁) :=
    measurable_euclidean_velocityPalette _ ((p.measurable_normalizedVelocity a).comp measurable_snd) a₁
  have hD₂ : MeasurableSet {z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) |
      finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a} :=
    (measurableSet_eq_fun hhist measurable_const).inter hU
  have hD₁ : MeasurableSet {z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) |
      z ∈ F.U a ∧ finitePacketHistory p.lev p.γ p.F stop z = e ∧
        p.labelledNormalizedPalette a a₁ z = q} :=
    hU.inter ((measurableSet_eq_fun hhist measurable_const).inter
      (measurableSet_eq_fun hpal measurable_const))
  have hb := coarse_palette F h.measurable_F hA a h.active he q
  have hb' : (Q.coarseLaw (p.lev a) (F.code a)).real
      {z | z ∈ F.U a ∧ finitePacketHistory p.lev p.γ p.F stop z = e ∧
        p.labelledNormalizedPalette a a₁ z = q} ≤
      (8 * A * (Q.coarseLaw (p.lev a) (F.code a)).real
          {z | p.labelledNormalizedPalette a a₁ z = q}) *
        (Q.coarseLaw (p.lev a) (F.code a)).real
          {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a} := by
    calc _ ≤ _ := hb
      _ = _ := by ring
  have hc : 0 ≤ 8 * A * (Q.coarseLaw (p.lev a) (F.code a)).real
      {z | p.labelledNormalizedPalette a a₁ z = q} := by
    have : 0 ≤ (Q.coarseLaw (p.lev a) (F.code a)).real
        {z | p.labelledNormalizedPalette a a₁ z = q} := measureReal_nonneg
    positivity
  have ht := world_ratio_of_cond_ratio_real (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
    (p.γ a) (F.weight_positive a h.active) h.sum_ne_top h.measurableSet_coarse h.coarse_world
    h.coarse_mass_ne_top h.coarse_mass_ne_zero hD₁ hD₂ hc hb'
  rw [h.inter_eq_of_subset_U (fun z hz => hz.1), h.inter_eq_of_subset_U (fun z hz => hz.2)] at ht
  exact ht

end

end Forward

end Submission.Obl.k4_isotropic_path_improvement.S294
