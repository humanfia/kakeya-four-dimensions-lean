/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ZoomIncidenceCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomCaps
import Submission.Obl.k4_scalar_graph_residual_discovery.SectionCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

def position (ρ : ℝ) (q : Fin 5 → ℤ) (p : ScalarIncidence) : Fin 3 → ℝ :=
  ![p.2, y ρ q p.1 p.2, x ρ q p.1 p.2]

theorem measurable_position (ρ : ℝ) (q : Fin 5 → ℤ) : Measurable (position ρ q) := by
  unfold position y x coeff
  fun_prop

theorem position_spatial (ρ : ℝ) (q : Fin 5 → ℤ) (p : ScalarIncidence) (e : Fin 2) :
    position ρ q p e.succ = zoomSpatial ρ q p.1 p.2 e := by fin_cases e <;> rfl

/-- Integrating the original fixed-time cap over one actual zoom time cell
preserves its external original-palette factor. -/
theorem zoom_cell_incidence_cap (θ : Measure ScalarLine) [SFinite θ]
    (μ : Measure ScalarIncidence) {U : ℝ≥0∞} (hμ : μ ≤ U • θ.prod volume)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    {ρ δ h : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hh : 0 < h)
    (q : Fin 5 → ℤ) (z : Fin 3 → ℤ) (C : ℝ≥0∞)
    (hcap : ∀ t a, θ {l | (l, t) ∈ E ∧ cell δ (spatial l t) = a} ≤ C) :
    μ {p | p ∈ E ∧ cell h (position ρ q p) = z} ≤
      U * ENNReal.ofReal h * ENNReal.ofReal ((ρ * h / δ + 2) ^ 2) * C := by
  let I := Ico ((z 0 : ℝ) * h) (((z 0 : ℝ) + 1) * h)
  let E' : Set ScalarIncidence := {p | p ∈ E ∧ cell h (position ρ q p) = z}
  have hE' : MeasurableSet E' := hE.inter
    ((measurable_cell h (measurable_position ρ q)) (measurableSet_singleton z))
  have htime (p : ScalarIncidence) (hp : p ∈ E') : p.2 ∈ I := by
    have he := congrFun hp.2 0
    change ⌊p.2 / h⌋ = z 0 at he
    have hf := Int.floor_eq_iff.mp he
    exact ⟨(le_div_iff₀ hh).mp hf.1, (div_lt_iff₀ hh).mp hf.2⟩
  have hsection (t : ℝ) : θ {l | (l, t) ∈ E'} ≤
      ENNReal.ofReal ((ρ * h / δ + 2) ^ 2) * C := by
    have hboxCap := zoom_cube_cap E t hρ hδ hh.le q C (hcap t)
      (fun e => (z e.succ : ℝ) * h)
    apply (measure_mono (t := {l | (l, t) ∈ E ∧ ∀ e : Fin 2,
      zoomSpatial ρ q l t e ∈ Ico ((z e.succ : ℝ) * h) ((z e.succ : ℝ) * h + h)}) ?_).trans hboxCap
    intro l hl
    refine ⟨hl.1, fun e => ?_⟩
    have he := congrFun hl.2 e.succ
    change ⌊position ρ q (l, t) e.succ / h⌋ = z e.succ at he
    rw [position_spatial] at he
    have hf := Int.floor_eq_iff.mp he
    refine ⟨(le_div_iff₀ hh).mp hf.1, ?_⟩
    have hh' := (div_lt_iff₀ hh).mp hf.2
    linarith
  have hmass := incidence_mass_of_section_caps θ μ hμ hE' measurableSet_Ico htime
    (ENNReal.ofReal ((ρ * h / δ + 2) ^ 2) * C) (fun t _ => hsection t)
  have hvol : volume I = ENNReal.ofReal h := by
    dsimp only [I]
    rw [Real.volume_Ico]
    congr 1
    ring
  rw [hvol] at hmass
  exact hmass.trans_eq (by ring)

end

end Zoom

namespace ScalarData

/-- The original frozen fixed-time caps and original incidence-density
ceiling give a zoom-cell incidence cap with the SAME fine palette bin. -/
theorem prepData.original_zoom_cell_incidence_cap {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k) :
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ D.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
      M = D.prepMesh hprep ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ r : ℝ,
        R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) →
        ∀ (μ : Measure ScalarIncidence), μ ≤ (D.ρ k g).restrict (E₀ k g) →
        ∀ ρ h : ℝ, 0 < ρ → 0 < h → ∀ (q : Fin 5 → ℤ) (z : Fin 3 → ℤ) (c : ℤ),
          μ {p | p ∈ E₀ k g ∧ p.1.2 1 ∈ D.vel k r c ∧ cell h (Zoom.position ρ q p) = z} ≤
            ENNReal.ofReal (H k) * ENNReal.ofReal h *
              ENNReal.ofReal ((ρ * h / D.N k ^ (-r) + 2) ^ 2) *
                ENNReal.ofReal (H k * D.N k ^ (-r - D.d * r)) * D.π k g (D.vel k r c) := by
  let M := D.prepMesh hprep
  obtain ⟨hM, hdata⟩ := Classical.choose_spec hprep.2
  refine ⟨M, hM, rfl, ?_⟩
  intro R hR
  filter_upwards [hdata R hR] with k hk
  intro g r hrlo hrhi hrgrid μ hμ ρ h hρ hh q z c
  obtain ⟨_, hθone, hEmeas, _, _, _, hdensup, _, hfixed⟩ := hk.2 g
  let : IsFiniteMeasure (θ k g) := ⟨lt_of_le_of_lt hθone (by simp)⟩
  have hdom : μ ≤ ENNReal.ofReal (H k) • (θ k g).prod volume := by
    apply Measure.le_iff.mpr
    intro A _
    calc
      μ A ≤ ((D.ρ k g).restrict (E₀ k g)) A := hμ _
      _ ≤ (ENNReal.ofReal (H k) • (((θ k g).prod volume).restrict (E₀ k g))) A := hdensup _
      _ ≤ (ENNReal.ofReal (H k) • (θ k g).prod volume) A := by
        rw [Measure.smul_apply, Measure.smul_apply]
        change ENNReal.ofReal (H k) * _ ≤ ENNReal.ofReal (H k) * _
        exact mul_le_mul_of_nonneg_left (Measure.restrict_le_self A) zero_le
  let E : Set ScalarIncidence := {p | p ∈ E₀ k g ∧ p.1.2 1 ∈ D.vel k r c}
  have hV : Measurable (fun p : ScalarIncidence => p.1.2 1) := by fun_prop
  have hE : MeasurableSet E := hEmeas.inter
    (measurableSet_eq_fun ((hV.div_const (D.N k ^ (-r))).floor) measurable_const)
  obtain ⟨m, hm⟩ := hrgrid
  have hraw (t : ℝ) := hfixed r r r t hrlo hrhi hrlo hrhi hrlo hrhi ⟨m, m, m, hm, hm, hm⟩
  have hcap (t : ℝ) (a : Fin 2 → ℤ) :
      θ k g {l | (l, t) ∈ E ∧ cell (D.N k ^ (-r)) (Zoom.spatial l t) = a} ≤
        ENNReal.ofReal (H k * D.N k ^ (-r - D.d * r)) * D.π k g (D.vel k r c) := by
    apply (measure_mono (t := {l | (l, t) ∈ E₀ k g ∧
      (⌊scalarY l t / D.N k ^ (-r)⌋ : ℤ) = a 0 ∧
      (⌊scalarX l t / D.N k ^ (-r)⌋ : ℤ) = a 1 ∧ l.2 1 ∈ D.vel k r c}) ?_).trans
      (hraw t (a 0) (a 1) c)
    intro l hl
    exact ⟨hl.1.1, congrFun hl.2 0, congrFun hl.2 1, hl.1.2⟩
  have hN0 : 0 < D.N k := by linarith [hN k]
  have hresult := Zoom.zoom_cell_incidence_cap (θ k g) μ hdom hE hρ
    (Real.rpow_pos_of_pos hN0 _) hh q z
    (ENNReal.ofReal (H k * D.N k ^ (-r - D.d * r)) * D.π k g (D.vel k r c)) hcap
  simpa only [E, mem_ofPred_eq, and_assoc, mul_assoc] using hresult

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
