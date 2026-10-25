/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit ecf664378ad8398f225a4f7cddbe679a98231d2a, file Submission/Obl/k4_horizontal_wide_interval_return/Core/LayerCaps.lean.
Namespace/imports renamed; only exact piece accessors and etaFun_mem retained. Earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.Datum
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.SheetGeometry

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.CompareSheets

noncomputable section

variable {α : Type} [MeasurableSpace α]

namespace LayerDatum

variable {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
  (L : LayerDatum cfg k ε R χ D depth)

theorem mem_bins {h : Fin 3} {i : Fin (L.np h)} {l : α} (hl : l ∈ L.C h i) :
    ⌊cfg.b k l 3 / χ⌋ = L.qp h i 0 ∧ ⌊cfg.b k l 0 / χ⌋ = L.qp h i 1 ∧
      ⌊cfg.b k l 1 / D⌋ = L.qp h i 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε) :=
  (L.piece h i).1 l hl

theorem key_bound (h : Fin 3) (i : Fin (L.np h)) :
    |(L.qp h i 0 : ℝ) * χ| + |(L.qp h i 1 : ℝ) * χ| + |(L.qp h i 2 : ℝ) * D| ≤ cfg.N k ^ ε :=
  (L.piece h i).2.1

theorem degree (h : Fin 3) (i : Fin (L.np h)) : (L.G h i).totalDegree ≤ 2 :=
  (L.piece h i).2.2.1

/-- The strip of a piece in the form `y₀ + t v + D w`. -/
theorem strip (h : Fin 3) (i : Fin (L.np h)) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, (L.qp h i 2 : ℝ) * D + t * -((L.qp h i 1 : ℝ) * χ) + D * w]
        (L.G h i)| ≤ cfg.N k ^ ε := by
  intro t ht w hw
  have := (L.piece h i).2.2.2.2.1 t ht w hw
  convert this using 4
  ring

theorem fit {h : Fin 3} {i : Fin (L.np h)} {l : α} (hl : l ∈ L.C h i) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |hidden (cfg.b k) (l, t) - MvPolynomial.eval ![t, basePt (cfg.b k) (l, t) 2] (L.G h i)| ≤
      cfg.N k ^ ε * cfg.N k ^ (-depth h) :=
  ((L.piece h i).2.2.2.2.2.1 l hl t ht).2

theorem floor (h : Fin 3) (i : Fin (L.np h)) :
    ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) *
      cfg.π k (Set.Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ)) ≤
      cfg.ρ k (L.C h i ×ˢ Set.Icc (0 : ℝ) 1) :=
  (L.piece h i).2.2.2.2.2.2

end LayerDatum

/-- Strip coordinates of the incidences of a piece stay in `[1/4, 1]`. -/
theorem LayerDatum.etaFun_mem {cfg : Data α} {k : ℕ} {ε R χ D : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) {h : Fin 3} {i : Fin (L.np h)} {p : α × ℝ}
    (hp : p.1 ∈ L.C h i) (hχ : 0 < χ) (hD : 0 < D) {ζ₀ : ℝ}
    (ht : p.2 ∈ Icc (0 : ℝ) 1) (hh : |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ ζ₀)
    (hdrift : ζ₀ + χ ≤ D / 4) :
    etaFun ((L.qp h i 2 : ℝ) * D) (-((L.qp h i 1 : ℝ) * χ)) D p.2 (basePt (cfg.b k) p 2) ∈
      Icc (1 / 4 : ℝ) 1 := by
  obtain ⟨-, h0, h1, -⟩ := L.mem_bins hp
  have hb1lo : (L.qp h i 2 : ℝ) * D ≤ cfg.b k p.1 1 := by
    have := Int.floor_le (cfg.b k p.1 1 / D); rw [h1, le_div_iff₀ hD] at this; linarith
  have hb1hi : cfg.b k p.1 1 < ((L.qp h i 2 : ℝ) + 1) * D := by
    have := Int.lt_floor_add_one (cfg.b k p.1 1 / D); rw [h1, div_lt_iff₀ hD] at this
    linarith
  have hb0lo : (L.qp h i 1 : ℝ) * χ ≤ cfg.b k p.1 0 := by
    have := Int.floor_le (cfg.b k p.1 0 / χ); rw [h0, le_div_iff₀ hχ] at this; linarith
  have hb0hi : cfg.b k p.1 0 < ((L.qp h i 1 : ℝ) + 1) * χ := by
    have := Int.lt_floor_add_one (cfg.b k p.1 0 / χ); rw [h0, div_lt_iff₀ hχ] at this
    linarith
  rw [abs_le] at hh
  have hdr : |cfg.b k p.1 4 + (L.qp h i 1 : ℝ) * χ| ≤ D / 4 := by
    rw [abs_le]; constructor <;> nlinarith
  obtain ⟨ht0, ht1⟩ := ht
  have hY : basePt (cfg.b k) p 2 = cfg.b k p.1 1 + p.2 * cfg.b k p.1 4 := rfl
  have heq : etaFun ((L.qp h i 2 : ℝ) * D) (-((L.qp h i 1 : ℝ) * χ)) D p.2
      (basePt (cfg.b k) p 2) = (cfg.b k p.1 1 - (L.qp h i 2 : ℝ) * D) / (4 * D) +
        p.2 * (cfg.b k p.1 4 + (L.qp h i 1 : ℝ) * χ) / (4 * D) + 1 / 2 := by
    rw [hY]; unfold etaFun; field_simp; ring
  rw [heq]
  have h4D : 0 < 4 * D := by positivity
  have hA : 0 ≤ (cfg.b k p.1 1 - (L.qp h i 2 : ℝ) * D) / (4 * D) :=
    div_nonneg (by linarith) h4D.le
  have hA' : (cfg.b k p.1 1 - (L.qp h i 2 : ℝ) * D) / (4 * D) ≤ 1 / 4 := by
    rw [div_le_iff₀ h4D]; nlinarith
  have hB : |p.2 * (cfg.b k p.1 4 + (L.qp h i 1 : ℝ) * χ) / (4 * D)| ≤ 1 / 16 := by
    rw [abs_div, abs_mul, abs_of_nonneg ht0, abs_of_pos h4D, div_le_iff₀ h4D]
    nlinarith [abs_nonneg (cfg.b k p.1 4 + (L.qp h i 1 : ℝ) * χ)]
  rw [abs_le] at hB
  constructor <;> linarith [hB.1, hB.2]

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core
