import Submission.Obl.k4_finite_affine_parent_sources.SourceGmVelCaps

/-! Transfer the retained window numerators to the velocity bins of every old label. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

theorem gmVelCaps : GmVelCaps := by
  classical
  intro W m Mp Dp p ℓ Nk L κ₁ δ₀ σ ω ν E B f sg hp hν hE hEm hNk
    D n unit e δv Cw S0w S1 S2 blur hD0 hN he hdepth hge hS0m hS0E hS1
    hCw hCK hwin hR0 hdom hblur hS2m hS21 hDS hSo hterm hSend
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  apply D.velCaps_of_end_numerator hp n unit hSo hterm hSend hge he hdepth
    (C := 4 * Cw) (by positivity) hCK
  intro h hlev hwh hanc v hv1 hv2 v₀
  have hwidth : 2 * blur ≤ (Nk ^ (unit * L)) ^ (-v) :=
    hblur.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have hnum := end_bin_numerator hp hν hE hEm D.w₀ D.i₀ e D.parent δv
    S0w hS0m hS0E S1 hS1 Cw hCw hwin hR0 D.π
    (fun x => (labelFrame p D.parent (B D.w₀) (δ Nk (p.r D.i₀))).eb x.1 3)
    hdom S2 hS2m hS21 hwidth (some h) v₀
  have hframe : D.frame Nk B = labelFrame p D.parent (B D.w₀)
      (δ Nk (p.r D.i₀)) := by
    unfold SourceData.frame
    rw [hD0]
    rfl
  have hsub : D.S ∩ p.counted h ∩
      {z | ⌊(D.stage Nk L unit ν B).b z.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} ⊆
      S2 ∩ ({x | p.history m e (D.w₀, x) = some h} ∩
        {x | ⌊(labelFrame p D.parent (B D.w₀) (δ Nk (p.r D.i₀))).eb x.1 3 /
          ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}) := by
    rintro x ⟨⟨hxS, hxc⟩, hxbin⟩
    refine ⟨hDS hxS, ?_, ?_⟩
    · rw [← hlev]
      exact history_eq_of_counted hp hwh (hterm hxS) hxc (hSend x hxS h)
    · change ⌊(D.frame Nk B).eb x.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀ at hxbin
      simpa only [hframe, Set.mem_setOf_eq] using hxbin
  have href : ((ν D.w₀).prod volume) (S0w ∩
      {x | p.history m D.i₀ (D.w₀, x) = some D.parent} ∩
      {x | p.history m e (D.w₀, x) = some h}) ≤
      ((ν D.w₀).prod volume) (p.packet h) := by
    apply measure_mono
    rintro x ⟨hxR, hxh⟩
    have hc : x ∈ p.counted h := (history_some hp hxh).2
    exact ⟨(hp.counted_support h x hc).2.1, (hp.counted_support h x hc).2.2.1⟩
  have hcoeff : (4 : ENNReal) * ENNReal.ofReal Cw = ENNReal.ofReal (4 * Cw) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  exact (measure_mono hsub).trans (hnum.trans (by
    rw [← hcoeff]
    exact mul_le_mul' (mul_le_mul' le_rfl href) le_rfl))

end

end Submission.Obl.k4_finite_affine_parent_sources
