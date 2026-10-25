import Submission.Lib.K4ExactProblemOps.Defs

/-!
# Transferring chart conditions between scale parameters

The chart conditions only use the scale `Nk` through the polynomial bound `Nk ^ M`
and the thickness `δ Nk r`.  A chart therefore stays a chart when the polynomial bound
only grows and the thickness is unchanged.  This is what reindexing and rescaling of
exact problems need.
-/

noncomputable section

namespace Submission.Lib.K4ExactProblemOps

open MeasureTheory

theorem fmt_mono {n : ℕ} {H H' : ℝ} {D : ℕ} {A : Set (Fin n → ℝ)} (h : fmt n H D A)
    (hH : H ≤ H') : fmt n H' D A := by
  obtain ⟨m₀, hm₀, p₀, hp₀, b₀, hb₀⟩ := h
  exact ⟨m₀, hm₀.trans hH, p₀, hp₀, b₀, hb₀⟩

/-- A chart stays a chart when its polynomial bound grows and its thickness is kept. -/
theorem chart_transfer {Nk Nk' : ℝ} {M M' D : ℕ} {κ : ℝ} {T : ℕ} {j r r' Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ}
    {A : Set (ℕ × (Fin 6 → ℝ))} {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (h : chart Nk M D κ T j r Bv Ev c u Q R A F ex) (hpow : Nk ^ M ≤ Nk' ^ M')
    (hδ : δ Nk r = δ Nk' r') (hex : ex → ex') :
    chart Nk' M' D κ T j r' Bv Ev c u Q R A F ex' := by
  obtain ⟨hdet, hcu, hQQ, hQ, hRdeg, hRcoeff, hA, hF, hfmt, hAbd, hFbd, hex0⟩ := h
  refine ⟨hdet, hcu.trans hpow, hQQ.trans hpow, hQ, hRdeg, fun e => (hRcoeff e).trans hpow,
    hA, hF, fun i => ⟨fmt_mono (hfmt i).1 hpow, fmt_mono (hfmt i).2 hpow⟩, ?_, hFbd, hex hex0⟩
  intro l hl
  obtain ⟨hl1, hl2, hlt⟩ := hAbd l hl
  refine ⟨hl1.trans hpow, fun e => (hl2 e).trans hpow, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hlt t ht
  exact ⟨h1, hδ ▸ h2, h3, hδ ▸ h4⟩

end Submission.Lib.K4ExactProblemOps
