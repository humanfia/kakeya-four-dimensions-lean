import Submission.Obl.k4_raw_critical_segment_forests.ForestMono

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The same true-chart predicate at an arbitrary actual depth of the original
problem, without changing the ambient original data. -/
def TrueDepth {p : Data} {k : ℕ} (a : Atlas p k) (M D : ℕ) (κ r : ℝ) : Prop :=
  a.Regular M D κ r (fun b =>
    ENNReal.ofReal (p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| /
      ((2 : ℝ) ^ a.T * κ)) ≤ priorMass p k (a.γ b) (a.F b))

lemma trueDepth_mono {p : Data} (hp : Valid p) {k M M' D D' : ℕ}
    {κ κ' r : ℝ} {a : Atlas p k} (hκ : 0 < κ) (hκκ : κ ≤ κ')
    (hM : M ≤ M') (hD : D ≤ D') (ha : TrueDepth a M D κ r) :
    TrueDepth a M' D' κ' r := by
  obtain ⟨hC, hsep, hchart, hmass⟩ := ha
  refine ⟨hC.trans (pow_le_pow_right₀ (hp.scale_ge_one k) hM), hsep, ?_,
    (ENNReal.ofReal_le_ofReal (inv_anti₀ hκ hκκ)).trans hmass⟩
  intro b
  apply k4_quadratic_atlas_normalization.chart_mono (hp.scale_ge_one k) hM hD
    hκ hκκ (hp.B_pos k (a.γ b)).le (hchart b)
  intro hfloor
  apply le_trans ?_ hfloor
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_left
    (mul_nonneg (Real.rpow_nonneg (hp.scale_pos k).le _) (abs_nonneg _))
    (mul_pos (by positivity) hκ) (mul_le_mul_of_nonneg_left hκκ (by positivity))

/-- An atlas does not depend on a problem's endpoint, cap or chosen angular
versions. These maps keep its original finite geometry and incidences. -/
abbrev toEndpoint {p : Data} {k : ℕ} (a : Atlas p k) (L d : ℝ)
    (G : (k : ℕ) → Fin (p.W k) → ℝ → (Observation × (Fin 2 → ℤ)) → ENNReal) :
    Atlas {p with L := L, d := d, G := G} k where
  T := a.T
  C := a.C
  γ := a.γ
  j := a.j
  c := a.c
  u := a.u
  Q := a.Q
  R := a.R
  A := a.A
  F := a.F
  lst := a.lst

abbrev fromEndpoint {p : Data} {k : ℕ} {L d : ℝ}
    {G : (k : ℕ) → Fin (p.W k) → ℝ → (Observation × (Fin 2 → ℤ)) → ENNReal}
    (a : Atlas {p with L := L, d := d, G := G} k) : Atlas p k where
  T := a.T
  C := a.C
  γ := a.γ
  j := a.j
  c := a.c
  u := a.u
  Q := a.Q
  R := a.R
  A := a.A
  F := a.F
  lst := a.lst

lemma fromEndpoint_trueDepth {p : Data} {k M D : ℕ} {L d κ : ℝ}
    {G : (k : ℕ) → Fin (p.W k) → ℝ → (Observation × (Fin 2 → ℤ)) → ENNReal}
    {a : Atlas {p with L := L, d := d, G := G} k}
    (ha : a.TrueAt M D κ) : TrueDepth (fromEndpoint a) M D κ L := ha

end
end Submission.Obl.k4_raw_critical_segment_forests
