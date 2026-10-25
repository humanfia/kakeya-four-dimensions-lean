-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ModelGood.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelBounds

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open MeasureTheory Set Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

structure GoodPoint (k : ℕ) (u : α × ℝ) : Prop where
  time : u.2 ∈ Icc (0 : ℝ) 1
  coefficients : |p.b k u.1 0| + |p.b k u.1 1| + |p.b k u.1 3| +
    |p.b k u.1 4| ≤ p.K k
  velocity : |p.b k u.1 3| ≤ p.K k
  contact : |p.b k u.1 4 + p.b k u.1 0| ≤ p.N k ^ (-p.e₀)
  fit : ∀ t ∈ Icc (0 : ℝ) 1,
    |MvPolynomial.eval (p.x k u.1 t) (p.P k)| ≤ p.K k ∧
    |MvPolynomial.eval (p.x k u.1 t) (MvPolynomial.pderiv 3 (p.P k))| ≤ p.K k ∧
    |MvPolynomial.eval (p.x k u.1 t)
      (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.P k)))| ≤ p.K k
  regular : (p.K k)⁻¹ ≤
    |MvPolynomial.eval (p.x k u.1 u.2) (MvPolynomial.pderiv 3 (p.P k))|

def Good (k : ℕ) : Set (α × ℝ) := {u | p.GoodPoint k u}

theorem Valid.ae_good (hp : p.Valid) (k : ℕ) : ∀ᵐ u ∂p.μ k, u ∈ p.Good k := by
  obtain ⟨hb, hν, _, hdom, _, hsupp, _, _, hcoeff, hnative⟩ := hp.basic k
  have : IsProbabilityMeasure (p.ν k) := hν
  have hbm : Measurable (fun u : α × ℝ => p.b k u.1) := hb.comp measurable_fst
  have hcoord (i : Fin 6) : Measurable (fun u : α × ℝ => p.b k u.1 i) :=
    (measurable_pi_apply i).comp hbm
  have hset : MeasurableSet {u : α × ℝ |
      |p.b k u.1 0| + |p.b k u.1 1| + |p.b k u.1 3| + |p.b k u.1 4| ≤ p.K k} := by
    apply measurableSet_le _ measurable_const
    exact (((hcoord 0).abs.add (hcoord 1).abs).add
      (hcoord 3).abs).add (hcoord 4).abs
  have hprod : ∀ᵐ (u : α × ℝ) ∂(p.ν k).prod volume,
      |p.b k u.1 0| + |p.b k u.1 1| + |p.b k u.1 3| + |p.b k u.1 4| ≤ p.K k := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    filter_upwards [hcoeff] with l hl
    exact ae_of_all _ (fun _ => hl)
  have hμcoeff := (Measure.ae_smul_measure hprod (ENNReal.ofReal (p.K k))).filter_mono
    (ae_mono hdom)
  have htime : ∀ᵐ u ∂p.μ k, u ∈ (univ ×ˢ Icc (0 : ℝ) 1 : Set (α × ℝ)) :=
    ae_iff.mpr hsupp
  filter_upwards [htime, hμcoeff, hp.contact k, hnative] with u hu hc hcontact hn
  refine ⟨hu.2, hc, ?_, hcontact, hn.1, hn.2⟩
  linarith [abs_nonneg (p.b k u.1 0), abs_nonneg (p.b k u.1 1),
    abs_nonneg (p.b k u.1 4)]

theorem Valid.g_pos (hp : p.Valid) (k : ℕ) (s : ℝ) : 0 < p.g k s :=
  Real.rpow_pos_of_pos (Valid.N_pos p hp k) _

theorem label_assignment_pos (hp : p.Valid) {k : ℕ} {s : ℝ}
    {i : Fin (p.n k s)} (hi : p.Label k s i) : 0 < p.ν k (p.A k s i) := by
  apply lt_of_lt_of_le _ hi.1
  apply ENNReal.ofReal_pos.mpr
  have ha := Valid.a_pos p hp k s
  have hq := p.q_pos k s
  have hg := Valid.g_pos p hp k s
  have hK := Valid.K_pos p hp k
  exact div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos ha _) (sq_pos_of_pos hq)) hg) hK

theorem label_incidence_pos (hp : p.Valid) {k : ℕ} {s : ℝ}
    {i : Fin (p.n k s)} (hi : p.Label k s i) :
    0 < p.μ k (p.B k s i ×ˢ p.I k s i) := by
  apply lt_of_lt_of_le _ hi.2.2.1
  apply ENNReal.mul_pos_iff.mpr
  exact ⟨ENNReal.ofReal_pos.mpr (div_pos (p.q_pos k s) (Valid.K_pos p hp k)),
    label_assignment_pos p hp hi⟩

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
