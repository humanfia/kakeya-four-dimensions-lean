import Submission.Obl.k4_graph_atlas_representative_realization.Normalize
import Submission.Obl.k4_graph_atlas_representative_realization.Depth
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

namespace Submission.Obl.k4_graph_atlas_representative_realization

open MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Point := Line × ℝ

/-- A single input chart, with its whole-block stable-root certificate. -/
def GraphChart (N : ℝ) (M D : ℕ) (κ : ℝ) (T : ℕ) (j e _B : ℝ)
    (E : Set Point) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (P : MvPolynomial (Fin 4) ℝ) (s : ℝ)
    (A : Set Line) (F : Set Point) : Prop :=
  Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ N ^ M ∧
  (∑ i : Fin 2, ∑ i' : Fin 2, (|Q i i'| + |Q⁻¹ i i'|)) ≤ N ^ M ∧
  (∑ i : Fin 2, ∑ i' : Fin 2, |Q i i'|) ≤ κ / (2 : ℝ) ^ T ∧
  P.totalDegree ≤ 2 ∧ (∀ d, |P.coeff d| ≤ N ^ M) ∧
  0 < s ∧ s ≤ N ^ M ∧ s⁻¹ ≤ N ^ M ∧
  MeasurableSet A ∧ MeasurableSet F ∧
  (∀ i, fmt 6 (N ^ M) D {z | (i,z) ∈ A} ∧
    fmt 7 (N ^ M) D {z : Fin 7 → ℝ | ((i, fun a : Fin 6 => z a.castSucc),z 6) ∈ F}) ∧
  (∀ l ∈ A, (l.1 : ℝ) ≤ N ^ M ∧ (∀ i, |l.2 i| ≤ N ^ M) ∧
    ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j+1) / (2 : ℝ) ^ T),
      ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ) ∧
  (∀ p ∈ F, p ∈ E ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j/(2 : ℝ)^T) ((j+1)/(2 : ℝ)^T)) ∧
  (∀ l ∈ A, ∀ t ∈ Set.Icc (j/(2 : ℝ)^T) ((j+1)/(2 : ℝ)^T),
    ∃ w : ℝ, |(x l t) 3 - w| ≤ e ∧
      eval (Function.update (x l t) 3 w) P = 0 ∧
      s/2 ≤ |eval (Function.update (x l t) 3 w) (pderiv 3 P)| ∧
      |eval (Function.update (x l t) 3 w) (pderiv 3 P)| ≤ 2*s)

/-- Realization of one chart preserves both original assignment sets exactly. -/
theorem realize_chart {N κ κ' j e B r : ℝ} {M M' D T : ℕ}
    {E : Set Point} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {P : MvPolynomial (Fin 4) ℝ} {s : ℝ}
    {A : Set Line} {F : Set Point}
    (hN : 2 ≤ N) (hM : M ≤ M') (hκ : κ ≤ κ') (hκ' : 8 ≤ κ')
    (hB : 0 < B) (hBV : B ≤ N ^ M) (hr : 0 ≤ r)
    (hcoef : 2 * (N ^ M) ^ 3 ≤ N ^ M')
    (herror : e ≤ δ N r / (8 * B))
    (h : GraphChart N M D κ T j e B E c u Q P s A F) :
    chart N M' D κ' T j r B E c u Q (normalizedTest P s B (δ N r)) A F True := by
  have hN1 : 1 ≤ N := by linarith
  have hpow := pow_le_pow_right₀ hN1 hM
  have hd : 0 < δ N r := by unfold δ; positivity
  obtain ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hs, hsV, hisV,
    hA, hF, hformat, hwhole, hselected, hroots⟩ := h
  have htests (l : Line) (hl : l ∈ A) (t : ℝ)
      (ht : t ∈ Set.Icc (j / (2 : ℝ)^T) ((j+1)/(2 : ℝ)^T)) :
      |eval (x l t) (normalizedTest P s B (δ N r))| ≤ κ' * δ N r ∧
      |eval (x l t) (pderiv 3 (normalizedTest P s B (δ N r)))| ≤ κ' * B ∧
      |eval (x l t) (pderiv 3 (pderiv 3 (normalizedTest P s B (δ N r))))| ≤
        κ' * B ^ 2 / δ N r ∧
      B / κ' ≤ |eval (x l t) (pderiv 3 (normalizedTest P s B (δ N r)))| := by
    obtain ⟨w, hw, hz, hlo, hhi⟩ := hroots l hl t ht
    exact normalizedTest_bounds P hdeg hs hB hd hκ' (x l t) w (hw.trans herror) hz hlo hhi
  refine ⟨hdet, hcu.trans hpow, hframe.trans hpow,
    hsize.trans (div_le_div_of_nonneg_right hκ (by positivity)),
    normalizedTest_degree P hdeg s B (δ N r), ?_, hA, hF, ?_, ?_, ?_, trivial⟩
  · intro d
    exact (normalizedTest_coeff P hdeg hs hB (delta_le_one hN1 hr)
      (one_le_pow₀ hN1) hBV hisV hcoeff d).trans hcoef
  · intro i
    exact ⟨Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hformat i).1 hpow le_rfl,
      Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hformat i).2 hpow le_rfl⟩
  · intro l hl
    obtain ⟨htag, hcoords, hspatial⟩ := hwhole l hl
    refine ⟨htag.trans hpow, fun i => (hcoords i).trans hpow, fun t ht => ?_⟩
    have hb := htests l hl t ht
    exact ⟨(hspatial t ht).trans hκ, hb.1, hb.2.1, hb.2.2.1⟩
  · intro p hp
    obtain ⟨hE, hl, ht⟩ := hselected p hp
    exact ⟨hE, hl, ht, (htests p.1 hl p.2 ht).2.2.2⟩

end Submission.Obl.k4_graph_atlas_representative_realization
