import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.P2
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.StripCoeff

/-!
# Flat slice laws at kept points

The slice laws have natural coefficient bounds `C₀ N^(3εL) / D²` (from their moving strip
bound). At every point kept by the two first prunings, the crossing gives the law's height
Lipschitz constant `crossLip`, hence a window bound for the hidden coordinate of nearby points
of the same slice.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The strip coefficient property with constant `C₀`. -/
def StripBound (C₀ : ℝ) : Prop :=
  ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ 2 →
    ∀ (c0 c1 β Λ E : ℝ), 0 < β → β ≤ 1 → 1 ≤ Λ → |c0| ≤ Λ → |c1| ≤ Λ → 0 ≤ E →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
        |MvPolynomial.eval ![t, c0 + t * c1 + β * w] P| ≤ E) →
      ∀ m, |P.coeff m| ≤ C₀ * E * Λ ^ 2 / β ^ 2

theorem exists_stripBound : ∃ C₀ : ℝ, 0 < C₀ ∧ StripBound C₀ := exists_strip_coeff_bound

/-- Natural coefficient bound of the slice laws. -/
theorem layer_coeff_bound (D : CoreData α) (H : CoreHyp D) {C₀ : ℝ} (hC₀ : StripBound C₀)
    (hεL : 0 ≤ D.εL) (hDw1 : D.Dw ≤ 1) (i : Fin D.Ly.n) :
    ∀ m, |(D.Ly.G i).coeff m| ≤ C₀ * D.N ^ D.εL * (D.N ^ D.εL) ^ 2 / D.Dw ^ 2 := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hE : 1 ≤ D.N ^ D.εL := Real.one_le_rpow (by linarith [H.N2]) hεL
  have hctr := H.lygood.ctr i
  have h0 : |(D.Ly.qp i 2 : ℝ) * D.Dw| ≤ D.N ^ D.εL := by
    linarith [abs_nonneg ((D.Ly.qp i 0 : ℝ) * D.χ), abs_nonneg ((D.Ly.qp i 1 : ℝ) * D.χ)]
  have h1 : |-((D.Ly.qp i 1 : ℝ) * D.χ)| ≤ D.N ^ D.εL := by
    rw [abs_neg]
    linarith [abs_nonneg ((D.Ly.qp i 0 : ℝ) * D.χ), abs_nonneg ((D.Ly.qp i 2 : ℝ) * D.Dw)]
  refine hC₀ (D.Ly.G i) (H.lygood.deg i) _ _ D.Dw (D.N ^ D.εL) (D.N ^ D.εL)
    (Real.rpow_pos_of_pos hN0 _) hDw1 hE h0 h1 (by linarith) ?_
  intro t ht w hw
  have := H.lygood.mov i t ht w hw
  have e : (D.Ly.qp i 2 : ℝ) * D.Dw + t * -((D.Ly.qp i 1 : ℝ) * D.χ) + D.Dw * w =
      (D.Ly.qp i 2 : ℝ) * D.Dw - t * ((D.Ly.qp i 1 : ℝ) * D.χ) + D.Dw * w := by ring
  rw [e]; exact this

namespace CoreData

variable (D : CoreData α)

def crossEa (r Hx : ℝ) : ℝ :=
  D.K * D.a₀ + 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (2 * D.N ^ (-r) + Hx)
def crossEb (r B : ℝ) : ℝ :=
  D.N ^ D.εL * D.a₁ + 9 * B * (2 * D.N ^ (-r)) * (1 + D.K + D.K ^ 2)
def crossG (r Hx B : ℝ) : ℝ := 9 * B * (1 + 2 * (D.K + 2 * Hx + 2 * D.N ^ (-r)))
def crossW (r Hx B : ℝ) : ℝ := 2 * D.crossEb r B + 2 * D.crossG r Hx B * D.N ^ (-r)
def crossTheta (r Hx K₁ B : ℝ) : ℝ :=
  Hx * D.a₁ ^ D.d / (2 * D.K * K₁ * D.crossW r Hx B ^ D.d * (Hx + 2 * D.N ^ (-r)))
def crossCs (r Hx K₁ : ℝ) : ℝ :=
  (8 * D.K + 2) * (Hx / D.N ^ (-r) + 2) * 2 * D.K * (D.N ^ (-r)) ^ 3 *
    (1 + 2 * D.crossEa r Hx / D.a₀) ^ D.d * D.a₀ ^ D.d /
    ((D.N ^ (-r)) ^ 2 * Hx * D.a₀ ^ D.d / K₁)
def crossLip (r Hx K₁ B : ℝ) : ℝ :=
  14 * crossB D.d ((D.crossEa r Hx + D.crossEb r B + D.crossG r Hx B * D.N ^ (-r)) / D.a₀)
      (D.crossCs r Hx K₁) (D.crossTheta r Hx K₁ B) * D.a₀ / (Hx + 2 * D.N ^ (-r)) +
    9 * B * (2 * D.N ^ (-r))

end CoreData

/-- Numerical side conditions of the crossing at the chosen scales. -/
structure CrossOK (D : CoreData α) (r Hx K₁ B : ℝ) : Prop where
  r1 : D.Rcap⁻¹ ≤ r
  r2 : r ≤ D.Rcap
  Hx0 : 0 < Hx
  K₁1 : 1 ≤ K₁
  M1 : D.Rcap⁻¹ ≤ D.M
  M2 : D.M ≤ D.Rcap
  s₀0 : 0 ≤ D.s₀
  s₀R : D.s₀ ≤ D.Rcap
  d0 : 0 ≤ D.d
  d1 : D.d < 1
  εL0 : 0 ≤ D.εL
  coef : ∀ i m, |(D.Ly.G i).coeff m| ≤ B
  B0 : 0 ≤ B
  w1 : D.crossW r Hx B ≤ 1
  w1s : -Real.logb D.N (D.crossW r Hx B) ≤ D.Rcap

theorem crossB_pos (d e Cs θ : ℝ) : 0 < crossB d e Cs θ :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

theorem crossLip_nonneg (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B : ℝ}
    (hok : CrossOK D r Hx K₁ B) : 0 ≤ D.crossLip r Hx K₁ B := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hB0 := hok.B0
  have hHx := hok.Hx0
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hh : 0 < D.N ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have hc := crossB_pos D.d ((D.crossEa r Hx + D.crossEb r B + D.crossG r Hx B * D.N ^ (-r)) /
    D.a₀) (D.crossCs r Hx K₁) (D.crossTheta r Hx K₁ B)
  unfold CoreData.crossLip
  positivity

/-- The slice law of a kept point is flat in the height near it. -/
theorem flat_at (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B : ℝ} (hok : CrossOK D r Hx K₁ B) :
    ∀ p ∈ D.G2 (D.N ^ (-r)) Hx K₁, ∃ i, p.1 ∈ D.Ly.C i ∧
      ∀ t : ℝ, |t - p.2| ≤ D.N ^ (-r) → |t| ≤ 1 →
      ∀ y ∈ Icc (x2 D.b p.1 p.2 - 2 * Hx) (x2 D.b p.1 p.2 + 3 * Hx),
      ∀ y' ∈ Icc (x2 D.b p.1 p.2 - 2 * Hx) (x2 D.b p.1 p.2 + 3 * Hx),
        |MvPolynomial.eval ![t, y] (D.Ly.G i) - MvPolynomial.eval ![t, y'] (D.Ly.G i)| ≤
          D.crossLip r Hx K₁ B * |y - y'| := by
  intro p hp
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hh : 0 < D.N ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have hK₁0 : 0 < K₁ := by linarith [hok.K₁1]
  obtain ⟨i, hi, hπ, hP2⟩ := G2_dense D H hh hok.Hx0 hK₁0 p hp
  refine ⟨i, hi, ?_⟩
  have hB0 : 0 ≤ B := hok.B0
  have hE : 1 ≤ D.N ^ D.εL := Real.one_le_rpow (by linarith [H.N2]) hok.εL0
  have ha₁ : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hra : D.a₁ ≤ D.crossW r Hx B := by
    unfold CoreData.crossW CoreData.crossEb CoreData.crossG
    have h1 : D.a₁ ≤ D.N ^ D.εL * D.a₁ := le_mul_of_one_le_left ha₁.le hE
    have h2 : 0 ≤ 9 * B * (2 * D.N ^ (-r)) * (1 + D.K + D.K ^ 2) := by
      have := H.K1; positivity
    have h3 : 0 ≤ 9 * B * (1 + 2 * (D.K + 2 * Hx + 2 * D.N ^ (-r))) * D.N ^ (-r) := by
      have := H.K1; have := hok.Hx0; positivity
    nlinarith
  have hp1 : p ∈ D.G1 (D.N ^ (-r)) Hx K₁ := G2_subset D _ _ _ hp
  have key := crossing_at_point D H (Ea := D.crossEa r Hx) (Eb := D.crossEb r B)
    (G' := D.crossG r Hx B) (w₁ := D.crossW r Hx B) hok.r1 hok.r2 hok.Hx0 hok.K₁1 hok.M1 hok.M2
    hok.s₀0 hok.s₀R hok.d0 hok.d1 (D.G1 (D.N ^ (-r)) Hx K₁) (measurableSet_G1 D H _ _ _)
    (fun q hq => ⟨(G1_subset D _ _ _ hq).1, (G1_subset D _ _ _ hq).2.1⟩)
    (G1_dense D H hh hok.Hx0 hK₁0) p hp1 i hi hP2 hπ (hok.coef i) le_rfl le_rfl le_rfl le_rfl
    hok.w1 hok.w1s hra
  intro t ht ht1 y hy y' hy'
  have hk := key t ht ht1 y hy y' hy'
  have hπt : 0 < (D.π (D.dirBin i)).toReal := by
    haveI := H.πprob
    exact ENNReal.toReal_pos hπ (measure_ne_top _ _)
  have hθ : (D.N ^ (-r)) ^ 2 * Hx * D.a₁ ^ D.d * (D.π (D.dirBin i)).toReal / K₁ /
      (2 * D.K * (D.N ^ (-r)) ^ 3 * D.crossW r Hx B ^ D.d * (D.π (D.dirBin i)).toReal) *
      D.N ^ (-r) / (Hx + 2 * D.N ^ (-r)) = D.crossTheta r Hx K₁ B := by
    unfold CoreData.crossTheta
    have hK0 : 0 < D.K := by linarith [H.K1]
    have hw0 : 0 < D.crossW r Hx B := ha₁.trans_le hra
    have hwd : 0 < D.crossW r Hx B ^ D.d := Real.rpow_pos_of_pos hw0 _
    have hHx2 : 0 < Hx + 2 * D.N ^ (-r) := by linarith [hok.Hx0]
    field_simp
  rw [hθ] at hk
  exact hk

/-- Hidden window of nearby points of the slice of a kept point. -/
theorem slice_window (D : CoreData α) (H : CoreHyp D) {r Hx K₁ B : ℝ}
    (hok : CrossOK D r Hx K₁ B) {p : α × ℝ} (hp : p ∈ D.G2 (D.N ^ (-r)) Hx K₁)
    {i : Fin D.Ly.n} (hpi : p.1 ∈ D.Ly.C i) {q : α × ℝ} (hqi : q.1 ∈ D.Ly.C i)
    (hq : NativeOK D q) (ht : |q.2 - p.2| ≤ D.N ^ (-r))
    (hy : |x2 D.b q.1 q.2 - x2 D.b p.1 p.2| ≤ Hx) :
    |x3 D.b q.1 q.2 - x3 D.b p.1 p.2| ≤
      2 * (D.N ^ D.εL * D.a₁) + D.crossLip r Hx K₁ B * |x2 D.b q.1 q.2 - x2 D.b p.1 p.2| +
        9 * B * (2 * |q.2 - p.2|) * (1 + D.K + D.K ^ 2) := by
  obtain ⟨i', hi', hflat⟩ := flat_at D H hok p hp
  have hii : i' = i := by
    by_contra hne
    exact Set.disjoint_left.mp (H.lygood.disj _ _ hne) hi' hpi
  subst hii
  have hp0 := G1_subset D _ _ _ (G2_subset D _ _ _ hp)
  have hpn := hp0.1
  have hq2 : |q.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1.1], hq.1.2⟩
  have hp2 : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hpn.1.1], hpn.1.2⟩
  have hfq := (H.lygood.fit i' q.1 hqi q.2 hq.1).2
  have hfp := (H.lygood.fit i' p.1 hpi p.2 hpn.1).2
  have hHx := hok.Hx0
  have hya : x2 D.b q.1 q.2 ∈ Icc (x2 D.b p.1 p.2 - 2 * Hx) (x2 D.b p.1 p.2 + 3 * Hx) := by
    have := abs_le.mp hy; constructor <;> linarith [this.1, this.2]
  have hyb : x2 D.b p.1 p.2 ∈ Icc (x2 D.b p.1 p.2 - 2 * Hx) (x2 D.b p.1 p.2 + 3 * Hx) := by
    constructor <;> linarith
  have hl := hflat q.2 ht hq2 _ hya _ hyb
  have hs := slice_law_time_shift (D.Ly.G i') (H.lygood.deg i') (hok.coef i')
    (y := x2 D.b p.1 p.2) hq2 hp2
  have hx2p := abs_x2_le_of_native D hpn
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hok.coef i' 0)
  have hs' : |MvPolynomial.eval ![q.2, x2 D.b p.1 p.2] (D.Ly.G i') -
      MvPolynomial.eval ![p.2, x2 D.b p.1 p.2] (D.Ly.G i')| ≤
        9 * B * (2 * |q.2 - p.2|) * (1 + D.K + D.K ^ 2) := by
    refine hs.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have := pow_le_pow_left₀ (abs_nonneg _) hx2p 2
    linarith
  calc |x3 D.b q.1 q.2 - x3 D.b p.1 p.2|
      ≤ |x3 D.b q.1 q.2 - MvPolynomial.eval ![q.2, x2 D.b q.1 q.2] (D.Ly.G i')| +
        |MvPolynomial.eval ![q.2, x2 D.b q.1 q.2] (D.Ly.G i') -
          MvPolynomial.eval ![q.2, x2 D.b p.1 p.2] (D.Ly.G i')| +
        |MvPolynomial.eval ![q.2, x2 D.b p.1 p.2] (D.Ly.G i') -
          MvPolynomial.eval ![p.2, x2 D.b p.1 p.2] (D.Ly.G i')| +
        |x3 D.b p.1 p.2 - MvPolynomial.eval ![p.2, x2 D.b p.1 p.2] (D.Ly.G i')| := by
        have e : x3 D.b q.1 q.2 - x3 D.b p.1 p.2 =
            (x3 D.b q.1 q.2 - MvPolynomial.eval ![q.2, x2 D.b q.1 q.2] (D.Ly.G i')) +
            (MvPolynomial.eval ![q.2, x2 D.b q.1 q.2] (D.Ly.G i') -
              MvPolynomial.eval ![q.2, x2 D.b p.1 p.2] (D.Ly.G i')) +
            (MvPolynomial.eval ![q.2, x2 D.b p.1 p.2] (D.Ly.G i') -
              MvPolynomial.eval ![p.2, x2 D.b p.1 p.2] (D.Ly.G i')) -
            (x3 D.b p.1 p.2 - MvPolynomial.eval ![p.2, x2 D.b p.1 p.2] (D.Ly.G i')) := by ring
        rw [e]
        refine (abs_sub _ _).trans ?_
        exact add_le_add (abs_add_three _ _ _) le_rfl
    _ ≤ D.N ^ D.εL * D.a₁ + D.crossLip r Hx K₁ B * |x2 D.b q.1 q.2 - x2 D.b p.1 p.2| +
        9 * B * (2 * |q.2 - p.2|) * (1 + D.K + D.K ^ 2) + D.N ^ D.εL * D.a₁ := by
        gcongr
    _ = _ := by ring

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
