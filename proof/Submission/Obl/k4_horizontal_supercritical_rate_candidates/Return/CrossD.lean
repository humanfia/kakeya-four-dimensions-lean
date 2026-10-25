import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CellCaps
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CrossingApp
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.PolyQuad
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.PredictorCells
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
# Non-steepness of a slice law at a sample point

At a point whose slice and whose crossing cell's coarse labels are dense, the slice law
`G(t, ·)` is Lipschitz in the height with constant `14 B a₀ / (Hx + 2h)` near the point.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Native bounds of a good point. -/
def NativeOK (D : CoreData α) (q : α × ℝ) : Prop :=
  q.2 ∈ Icc (0 : ℝ) 1 ∧ (∀ e, |D.b q.1 e| ≤ 2 * D.K) ∧
    |D.b q.1 0| + |D.b q.1 1| + |D.b q.1 3| + |D.b q.1 4| ≤ D.K

/-- The crossing constant. -/
def crossB (d e Cs θ : ℝ) : ℝ := max 1 ((2 * e + 40 * e * Cs / θ ^ 2) ^ (1 / (1 - d)))

theorem fitVal_sub (L : Fin 4 → ℝ) (t y z t' y' z' : ℝ) :
    (L 0 + L 1 * t + L 2 * y + L 3 * z) - (L 0 + L 1 * t' + L 2 * y' + L 3 * z') =
      L 1 * (t - t') + L 2 * (y - y') + L 3 * (z - z') := by ring

theorem floor_div_eq_iff_mem_Ico {u χ : ℝ} (hχ : 0 < χ) (v : ℤ) :
    ⌊u / χ⌋ = v ↔ u ∈ Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ) := by
  rw [Int.floor_eq_iff, le_div_iff₀ hχ, div_lt_iff₀ hχ]; simp [Set.mem_Ico]

theorem dirBin_eq (D : CoreData α) (hχ : 0 < D.χ) (i : Fin D.Ly.n) :
    {u : ℝ | ⌊u / D.χ⌋ = D.Ly.qp i 0} = D.dirBin i := by
  ext u; simp only [mem_ofPred_eq, CoreData.dirBin]; exact floor_div_eq_iff_mem_Ico hχ _

theorem same_cell_bounds {b : α → Fin 6 → ℝ} {h Hc : ℝ} (hh : 0 < h) (hHc : 0 < Hc)
    {p q : α × ℝ} (hpq : xcell b h Hc q = xcell b h Hc p) :
    |q.2 - p.2| < h ∧ |x1 b q.1 q.2 - x1 b p.1 p.2| < h ∧ |x2 b q.1 q.2 - x2 b p.1 p.2| < Hc := by
  unfold xcell at hpq
  have e1 : ⌊q.2 / h⌋ = ⌊p.2 / h⌋ := congrArg Prod.fst hpq
  have e2 : ⌊x1 b q.1 q.2 / h⌋ = ⌊x1 b p.1 p.2 / h⌋ := congrArg (fun z => z.2.1) hpq
  have e3 : ⌊x2 b q.1 q.2 / Hc⌋ = ⌊x2 b p.1 p.2 / Hc⌋ := congrArg (fun z => z.2.2) hpq
  have key : ∀ {u v c : ℝ}, 0 < c → ⌊u / c⌋ = ⌊v / c⌋ → |u - v| < c := by
    intro u v c hc huv
    have h1 := Int.floor_le (u / c); have h2 := Int.lt_floor_add_one (u / c)
    have h3 := Int.floor_le (v / c); have h4 := Int.lt_floor_add_one (v / c)
    rw [huv] at h1 h2
    have a1 : (⌊v / c⌋ : ℝ) * c ≤ u := by rwa [le_div_iff₀ hc] at h1
    have a2 : u < ((⌊v / c⌋ : ℝ) + 1) * c := by rwa [div_lt_iff₀ hc] at h2
    have a3 : (⌊v / c⌋ : ℝ) * c ≤ v := by rwa [le_div_iff₀ hc] at h3
    have a4 : v < ((⌊v / c⌋ : ℝ) + 1) * c := by rwa [div_lt_iff₀ hc] at h4
    rw [abs_lt]; constructor <;> nlinarith
  exact ⟨key hh e1, key hh e2, key hHc e3⟩

theorem abs_x1_le_of_native (D : CoreData α) {q : α × ℝ} (hq : NativeOK D q) :
    |x1 D.b q.1 q.2| ≤ D.K := by
  obtain ⟨ht, -, hsum⟩ := hq
  have h1 : |q.2 * D.b q.1 3| ≤ |D.b q.1 3| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
  unfold x1
  calc |D.b q.1 0 + q.2 * D.b q.1 3| ≤ |D.b q.1 0| + |q.2 * D.b q.1 3| := abs_add_le _ _
    _ ≤ D.K := by linarith [abs_nonneg (D.b q.1 1), abs_nonneg (D.b q.1 4)]

theorem abs_x2_le_of_native (D : CoreData α) {q : α × ℝ} (hq : NativeOK D q) :
    |x2 D.b q.1 q.2| ≤ D.K := by
  obtain ⟨ht, -, hsum⟩ := hq
  have h1 : |q.2 * D.b q.1 4| ≤ |D.b q.1 4| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
  unfold x2
  calc |D.b q.1 1 + q.2 * D.b q.1 4| ≤ |D.b q.1 1| + |q.2 * D.b q.1 4| := abs_add_le _ _
    _ ≤ D.K := by linarith [abs_nonneg (D.b q.1 0), abs_nonneg (D.b q.1 3)]

theorem abs_x3_le_of_native (D : CoreData α) {q : α × ℝ} (hq : NativeOK D q) :
    |x3 D.b q.1 q.2| ≤ 4 * D.K := by
  obtain ⟨ht, hb, -⟩ := hq
  have h1 : |q.2 * D.b q.1 5| ≤ |D.b q.1 5| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
  unfold x3
  calc |D.b q.1 2 + q.2 * D.b q.1 5| ≤ |D.b q.1 2| + |q.2 * D.b q.1 5| := abs_add_le _ _
    _ ≤ 4 * D.K := by linarith [hb 2, hb 5]

theorem f₀_q_pos (D : CoreData α) : 0 < D.f₀.q := by unfold Fam.q; positivity

theorem f₀_q_le_one (D : CoreData α) : D.f₀.q ≤ 1 := by
  unfold Fam.q; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- A coarse label's fit, frozen at the cell's sample point, holds on the whole cell. -/
theorem cell_fit_bound (D : CoreData α) (H : CoreHyp D) {h Hx Ea : ℝ} (hh : 0 < h)
    (hHx : 0 < Hx)
    (hEa : D.K * D.a₀ + 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (2 * h + Hx) ≤ Ea)
    {p q : α × ℝ} (hqnat : NativeOK D q) (j : Fin D.f₀.n)
    (hqj : q.1 ∈ D.f₀.B j ∧ q.2 ∈ D.f₀.I j) (hcell : xcell D.b h Hx q = xcell D.b h Hx p) :
    |x3 D.b q.1 q.2 - D.f₀.fitVal j p.2 (x1 D.b p.1 p.2) (x2 D.b p.1 p.2)| ≤ Ea := by
  obtain ⟨ht, hx1, hx2⟩ := same_cell_bounds hh hHx hcell
  have hfit : |x3 D.b q.1 q.2 - D.f₀.fitVal j q.2 (x1 D.b q.1 q.2) (x2 D.b q.1 q.2)| ≤
      D.K * D.a₀ := H.f₀good.fit j q.1 hqj.1 q.2 hqj.2
  have hsl := H.f₀good.slope j q.1 hqj.1 q.2 hqj.2
  have hL3 := H.f₀good.L3bd j
  have ha₀ : 0 ≤ D.N ^ (-D.s₀) := Real.rpow_nonneg (by linarith [H.N2]) _
  obtain ⟨hL1, hL2, hL3'⟩ := horizontal_affine_coeff_bounds (D.f₀.L j) H.K1 ha₀ (f₀_q_pos D)
    (f₀_q_le_one D) (abs_x1_le_of_native D hqnat) hqnat.1 hL3 hsl
  set C := 2 * D.K ^ 2 * (1 + D.N ^ (-D.s₀) / D.f₀.q ^ 2) with hC
  have hdiff : |D.f₀.fitVal j q.2 (x1 D.b q.1 q.2) (x2 D.b q.1 q.2) -
      D.f₀.fitVal j p.2 (x1 D.b p.1 p.2) (x2 D.b p.1 p.2)| ≤ C * (2 * h + Hx) := by
    unfold Fam.fitVal
    rw [fitVal_sub]
    have e1 : |D.f₀.L j 1 * (q.2 - p.2)| ≤ C * h := by
      rw [abs_mul]; exact mul_le_mul hL1 ht.le (abs_nonneg _) ((abs_nonneg _).trans hL1)
    have e2 : |D.f₀.L j 2 * (x1 D.b q.1 q.2 - x1 D.b p.1 p.2)| ≤ C * h := by
      rw [abs_mul]; exact mul_le_mul hL2 hx1.le (abs_nonneg _) ((abs_nonneg _).trans hL1)
    have e3 : |D.f₀.L j 3 * (x2 D.b q.1 q.2 - x2 D.b p.1 p.2)| ≤ C * Hx := by
      rw [abs_mul]; exact mul_le_mul hL3' hx2.le (abs_nonneg _) ((abs_nonneg _).trans hL1)
    calc _ ≤ |D.f₀.L j 1 * (q.2 - p.2)| + |D.f₀.L j 2 * (x1 D.b q.1 q.2 - x1 D.b p.1 p.2)| +
          |D.f₀.L j 3 * (x2 D.b q.1 q.2 - x2 D.b p.1 p.2)| := abs_add_three _ _ _
      _ ≤ C * h + C * h + C * Hx := add_le_add (add_le_add e1 e2) e3
      _ = C * (2 * h + Hx) := by ring
  calc _ ≤ |x3 D.b q.1 q.2 - D.f₀.fitVal j q.2 (x1 D.b q.1 q.2) (x2 D.b q.1 q.2)| +
        |D.f₀.fitVal j q.2 (x1 D.b q.1 q.2) (x2 D.b q.1 q.2) -
          D.f₀.fitVal j p.2 (x1 D.b p.1 p.2) (x2 D.b p.1 p.2)| := abs_sub_le _ _ _
    _ ≤ D.K * D.a₀ + C * (2 * h + Hx) := add_le_add hfit hdiff
    _ ≤ Ea := hEa

/-- Moving the time of a degree-two slice law. -/
theorem slice_law_time_shift (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) {B : ℝ}
    (hB : ∀ m, |P.coeff m| ≤ B) {t t' y : ℝ} (ht : |t| ≤ 1) (ht' : |t'| ≤ 1) :
    |MvPolynomial.eval ![t, y] P - MvPolynomial.eval ![t', y] P| ≤
      9 * B * (2 * |t - t'|) * (1 + |y| + |y| ^ 2) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hcard : (P.support.card : ℝ) ≤ 9 := by
    have := Submission.Lib.K4ChartLifting.card_support_le (D := 2) P hP
    exact_mod_cast this
  have hk : ∀ k, |ycoef P k t - ycoef P k t'| ≤ 9 * B * (2 * |t - t'|) := fun k =>
    (abs_ycoef_sub_le P hP hB k ht ht').trans (by gcongr)
  rw [eval_eq_quad P hP, eval_eq_quad P hP]
  have e : ycoef P 0 t + ycoef P 1 t * y + ycoef P 2 t * y ^ 2 -
      (ycoef P 0 t' + ycoef P 1 t' * y + ycoef P 2 t' * y ^ 2) =
      (ycoef P 0 t - ycoef P 0 t') + (ycoef P 1 t - ycoef P 1 t') * y +
        (ycoef P 2 t - ycoef P 2 t') * y ^ 2 := by ring
  rw [e]
  set E := 9 * B * (2 * |t - t'|)
  calc _ ≤ |ycoef P 0 t - ycoef P 0 t'| + |(ycoef P 1 t - ycoef P 1 t') * y| +
        |(ycoef P 2 t - ycoef P 2 t') * y ^ 2| := abs_add_three _ _ _
    _ ≤ E + E * |y| + E * |y| ^ 2 := by
        rw [abs_mul, abs_mul, abs_pow]
        exact add_le_add (add_le_add (hk 0) (mul_le_mul_of_nonneg_right (hk 1) (abs_nonneg _)))
          (mul_le_mul_of_nonneg_right (hk 2) (by positivity))
    _ = E * (1 + |y| + |y| ^ 2) := by ring

/-- Lipschitz bound of a degree-two slice law in the height. -/
theorem slice_law_lip (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) {B : ℝ}
    (hB : ∀ m, |P.coeff m| ≤ B) {t u u' R : ℝ} (ht : |t| ≤ 1) (hu : |u| ≤ R) (hu' : |u'| ≤ R) :
    |(ycoef P 0 t + ycoef P 1 t * u + ycoef P 2 t * u ^ 2) -
        (ycoef P 0 t + ycoef P 1 t * u' + ycoef P 2 t * u' ^ 2)| ≤
      9 * B * (1 + 2 * R) * |u - u'| := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hcard : (P.support.card : ℝ) ≤ 9 := by
    have := Submission.Lib.K4ChartLifting.card_support_le (D := 2) P hP
    exact_mod_cast this
  have hk : ∀ k, |ycoef P k t| ≤ 9 * B := fun k =>
    (abs_ycoef_le P hB k ht).trans (by gcongr)
  have e : (ycoef P 0 t + ycoef P 1 t * u + ycoef P 2 t * u ^ 2) -
      (ycoef P 0 t + ycoef P 1 t * u' + ycoef P 2 t * u' ^ 2) =
      (ycoef P 1 t + ycoef P 2 t * (u + u')) * (u - u') := by ring
  rw [e, abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have huu : |u + u'| ≤ 2 * R := (abs_add_le _ _).trans (by linarith)
  calc |ycoef P 1 t + ycoef P 2 t * (u + u')| ≤ |ycoef P 1 t| + |ycoef P 2 t| * |u + u'| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ 9 * B + 9 * B * (2 * R) := add_le_add (hk 1)
        (mul_le_mul (hk 2) huu (abs_nonneg _) (by positivity))
    _ = 9 * B * (1 + 2 * R) := by ring

/-- Mass of a slice's points in one cube and one hidden window. -/
theorem slice_cube_cap (D : CoreData α) (H : CoreHyp D) {r w₁ : ℝ}
    (hr1 : D.Rcap⁻¹ ≤ r) (hr2 : r ≤ D.Rcap) (hM1 : D.Rcap⁻¹ ≤ D.M) (hM2 : D.M ≤ D.Rcap)
    (hw₀ : 0 < w₁) (hw₁1 : w₁ ≤ 1) (hw₁s : -Real.logb D.N w₁ ≤ D.Rcap)
    (i : Fin D.Ly.n) (E : Set (α × ℝ)) (hE : ∀ q ∈ E, q.1 ∈ D.Ly.C i)
    (Q : Fin 3 → ℤ) (hEQ : ∀ q ∈ E, cube D.b (D.N ^ (-r)) q = Q)
    (w : ℝ) (hEw : ∀ q ∈ E, x3 D.b q.1 q.2 ∈ Icc w (w + w₁)) :
    D.ρs E ≤ ENNReal.ofReal
      (2 * D.K * (D.N ^ (-r)) ^ 3 * w₁ ^ D.d * (D.π (D.dirBin i)).toReal) := by
  haveI := H.πprob
  have hN : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  set σ := -Real.logb D.N w₁ with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ, neg_nonneg]; exact Real.logb_nonpos hN hw₀.le hw₁1
  have hNσ : D.N ^ (-σ) = w₁ := by
    rw [hσ, neg_neg, Real.rpow_logb hN0 hN.ne' hw₀]
  have hsub : E ⊆ {p | cube D.b (D.N ^ (-r)) p = Q} ∩
      {p | x3 D.b p.1 p.2 ∈ Icc w (w + D.N ^ (-σ))} ∩
      {p | ⌊D.b p.1 3 / D.N ^ (-D.M)⌋ = D.Ly.qp i 0} := by
    intro q hq
    refine ⟨⟨hEQ q hq, ?_⟩, ?_⟩
    · show x3 D.b q.1 q.2 ∈ Icc w (w + D.N ^ (-σ))
      rw [hNσ]; exact hEw q hq
    · exact (H.lygood.bins i q.1 (hE q hq)).1
  have hm : D.ρs ≤ D.μ := H.ρsρ.trans H.ρμ
  have hcap := cube_dir_cap H.caps hN hr1 hr2 hσ0 hw₁s hM1 hM2 Q w (D.Ly.qp i 0) D.ρs hm
  refine (measure_mono hsub).trans (hcap.trans (le_of_eq ?_))
  have hχ : 0 < D.χ := Real.rpow_pos_of_pos hN0 _
  have hbin : {u : ℝ | ⌊u / D.N ^ (-D.M)⌋ = D.Ly.qp i 0} = D.dirBin i := dirBin_eq D hχ i
  have hpow : D.N ^ (-3 * r - D.d * σ) = (D.N ^ (-r)) ^ 3 * w₁ ^ D.d := by
    rw [show -3 * r - D.d * σ = (-r) * ((3 : ℕ) : ℝ) + (-σ) * D.d by push_cast; ring,
      Real.rpow_add hN0, Real.rpow_mul hN0.le, Real.rpow_mul hN0.le, Real.rpow_natCast, hNσ]
  have hπfin : D.π (D.dirBin i) ≠ ⊤ := measure_ne_top _ _
  rw [hbin, hpow, ENNReal.ofReal_mul (p := 2 * D.K * (D.N ^ (-r)) ^ 3 * w₁ ^ D.d) (by positivity),
    ENNReal.ofReal_toReal hπfin]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- Window caps on one cell, at every width from `a₀` up. -/
theorem cell_window_cap (D : CoreData α) (H : CoreHyp D) {r Hx : ℝ}
    (hr1 : D.Rcap⁻¹ ≤ r) (hr2 : r ≤ D.Rcap) (hHx : 0 < Hx) (hs₀ : 0 ≤ D.s₀)
    (hs₀R : D.s₀ ≤ D.Rcap) (hd0 : 0 ≤ D.d) (ω : ℤ × ℤ × ℤ) (Ω : Set (α × ℝ))
    (hΩ : ∀ q ∈ Ω, xcell D.b (D.N ^ (-r)) Hx q = ω) (hΩnat : ∀ q ∈ Ω, NativeOK D q) :
    ∀ w W', D.a₀ ≤ W' → D.ρs (Ω ∩ {q | x3 D.b q.1 q.2 ∈ Icc w (w + W')}) ≤
      ENNReal.ofReal ((8 * D.K + 2) * (Hx / D.N ^ (-r) + 2) * 2 * D.K * (D.N ^ (-r)) ^ 3 *
        W' ^ D.d) := by
  have hN : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  set h := D.N ^ (-r) with hhdef
  have hh : 0 < h := Real.rpow_pos_of_pos hN0 _
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hm : D.ρs ≤ D.μ := H.ρsρ.trans H.ρμ
  have ha₀pos : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have ha₀1 : D.a₀ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
  have base : ∀ w W, D.a₀ ≤ W → W ≤ 1 →
      D.ρs (Ω ∩ {q | x3 D.b q.1 q.2 ∈ Icc w (w + W)}) ≤
        ENNReal.ofReal ((Hx / h + 2) * 2 * D.K * h ^ 3 * W ^ D.d) := by
    intro w W hW0 hW1
    have hWpos : 0 < W := ha₀pos.trans_le hW0
    have hlog : -Real.logb D.N W ≤ D.s₀ := by
      have := Real.logb_le_logb_of_le hN ha₀pos hW0
      rw [CoreData.a₀, Real.logb_rpow hN0 hN.ne'] at this
      linarith
    have hc := window_cap_cell H.caps hN hr1 hr2 hHx ω w W hWpos hW1 (hlog.trans hs₀R) D.ρs hm
    have hsub : Ω ∩ {q | x3 D.b q.1 q.2 ∈ Icc w (w + W)} ⊆
        {q | xcell D.b h Hx q = ω} ∩ {q | x3 D.b q.1 q.2 ∈ Icc w (w + W)} :=
      fun q hq => ⟨hΩ q hq.1, hq.2⟩
    refine (measure_mono hsub).trans (hc.trans (le_of_eq ?_))
    congr 1
    have hpow : D.N ^ (-3 * r - D.d * -Real.logb D.N W) = h ^ 3 * W ^ D.d := by
      rw [show -3 * r - D.d * -Real.logb D.N W =
          (-r) * ((3 : ℕ) : ℝ) + Real.logb D.N W * D.d by push_cast; ring,
        Real.rpow_add hN0, Real.rpow_mul hN0.le, Real.rpow_mul hN0.le, Real.rpow_natCast,
        Real.rpow_logb hN0 hN.ne' hWpos]
    rw [hpow]; ring
  intro w W' hW'
  have hX : 0 ≤ (Hx / h + 2) * 2 * D.K * h ^ 3 := by positivity
  rcases le_or_gt W' 1 with hW1 | hW1
  · refine (base w W' hW' hW1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hWd : 0 ≤ W' ^ D.d := Real.rpow_nonneg (ha₀pos.le.trans hW') _
    have : (Hx / h + 2) * 2 * D.K * h ^ 3 * W' ^ D.d ≤
        (8 * D.K + 2) * ((Hx / h + 2) * 2 * D.K * h ^ 3 * W' ^ D.d) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  · set n := ⌊8 * D.K⌋₊ + 1 with hn
    have hsub : Ω ∩ {q | x3 D.b q.1 q.2 ∈ Icc w (w + W')} ⊆
        ⋃ k ∈ Finset.range n,
          Ω ∩ {q | x3 D.b q.1 q.2 ∈ Icc (-4 * D.K + k) (-4 * D.K + k + 1)} := by
      intro q hq
      have hx := abs_le.mp (abs_x3_le_of_native D (hΩnat q hq.1))
      set k := ⌊x3 D.b q.1 q.2 + 4 * D.K⌋₊ with hk
      have hk1 : (k : ℝ) ≤ x3 D.b q.1 q.2 + 4 * D.K := Nat.floor_le (by linarith)
      have hk2 : x3 D.b q.1 q.2 + 4 * D.K < k + 1 := Nat.lt_floor_add_one _
      have hkn : k < n := by
        have : k ≤ ⌊8 * D.K⌋₊ := Nat.floor_le_floor (by linarith)
        omega
      refine mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hkn, hq.1, ?_, ?_⟩ <;> linarith
    calc D.ρs (Ω ∩ {q | x3 D.b q.1 q.2 ∈ Icc w (w + W')})
        ≤ ∑ k ∈ Finset.range n,
            D.ρs (Ω ∩ {q | x3 D.b q.1 q.2 ∈ Icc (-4 * D.K + k) (-4 * D.K + k + 1)}) :=
          (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _k ∈ Finset.range n, ENNReal.ofReal ((Hx / h + 2) * 2 * D.K * h ^ 3) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have := base (-4 * D.K + k) 1 ha₀1 le_rfl
          rwa [Real.one_rpow, mul_one] at this
      _ = ENNReal.ofReal (n * ((Hx / h + 2) * 2 * D.K * h ^ 3)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (p := (n : ℝ)) (by positivity), ENNReal.ofReal_natCast]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hn' : (n : ℝ) ≤ 8 * D.K + 2 := by
            have := Nat.floor_le (show 0 ≤ 8 * D.K by linarith)
            rw [hn]; push_cast; linarith
          have hWd : 1 ≤ W' ^ D.d := Real.one_le_rpow hW1.le hd0
          calc (n : ℝ) * ((Hx / h + 2) * 2 * D.K * h ^ 3)
              ≤ (8 * D.K + 2) * ((Hx / h + 2) * 2 * D.K * h ^ 3) :=
                mul_le_mul_of_nonneg_right hn' hX
            _ ≤ (8 * D.K + 2) * ((Hx / h + 2) * 2 * D.K * h ^ 3) * W' ^ D.d :=
                le_mul_of_one_le_right (by positivity) hWd
            _ = _ := by ring

/-- Non-steepness of the slice law at a point with dense slice and dense coarse labels. -/
theorem crossing_at_point (D : CoreData α) (H : CoreHyp D)
    {r Hx K₁ Ea Eb G' w₁ B : ℝ}
    (hr1 : D.Rcap⁻¹ ≤ r) (hr2 : r ≤ D.Rcap) (hHx : 0 < Hx) (hK₁ : 1 ≤ K₁)
    (hM1 : D.Rcap⁻¹ ≤ D.M) (hM2 : D.M ≤ D.Rcap) (hs₀ : 0 ≤ D.s₀) (hs₀R : D.s₀ ≤ D.Rcap)
    (hd0 : 0 ≤ D.d) (hd1 : D.d < 1)
    (G₁ : Set (α × ℝ)) (hG₁m : MeasurableSet G₁)
    (hG₁nat : ∀ q ∈ G₁, NativeOK D q ∧ ∀ k : ℕ, q.2 ≠ (k : ℝ) / 2 ^ D.f₀.T)
    (hG₁lab : ∀ q ∈ G₁, ∃ j, q.1 ∈ D.f₀.B j ∧ q.2 ∈ D.f₀.I j ∧
        ENNReal.ofReal ((D.N ^ (-r)) ^ 2 * Hx * D.a₀ ^ D.d / K₁) ≤
          D.ρs ((D.f₀.B j ×ˢ D.f₀.I j) ∩ G₁ ∩
            {p | xcell D.b (D.N ^ (-r)) Hx p = xcell D.b (D.N ^ (-r)) Hx q}))
    (p : α × ℝ) (hp : p ∈ G₁) (i : Fin D.Ly.n) (hpi : p.1 ∈ D.Ly.C i)
    (hP2 : ENNReal.ofReal ((D.N ^ (-r)) ^ 2 * Hx * D.a₁ ^ D.d / K₁) * D.π (D.dirBin i) ≤
        D.ρs (G₁ ∩ (D.Ly.C i ×ˢ univ) ∩
          {q | xcell D.b (D.N ^ (-r)) Hx q = xcell D.b (D.N ^ (-r)) Hx p}))
    (hπpos : D.π (D.dirBin i) ≠ 0)
    (hB : ∀ m, |(D.Ly.G i).coeff m| ≤ B)
    (hEa : D.K * D.a₀ + 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (2 * D.N ^ (-r) + Hx) ≤ Ea)
    (hEb : D.N ^ D.εL * D.a₁ + 9 * B * (2 * D.N ^ (-r)) * (1 + D.K + D.K ^ 2) ≤ Eb)
    (hG' : 9 * B * (1 + 2 * (D.K + 2 * Hx + 2 * D.N ^ (-r))) ≤ G')
    (hw₁ : 2 * Eb + 2 * G' * D.N ^ (-r) ≤ w₁) (hw₁1 : w₁ ≤ 1)
    (hw₁s : -Real.logb D.N w₁ ≤ D.Rcap) (hra : D.a₁ ≤ w₁) :
    ∀ t : ℝ, |t - p.2| ≤ D.N ^ (-r) → |t| ≤ 1 →
      ∀ y ∈ Icc (x2 D.b p.1 p.2 - 2 * Hx) (x2 D.b p.1 p.2 + 3 * Hx),
      ∀ y' ∈ Icc (x2 D.b p.1 p.2 - 2 * Hx) (x2 D.b p.1 p.2 + 3 * Hx),
        |MvPolynomial.eval ![t, y] (D.Ly.G i) - MvPolynomial.eval ![t, y'] (D.Ly.G i)| ≤
          (14 * crossB D.d ((Ea + Eb + G' * D.N ^ (-r)) / D.a₀)
              ((8 * D.K + 2) * (Hx / D.N ^ (-r) + 2) * 2 * D.K * (D.N ^ (-r)) ^ 3 *
                (1 + 2 * Ea / D.a₀) ^ D.d * D.a₀ ^ D.d /
                ((D.N ^ (-r)) ^ 2 * Hx * D.a₀ ^ D.d / K₁))
              (((D.N ^ (-r)) ^ 2 * Hx * D.a₁ ^ D.d * (D.π (D.dirBin i)).toReal / K₁) /
                (2 * D.K * (D.N ^ (-r)) ^ 3 * w₁ ^ D.d * (D.π (D.dirBin i)).toReal) *
                D.N ^ (-r) / (Hx + 2 * D.N ^ (-r))) * D.a₀ / (Hx + 2 * D.N ^ (-r)) +
            9 * B * (2 * D.N ^ (-r))) * |y - y'| := by
  classical
  intro t ht ht1 y hy y' hy'
  haveI := H.πprob
  have hN : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  set h := D.N ^ (-r) with hhdef
  have hh : 0 < h := Real.rpow_pos_of_pos hN0 _
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have ha₀ : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have ha₁ : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hw₀ : 0 < w₁ := ha₁.trans_le hra
  have hpnat := (hG₁nat p hp).1
  have hp2 : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hpnat.1.1], hpnat.1.2⟩
  have hdeg := H.lygood.deg i
  have hcoef : ∀ m, |(D.Ly.G i).coeff m| ≤ B := hB
  have hRL0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set cellp := xcell D.b h Hx p with hcellp
  set Ω : Set (α × ℝ) := G₁ ∩ {q | xcell D.b h Hx q = cellp} with hΩdef
  set Es : Set (α × ℝ) := G₁ ∩ (D.Ly.C i ×ˢ univ) ∩ {q | xcell D.b h Hx q = cellp} with hEsdef
  set Eℓ : Fin D.f₀.n → Set (α × ℝ) :=
    fun j => (D.f₀.B j ×ˢ D.f₀.I j) ∩ G₁ ∩ {q | xcell D.b h Hx q = cellp} with hEℓdef
  set θ₁ := h ^ 2 * Hx * D.a₀ ^ D.d / K₁ with hθ₁def
  set S : Finset (Fin D.f₀.n) :=
    Finset.univ.filter (fun j => ENNReal.ofReal θ₁ ≤ D.ρs (Eℓ j)) with hSdef
  set z := (⌊x2 D.b p.1 p.2 / Hx⌋ : ℝ) * Hx with hzdef
  have hz1 : z ≤ x2 D.b p.1 p.2 := by
    have := Int.floor_le (x2 D.b p.1 p.2 / Hx); rwa [le_div_iff₀ hHx] at this
  have hz2 : x2 D.b p.1 p.2 < z + Hx := by
    have := Int.lt_floor_add_one (x2 D.b p.1 p.2 / Hx)
    rw [div_lt_iff₀ hHx] at this; linarith
  set A0 := ycoef (D.Ly.G i) 0 p.2 with hA0
  set A1 := ycoef (D.Ly.G i) 1 p.2 with hA1
  set A2 := ycoef (D.Ly.G i) 2 p.2 with hA2
  have hGp : ∀ u, MvPolynomial.eval ![p.2, u] (D.Ly.G i) = A0 + A1 * u + A2 * u ^ 2 :=
    fun u => eval_eq_quad _ hdeg _ _
  set πt := (D.π (D.dirBin i)).toReal with hπt
  have hπfin : D.π (D.dirBin i) ≠ ⊤ := measure_ne_top _ _
  have hπt0 : 0 < πt := ENNReal.toReal_pos hπpos hπfin
  set Mlo := h ^ 2 * Hx * D.a₁ ^ D.d * πt / K₁ with hMlodef
  set c := 2 * D.K * h ^ 3 * w₁ ^ D.d * πt with hcdef
  set Ccap := (8 * D.K + 2) * (Hx / h + 2) * 2 * D.K * h ^ 3 with hCcapdef
  -- membership in the cell
  have hcellmem : ∀ q, xcell D.b h Hx q = cellp →
      ⌊q.2 / h⌋ = ⌊p.2 / h⌋ ∧ ⌊x1 D.b q.1 q.2 / h⌋ = ⌊x1 D.b p.1 p.2 / h⌋ ∧
        ⌊x2 D.b q.1 q.2 / Hx⌋ = ⌊x2 D.b p.1 p.2 / Hx⌋ := by
    intro q hq
    exact ⟨congrArg Prod.fst hq, congrArg (fun z => z.2.1) hq, congrArg (fun z => z.2.2) hq⟩
  have hEsy : ∀ q ∈ Es, x2 D.b q.1 q.2 ∈ Icc z (z + Hx) := by
    intro q hq
    have h3 := (hcellmem q hq.2).2.2
    have := (floor_div_eq_iff_mem_Ico hHx _).mp h3
    exact ⟨this.1, by linarith [this.2]⟩
  have hEslab : ∀ q ∈ Es, ∃ j ∈ S, q ∈ Eℓ j := by
    intro q hq
    obtain ⟨j, hBj, hIj, hden⟩ := hG₁lab q hq.1.1
    have hq3 : xcell D.b h Hx q = cellp := hq.2
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ⟨⟨hBj, hIj⟩, hq.1.1⟩, hq3⟩
    simp only [hEℓdef]
    rw [← hq3]; exact hden
  have hlablev : ∀ j ∈ S, ∀ q ∈ Eℓ j,
      |x3 D.b q.1 q.2 - D.f₀.fitVal j p.2 (x1 D.b p.1 p.2) (x2 D.b p.1 p.2)| ≤ Ea := by
    intro j _ q hq
    exact cell_fit_bound D H hh hHx hEa (hG₁nat q hq.1.2).1 j hq.1.1 hq.2
  have hEslaw : ∀ q ∈ Es, |x3 D.b q.1 q.2 - (A0 + A1 * x2 D.b q.1 q.2 + A2 * x2 D.b q.1 q.2 ^ 2)|
      ≤ Eb := by
    intro q hq
    have hqnat := (hG₁nat q hq.1.1).1
    have hq2 : |q.2| ≤ 1 := abs_le.mpr ⟨by linarith [hqnat.1.1], hqnat.1.2⟩
    have hfit := (H.lygood.fit i q.1 hq.1.2.1 q.2 hqnat.1).2
    have hshift := slice_law_time_shift (D.Ly.G i) hdeg hcoef (y := x2 D.b q.1 q.2) hq2 hp2
    have htq : |q.2 - p.2| ≤ h := (same_cell_bounds hh hHx hq.2).1.le
    have hx2q := abs_x2_le_of_native D hqnat
    have hy2 : 1 + |x2 D.b q.1 q.2| + |x2 D.b q.1 q.2| ^ 2 ≤ 1 + D.K + D.K ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) hx2q 2
      linarith
    have hshift' : |MvPolynomial.eval ![q.2, x2 D.b q.1 q.2] (D.Ly.G i) -
        MvPolynomial.eval ![p.2, x2 D.b q.1 q.2] (D.Ly.G i)| ≤
          9 * B * (2 * h) * (1 + D.K + D.K ^ 2) := by
      refine hshift.trans ?_
      have h0 : 0 ≤ 1 + |x2 D.b q.1 q.2| + |x2 D.b q.1 q.2| ^ 2 := by positivity
      calc 9 * B * (2 * |q.2 - p.2|) * (1 + |x2 D.b q.1 q.2| + |x2 D.b q.1 q.2| ^ 2)
          ≤ 9 * B * (2 * h) * (1 + |x2 D.b q.1 q.2| + |x2 D.b q.1 q.2| ^ 2) := by
            gcongr
        _ ≤ 9 * B * (2 * h) * (1 + D.K + D.K ^ 2) := by gcongr
    rw [← hGp]
    calc _ ≤ |x3 D.b q.1 q.2 - MvPolynomial.eval ![q.2, x2 D.b q.1 q.2] (D.Ly.G i)| +
          |MvPolynomial.eval ![q.2, x2 D.b q.1 q.2] (D.Ly.G i) -
            MvPolynomial.eval ![p.2, x2 D.b q.1 q.2] (D.Ly.G i)| := abs_sub_le _ _ _
      _ ≤ D.N ^ D.εL * D.a₁ + 9 * B * (2 * h) * (1 + D.K + D.K ^ 2) :=
          add_le_add hfit hshift'
      _ ≤ Eb := hEb
  have hglip : ∀ u ∈ Icc (z - 2 * h) (z + Hx + 2 * h), ∀ u' ∈ Icc (z - 2 * h) (z + Hx + 2 * h),
      |(A0 + A1 * u + A2 * u ^ 2) - (A0 + A1 * u' + A2 * u' ^ 2)| ≤ G' * |u - u'| := by
    intro u hu u' hu'
    have hx2p := abs_le.mp (abs_x2_le_of_native D hpnat)
    have hR : ∀ v ∈ Icc (z - 2 * h) (z + Hx + 2 * h), |v| ≤ D.K + 2 * Hx + 2 * h := by
      intro v hv; rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
    have := slice_law_lip (D.Ly.G i) hdeg hcoef hp2 (hR u hu) (hR u' hu')
    exact this.trans (mul_le_mul_of_nonneg_right hG' (abs_nonneg _))
  have hEa0 : 0 ≤ Ea := le_trans (by have := f₀_q_pos D; positivity) hEa
  have hEb0 : 0 ≤ Eb := le_trans (by positivity) hEb
  have hG'0 : 0 ≤ G' := le_trans (by positivity) hG'
  have hKpos : 0 < D.K := by linarith [H.K1]
  have hK₁0 : 0 < K₁ := by linarith
  have hc : 0 < c := by positivity
  have hMlo : 0 < Mlo := by
    have : 0 < K₁ := by linarith
    positivity
  have hθ₁ : 0 < θ₁ := by
    have : 0 < K₁ := by linarith
    positivity
  have hCcap : 0 ≤ Ccap := by positivity
  have hθ1 : Mlo / c * h ≤ Hx + 2 * h := by
    have hwd : 0 < w₁ ^ D.d := Real.rpow_pos_of_pos hw₀ _
    have hrat : D.a₁ ^ D.d ≤ w₁ ^ D.d := Real.rpow_le_rpow ha₁.le hra hd0
    have e : Mlo / c * h = Hx * D.a₁ ^ D.d / (2 * D.K * K₁ * w₁ ^ D.d) := by
      rw [hMlodef, hcdef]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : Hx * D.a₁ ^ D.d ≤ Hx * w₁ ^ D.d := mul_le_mul_of_nonneg_left hrat hHx.le
    have h2 : 1 ≤ 2 * D.K * K₁ := by
      have : 1 ≤ D.K * K₁ := one_le_mul_of_one_le_of_one_le H.K1 hK₁
      linarith
    calc Hx * D.a₁ ^ D.d ≤ Hx * w₁ ^ D.d * 1 := by rw [mul_one]; exact h1
      _ ≤ Hx * w₁ ^ D.d * (2 * D.K * K₁) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Hx * w₁ ^ D.d * (2 * D.K * K₁) + 2 * h * (2 * D.K * K₁ * w₁ ^ D.d) :=
          le_add_of_nonneg_right (by positivity)
      _ = (Hx + 2 * h) * (2 * D.K * K₁ * w₁ ^ D.d) := by ring
  have hmass : ENNReal.ofReal Mlo ≤ D.ρs Es := by
    have e : Mlo = h ^ 2 * Hx * D.a₁ ^ D.d / K₁ * πt := by rw [hMlodef]; ring
    rw [e, ENNReal.ofReal_mul (by have : 0 < K₁ := by linarith
                                  positivity), hπt, ENNReal.ofReal_toReal hπfin]
    exact hP2
  have hcube : ∀ k : ℤ, D.ρs (Es ∩ {q | ⌊x2 D.b q.1 q.2 / h⌋ = k}) ≤ ENNReal.ofReal c := by
    intro k
    refine slice_cube_cap D H hr1 hr2 hM1 hM2 hw₀ hw₁1 hw₁s i _ (fun q hq => hq.1.1.2.1)
      ![⌊p.2 / h⌋, ⌊x1 D.b p.1 p.2 / h⌋, k] ?_
      (A0 + A1 * ((k : ℝ) * h) + A2 * ((k : ℝ) * h) ^ 2 - Eb - G' * h) ?_
    · intro q hq
      obtain ⟨e1, e2, -⟩ := hcellmem q hq.1.2
      funext e
      fin_cases e
      · exact e1
      · exact e2
      · exact hq.2
    · intro q hq
      have hlaw := abs_le.mp (hEslaw q hq.1)
      have hy := hEsy q hq.1
      have hkq := (floor_div_eq_iff_mem_Ico hh k).mp hq.2
      have hu : x2 D.b q.1 q.2 ∈ Icc (z - 2 * h) (z + Hx + 2 * h) :=
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hu' : (k : ℝ) * h ∈ Icc (z - 2 * h) (z + Hx + 2 * h) :=
        ⟨by linarith [hy.1, hkq.2], by linarith [hy.2, hkq.1]⟩
      have hl := hglip _ hu _ hu'
      have hd : |x2 D.b q.1 q.2 - (k : ℝ) * h| ≤ h := by
        rw [abs_le]; constructor <;> linarith [hkq.1, hkq.2]
      have hl' := abs_le.mp (hl.trans (mul_le_mul_of_nonneg_left hd hG'0))
      constructor <;> linarith [hl'.1, hl'.2, hlaw.1, hlaw.2]
  have hdense : ∀ j ∈ S, ENNReal.ofReal θ₁ ≤ D.ρs (Eℓ j) :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hmeasEℓ : ∀ j ∈ S, MeasurableSet (Eℓ j) := by
    intro j _
    have hI : MeasurableSet (D.f₀.I j) := by unfold Fam.I blk; exact measurableSet_Icc
    exact (((H.f₀good.measB j).prod hI).inter hG₁m).inter
      (measurableSet_xcell_eq H.bmeas h Hx cellp)
  have hdisj : ∀ j ∈ S, ∀ j' ∈ S, j ≠ j' → Disjoint (Eℓ j) (Eℓ j') := by
    intro j _ j' _ hjj'
    refine Set.disjoint_left.mpr (fun q hq hq' => hjj' ?_)
    exact D.f₀.label_unique H.f₀good.disj (hG₁nat q hq.1.2).2
      ⟨H.f₀good.BA j hq.1.1.1, hq.1.1.2⟩ ⟨H.f₀good.BA j' hq'.1.1.1, hq'.1.1.2⟩
  have hΩsub : ∀ j ∈ S, Eℓ j ⊆ Ω := fun j _ q hq => ⟨hq.1.2, hq.2⟩
  have hcap : ∀ w W' : ℝ, D.a₀ ≤ W' → D.ρs (Ω ∩ {q | x3 D.b q.1 q.2 ∈ Icc w (w + W')}) ≤
      ENNReal.ofReal (Ccap * W' ^ D.d) :=
    cell_window_cap D H hr1 hr2 hHx hs₀ hs₀R hd0 cellp Ω (fun q hq => hq.2)
      (fun q hq => (hG₁nat q hq.1).1)
  have key := crossing_point D.ρs S Eℓ (fun j => D.f₀.fitVal j p.2 (x1 D.b p.1 p.2) (x2 D.b p.1 p.2))
    Es Ω (fun q => x2 D.b q.1 q.2) (fun q => x3 D.b q.1 q.2) A0 A1 A2
    hh hHx hc hG'0 hEa0 hEb0 hMlo hd0 hd1 ha₀ hθ₁ hCcap hθ1 hEsy hEslab hlablev hEslaw hglip
    hmass hcube hdense hmeasEℓ hdisj hΩsub hcap
  have hyr : y ∈ Icc (z - 3 * Hx) (z + 4 * Hx) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hyr' : y' ∈ Icc (z - 3 * Hx) (z + 4 * Hx) := ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  have hk := key y hyr y' hyr'
  rw [eval_eq_quad _ hdeg, eval_eq_quad _ hdeg]
  have hc2 : ycoef (D.Ly.G i) 2 t = A2 := ycoef_two_const _ hdeg t p.2
  have hcard : ((D.Ly.G i).support.card : ℝ) ≤ 9 := by
    have := Submission.Lib.K4ChartLifting.card_support_le (D := 2) (D.Ly.G i) hdeg
    exact_mod_cast this
  have hc1 : |ycoef (D.Ly.G i) 1 t - A1| ≤ 9 * B * (2 * h) := by
    refine (abs_ycoef_one_sub_le _ hdeg hcoef t p.2).trans ?_
    calc ((D.Ly.G i).support.card : ℝ) * B * |t - p.2| ≤ 9 * B * h := by
          gcongr
      _ ≤ 9 * B * (2 * h) := by linarith [mul_nonneg hRL0 hh.le]
  have e : ycoef (D.Ly.G i) 0 t + ycoef (D.Ly.G i) 1 t * y + ycoef (D.Ly.G i) 2 t * y ^ 2 -
      (ycoef (D.Ly.G i) 0 t + ycoef (D.Ly.G i) 1 t * y' + ycoef (D.Ly.G i) 2 t * y' ^ 2) =
      ((A0 + A1 * y + A2 * y ^ 2) - (A0 + A1 * y' + A2 * y' ^ 2)) +
        (ycoef (D.Ly.G i) 1 t - A1) * (y - y') := by
    rw [hc2]; ring
  rw [e]
  calc _ ≤ |(A0 + A1 * y + A2 * y ^ 2) - (A0 + A1 * y' + A2 * y' ^ 2)| +
        |(ycoef (D.Ly.G i) 1 t - A1) * (y - y')| := abs_add_le _ _
    _ ≤ 14 * crossB D.d ((Ea + Eb + G' * h) / D.a₀)
          (Ccap * (1 + 2 * Ea / D.a₀) ^ D.d * D.a₀ ^ D.d / θ₁)
          (Mlo / c * h / (Hx + 2 * h)) * D.a₀ / (Hx + 2 * h) * |y - y'| +
        9 * B * (2 * h) * |y - y'| := by
          refine add_le_add hk ?_
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
    _ = _ := by ring

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
