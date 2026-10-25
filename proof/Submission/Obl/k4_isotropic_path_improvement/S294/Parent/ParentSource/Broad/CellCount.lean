-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.CellCount, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/CellCount.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/CellCount.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.ObservationGrid
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.ObservationCell
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.ChartGraph

/-!
# Observation cells met by one packet

The incidences of a frozen chart `ch` (one packet, block length `h = 2^{-T}`) meet few
observation cells of the grid `cellIdx p Bv a`:

* their base points lie within `κ² h` of the centre line `c + t u` over a time interval of
  length `h` (the packet frame), so they meet at most `(h/p + 2)(2‖u‖ + 2κ²h/p + 2)²` base cubes
  of side `p` (`exists_cube_finset_of_chart`);
* in one base cube, incidences with one sign of `∂₃R` have hidden coordinates within
  `6κ²δ/Bv` of each other, once the cube is small against the crude Lipschitz constants of `R`
  and `∂₃R`: the chart test is `κδ`-small, `|∂₃R| ≥ Bv/κ`, and the exact two-point identity
  along the hidden direction converts values into hidden distances.  So they meet at most
  `24κ²δ/a + 4` hidden bins of the observation `obs Bv a` (`exists_bin_finset_of_chart`).

Together: at most `(h/p + 2)(2‖u‖ + 2κ²h/p + 2)² (24κ²δ/a + 4)` observation cells
(`exists_cell_finset_of_chart`).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

/-- The crude box Lipschitz constant of `abs_eval_sub_eval_le_box`. -/
def lipBox {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) (Bx : ℝ) : ℝ :=
  Q.totalDegree * coeffL1 Q * Bx ^ Q.totalDegree

lemma lipBox_nonneg {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) {Bx : ℝ} (hBx : 0 ≤ Bx) :
    0 ≤ lipBox Q Bx := by
  unfold lipBox coeffL1; positivity

lemma xp_eq_x : xp = x := rfl

/-! ### Counting integers -/

lemma toNat_cast_le {z : ℤ} {b : ℝ} (hb : 0 ≤ b) (hz : (z : ℝ) ≤ b) :
    ((z.toNat : ℕ) : ℝ) ≤ b := by
  rcases le_or_gt 0 z with h | h
  · have h' : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
    have : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast h'
    rw [this]; exact hz
  · rw [Int.toNat_of_nonpos h.le]; simpa using hb

lemma card_Icc_floor_le {α ℓ p : ℝ} (hp : 0 < p) (hℓ : 0 ≤ ℓ) :
    ((Finset.Icc ⌊α / p⌋ ⌊(α + ℓ) / p⌋).card : ℝ) ≤ ℓ / p + 2 := by
  rw [Int.card_Icc]
  apply toNat_cast_le (by positivity)
  push_cast
  have h1 := Int.floor_le ((α + ℓ) / p)
  have h2 := Int.sub_one_lt_floor (α / p)
  have h3 : (α + ℓ) / p = α / p + ℓ / p := by ring
  linarith

/-- Values within `ℓ` of each other have at most `2cℓ + 2` integer parts after scaling by `c`. -/
lemma exists_floor_finset_of_close {β : Type*} (X : Set β) (g : β → ℝ) {c ℓ : ℝ} (hc : 0 ≤ c)
    (hℓ : 0 ≤ ℓ) (hclose : ∀ y ∈ X, ∀ y' ∈ X, |g y - g y'| ≤ ℓ) :
    ∃ S : Finset ℤ, (∀ y ∈ X, ⌊c * g y⌋ ∈ S) ∧ (S.card : ℝ) ≤ 2 * c * ℓ + 2 := by
  rcases X.eq_empty_or_nonempty with hX | ⟨y₀, hy₀⟩
  · refine ⟨∅, fun y hy => by simp [hX] at hy, by simp; positivity⟩
  · refine ⟨Finset.Icc ⌊c * g y₀ - c * ℓ⌋ ⌊c * g y₀ + c * ℓ⌋, ?_, ?_⟩
    · intro y hy
      obtain ⟨h1, h2⟩ := abs_le.mp (hclose y hy y₀ hy₀)
      rw [Finset.mem_Icc]
      constructor
      · apply Int.floor_mono
        nlinarith [mul_nonneg hc (show 0 ≤ g y - g y₀ + ℓ by linarith)]
      · apply Int.floor_mono
        nlinarith [mul_nonneg hc (show 0 ≤ ℓ - (g y - g y₀) by linarith)]
    · rw [Int.card_Icc]
      apply toNat_cast_le (by positivity)
      push_cast
      have h1 := Int.floor_le (c * g y₀ + c * ℓ)
      have h2 := Int.sub_one_lt_floor (c * g y₀ - c * ℓ)
      linarith

/-! ### The packet frame -/

/-- The frame of a chart controls each coordinate of the spatial error.  This is the
coordinatewise form of `Native.physical_error_le_of_frame` on branch x0943 of this tree
(itself adapted there from o204 x0749 and o116 x0389); written out here. -/
lemma frame_error_coord_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) {S κ : ℝ}
    (hS : (∑ i, ∑ j, |Q i j|) ≤ S) (hκ : 0 ≤ κ) {v : EuclideanSpace ℝ (Fin 2)}
    (hfit : ‖Matrix.toEuclideanLin Q⁻¹ v‖ ≤ κ) (e : Fin 2) : |v e| ≤ S * κ := by
  have hid : Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ v) = v := by
    have hmul := congrArg (fun L => L v) (Matrix.toLpLin_mul 2 2 2 Q Q⁻¹)
    rw [Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ), Matrix.toLpLin_one] at hmul
    exact hmul.symm
  set w := Matrix.toEuclideanLin Q⁻¹ v with hw
  rw [← hid]
  change |∑ j, Q e j * w j| ≤ S * κ
  calc |∑ j, Q e j * w j| ≤ ∑ j, |Q e j| * ‖w‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le w j) (abs_nonneg _)
    _ = (∑ j, |Q e j|) * ‖w‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ j, |Q i j|) * κ := by
        apply mul_le_mul _ hfit (norm_nonneg _)
          (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, |Q i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ e)
    _ ≤ S * κ := mul_le_mul_of_nonneg_right hS hκ

/-- Coordinates of trajectories of a chart within the unit time interval. -/
lemma abs_x_le {l : Ln} {t M : ℝ} (hM : 1 ≤ M) (hl : ∀ e, |l.2 e| ≤ M)
    (ht : t ∈ Icc (0:ℝ) 1) (i : Fin 4) : |x l t i| ≤ 2 * M := by
  have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hlin : ∀ a b : Fin 6, |l.2 a + t * l.2 b| ≤ 2 * M := by
    intro a b
    calc |l.2 a + t * l.2 b| ≤ |l.2 a| + |t| * |l.2 b| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ M + 1 * M := by
          gcongr
          · exact hl a
          · exact hl b
      _ = 2 * M := by ring
  fin_cases i
  · simp only [x]; simp; linarith
  · simp only [x]; simpa using hlin 0 3
  · simp only [x]; simpa using hlin 1 4
  · simp only [x]; simpa using hlin 2 5

/-! ### Hidden coordinates in one base cube -/

/-- The exact two-point identity of a quadratic along the hidden direction. -/
lemma hidden_two_point {R : MvPolynomial (Fin 4) ℝ} (hR : R.totalDegree ≤ 2)
    (z z' : Fin 4 → ℝ) (hzz : ∀ i : Fin 4, i ≠ 3 → z i = z' i) :
    MvPolynomial.eval z R - MvPolynomial.eval z' R =
      (z 3 - z' 3) * (MvPolynomial.eval z (pderiv 3 R) +
        MvPolynomial.eval z' (pderiv 3 R)) / 2 := by
  set q := Submission.Obl.k4_polynomial_variation_tube.lineRestrict R (hiddenBase z') hiddenDir
    with hqdef
  have hqeval : ∀ s, q.eval s = MvPolynomial.eval (Function.update z' 3 s) R := by
    intro s
    rw [hqdef, Submission.Obl.k4_polynomial_variation_tube.eval_lineRestrict, hidden_line_eq]
  have hqdeg : q.natDegree ≤ 2 :=
    (Submission.Obl.k4_polynomial_variation_tube.natDegree_lineRestrict_le _ _ _).trans hR
  have hqder : ∀ s, q.derivative.eval s =
      MvPolynomial.eval (Function.update z' 3 s) (pderiv 3 R) := by
    intro s
    set e : Fin 4 → ℝ := Pi.single (3 : Fin 4) (1 : ℝ) with he
    have hcurve : ∀ i, HasDerivAt (fun u => Function.update z' 3 u i) (e i) s := by
      intro i
      by_cases hi : i = 3
      · subst hi; simpa [he] using hasDerivAt_id' s
      · simpa [Function.update_of_ne hi, he, Pi.single_apply, hi] using hasDerivAt_const s (z' i)
    have h2 := Submission.Lib.K4CubicTests.hasDerivAt_eval_finite_polynomial_curve R
      (fun u => Function.update z' 3 u) e s hcurve
    have h1 := q.hasDerivAt s
    have heq : (fun u => q.eval u) = fun u => MvPolynomial.eval (Function.update z' 3 u) R := by
      funext u; exact hqeval u
    rw [heq] at h1
    rw [h1.unique h2]
    simp [he, Pi.single_apply, Finset.sum_ite_eq']
  have hz : z = Function.update z' 3 (z 3) := by
    funext i
    by_cases hi : i = 3
    · subst hi; simp
    · simp [Function.update_of_ne hi, hzz i hi]
  have hz' : z' = Function.update z' 3 (z' 3) := by simp
  have key := quadratic_two_point q hqdeg (z 3) (z' 3)
  rw [hqeval, hqeval, ← hz, ← hz', hqder, hqder, ← hz, ← hz'] at key
  exact key

/-- **Hidden coordinates in a thin base cell.**  Two points whose base coordinates are within
`ϱ` in `ℓ¹`, where a quadratic is `V`-small and its hidden derivative has one sign and modulus
at least `D`, have hidden coordinates within `2 (2V + Lip ϱ) / D`, provided the hidden
derivative moves by at most `D` across the cell. -/
lemma hidden_close_of_cell {R : MvPolynomial (Fin 4) ℝ} (hR : R.totalDegree ≤ 2)
    {Bx V D ϱ : ℝ} (hBx : 1 ≤ Bx) (w w' : Fin 4 → ℝ) (hbox : ∀ i, |w i| ≤ Bx)
    (hbox' : ∀ i, |w' i| ≤ Bx)
    (hbase : |w 0 - w' 0| + |w 1 - w' 1| + |w 2 - w' 2| ≤ ϱ)
    (hval : |MvPolynomial.eval w R| ≤ V) (hval' : |MvPolynomial.eval w' R| ≤ V)
    (hder : D ≤ |MvPolynomial.eval w (pderiv 3 R)|)
    (hder' : D ≤ |MvPolynomial.eval w' (pderiv 3 R)|)
    (hsign : 0 ≤ MvPolynomial.eval w (pderiv 3 R) * MvPolynomial.eval w' (pderiv 3 R))
    (hsmall : lipBox (pderiv 3 R) Bx * ϱ ≤ D) :
    |w 3 - w' 3| * D ≤ 2 * (2 * V + lipBox R Bx * ϱ) := by
  have hϱ : 0 ≤ ϱ := le_trans (by positivity) hbase
  have hV : 0 ≤ V := le_trans (abs_nonneg _) hval
  have hL : 0 ≤ lipBox R Bx := lipBox_nonneg R (by linarith)
  have hLD : 0 ≤ lipBox (pderiv 3 R) Bx := lipBox_nonneg _ (by linarith)
  rcases le_or_gt D 0 with hD | hD
  · have : |w 3 - w' 3| * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hD
    have : 0 ≤ 2 * (2 * V + lipBox R Bx * ϱ) := by positivity
    linarith
  set m := mixPoint w w' with hm
  have hboxm : ∀ i, |m i| ≤ Bx := by
    intro i
    by_cases hi : i = 3
    · subst hi; rw [hm, mixPoint_hidden]; exact hbox 3
    · rw [hm, mixPoint_base w w' i hi]; exact hbox' i
  -- base move
  have h1 : |MvPolynomial.eval w R - MvPolynomial.eval m R| ≤ lipBox R Bx * ϱ := by
    have := abs_eval_sub_eval_le_box R hBx w m hbox hboxm
    rw [sum_abs_sub_mixPoint] at this
    exact this.trans (mul_le_mul_of_nonneg_left hbase hL)
  have h2 : |MvPolynomial.eval w (pderiv 3 R) - MvPolynomial.eval m (pderiv 3 R)| ≤ D := by
    have := abs_eval_sub_eval_le_box (pderiv 3 R) hBx w m hbox hboxm
    rw [sum_abs_sub_mixPoint] at this
    exact (this.trans (mul_le_mul_of_nonneg_left hbase hLD)).trans hsmall
  -- hidden move: the two-point identity
  have hmw' : ∀ i : Fin 4, i ≠ 3 → m i = w' i := fun i hi => mixPoint_base w w' i hi
  have key := hidden_two_point hR m w' hmw'
  have hm3 : m 3 = w 3 := mixPoint_hidden w w'
  rw [hm3] at key
  set a := MvPolynomial.eval w (pderiv 3 R) with ha
  set a' := MvPolynomial.eval w' (pderiv 3 R) with ha'
  set b := MvPolynomial.eval m (pderiv 3 R) with hb
  -- one sign: `|a + a'| = |a| + |a'| ≥ 2D`
  have hsum2 : 2 * D ≤ |a + a'| := by
    rcases lt_trichotomy a 0 with h | h | h
    · have ha'0 : a' ≤ 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      rw [abs_of_neg h] at hder
      rw [abs_of_nonpos ha'0] at hder'
      rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [h, abs_zero] at hder; linarith
    · have ha'0 : 0 ≤ a' := by
        by_contra hc
        push Not at hc
        nlinarith
      rw [abs_of_pos h] at hder
      rw [abs_of_nonneg ha'0] at hder'
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hsum : D ≤ |b + a'| := by
    have := abs_sub_abs_le_abs_sub (a + a') (b + a')
    have h3 : (a + a') - (b + a') = a - b := by ring
    rw [h3] at this
    linarith
  have hkey : (w 3 - w' 3) * (b + a') =
      2 * (MvPolynomial.eval m R - MvPolynomial.eval w' R) := by
    rw [key]; ring
  calc |w 3 - w' 3| * D ≤ |w 3 - w' 3| * |b + a'| :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = 2 * |MvPolynomial.eval m R - MvPolynomial.eval w' R| := by
        rw [← abs_mul, hkey, abs_mul, abs_two]
    _ ≤ 2 * (|MvPolynomial.eval w R - MvPolynomial.eval m R| + |MvPolynomial.eval w R| +
          |MvPolynomial.eval w' R|) := by
        gcongr
        calc |MvPolynomial.eval m R - MvPolynomial.eval w' R|
            = |-(MvPolynomial.eval w R - MvPolynomial.eval m R) + MvPolynomial.eval w R -
                MvPolynomial.eval w' R| := by ring_nf
          _ ≤ |-(MvPolynomial.eval w R - MvPolynomial.eval m R) + MvPolynomial.eval w R| +
                |MvPolynomial.eval w' R| := abs_sub _ _
          _ ≤ _ := by
              gcongr
              exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ 2 * (lipBox R Bx * ϱ + V + V) := by gcongr
    _ = 2 * (2 * V + lipBox R Bx * ϱ) := by ring

/-! ### Cells met by a chart -/

/-- **Base cubes met by a packet.** -/
theorem exists_cube_finset_of_chart {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T jj : ℕ} {rr Bv : ℝ}
    {Evs : Set Ev} {c u : P2} {Qm : Matrix (Fin 2) (Fin 2) ℝ} {R : Po} {A : Set Ln}
    {F : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ T (jj : ℝ) rr Bv Evs c u Qm R A F ex) (hκ : 0 ≤ κ)
    {p : ℝ} (hp : 0 < p) :
    ∃ S : Finset (Fin 3 → ℤ), (∀ q ∈ F, cubeIdx p q ∈ S) ∧
      (S.card : ℝ) ≤ (((2:ℝ) ^ T)⁻¹ / p + 2) *
        (2 * ‖u‖ + 2 * κ ^ 2 * ((2:ℝ) ^ T)⁻¹ / p + 2) ^ 2 := by
  obtain ⟨hdet, _, _, hsize, _, _, _, _, _, hA, hF, _⟩ := hch
  set h : ℝ := ((2:ℝ) ^ T)⁻¹ with hh
  have hh0 : 0 < h := by positivity
  set t₀ : ℝ := (jj : ℝ) / (2:ℝ) ^ T with ht₀
  have hblock : ((jj : ℝ) + 1) / (2:ℝ) ^ T = t₀ + h := by rw [ht₀, hh]; ring
  set Er : ℝ := κ ^ 2 * h with hEr
  have hEr0 : 0 ≤ Er := by positivity
  set lo : Fin 2 → ℤ → ℝ := fun e n₀ => c e + (n₀ : ℝ) * p * u e - |u e| * p - Er with hlo
  set Y : Fin 2 → ℤ → Finset ℤ := fun e n₀ =>
    Finset.Icc ⌊lo e n₀ / p⌋ ⌊(lo e n₀ + (2 * |u e| * p + 2 * Er)) / p⌋ with hY
  set Tset : Finset ℤ := Finset.Icc ⌊t₀ / p⌋ ⌊(t₀ + h) / p⌋ with hTset
  refine ⟨Tset.biUnion (fun n₀ => ((Y 0 n₀) ×ˢ (Y 1 n₀)).image
    (fun ab => ![n₀, ab.1, ab.2])), ?_, ?_⟩
  · intro q hq
    obtain ⟨-, hqA, hqt, -⟩ := hF q hq
    have hfit := ((hA q.1 hqA).2.2 q.2 hqt).1
    have hcoord : ∀ e : Fin 2, |(y q.1 q.2 - c - q.2 • u) e| ≤ Er := by
      intro e
      have := frame_error_coord_le hdet hsize hκ hfit e
      calc _ ≤ κ / (2:ℝ) ^ T * κ := this
        _ = Er := by rw [hEr, hh]; ring
    rw [hblock] at hqt
    set n₀ := ⌊q.2 / p⌋ with hn₀
    have hn₀T : n₀ ∈ Tset := Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right hqt.1 hp.le),
        Int.floor_mono (div_le_div_of_nonneg_right hqt.2 hp.le)⟩
    have hlo' : (n₀ : ℝ) * p ≤ q.2 := by
      have := Int.floor_le (q.2 / p); rwa [le_div_iff₀ hp] at this
    have hhi' : q.2 < ((n₀ : ℝ) + 1) * p := by
      have := Int.lt_floor_add_one (q.2 / p); rwa [div_lt_iff₀ hp] at this
    have hyidx : ∀ e : Fin 2, ⌊(y q.1 q.2) e / p⌋ ∈ Y e n₀ := by
      intro e
      have h1 := abs_le.mp (hcoord e)
      have hye : (y q.1 q.2 - c - q.2 • u) e = (y q.1 q.2) e - c e - q.2 * u e := by simp
      rw [hye] at h1
      have hu : |(q.2 - n₀ * p) * u e| ≤ |u e| * p := by
        rw [abs_mul, mul_comm]
        have : |q.2 - n₀ * p| ≤ p := by rw [abs_of_nonneg (by linarith)]; linarith
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      have hu' := abs_le.mp hu
      rw [Finset.mem_Icc]
      constructor
      · apply Int.floor_mono
        apply div_le_div_of_nonneg_right _ hp.le
        show c e + (n₀ : ℝ) * p * u e - |u e| * p - Er ≤ (y q.1 q.2) e
        nlinarith [h1.1, hu'.1]
      · apply Int.floor_mono
        apply div_le_div_of_nonneg_right _ hp.le
        show (y q.1 q.2) e ≤ c e + (n₀ : ℝ) * p * u e - |u e| * p - Er + (2 * |u e| * p + 2 * Er)
        nlinarith [h1.2, hu'.2]
    have hcube : cubeIdx p q = ![n₀, ⌊(y q.1 q.2) 0 / p⌋, ⌊(y q.1 q.2) 1 / p⌋] := by
      funext e
      fin_cases e <;> simp [cubeIdx, basePoint, y, x, hn₀]
    rw [hcube]
    exact Finset.mem_biUnion.mpr ⟨n₀, hn₀T, Finset.mem_image.mpr
      ⟨(⌊(y q.1 q.2) 0 / p⌋, ⌊(y q.1 q.2) 1 / p⌋),
        Finset.mem_product.mpr ⟨hyidx 0, hyidx 1⟩, rfl⟩⟩
  · have hYc : ∀ e n₀, ((Y e n₀).card : ℝ) ≤ 2 * ‖u‖ + 2 * κ ^ 2 * h / p + 2 := by
      intro e n₀
      have := card_Icc_floor_le (α := lo e n₀) hp
        (show 0 ≤ 2 * |u e| * p + 2 * Er by positivity)
      refine this.trans ?_
      have hue : |u e| ≤ ‖u‖ := PiLp.norm_apply_le u e
      have : (2 * |u e| * p + 2 * Er) / p = 2 * |u e| + 2 * κ ^ 2 * h / p := by
        rw [hEr]; field_simp
      rw [this]; linarith
    have hTc : (Tset.card : ℝ) ≤ h / p + 2 := card_Icc_floor_le hp hh0.le
    have hK : 0 ≤ 2 * ‖u‖ + 2 * κ ^ 2 * h / p + 2 := by positivity
    calc ((Tset.biUnion (fun n₀ => ((Y 0 n₀) ×ˢ (Y 1 n₀)).image
          (fun ab => ![n₀, ab.1, ab.2]))).card : ℝ)
        ≤ ∑ n₀ ∈ Tset, ((((Y 0 n₀) ×ˢ (Y 1 n₀)).image
            (fun ab => ![n₀, ab.1, ab.2])).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ n₀ ∈ Tset, (((Y 0 n₀).card : ℝ) * (Y 1 n₀).card) := by
          apply Finset.sum_le_sum
          intro n₀ _
          have := Finset.card_image_le (s := (Y 0 n₀) ×ˢ (Y 1 n₀))
            (f := fun ab => ![n₀, ab.1, ab.2])
          rw [Finset.card_product] at this
          exact_mod_cast this
      _ ≤ ∑ _n₀ ∈ Tset, (2 * ‖u‖ + 2 * κ ^ 2 * h / p + 2) ^ 2 := by
          apply Finset.sum_le_sum
          intro n₀ _
          rw [sq]
          exact mul_le_mul (hYc 0 n₀) (hYc 1 n₀) (by positivity) hK
      _ = (Tset.card : ℝ) * (2 * ‖u‖ + 2 * κ ^ 2 * h / p + 2) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (h / p + 2) * (2 * ‖u‖ + 2 * κ ^ 2 * h / p + 2) ^ 2 := by gcongr

/-- **Hidden bins met by a packet in one base cube.** -/
theorem exists_bin_finset_of_chart {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T jj : ℕ} {rr Bv : ℝ}
    {Evs : Set Ev} {c u : P2} {Qm : Matrix (Fin 2) (Fin 2) ℝ} {R : Po} {A : Set Ln}
    {F : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ T (jj : ℝ) rr Bv Evs c u Qm R A F ex) (hjj : jj < 2 ^ T)
    (hN : 1 ≤ Nk) (hκ : 0 < κ) (hBv : 0 < Bv) {p a : ℝ} (hp : 0 < p) (ha : 0 < a)
    (hpR : 3 * lipBox R (2 * Nk ^ Mp) * p ≤ κ * δ Nk rr)
    (hpD : 3 * lipBox (pderiv 3 R) (2 * Nk ^ Mp) * p ≤ Bv / κ) (n : Fin 3 → ℤ) :
    ∃ S : Finset ℤ, (∀ q ∈ F, cubeIdx p q = n → binIdx Bv a q ∈ S) ∧
      (S.card : ℝ) ≤ 24 * κ ^ 2 * δ Nk rr / a + 4 := by
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hA, hF, _⟩ := hch
  set Bx : ℝ := 2 * Nk ^ Mp with hBx
  have hNM : 1 ≤ Nk ^ Mp := one_le_pow₀ hN
  have hBx1 : 1 ≤ Bx := by rw [hBx]; linarith
  have hδ := δ_pos Nk rr
  have hunit : ∀ q ∈ F, q.2 ∈ Icc (0:ℝ) 1 := by
    intro q hq
    obtain ⟨-, -, hqt, -⟩ := hF q hq
    have h2T : (0:ℝ) < (2:ℝ) ^ T := by positivity
    have hj : ((jj : ℝ) + 1) ≤ (2:ℝ) ^ T := by exact_mod_cast hjj
    refine ⟨le_trans (by positivity) hqt.1, hqt.2.trans ?_⟩
    rw [div_le_one h2T]; exact hj
  have hbox : ∀ q ∈ F, ∀ i, |x q.1 q.2 i| ≤ Bx := by
    intro q hq i
    obtain ⟨-, hqA, -, -⟩ := hF q hq
    exact abs_x_le hNM (hA q.1 hqA).2.1 (hunit q hq) i
  have hval : ∀ q ∈ F, |MvPolynomial.eval (x q.1 q.2) R| ≤ κ * δ Nk rr := by
    intro q hq
    obtain ⟨-, hqA, hqt, -⟩ := hF q hq
    exact ((hA q.1 hqA).2.2 q.2 hqt).2.1
  have hder : ∀ q ∈ F, Bv / κ ≤ |MvPolynomial.eval (x q.1 q.2) (pderiv 3 R)| := by
    intro q hq
    exact (hF q hq).2.2.2
  have hpair : ∀ q ∈ F, ∀ q' ∈ F, cubeIdx p q = cubeIdx p q' →
      0 ≤ MvPolynomial.eval (x q.1 q.2) (pderiv 3 R) *
        MvPolynomial.eval (x q'.1 q'.2) (pderiv 3 R) →
      |x q.1 q.2 3 - x q'.1 q'.2 3| ≤ 6 * κ ^ 2 * δ Nk rr / Bv := by
    intro q hq q' hq' hcube hsign
    have hbase : |x q.1 q.2 0 - x q'.1 q'.2 0| + |x q.1 q.2 1 - x q'.1 q'.2 1| +
        |x q.1 q.2 2 - x q'.1 q'.2 2| ≤ 3 * p := by
      have h0 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 0
      have h1 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 1
      have h2 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 2
      rw [basePoint_apply_zero, basePoint_apply_zero] at h0
      rw [basePoint_apply_one, basePoint_apply_one] at h1
      rw [basePoint_apply_two, basePoint_apply_two] at h2
      have hx0 : ∀ q : Ev, x q.1 q.2 0 = q.2 := fun q => by simp [x]
      rw [hx0, hx0]
      rw [xp_eq_x] at h1 h2
      linarith
    have hsmall : lipBox (pderiv 3 R) Bx * (3 * p) ≤ Bv / κ := by linarith [hpD]
    have hlip : lipBox R Bx * (3 * p) ≤ κ * δ Nk rr := by linarith [hpR]
    have hc := hidden_close_of_cell hdeg hBx1 (x q.1 q.2) (x q'.1 q'.2) (hbox q hq)
      (hbox q' hq') hbase (hval q hq) (hval q' hq') (hder q hq) (hder q' hq') hsign hsmall
    have h' : |x q.1 q.2 3 - x q'.1 q'.2 3| * (Bv / κ) ≤ 6 * κ * δ Nk rr := by linarith
    have hBk : 0 < Bv / κ := by positivity
    have heq : 6 * κ ^ 2 * δ Nk rr / Bv = (6 * κ * δ Nk rr) / (Bv / κ) := by
      field_simp
    rw [heq, le_div_iff₀ hBk]
    exact h'
  set g : Ev → ℝ := fun q => x q.1 q.2 3 with hg
  set Xp : Set Ev := {q | q ∈ F ∧ cubeIdx p q = n ∧
    0 < MvPolynomial.eval (x q.1 q.2) (pderiv 3 R)} with hXp
  set Xm : Set Ev := {q | q ∈ F ∧ cubeIdx p q = n ∧
    MvPolynomial.eval (x q.1 q.2) (pderiv 3 R) < 0} with hXm
  have hℓ : 0 ≤ 6 * κ ^ 2 * δ Nk rr / Bv := by positivity
  obtain ⟨Sp, hSp, hSpc⟩ := exists_floor_finset_of_close Xp g (c := Bv / a) (by positivity) hℓ
    (fun q hq q' hq' => hpair q hq.1 q' hq'.1 (hq.2.1.trans hq'.2.1.symm)
      (mul_nonneg hq.2.2.le hq'.2.2.le))
  obtain ⟨Sm, hSm, hSmc⟩ := exists_floor_finset_of_close Xm g (c := Bv / a) (by positivity) hℓ
    (fun q hq q' hq' => hpair q hq.1 q' hq'.1 (hq.2.1.trans hq'.2.1.symm)
      (mul_nonneg_of_nonpos_of_nonpos hq.2.2.le hq'.2.2.le))
  refine ⟨Sp ∪ Sm, ?_, ?_⟩
  · intro q hq hqn
    have hne : MvPolynomial.eval (x q.1 q.2) (pderiv 3 R) ≠ 0 := by
      intro h0
      have := hder q hq
      rw [h0, abs_zero] at this
      have : 0 < Bv / κ := by positivity
      linarith
    have hbin : binIdx Bv a q = ⌊Bv / a * g q⌋ := by
      simp only [binIdx, hg, xp_eq_x]
      congr 1
      ring
    rw [hbin]
    rcases lt_or_gt_of_ne hne with h | h
    · exact Finset.mem_union_right _ (hSm q ⟨hq, hqn, h⟩)
    · exact Finset.mem_union_left _ (hSp q ⟨hq, hqn, h⟩)
  · calc ((Sp ∪ Sm).card : ℝ) ≤ Sp.card + Sm.card := by
          exact_mod_cast Finset.card_union_le Sp Sm
      _ ≤ (2 * (Bv / a) * (6 * κ ^ 2 * δ Nk rr / Bv) + 2) +
          (2 * (Bv / a) * (6 * κ ^ 2 * δ Nk rr / Bv) + 2) := add_le_add hSpc hSmc
      _ = 24 * κ ^ 2 * δ Nk rr / a + 4 := by field_simp; ring

/-- **Observation cells met by a packet.** -/
theorem exists_cell_finset_of_chart {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T jj : ℕ} {rr Bv : ℝ}
    {Evs : Set Ev} {c u : P2} {Qm : Matrix (Fin 2) (Fin 2) ℝ} {R : Po} {A : Set Ln}
    {F : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ T (jj : ℝ) rr Bv Evs c u Qm R A F ex) (hjj : jj < 2 ^ T)
    (hN : 1 ≤ Nk) (hκ : 0 < κ) (hBv : 0 < Bv) {p a : ℝ} (hp : 0 < p) (ha : 0 < a)
    (hpR : 3 * lipBox R (2 * Nk ^ Mp) * p ≤ κ * δ Nk rr)
    (hpD : 3 * lipBox (pderiv 3 R) (2 * Nk ^ Mp) * p ≤ Bv / κ) :
    ∃ S : Finset ((Fin 3 → ℤ) × ℤ), (∀ q ∈ F, cellIdx p Bv a q ∈ S) ∧
      (S.card : ℝ) ≤ ((((2:ℝ) ^ T)⁻¹ / p + 2) *
        (2 * ‖u‖ + 2 * κ ^ 2 * ((2:ℝ) ^ T)⁻¹ / p + 2) ^ 2) *
          (24 * κ ^ 2 * δ Nk rr / a + 4) := by
  obtain ⟨Sc, hSc, hScc⟩ := exists_cube_finset_of_chart hch hκ.le hp
  have hbins := fun n => exists_bin_finset_of_chart hch hjj hN hκ hBv hp ha hpR hpD n
  choose Sb hSb hSbc using hbins
  refine ⟨Sc.biUnion (fun n => (Sb n).image (fun k => (n, k))), ?_, ?_⟩
  · intro q hq
    exact Finset.mem_biUnion.mpr ⟨cubeIdx p q, hSc q hq,
      Finset.mem_image.mpr ⟨binIdx Bv a q, hSb _ q hq rfl, rfl⟩⟩
  · have hKb : 0 ≤ 24 * κ ^ 2 * δ Nk rr / a + 4 := by
      have := δ_pos Nk rr
      positivity
    calc ((Sc.biUnion (fun n => (Sb n).image (fun k => (n, k)))).card : ℝ)
        ≤ ∑ n ∈ Sc, (((Sb n).image (fun k => (n, k))).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _n ∈ Sc, (24 * κ ^ 2 * δ Nk rr / a + 4) := by
          apply Finset.sum_le_sum
          intro n _
          refine le_trans ?_ (hSbc n)
          exact_mod_cast Finset.card_image_le
      _ = (Sc.card : ℝ) * (24 * κ ^ 2 * δ Nk rr / a + 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad
