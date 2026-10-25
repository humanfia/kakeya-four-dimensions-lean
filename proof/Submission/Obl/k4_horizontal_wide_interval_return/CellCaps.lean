/- The coordinate and residual-window computations adapt o218/x0764,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/CellCaps.lean.
The native finite-cell integration is imported from the accepted
K4OutputReferenceMenus library. Separate geometric and affine coefficient
bounds ensure that fixed-power native coefficients affect only the mesh. -/
import Submission.Obl.k4_horizontal_wide_interval_return.CellLipschitz
import Submission.Obl.k4_horizontal_wide_interval_return.ScalarCell
import Submission.Lib.K4OutputReferenceMenus.WindowCaps

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set
open Submission.Lib.K4MovingMeshBoxes
open Submission.Lib.K4OutputReferenceMenus
open scoped ENNReal

namespace CellFrame

variable {F : CellFrame}

/-- Original finite joint caps transfer to one normalized scalar cell.
The fixed-power bound `Lbound` on the native affine fit enters only the
required mesh accuracy. The final cap depends on the geometric bound `H`. -/
theorem cell_residual_cap {α : Type*} [MeasurableSpace α]
    (lam : Measure (α × ℝ)) (b : α → Fin 6 → ℝ)
    {H Lbound σ ρ δ C d : ℝ} (weight : ℝ≥0∞)
    (hH : 1 ≤ H) (hLbound : 0 ≤ Lbound)
    (hq : 0 < F.q) (hg : 0 < F.g) (hg1 : F.g ≤ 1) (ha : 0 < F.a)
    (hσ : 0 < σ) (hσg : σ ≤ F.g) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hmesh₀ : 4 * H ^ 2 * δ ≤ F.q * σ)
    (hmesh₁ : 4 * H ^ 2 * δ ≤ F.q * F.g)
    (hmeshOffset : (3 * Lbound * (F.q * F.g) + 40 * F.a * H ^ 3) * δ ≤
      F.a * ρ * (F.q * F.g))
    (hc : ∀ i, |F.c i| ≤ H) (hC : ∀ i, |F.C i| ≤ H)
    (hL : ∀ i, |F.L i| ≤ Lbound) (hcapC : 0 ≤ C)
    (E : Set (α × ℝ))
    (hE : ∀ p ∈ E, p.2 ∈ Icc F.t₀ (F.t₀ + F.q) ∧
      |F.zZ p.2 (lineZ (b p.1) p.2)| ≤ H ∧
      |F.U p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2)| ≤ H)
    (q₀ : Fin 2 → ℤ) (j : ℤ)
    (hcap : ∀ c k, lam {p | baseMesh δ
        (![p.2, lineZ (b p.1) p.2, lineY (b p.1) p.2] : Fin 3 → ℝ) = c ∧
        ⌊lineX (b p.1) p.2 / (F.a * ρ)⌋ = k} ≤
      ENNReal.ofReal (C * δ ^ 3 * (F.a * ρ) ^ d) * weight) :
    lam (E ∩ {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
      ⌊F.cellSig (b p.1) p.2 / ρ⌋ = j}) ≤
      ENNReal.ofReal (3000 * C * H * F.q ^ 3 * F.g * σ ^ 2 * (F.a * ρ) ^ d) * weight := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHsq : 1 ≤ H ^ 2 := one_le_pow₀ hH
  have hqg : 0 < F.q * F.g := mul_pos hq hg
  have hqσ : 0 < F.q * σ := mul_pos hq hσ
  have hδqg : δ ≤ F.q * F.g := by nlinarith
  have hδradius : δ ≤ F.q * σ / 2 := by nlinarith
  let point : α × ℝ → Fin 3 → ℝ :=
    fun p => ![p.2, lineZ (b p.1) p.2, lineY (b p.1) p.2]
  let offset : (Fin 3 → ℝ) → ℝ := fun y =>
    F.fit (y 0) (y 1) (y 2) + F.a * F.Pnc (y 0) (y 1) (y 2) + F.a * ρ * j
  let tc := F.t₀ + F.q * σ * ((q₀ 0 : ℝ) + 1 / 2)
  let pc := F.c 0 + F.q * σ * ((q₀ 1 : ℝ) + 1 / 2)
  let center : Fin 2 → ℝ := ![pc, F.c 2 + F.c 4 * pc]
  let velocity : Fin 2 → ℝ := ![F.c 1, F.c 3 + F.c 4 * F.c 1]
  let width : Fin 2 → ℝ := ![F.q * σ / 2, 2 * H * F.q * F.g]
  have hv : ∀ i, |velocity i| ≤ 2 * H ^ 2 := by
    intro i
    fin_cases i
    · exact (hc 1).trans (by nlinarith)
    · change |F.c 3 + F.c 4 * F.c 1| ≤ 2 * H ^ 2
      calc _ ≤ |F.c 3| + |F.c 4| * |F.c 1| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ H + H * H := by gcongr <;> exact hc _
        _ ≤ 2 * H ^ 2 := by nlinarith
  have hdw : ∀ i, δ ≤ width i := by
    intro i
    fin_cases i
    · exact hδradius
    · change δ ≤ 2 * H * F.q * F.g
      nlinarith
  have hmove : ∀ i, (2 * H ^ 2) * δ ≤ width i := by
    intro i
    fin_cases i
    · change 2 * H ^ 2 * δ ≤ F.q * σ / 2
      linarith
    · change 2 * H ^ 2 * δ ≤ 2 * H * F.q * F.g
      nlinarith
  have hoff : ∀ p ∈ E ∩ {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
      ⌊F.cellSig (b p.1) p.2 / ρ⌋ = j}, ∀ y : Fin 3 → ℝ,
      (∀ i, |point p i - y i| ≤ δ) → |offset (point p) - offset y| ≤ F.a * ρ := by
    rintro p ⟨hp, _⟩ y hy
    obtain ⟨hpt, hzZ, hU⟩ := hE p hp
    have hzt : F.zt p.2 ∈ Icc (0 : ℝ) 1 := by
      exact ⟨div_nonneg (by linarith [hpt.1]) hq.le,
        (div_le_one hq).mpr (by linarith [hpt.2])⟩
    have h0 : |p.2 - y 0| ≤ δ := hy 0
    have h1 : |lineZ (b p.1) p.2 - y 1| ≤ δ := hy 1
    have h2 : |lineY (b p.1) p.2 - y 2| ≤ δ := hy 2
    have hfit := fit_sub_le hL h0 h1 h2
    have hP := Pnc_sub_le hH hq hg hg1 hδ.le hδqg hc hC hzt hzZ hU h0 h1 h2
    have heq : offset (point p) - offset y =
        (F.fit p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2) - F.fit (y 0) (y 1) (y 2)) +
        F.a * (F.Pnc p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2) - F.Pnc (y 0) (y 1) (y 2)) := by
      simp only [offset, point, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring
    rw [heq]
    calc _ ≤ 3 * Lbound * δ + F.a * (40 * H ^ 3 * δ / (F.q * F.g)) := by
          refine (abs_add_le _ _).trans (add_le_add hfit ?_)
          rw [abs_mul, abs_of_pos ha]
          exact mul_le_mul_of_nonneg_left hP ha.le
      _ = ((3 * Lbound * (F.q * F.g) + 40 * F.a * H ^ 3) * δ) / (F.q * F.g) := by
          field_simp
      _ ≤ F.a * ρ := (div_le_iff₀ hqg).mpr hmeshOffset
  have hcontain : ∀ p ∈ E ∩ {p | F.cellCode σ (b p.1) p.2 = q₀ ∧
      ⌊F.cellSig (b p.1) p.2 / ρ⌋ = j},
      point p ∈ movingBox tc (F.q * σ / 2) center velocity width ∧
        offset (point p) ≤ lineX (b p.1) p.2 ∧
        lineX (b p.1) p.2 ≤ offset (point p) + F.a * ρ := by
    rintro p ⟨hp, hcode, hbin⟩
    obtain ⟨hpt, hzZ, hU⟩ := hE p hp
    have hc0 : ⌊F.zt p.2 / σ⌋ = q₀ 0 := by
      have := congrFun hcode 0; simpa [cellCode] using this
    have hc1 : ⌊F.zZ p.2 (lineZ (b p.1) p.2) / σ⌋ = q₀ 1 := by
      have := congrFun hcode 1; simpa [cellCode] using this
    have htlo := (le_div_iff₀ hσ).mp (Int.floor_le (F.zt p.2 / σ))
    have hthi := (div_lt_iff₀ hσ).mp (Int.lt_floor_add_one (F.zt p.2 / σ))
    rw [hc0] at htlo hthi
    have hZlo := (le_div_iff₀ hσ).mp
      (Int.floor_le (F.zZ p.2 (lineZ (b p.1) p.2) / σ))
    have hZhi := (div_lt_iff₀ hσ).mp
      (Int.lt_floor_add_one (F.zZ p.2 (lineZ (b p.1) p.2) / σ))
    rw [hc1] at hZlo hZhi
    have htime : |p.2 - tc| ≤ F.q * σ / 2 := by
      unfold zt at htlo hthi
      have h1 := (le_div_iff₀ hq).mp htlo
      have h2 := (div_lt_iff₀ hq).mp hthi
      dsimp only [tc]
      rw [abs_le]
      constructor <;> nlinarith
    have hZ : |lineZ (b p.1) p.2 - (pc + p.2 * F.c 1)| ≤ F.q * σ / 2 := by
      unfold zZ at hZlo hZhi
      have h1 := (le_div_iff₀ hq).mp hZlo
      have h2 := (div_lt_iff₀ hq).mp hZhi
      dsimp only [pc]
      rw [abs_le]
      constructor <;> nlinarith
    refine ⟨⟨htime, ?_⟩, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hZ
      · change |lineY (b p.1) p.2 -
          ((F.c 2 + F.c 4 * pc) + p.2 * (F.c 3 + F.c 4 * F.c 1))| ≤
            2 * H * F.q * F.g
        have heq : lineY (b p.1) p.2 -
            ((F.c 2 + F.c 4 * pc) + p.2 * (F.c 3 + F.c 4 * F.c 1)) =
            F.q * F.g * F.U p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2) +
              F.c 4 * (lineZ (b p.1) p.2 - (pc + p.2 * F.c 1)) := by
          unfold U
          field_simp
          ring
        rw [heq]
        calc _ ≤ F.q * F.g * H + H * (F.q * σ / 2) := by
              refine (abs_add_le _ _).trans ?_
              simp only [abs_mul, abs_of_pos hq, abs_of_pos hg]
              exact add_le_add (mul_le_mul_of_nonneg_left hU hqg.le)
                (mul_le_mul (hc 4) hZ (abs_nonneg _) hH0)
          _ ≤ 2 * H * F.q * F.g := by
              nlinarith only [mul_le_mul_of_nonneg_left hσg (mul_nonneg hH0 hq.le),
                mul_nonneg hH0 hqg.le]
    · have hlo := (le_div_iff₀ hρ).mp (Int.floor_le (F.cellSig (b p.1) p.2 / ρ))
      rw [hbin] at hlo
      simp only [cellSig, sig, resid] at hlo
      have h' : ((j : ℝ) * ρ + F.Pnc p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2)) * F.a ≤
          lineX (b p.1) p.2 - F.fit p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2) := by
        rw [← le_div_iff₀ ha]
        linarith
      dsimp only [offset, point]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      nlinarith only [h']
    · have hhi := (div_lt_iff₀ hρ).mp (Int.lt_floor_add_one (F.cellSig (b p.1) p.2 / ρ))
      rw [hbin] at hhi
      simp only [cellSig, sig, resid] at hhi
      have h' : lineX (b p.1) p.2 - F.fit p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2) <
          (((j : ℝ) + 1) * ρ + F.Pnc p.2 (lineZ (b p.1) p.2) (lineY (b p.1) p.2)) * F.a := by
        rw [← div_lt_iff₀ ha]
        linarith
      dsimp only [offset, point]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      nlinarith only [h']
  have hresult := moving_box_signal_cap lam point (fun p => lineX (b p.1) p.2)
    offset (E ∩ {p | F.cellCode σ (b p.1) p.2 = q₀ ∧ ⌊F.cellSig (b p.1) p.2 / ρ⌋ = j})
    hδ (mul_pos ha hρ) (mul_nonneg ha.le hρ.le) le_rfl hδradius (by positivity)
    hcapC tc center velocity width hv hdw hmove hoff hcontain weight hcap
  convert hresult using 1 <;> congr 2 <;> simp only [width, Matrix.cons_val] <;> ring

end CellFrame

end Submission.Obl.k4_horizontal_wide_interval_return
