import Submission.Obl.k4_scalar_grid_polynomial_qualification.RowPreparation
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Assembly

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory Filter
open Submission.Lib.K4CommonLocalChoice

def scalarPosition (p : ScalarIncidence) : Fin 3 → ℝ :=
  ![p.2, scalarY p.1 p.2, scalarX p.1 p.2]

theorem measurable_scalarPosition : Measurable scalarPosition := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp [scalarPosition, scalarY, scalarX] <;> fun_prop

noncomputable def powerWidth (N : ℝ) (J i : ℕ) : ℝ := N ^ (-((i : ℝ) / (J : ℝ)))

theorem powerWidth_ratio {N : ℝ} (hN : 0 < N) (J i : ℕ) :
    powerWidth N J i = N ^ ((1 : ℝ) / (J : ℝ)) * powerWidth N J (i + 1) := by
  rw [powerWidth, powerWidth, ← Real.rpow_add hN]
  congr 1
  push_cast
  ring

theorem powerWidth_last (N : ℝ) {J : ℕ} (hJ : 1 ≤ J) (C : ℕ) :
    powerWidth N J (C * J + 1 - 1) = N ^ (-(C : ℝ)) := by
  have hJne : (J : ℝ) ≠ 0 := by exact_mod_cast (by omega : J ≠ 0)
  simp only [Nat.add_sub_cancel, powerWidth, Nat.cast_mul, mul_div_cancel_right₀ _ hJne]

namespace ScalarData

/-- First common-local-choice step, derived directly from the original
frozen graph certificate, on every residual submeasure. The retained set is
a set of original fine physical codes, so conditional velocities within
each retained fine state are unchanged. -/
theorem graphData.original_row_selection {D : ScalarData}
    {E₀ E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    {L B : ℝ} {H : ℕ → ℝ}
    {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    (hgraph : D.graphData E₀ L H B G E) (hN : ∀ k, 2 ≤ D.N k)
    (C J : ℕ) (hC : 1 ≤ C) (hJ : 1 ≤ J) (hCL : (C : ℝ) ≤ L) :
    ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ μ : Measure ScalarIncidence,
      μ ≤ (D.ρ k g).restrict (E k g) →
      ∃ S : Set (Fin 3 → ℤ), MeasurableSet S ∧
        μ univ ≤ ((4 : ENNReal) ^ 3 * (2 ^ 3 * (⌈(2 * H k + 2) ^ 2⌉₊ : ENNReal))) ^ (C * J + 1) *
          μ {p | D.phys k B p ∈ S} ∧
        ∀ p, D.phys k B p ∈ S → ∀ p', D.phys k B p' ∈ S →
          ‖G k g (D.phys k B p) - G k g (D.phys k B p')‖ ≤
            6 * (D.N k ^ ((1 : ℝ) / (J : ℝ)) + (2 * H k + 2) ^ 2) *
              (‖scalarPosition p - scalarPosition p'‖ + D.N k ^ (-(C : ℝ))) := by
  let R : ℝ := (J : ℝ) + (C : ℝ) + 2
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (by omega : 0 < C)
  have hR : 1 < R := by dsimp only [R]; linarith
  filter_upwards [hgraph.2.2 R hR] with k hk
  intro g μ hμ
  obtain ⟨hEm, hsub, hfit, hlist, hvel⟩ := hk.2 g
  have hN0 : 0 < D.N k := by linarith [hN k]
  have hN1 : 1 ≤ D.N k := by linarith [hN k]
  have hH : 1 ≤ H k := hgraph.1.1 k
  let H' : ℝ := (2 * H k + 2) ^ 2
  have hHH' : H k ≤ H' := by dsimp only [H']; nlinarith
  let ν := (D.ρ k g).restrict (E k g)
  let f : ScalarIncidence → Fin 2 → ℝ := fun p => G k g (D.phys k B p)
  have hphys (r : ℝ) (p : ScalarIncidence) :
      D.phys k r p = cell (D.N k ^ (-r)) (scalarPosition p) := by
    funext e
    rfl
  have hrowbin (r : ℝ) (v : Fin 2 → ℝ) : D.rowbin k r v = cell (D.N k ^ (-r)) v := by
    funext e
    rfl
  have hbound : ∀ᵐ p ∂ν, ∀ e, |f p e| ≤ H k := by
    filter_upwards [ae_restrict_mem hEm] with p hp
    exact (hfit p hp).1
  have hbound' : ∀ᵐ p ∂ν, ∀ e, |f p e| ≤ H' :=
    hbound.mono (fun p hp e => (hp e).trans hHH')
  have hiC (i : ℕ) (hi : i < C * J + 1) : (i : ℝ) / (J : ℝ) ≤ C := by
    apply (div_le_iff₀ hJ0).2
    exact_mod_cast (by omega : i ≤ C * J)
  have hcount (i : ℕ) (hi : i < C * J + 1) (n : Fin 3 → ℤ) :
      ((positiveRowValues ν (fun p => cell (powerWidth (D.N k) J i) (scalarPosition p))
        f (powerWidth (D.N k) J i) n).ncard : ℝ) ≤ H' := by
    by_cases hi0 : i = 0
    · have h := original_row_count_of_bound ν
        (fun p => cell (powerWidth (D.N k) J i) (scalarPosition p)) f
        (show 0 < powerWidth (D.N k) J i by exact Real.rpow_pos_of_pos hN0 _)
        (by linarith : 0 ≤ H k) hbound n
      simpa only [hi0, powerWidth, Nat.cast_zero, zero_div, neg_zero, Real.rpow_zero,
        div_one, H'] using h
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (by omega : 1 ≤ i)
    have hrlo : R⁻¹ ≤ (i : ℝ) / (J : ℝ) := by
      have hJR : (J : ℝ) ≤ R := by dsimp only [R]; linarith
      have h₁ := one_div_le_one_div_of_le hJ0 hJR
      have h₂ := div_le_div_of_nonneg_right hi1 hJ0.le
      simpa only [one_div] using h₁.trans h₂
    have hrhi : (i : ℝ) / (J : ℝ) ≤ R := (hiC i hi).trans (by dsimp only [R]; linarith)
    have h := hlist ((i : ℝ) / (J : ℝ)) hrlo hrhi ((hiC i hi).trans hCL) n
    apply le_trans ?_ hHH'
    simpa only [positiveRowValues, ν, f, powerWidth, hphys, hrowbin] using h
  have hbscale (i : ℕ) (hi : i < C * J + 1) : D.N k ^ (-B) ≤ powerWidth (D.N k) J i := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hCB : (C : ℝ) ≤ B := hCL.trans (by linarith [hgraph.2.1])
    linarith [hiC i hi]
  obtain ⟨S, hS, hmass, hcmp⟩ := prepare_original_graph_rows μ ν hμ scalarPosition measurable_scalarPosition
    (show 0 < D.N k ^ (-B) by positivity) (G k g) (sq_nonneg _) hbound'
    (C * J + 1) (by omega) (powerWidth (D.N k) J)
    (D.N k ^ ((1 : ℝ) / (J : ℝ)))
    (Real.one_le_rpow hN1 (by positivity))
    (by simp [powerWidth]) (fun i => by exact Real.rpow_pos_of_pos hN0 _)
    hbscale (fun i _ => (powerWidth_ratio hN0 J i).le) hcount
  refine ⟨S, hS, ?_, ?_⟩
  · simpa only [Finset.prod_const, Finset.card_range, hphys, H'] using hmass
  · simpa only [hphys, powerWidth_last _ hJ C, H'] using hcmp

end ScalarData

end Submission.Obl.k4_scalar_grid_polynomial_qualification
