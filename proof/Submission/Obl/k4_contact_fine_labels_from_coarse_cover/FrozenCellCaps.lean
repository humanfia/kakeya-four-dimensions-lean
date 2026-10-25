-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/FrozenCellCaps.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.QuadraticFiberCaps
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.QuadraticVariation
import Submission.Lib.K4CommonLocalChoice

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_slope_volume
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable def hiddenFiber (F : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℝ) : Polynomial ℝ :=
  coordinatePolynomialHom (Fin.snoc z 0) (Fin.last 3) F

theorem hiddenFiber_degree (F : MvPolynomial (Fin 4) ℝ) (hF : F.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) : (hiddenFiber F z).natDegree ≤ 2 := by
  unfold hiddenFiber coordinatePolynomialHom
  apply (natDegree_eval₂_affine_le F _ ?_).trans hF
  intro i
  split_ifs <;> simp

theorem eval_hiddenFiber (F : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℝ) (w : ℝ) :
    (hiddenFiber F z).eval w = eval (Fin.snoc z w) F := by
  rw [hiddenFiber, eval_coordinatePolynomialHom, update_snoc_hidden]

theorem eval_derivative_hiddenFiber (F : MvPolynomial (Fin 4) ℝ)
    (z : Fin 3 → ℝ) (w : ℝ) :
    (hiddenFiber F z).derivative.eval w = eval (Fin.snoc z w) (pderiv (3 : Fin 4) F) := by
  rw [hiddenFiber, derivative_coordinatePolynomialHom, eval_coordinatePolynomialHom,
    update_snoc_hidden, show (Fin.last 3 : Fin 4) = 3 by decide]

theorem scalar_bin_distance {a x y : ℝ} (ha : 0 < a)
    (hbin : ⌊x / a⌋ = ⌊y / a⌋) : |x - y| ≤ a := by
  have hcell : Submission.Lib.K4CommonLocalChoice.cell a (fun _ : Fin 1 => x) =
      Submission.Lib.K4CommonLocalChoice.cell a (fun _ : Fin 1 => y) := by
    funext i
    exact hbin
  have h := Submission.Lib.K4CommonLocalChoice.norm_sub_lt_of_cell_eq ha hcell
  have hc := (norm_le_pi_norm ((fun _ : Fin 1 => x) - (fun _ => y)) (0 : Fin 1)).trans h.le
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hc

/-- The fine native cell bound obtained by freezing a regular true test.
All caps belong to the ORIGINAL law and may contain any palette numerator. -/
theorem original_frozen_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S T : Set Ω) (hST : S ⊆ T)
    (base : Ω → Fin 3 → ℝ) (hidden native : Ω → ℝ)
    (F P : MvPolynomial (Fin 4) ℝ) (hF : F.totalDegree ≤ 2) (hP : P.totalDegree ≤ 2)
    {K a A R δ H : ℝ} (hK : 1 ≤ K) (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : 0 ≤ A) (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hH : 0 ≤ H)
    (hFγ : ∀ e, |(restrictBase F).coeff e| ≤ A)
    (hFβ : ∀ e, |(restrictBase (pderiv (3 : Fin 4) F)).coeff e| ≤ A)
    (hPγ : ∀ e, |(restrictBase P).coeff e| ≤ A)
    (hPβ : ∀ e, |(restrictBase (pderiv (3 : Fin 4) P)).coeff e| ≤ A)
    (hmesh : 216 * A * R ^ 2 * (1 + H) * δ ≤ a ∧
      216 * A * R ^ 2 * (1 + H) * δ ≤ (2 * K)⁻¹)
    (hbase : ∀ p ∈ S, ∀ i, |base p i| ≤ R)
    (hclose : ∀ p ∈ S, ∀ p' ∈ S, ∀ i, |base p' i - base p i| ≤ δ)
    (hhidden : ∀ p ∈ S, |hidden p| ≤ H)
    (hfit : ∀ p ∈ S, |eval (Fin.snoc (base p) (hidden p)) F| ≤ K * a ∧
      K⁻¹ ≤ |eval (Fin.snoc (base p) (hidden p)) (pderiv (3 : Fin 4) F)|)
    (hnative : ∀ p ∈ S, native p = eval (Fin.snoc (base p) (hidden p)) P ∧
      |eval (Fin.snoc (base p) (hidden p)) (pderiv (3 : Fin 4) P)| ≤ K)
    (hcurv : |curvature P (3 : Fin 4)| ≤ K)
    (cap : ENNReal)
    (hcap : ∀ j : ℤ, μ {p | p ∈ T ∧ ⌊native p / a⌋ = j} ≤ cap) :
    μ S ≤ ENNReal.ofReal (320 * K ^ 3) * cap := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
  · simp
  have hK0 : 0 < K := by linarith
  have hV : 0 ≤ 216 * A * R ^ 2 * δ := by positivity
  have hVle : 216 * A * R ^ 2 * δ ≤ 216 * A * R ^ 2 * (1 + H) * δ := by
    nlinarith [mul_nonneg hV hH]
  have hfreeze : ∀ p ∈ S,
      |(hiddenFiber F (base c)).eval (hidden p) -
        eval (Fin.snoc (base p) (hidden p)) F| ≤ K * a ∧
      |(hiddenFiber F (base c)).derivative.eval (hidden p) -
        eval (Fin.snoc (base p) (hidden p)) (pderiv (3 : Fin 4) F)| ≤ (2 * K)⁻¹ := by
    intro p hp
    have h := quadratic_freezing_variation F hF hA hR hδ hδ1 hH hFγ hFβ
      (base p) (base c) (hbase p hp) (hclose p hp c hc) (hidden p) (hhidden p hp)
    rw [eval_hiddenFiber, eval_derivative_hiddenFiber]
    exact ⟨h.1.trans (hmesh.1.trans (le_mul_of_one_le_left ha.le hK)),
      h.2.trans (hVle.trans hmesh.2)⟩
  have hosc : ∀ p ∈ S, ∀ p' ∈ S, ⌊hidden p / a⌋ = ⌊hidden p' / a⌋ →
      dist (native p) (native p') ≤ (1 + 2 * K) * a := by
    intro p hp p' hp' hbin
    have h := quadratic_freezing_variation P hP hA hR hδ hδ1 hH hPγ hPβ
      (base p) (base p') (hbase p hp) (hclose p hp p' hp') (hidden p') (hhidden p' hp')
    rw [(hnative p hp).1, (hnative p' hp').1, dist_comm]
    apply native_oscillation_of_base_control P hP (base p) (base p')
      (hidden p) (hidden p') hK0.le ha.le ha1 (hnative p hp).2 hcurv
      (scalar_bin_distance ha hbin.symm) (h.1.trans hmesh.1)
  have h := quadratic_fiber_cap_of_freezing μ S T hST hidden native
    (fun p => eval (Fin.snoc (base p) (hidden p)) F)
    (fun p => eval (Fin.snoc (base p) (hidden p)) (pderiv (3 : Fin 4) F))
    (hiddenFiber F (base c)) (hiddenFiber_degree F hF (base c)) hK0 ha
    (by positivity : 0 ≤ 1 + 2 * K) (fun p hp => (hfit p hp).1)
    (fun p hp => (hfit p hp).2) hfreeze hosc cap hcap
  apply h.trans
  apply mul_le_mul _ le_rfl bot_le bot_le
  apply ENNReal.ofReal_le_ofReal
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have h1 : 1 + 4 * K ^ 2 ≤ 5 * K ^ 2 := by linarith
  have h2 : 2 * (1 + 2 * K) + 2 ≤ 8 * K := by linarith
  calc
    _ ≤ 8 * (5 * K ^ 2) * (8 * K) := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
