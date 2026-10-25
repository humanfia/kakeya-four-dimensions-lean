-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Combine, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Combine.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Combine.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Combine.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Projection
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.JetAlgebra

set_option autoImplicit false

/-!
# One pair of the time tree, version 2 (paper, proof of `prop:higher-jets`)

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `b03d2c4a`,
`Jets/Combine.lean`, with rows in `(ℝ²)^*`.  The tail and compatibility tests divide by a row:
here a vector row is normalized by its largest coordinate (`exists_normalized_row`), and the
resulting projection of `y` is excluded by the slab estimate `Determined.mass_le`.

Two times `t, s` at distance `|s - t| ∈ [H/Kg, H]`, child row sequences `Rt, Rs` (with
`Rt 0 = F t`, `Rs 0 = F s`), the first-jet Taylor estimate at the pair, and child lists: every
jet `J_j` (`1 ≤ j ≤ m`) at each time is determined within `δL` by the `q`-bin of the scalar at
that time.  On a set `D` of trajectories labelled at both times:

* `PairData.grad_jet`: the divided difference `∇J_j` is determined by the scalar bin at `t`;
* `PairData.grad_lt`: the divided row difference `g_j = (Rs j - Rt j)/(s - t)` is bounded,
  otherwise the projection estimate would make `D` light;
* `PairData.compat_lt`: compatibility `g_j ≈ Rt (j+1)`;
* `PairData.new_jet`: the new jet `J_{m+1}` with row `g_m` is determined by the scalar bin at `t`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set

noncomputable section

/-- The data of one pair. -/
structure PairData {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 7 → ℝ)
    (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Λ → Fin 7 → ℤ) (K ζ d : ℝ) (D : Set Λ)
    (t s H Kg : ℝ) (Rt Rs : ℕ → Fin 2 → ℝ) (BR eT : ℝ) : Prop where
  hSN : ScalarNormal ν c E F piece K ζ d
  hd1 : d ≤ 1
  ht : t ∈ Icc (0 : ℝ) 1
  hs : s ∈ Icc (0 : ℝ) 1
  hH : 0 < H
  hKg : 1 ≤ Kg
  gap_lo : H / Kg ≤ |s - t|
  gap_hi : |s - t| ≤ H
  lab : ∀ l ∈ D, (l, t) ∈ E ∧ (l, s) ∈ E
  Rt0 : Rt 0 = F t
  Rs0 : Rs 0 = F s
  Rt_le : ∀ i, ‖Rt i‖ ≤ BR
  Rs_le : ∀ i, ‖Rs i‖ ≤ BR
  taylor : ‖F s - F t - (s - t) • Rt 1‖ ≤ eT

namespace PairData

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
  {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ} {D : Set Λ}
  {t s H Kg : ℝ} {Rt Rs : ℕ → Fin 2 → ℝ} {BR eT : ℝ}

/-- The scalar at time `t` as a function of the trajectory. -/
abbrev St (F : ℝ → Fin 2 → ℝ) (c : Λ → Fin 7 → ℝ) (t : ℝ) : Λ → ℝ := fun l => zS F (c l) t

/-- The divided row differences. -/
def grad (Rt Rs : ℕ → Fin 2 → ℝ) (t s : ℝ) (j : ℕ) : Fin 2 → ℝ := (s - t)⁻¹ • (Rs j - Rt j)

theorem K_nonneg (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : 0 ≤ K := by
  linarith [P.hSN.one_le_K]

theorem BR_nonneg (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : 0 ≤ BR :=
  le_trans (norm_nonneg _) (P.Rt_le 0)

theorem delta_pos (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : 0 < |s - t| :=
  lt_of_lt_of_le (div_pos P.hH (by linarith [P.hKg])) P.gap_lo

theorem delta_ne (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : s - t ≠ 0 :=
  abs_pos.mp P.delta_pos

theorem eT_nonneg (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : 0 ≤ eT :=
  le_trans (norm_nonneg _) P.taylor

/-- Error of the scalar transport. -/
def errS (K BR H eT : ℝ) : ℝ := H ^ 2 * (K + 2 * BR * K) + eT * (4 * K)

/-- The scalar at `s` is determined by the scalar bin at `t`. -/
theorem scalar_transport (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL : ℝ} {nL : ℕ} (hq : 0 < q)
    (hJ1 : Determined E (St F c t) D t q (fun l => jet Rt (c l) t 1) δL nL) :
    Determined E (St F c t) D t q (St F c s) (q + |s - t| * δL + errS K BR H eT) (1 * nL) := by
  have h := (Determined.self (E := E) (S := St F c t) (D := D) (t := t) hq).add
    (hJ1.const_mul (s - t))
  refine h.perturb fun l hl hlt => ?_
  have hcs : ∀ e, |c l e| ≤ K := P.hSN.coeff_le _ hlt
  have hid := zS_sub_eq (F := F) (R := Rt) (c := c l) (s := s) (t := t) P.Rt0
  have hy := norm_zy_le hcs P.hs
  have hv := norm_zv_le hcs
  have hK := P.K_nonneg
  have hBR := P.BR_nonneg
  have h2 : |c l 2 - Rt 1 ⬝ᵥ zv (c l)| ≤ K + 2 * BR * K := by
    have hd := abs_dot_le (Rt 1) (zv (c l))
    have : 2 * ‖Rt 1‖ * ‖zv (c l)‖ ≤ 2 * BR * K := by gcongr; exact P.Rt_le 1
    calc |c l 2 - Rt 1 ⬝ᵥ zv (c l)| ≤ |c l 2| + |Rt 1 ⬝ᵥ zv (c l)| := abs_sub _ _
      _ ≤ K + 2 * BR * K := by linarith [hcs 2]
  have hsq : (s - t) ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) P.gap_hi 2
  have he : |(F s - F t - (s - t) • Rt 1) ⬝ᵥ zy (c l) s| ≤ eT * (4 * K) := by
    have hd := abs_dot_le (F s - F t - (s - t) • Rt 1) (zy (c l) s)
    have heT := P.eT_nonneg
    have : 2 * ‖F s - F t - (s - t) • Rt 1‖ * ‖zy (c l) s‖ ≤ 2 * eT * (2 * K) :=
      mul_le_mul (mul_le_mul_of_nonneg_left P.taylor (by norm_num)) hy (norm_nonneg _)
        (by positivity)
    linarith
  show |St F c s l - (St F c t l + (s - t) * jet Rt (c l) t 1)| ≤ errS K BR H eT
  simp only [St]
  rw [show zS F (c l) s - (zS F (c l) t + (s - t) * jet Rt (c l) t 1) =
    (s - t) ^ 2 * (c l 2 - Rt 1 ⬝ᵥ zv (c l)) - (F s - F t - (s - t) • Rt 1) ⬝ᵥ zy (c l) s by
      linarith [hid]]
  unfold errS
  calc |(s - t) ^ 2 * (c l 2 - Rt 1 ⬝ᵥ zv (c l)) - (F s - F t - (s - t) • Rt 1) ⬝ᵥ zy (c l) s|
      ≤ |(s - t) ^ 2 * (c l 2 - Rt 1 ⬝ᵥ zv (c l))| +
          |(F s - F t - (s - t) • Rt 1) ⬝ᵥ zy (c l) s| := abs_sub _ _
    _ = (s - t) ^ 2 * |c l 2 - Rt 1 ⬝ᵥ zv (c l)| +
          |(F s - F t - (s - t) • Rt 1) ⬝ᵥ zy (c l) s| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ H ^ 2 * (K + 2 * BR * K) + eT * (4 * K) :=
        add_le_add (mul_le_mul hsq h2 (abs_nonneg _) (by positivity)) he

/-- Candidates for the divided jet difference. -/
def nGrad (nL : ℕ) (q δ1 : ℝ) : ℕ := nL * ((1 * nL) * (⌊2 * δ1 / q⌋₊ + 2)) * nL

theorem errS_nonneg (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) :
    0 ≤ errS K BR H eT := by
  have hK := P.K_nonneg
  have hBR := P.BR_nonneg
  have := P.eT_nonneg
  unfold errS; positivity

/-- **The divided jet difference is determined by the scalar bin at `t`.** -/
theorem grad_jet (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL : ℝ} {nL : ℕ} {j : ℕ} (hq : 0 < q) (hδL : 0 ≤ δL)
    (hJ1 : Determined E (St F c t) D t q (fun l => jet Rt (c l) t 1) δL nL)
    (hJt : Determined E (St F c t) D t q (fun l => jet Rt (c l) t j) δL nL)
    (hJs : Determined E (St F c s) D s q (fun l => jet Rs (c l) s j) δL nL) :
    Determined E (St F c t) D t q
      (fun l => (jet Rs (c l) s j - jet Rt (c l) t j) / (s - t)) ((δL + δL) / |s - t|)
      (nGrad nL q (q + |s - t| * δL + errS K BR H eT)) := by
  have hT := P.scalar_transport hq hJ1
  have hδ1 : 0 ≤ q + |s - t| * δL + errS K BR H eT := by
    have := P.errS_nonneg; positivity
  have hJs' := hJs.transport hq hT (fun l hl _ => (P.lab l hl).2) hδ1
  have h := (hJs'.sub hJt).const_mul (1 / (s - t))
  refine (h.congr ?_).mono (le_of_eq ?_) le_rfl
  · intro l _ _; field_simp
  · rw [abs_div, abs_one]; ring

/-- The identity behind the tail and compatibility tests. -/
theorem grad_identity (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) {j : ℕ}
    (hj : 1 ≤ j) (cl : Fin 7 → ℝ) :
    (jet Rs cl s j - jet Rt cl t j) / (s - t) = xder cl t (j + 1) -
      grad Rt Rs t s j ⬝ᵥ zy cl t - Rs j ⬝ᵥ zv cl -
        (j : ℝ) * (grad Rt Rs t s (j - 1) ⬝ᵥ zv cl) := by
  have hΔ := P.delta_ne
  rw [jet_sub_eq hj]
  simp only [grad, smul_dotProduct, smul_eq_mul]
  field_simp

theorem abs_xder_le {cl : Fin 7 → ℝ} {K t : ℝ} (hc : ∀ e, |cl e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1)
    (j : ℕ) : |xder cl t j| ≤ 3 * K := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hc 0)
  match j with
  | 0 => exact abs_zx_le hc ht
  | 1 =>
    simp only [xder]
    have h1 := hc 1; have h2 := hc 2
    calc |cl 1 + 2 * cl 2 * t| ≤ |cl 1| + |2 * cl 2 * t| := abs_add_le _ _
      _ = |cl 1| + 2 * |cl 2| * t := by
          rw [abs_mul, abs_mul, abs_two, abs_of_nonneg ht.1]
      _ ≤ K + 2 * K * 1 := by
          have := mul_le_mul (by linarith : 2 * |cl 2| ≤ 2 * K) ht.2 ht.1 (by positivity)
          linarith
      _ = 3 * K := by ring
  | 2 =>
    simp only [xder]
    rw [abs_mul, abs_two]; linarith [hc 2]
  | (n + 3) => simp [xder]; positivity

omit [MeasurableSpace Λ] in
/-- Dividing a determined combination by the largest coordinate of a large row: if
`g · y = A l - X l` with `X` determined within `δ`, `|A l| ≤ a` and `‖g‖ ≥ Λ > 0`, then the
normalized projection `ê · y` (`ê = g / g k`) is determined within `(δ + a)/Λ`. -/
theorem determined_normalized {E : Set (Λ × ℝ)} {S : Λ → ℝ} {D : Set Λ} {t q δ a Λ' : ℝ}
    {n : ℕ} {X A : Λ → ℝ} {Y : Λ → Fin 2 → ℝ} {g : Fin 2 → ℝ} (hΛ : 0 < Λ') (hg : Λ' ≤ ‖g‖)
    (hδ : 0 ≤ δ) (hX : Determined E S D t q X δ n) (hA : ∀ l ∈ D, (l, t) ∈ E → |A l| ≤ a)
    (hid : ∀ l ∈ D, (l, t) ∈ E → g ⬝ᵥ Y l = A l - X l) :
    ∃ k : Fin 2, ((g k)⁻¹ • g) k = 1 ∧ |((g k)⁻¹ • g) (Fin.rev k)| ≤ 1 ∧
      Determined E S D t q (fun l => ((g k)⁻¹ • g) ⬝ᵥ Y l) ((δ + a) / Λ') n := by
  have hgpos : 0 < ‖g‖ := lt_of_lt_of_le hΛ hg
  obtain ⟨k, hgk, hek, he'⟩ := exists_normalized_row hgpos
  refine ⟨k, hek, he', ?_⟩
  have hinv : ‖g‖⁻¹ ≤ Λ'⁻¹ := inv_anti₀ hΛ hg
  have h1 := hX.const_mul (-(g k)⁻¹)
  have h2 := h1.perturb (Ψ := fun l => ((g k)⁻¹ • g) ⬝ᵥ Y l) (ε := a / Λ') (fun l hl hlt => ?_)
  · refine h2.mono ?_ le_rfl
    rw [abs_neg, abs_inv, hgk]
    calc ‖g‖⁻¹ * δ + a / Λ' ≤ Λ'⁻¹ * δ + a / Λ' := by gcongr
      _ = (δ + a) / Λ' := by field_simp
  · have hl' := hid l hl hlt
    have e : ((g k)⁻¹ • g) ⬝ᵥ Y l - -(g k)⁻¹ * X l = (g k)⁻¹ * A l := by
      rw [smul_dotProduct, smul_eq_mul, hl']; ring
    rw [e, abs_mul, abs_inv, hgk]
    have hAl := hA l hl hlt
    have ha : 0 ≤ a := le_trans (abs_nonneg _) hAl
    calc ‖g‖⁻¹ * |A l| ≤ Λ'⁻¹ * a := mul_le_mul hinv hAl (abs_nonneg _) (by positivity)
      _ = a / Λ' := by field_simp

/-- The combination of the new and the old rows in the compatibility test and the new jet. -/
theorem norm_combo_le (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) {j : ℕ}
    {G δ' : ℝ} (hG : ‖grad Rt Rs t s j‖ ≤ G) (hδ' : ‖grad Rt Rs t s (j - 1) - Rt j‖ ≤ δ') :
    ‖(s - t) • grad Rt Rs t s j + (j : ℝ) • (grad Rt Rs t s (j - 1) - Rt j)‖ ≤
      H * G + j * δ' := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) hG
  calc ‖(s - t) • grad Rt Rs t s j + (j : ℝ) • (grad Rt Rs t s (j - 1) - Rt j)‖
      ≤ ‖(s - t) • grad Rt Rs t s j‖ + ‖(j : ℝ) • (grad Rt Rs t s (j - 1) - Rt j)‖ :=
        norm_add_le _ _
    _ = |s - t| * ‖grad Rt Rs t s j‖ + (j : ℝ) * ‖grad Rt Rs t s (j - 1) - Rt j‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hj]
    _ ≤ H * G + j * δ' := add_le_add (mul_le_mul P.gap_hi hG (norm_nonneg _) P.hH.le)
        (mul_le_mul_of_nonneg_left hδ' hj)

/-- The exact difference of the new jet and the divided jet difference. -/
theorem new_jet_identity (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) {m : ℕ}
    (hm : 1 ≤ m) (cl : Fin 7 → ℝ) :
    jet (Function.update Rt (m + 1) (grad Rt Rs t s m)) cl t (m + 1) -
      (jet Rs cl s m - jet Rt cl t m) / (s - t) =
      ((s - t) • grad Rt Rs t s m + (m : ℝ) • (grad Rt Rs t s (m - 1) - Rt m)) ⬝ᵥ zv cl := by
  have hΔ := P.delta_ne
  have hid := P.grad_identity hm cl
  have hjet : jet (Function.update Rt (m + 1) (grad Rt Rs t s m)) cl t (m + 1) =
      xder cl t (m + 1) - grad Rt Rs t s m ⬝ᵥ zy cl t - ((m : ℝ) + 1) * (Rt m ⬝ᵥ zv cl) := by
    simp only [jet, Function.update_self]
    have : Function.update Rt (m + 1) (grad Rt Rs t s m) (m + 1 - 1) = Rt m := by
      simp
    rw [this]; push_cast; ring
  have hgr : Rs m = Rt m + (s - t) • grad Rt Rs t s m := by
    simp only [grad, smul_smul, mul_inv_cancel₀ hΔ, one_smul]; abel
  rw [hjet, hid]
  simp only [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul]
  rw [hgr]
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

/-- **Tail test.**  A large divided row difference would determine a normalized tangential
projection and make `D` light. -/
theorem grad_lt (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL : ℝ} {nL : ℕ} {j : ℕ} (hj : 1 ≤ j) (hζq : ζ ≤ q) (hq1 : q ≤ 1) (hδL : 0 ≤ δL)
    (hJ1 : Determined E (St F c t) D t q (fun l => jet Rt (c l) t 1) δL nL)
    (hJt : Determined E (St F c t) D t q (fun l => jet Rt (c l) t j) δL nL)
    (hJs : Determined E (St F c s) D s q (fun l => jet Rs (c l) s j) δL nL)
    {G' Lam mD : ℝ} (hG' : ‖grad Rt Rs t s (j - 1)‖ ≤ G') (hΛ : 0 < Lam)
    (hmass : ENNReal.ofReal mD ≤ ν D)
    (hsmall : 4000 * K ^ 6 * (nGrad nL q (q + |s - t| * δL + errS K BR H eT) : ℝ) *
      (((δL + δL) / |s - t| + (3 * K + 2 * BR * K + 2 * j * G' * K)) / Lam + q) < mD) :
    ‖grad Rt Rs t s j‖ < Lam := by
  have hq : 0 < q := lt_of_lt_of_le P.hSN.zeta_pos hζq
  have hK := P.K_nonneg
  have hBR := P.BR_nonneg
  have hG'0 : 0 ≤ G' := le_trans (norm_nonneg _) hG'
  have hΔ := P.delta_pos
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  by_contra hge
  push Not at hge
  have hgrad := P.grad_jet hq hδL hJ1 hJt hJs
  set A : Λ → ℝ := fun l => xder (c l) t (j + 1) - Rs j ⬝ᵥ zv (c l) -
    (j : ℝ) * (grad Rt Rs t s (j - 1) ⬝ᵥ zv (c l)) with hAdef
  have hA : ∀ l ∈ D, (l, t) ∈ E → |A l| ≤ 3 * K + 2 * BR * K + 2 * j * G' * K := by
    intro l _ hlt
    have hc : ∀ e, |c l e| ≤ K := P.hSN.coeff_le _ hlt
    have hx := abs_xder_le hc P.ht (j + 1)
    have hv := norm_zv_le hc
    have h1 := abs_dot_le (Rs j) (zv (c l))
    have h2 := abs_dot_le (grad Rt Rs t s (j - 1)) (zv (c l))
    have h1' : 2 * ‖Rs j‖ * ‖zv (c l)‖ ≤ 2 * BR * K :=
      mul_le_mul (mul_le_mul_of_nonneg_left (P.Rs_le j) (by norm_num)) hv (norm_nonneg _)
        (by positivity)
    have h2' : 2 * ‖grad Rt Rs t s (j - 1)‖ * ‖zv (c l)‖ ≤ 2 * G' * K :=
      mul_le_mul (mul_le_mul_of_nonneg_left hG' (by norm_num)) hv (norm_nonneg _)
        (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h2.trans h2') hj0
    simp only [hAdef]
    calc |xder (c l) t (j + 1) - Rs j ⬝ᵥ zv (c l) -
          (j : ℝ) * (grad Rt Rs t s (j - 1) ⬝ᵥ zv (c l))|
        ≤ |xder (c l) t (j + 1)| + |Rs j ⬝ᵥ zv (c l)| +
            (j : ℝ) * |grad Rt Rs t s (j - 1) ⬝ᵥ zv (c l)| := by
          have h4 := abs_sub (xder (c l) t (j + 1) - Rs j ⬝ᵥ zv (c l))
            ((j : ℝ) * (grad Rt Rs t s (j - 1) ⬝ᵥ zv (c l)))
          have h5 := abs_sub (xder (c l) t (j + 1)) (Rs j ⬝ᵥ zv (c l))
          rw [abs_mul (j : ℝ), abs_of_nonneg hj0] at h4
          linarith
      _ ≤ 3 * K + 2 * BR * K + 2 * j * G' * K := by nlinarith
  have hid : ∀ l ∈ D, (l, t) ∈ E → grad Rt Rs t s j ⬝ᵥ zy (c l) t =
      A l - (jet Rs (c l) s j - jet Rt (c l) t j) / (s - t) := by
    intro l _ _
    have := P.grad_identity hj (c l)
    simp only [hAdef]
    linarith
  have hδ : 0 ≤ (δL + δL) / |s - t| := by positivity
  obtain ⟨k, hek, he', hdet⟩ := determined_normalized hΛ hge hδ hgrad hA hid
  have hmL := Determined.mass_le P.hSN P.hd1 hζq hq1 (by positivity) hek he' hdet
  have hsub : D ⊆ {l | l ∈ D ∧ (l, t) ∈ E} := fun l hl => ⟨hl, (P.lab l hl).1⟩
  have := (hmass.trans (measure_mono hsub)).trans hmL
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  linarith

/-- **Compatibility test.** -/
theorem compat_lt (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL : ℝ} {nL : ℕ} {j : ℕ} (hj : 1 ≤ j) (hζq : ζ ≤ q) (hq1 : q ≤ 1) (hδL : 0 ≤ δL)
    (hJ1 : Determined E (St F c t) D t q (fun l => jet Rt (c l) t 1) δL nL)
    (hJt : Determined E (St F c t) D t q (fun l => jet Rt (c l) t j) δL nL)
    (hJs : Determined E (St F c s) D s q (fun l => jet Rs (c l) s j) δL nL)
    (hJt' : Determined E (St F c t) D t q (fun l => jet Rt (c l) t (j + 1)) δL nL)
    {G δ' δ'' mD : ℝ} (hG : ‖grad Rt Rs t s j‖ ≤ G)
    (hδ' : ‖grad Rt Rs t s (j - 1) - Rt j‖ ≤ δ') (hδ'' : 0 < δ'')
    (hmass : ENNReal.ofReal mD ≤ ν D)
    (hsmall : 4000 * K ^ 6 * ((nGrad nL q (q + |s - t| * δL + errS K BR H eT) * nL : ℕ) : ℝ) *
      (((δL + δL) / |s - t| + δL + 2 * K * (H * G + j * δ')) / δ'' + q) < mD) :
    ‖grad Rt Rs t s j - Rt (j + 1)‖ < δ'' := by
  have hq : 0 < q := lt_of_lt_of_le P.hSN.zeta_pos hζq
  have hK := P.K_nonneg
  have hH0 : 0 ≤ H := P.hH.le
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) hG
  have hδ'0 : 0 ≤ δ' := le_trans (norm_nonneg _) hδ'
  have hΔ := P.delta_pos
  have hΔne := P.delta_ne
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  by_contra hge
  push Not at hge
  have hgrad := P.grad_jet hq hδL hJ1 hJt hJs
  have hX := hgrad.sub hJt'
  have hW := P.norm_combo_le hG hδ'
  set W : Fin 2 → ℝ := (s - t) • grad Rt Rs t s j + (j : ℝ) • (grad Rt Rs t s (j - 1) - Rt j)
    with hWdef
  have hA : ∀ l ∈ D, (l, t) ∈ E → |-(W ⬝ᵥ zv (c l))| ≤ 2 * K * (H * G + j * δ') := by
    intro l _ hlt
    have hc : ∀ e, |c l e| ≤ K := P.hSN.coeff_le _ hlt
    have hv := norm_zv_le hc
    rw [abs_neg]
    have h1 := abs_dot_le W (zv (c l))
    have : 2 * ‖W‖ * ‖zv (c l)‖ ≤ 2 * (H * G + j * δ') * K :=
      mul_le_mul (mul_le_mul_of_nonneg_left hW (by norm_num)) hv (norm_nonneg _)
        (by positivity)
    linarith
  have hid : ∀ l ∈ D, (l, t) ∈ E → (grad Rt Rs t s j - Rt (j + 1)) ⬝ᵥ zy (c l) t =
      -(W ⬝ᵥ zv (c l)) -
        ((jet Rs (c l) s j - jet Rt (c l) t j) / (s - t) - jet Rt (c l) t (j + 1)) := by
    intro l _ _
    have hgi := P.grad_identity hj (c l)
    have hjet : jet Rt (c l) t (j + 1) = xder (c l) t (j + 1) - Rt (j + 1) ⬝ᵥ zy (c l) t -
        ((j : ℝ) + 1) * (Rt j ⬝ᵥ zv (c l)) := by
      simp only [jet]; push_cast; simp
    have hgr : Rs j = Rt j + (s - t) • grad Rt Rs t s j := by
      simp only [grad, smul_smul, mul_inv_cancel₀ hΔne, one_smul]; abel
    rw [hgi, hjet, hWdef]
    simp only [sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hgr]
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  have hδ : 0 ≤ (δL + δL) / |s - t| + δL := by positivity
  obtain ⟨k, hek, he', hdet⟩ := determined_normalized hδ'' hge hδ hX hA hid
  have hmL := Determined.mass_le P.hSN P.hd1 hζq hq1 (by positivity) hek he' hdet
  have hsub : D ⊆ {l | l ∈ D ∧ (l, t) ∈ E} := fun l hl => ⟨hl, (P.lab l hl).1⟩
  have := (hmass.trans (measure_mono hsub)).trans hmL
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  linarith

/-- **The new jet** with row `g_m` is determined by the scalar bin at `t`. -/
theorem new_jet (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL : ℝ} {nL : ℕ} {m : ℕ} (hm : 1 ≤ m) (hq : 0 < q) (hδL : 0 ≤ δL)
    (hJ1 : Determined E (St F c t) D t q (fun l => jet Rt (c l) t 1) δL nL)
    (hJt : Determined E (St F c t) D t q (fun l => jet Rt (c l) t m) δL nL)
    (hJs : Determined E (St F c s) D s q (fun l => jet Rs (c l) s m) δL nL)
    {G δ' : ℝ} (hG : ‖grad Rt Rs t s m‖ ≤ G) (hδ' : ‖grad Rt Rs t s (m - 1) - Rt m‖ ≤ δ') :
    Determined E (St F c t) D t q
      (fun l => jet (Function.update Rt (m + 1) (grad Rt Rs t s m)) (c l) t (m + 1))
      ((δL + δL) / |s - t| + 2 * K * (H * G + m * δ'))
      (nGrad nL q (q + |s - t| * δL + errS K BR H eT)) := by
  have hgrad := P.grad_jet hq hδL hJ1 hJt hJs
  have hK := P.K_nonneg
  have hH0 : 0 ≤ H := P.hH.le
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) hG
  have hδ'0 : 0 ≤ δ' := le_trans (norm_nonneg _) hδ'
  refine hgrad.perturb fun l hl hlt => ?_
  have hc : ∀ e, |c l e| ≤ K := P.hSN.coeff_le _ hlt
  have hv := norm_zv_le hc
  rw [P.new_jet_identity hm (c l)]
  have hW := P.norm_combo_le hG hδ'
  have h1 := abs_dot_le ((s - t) • grad Rt Rs t s m + (m : ℝ) • (grad Rt Rs t s (m - 1) - Rt m))
    (zv (c l))
  have : 2 * ‖(s - t) • grad Rt Rs t s m + (m : ℝ) • (grad Rt Rs t s (m - 1) - Rt m)‖ *
      ‖zv (c l)‖ ≤ 2 * (H * G + m * δ') * K :=
    mul_le_mul (mul_le_mul_of_nonneg_left hW (by norm_num)) hv (norm_nonneg _) (by positivity)
  linarith

end PairData

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
