import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Determined
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.JetAlgebra

/-!
# One pair of the time tree (paper, proof of `prop:higher-jets`, "Inductive information statement")

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

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set

noncomputable section

/-- The data of one pair. -/
structure PairData {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 5 → ℝ)
    (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (piece : ℝ → Λ → Fin 5 → ℤ) (K ζ d : ℝ) (D : Set Λ)
    (t s H Kg : ℝ) (Rt Rs : ℕ → ℝ) (BR eT : ℝ) : Prop where
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
  Rt_le : ∀ i, |Rt i| ≤ BR
  Rs_le : ∀ i, |Rs i| ≤ BR
  taylor : |F s - F t - (s - t) * Rt 1| ≤ eT

namespace PairData

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 5 → ℝ}
  {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {piece : ℝ → Λ → Fin 5 → ℤ} {K ζ d : ℝ} {D : Set Λ}
  {t s H Kg : ℝ} {Rt Rs : ℕ → ℝ} {BR eT : ℝ}

/-- The scalar at time `t` as a function of the trajectory. -/
abbrev St (F : ℝ → ℝ) (c : Λ → Fin 5 → ℝ) (t : ℝ) : Λ → ℝ := fun l => zS F (c l) t

/-- The divided row differences. -/
def grad (Rt Rs : ℕ → ℝ) (t s : ℝ) (j : ℕ) : ℝ := (Rs j - Rt j) / (s - t)

theorem K_nonneg (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : 0 ≤ K := by
  linarith [P.hSN.one_le_K]

theorem BR_nonneg (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : 0 ≤ BR :=
  le_trans (abs_nonneg _) (P.Rt_le 0)

theorem delta_pos (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : 0 < |s - t| :=
  lt_of_lt_of_le (div_pos P.hH (by linarith [P.hKg])) P.gap_lo

theorem delta_ne (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) : s - t ≠ 0 :=
  abs_pos.mp P.delta_pos

/-- Error of the scalar transport. -/
def errS (K BR H eT : ℝ) : ℝ := H ^ 2 * (K + BR * K) + eT * (2 * K)

/-- The scalar at `s` is determined by the scalar bin at `t`. -/
theorem scalar_transport (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL : ℝ} {nL : ℕ} (hq : 0 < q)
    (hJ1 : Determined E (St F c t) D t q (fun l => jet Rt (c l) t 1) δL nL) :
    Determined E (St F c t) D t q (St F c s) (q + |s - t| * δL + errS K BR H eT) (1 * nL) := by
  have h := (Determined.self (E := E) (S := St F c t) (D := D) (t := t) hq).add
    (hJ1.const_mul (s - t))
  refine h.perturb fun l hl hlt => ?_
  have hc := P.hSN.coeff_le _ hlt
  have hcs : ∀ e, |c l e| ≤ K := hc
  have hid := zS_sub_eq (F := F) (R := Rt) (c := c l) (s := s) (t := t) P.Rt0
  have hy := abs_zy_le hcs P.hs
  have hK := P.K_nonneg
  have hBR := P.BR_nonneg
  have h2 : |c l 2 - Rt 1 * c l 4| ≤ K + BR * K := by
    calc |c l 2 - Rt 1 * c l 4| ≤ |c l 2| + |Rt 1| * |c l 4| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ K + BR * K := by gcongr; exacts [hcs 2, P.Rt_le 1, hcs 4]
  have hsq : (s - t) ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) P.gap_hi 2
  show |St F c s l - (St F c t l + (s - t) * jet Rt (c l) t 1)| ≤ errS K BR H eT
  simp only [St]
  rw [show zS F (c l) s - (zS F (c l) t + (s - t) * jet Rt (c l) t 1) =
    (s - t) ^ 2 * (c l 2 - Rt 1 * c l 4) - (F s - F t - (s - t) * Rt 1) * zy (c l) s by
      linarith [hid]]
  unfold errS
  calc |(s - t) ^ 2 * (c l 2 - Rt 1 * c l 4) - (F s - F t - (s - t) * Rt 1) * zy (c l) s|
      ≤ |(s - t) ^ 2 * (c l 2 - Rt 1 * c l 4)| + |(F s - F t - (s - t) * Rt 1) * zy (c l) s| :=
        abs_sub _ _
    _ = (s - t) ^ 2 * |c l 2 - Rt 1 * c l 4| + |F s - F t - (s - t) * Rt 1| * |zy (c l) s| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ H ^ 2 * (K + BR * K) + eT * (2 * K) := by
        have heT : 0 ≤ eT := le_trans (abs_nonneg _) P.taylor
        exact add_le_add (mul_le_mul hsq h2 (abs_nonneg _) (by positivity))
          (mul_le_mul P.taylor hy (abs_nonneg _) heT)

/-- Candidates for the divided jet difference. -/
def nGrad (nL : ℕ) (q δ1 : ℝ) : ℕ := nL * ((1 * nL) * (⌊2 * δ1 / q⌋₊ + 2)) * nL

theorem errS_nonneg (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) :
    0 ≤ errS K BR H eT := by
  have hK := P.K_nonneg
  have hBR := P.BR_nonneg
  have : 0 ≤ eT := le_trans (abs_nonneg _) P.taylor
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
    (hj : 1 ≤ j) (cl : Fin 5 → ℝ) :
    (jet Rs cl s j - jet Rt cl t j) / (s - t) = xder cl t (j + 1) -
      grad Rt Rs t s j * zy cl t - Rs j * cl 4 - (j : ℝ) * grad Rt Rs t s (j - 1) * cl 4 := by
  have hΔ := P.delta_ne
  rw [jet_sub_eq hj]
  simp only [grad]
  field_simp

theorem abs_xder_le {cl : Fin 5 → ℝ} {K t : ℝ} (hc : ∀ e, |cl e| ≤ K) (ht : t ∈ Icc (0 : ℝ) 1)
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

/-- **Tail test.**  A large divided row difference would determine the tangential coordinate
and make `D` light. -/
theorem grad_lt (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL : ℝ} {nL : ℕ} {j : ℕ} (hj : 1 ≤ j) (hζq : ζ ≤ q) (hq1 : q ≤ 1) (hδL : 0 ≤ δL)
    (hJ1 : Determined E (St F c t) D t q (fun l => jet Rt (c l) t 1) δL nL)
    (hJt : Determined E (St F c t) D t q (fun l => jet Rt (c l) t j) δL nL)
    (hJs : Determined E (St F c s) D s q (fun l => jet Rs (c l) s j) δL nL)
    {G' Λ mD : ℝ} (hG' : |grad Rt Rs t s (j - 1)| ≤ G') (hΛ : 0 < Λ)
    (hmass : ENNReal.ofReal mD ≤ ν D)
    (hsmall : 400 * K ^ 5 * (nGrad nL q (q + |s - t| * δL + errS K BR H eT) : ℝ) *
      (((δL + δL) / |s - t| + 3 * K + BR * K + j * G' * K) / Λ + q) < mD) :
    |grad Rt Rs t s j| < Λ := by
  have hq : 0 < q := lt_of_lt_of_le P.hSN.zeta_pos hζq
  have hK := P.K_nonneg
  have hBR := P.BR_nonneg
  have hG'0 : 0 ≤ G' := le_trans (abs_nonneg _) hG'
  by_contra hge
  push Not at hge
  set g := grad Rt Rs t s j
  have hg0 : g ≠ 0 := by
    intro h; rw [h, abs_zero] at hge; linarith
  have hgrad := P.grad_jet hq hδL hJ1 hJt hJs
  set L := ((δL + δL) / |s - t| + 3 * K + BR * K + j * G' * K) / Λ
  have hdet : Determined E (St F c t) D t q (fun l => zy (c l) t) L
      (nGrad nL q (q + |s - t| * δL + errS K BR H eT)) := by
    have h1 := hgrad.const_mul (-1 / g)
    have h2 := h1.perturb (Ψ := fun l => zy (c l) t)
      (ε := (3 * K + BR * K + j * G' * K) / Λ) (fun l hl hlt => ?_)
    · refine h2.mono ?_ le_rfl
      have hgΛ : 1 / |g| ≤ 1 / Λ := one_div_le_one_div_of_le hΛ hge
      have hΔ := P.delta_pos
      rw [abs_div, abs_neg, abs_one]
      calc 1 / |g| * ((δL + δL) / |s - t|) + (3 * K + BR * K + j * G' * K) / Λ
          ≤ 1 / Λ * ((δL + δL) / |s - t|) + (3 * K + BR * K + j * G' * K) / Λ := by
            gcongr
        _ = L := by simp only [L]; ring
    · have hc : ∀ e, |c l e| ≤ K := P.hSN.coeff_le _ hlt
      have hid := P.grad_identity hj (c l)
      have hx := abs_xder_le hc P.ht (j + 1)
      have e : zy (c l) t - -1 / g * ((jet Rs (c l) s j - jet Rt (c l) t j) / (s - t)) =
          (xder (c l) t (j + 1) - Rs j * c l 4 -
            (j : ℝ) * grad Rt Rs t s (j - 1) * c l 4) / g := by
        rw [hid]; field_simp; ring
      rw [e, abs_div]
      apply div_le_div₀ (by positivity) _ hΛ hge
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      calc |xder (c l) t (j + 1) - Rs j * c l 4 - (j : ℝ) * grad Rt Rs t s (j - 1) * c l 4|
          ≤ |xder (c l) t (j + 1)| + |Rs j| * |c l 4| +
              (j : ℝ) * |grad Rt Rs t s (j - 1)| * |c l 4| := by
            have h1 := abs_sub (xder (c l) t (j + 1) - Rs j * c l 4)
              ((j : ℝ) * grad Rt Rs t s (j - 1) * c l 4)
            have h2 := abs_sub (xder (c l) t (j + 1)) (Rs j * c l 4)
            rw [abs_mul (Rs j), abs_mul ((j : ℝ) * grad Rt Rs t s (j - 1)), abs_mul (j : ℝ),
              abs_of_nonneg hj0] at *
            linarith
        _ ≤ 3 * K + BR * K + j * G' * K := by
            gcongr
            · exact P.Rs_le j
            · exact hc 4
            · exact hc 4
  have hmL := Determined.mass_le P.hSN P.hd1 hζq hq1 (by positivity) hdet
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
    {G δ' δ'' mD : ℝ} (hG : |grad Rt Rs t s j| ≤ G) (hδ' : |grad Rt Rs t s (j - 1) - Rt j| ≤ δ')
    (hδ'' : 0 < δ'') (hmass : ENNReal.ofReal mD ≤ ν D)
    (hsmall : 400 * K ^ 5 * ((nL * nGrad nL q (q + |s - t| * δL + errS K BR H eT) : ℕ) : ℝ) *
      ((δL + (δL + δL) / |s - t| + K * (H * G + j * δ')) / δ'' + q) < mD) :
    |grad Rt Rs t s j - Rt (j + 1)| < δ'' := by
  have hq : 0 < q := lt_of_lt_of_le P.hSN.zeta_pos hζq
  have hK := P.K_nonneg
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) hG
  have hδ'0 : 0 ≤ δ' := le_trans (abs_nonneg _) hδ'
  have hHnn : 0 ≤ H := P.hH.le
  by_contra hge
  push Not at hge
  set e := grad Rt Rs t s j - Rt (j + 1)
  have he0 : e ≠ 0 := by
    intro h; rw [h, abs_zero] at hge; linarith
  have hgrad := P.grad_jet hq hδL hJ1 hJt hJs
  set L := (δL + (δL + δL) / |s - t| + K * (H * G + j * δ')) / δ''
  have hdet : Determined E (St F c t) D t q (fun l => zy (c l) t) L
      (nL * nGrad nL q (q + |s - t| * δL + errS K BR H eT)) := by
    have h1 := (hJt'.sub hgrad).const_mul (1 / e)
    have h2 := h1.perturb (Ψ := fun l => zy (c l) t)
      (ε := K * (H * G + j * δ') / δ'') (fun l hl hlt => ?_)
    · refine h2.mono ?_ le_rfl
      have heΛ : 1 / |e| ≤ 1 / δ'' := one_div_le_one_div_of_le hδ'' hge
      rw [abs_div, abs_one]
      calc 1 / |e| * (δL + (δL + δL) / |s - t|) + K * (H * G + j * δ') / δ''
          ≤ 1 / δ'' * (δL + (δL + δL) / |s - t|) + K * (H * G + j * δ') / δ'' := by
            gcongr
        _ = L := by simp only [L]; ring
    · have hc : ∀ e, |c l e| ≤ K := P.hSN.coeff_le _ hlt
      have hid := P.grad_identity hj (c l)
      have hjet : jet Rt (c l) t (j + 1) = xder (c l) t (j + 1) - Rt (j + 1) * zy (c l) t -
          ((j : ℝ) + 1) * Rt j * c l 4 := by
        simp only [jet]; push_cast; simp
      have hΔ := P.delta_ne
      have hgr : Rs j = Rt j + (s - t) * grad Rt Rs t s j := by
        simp only [grad]; field_simp; ring
      have hXY : e * zy (c l) t - (jet Rt (c l) t (j + 1) -
          (jet Rs (c l) s j - jet Rt (c l) t j) / (s - t)) =
          -(((s - t) * grad Rt Rs t s j + (j : ℝ) * (grad Rt Rs t s (j - 1) - Rt j)) * c l 4) := by
        rw [hid, hjet, hgr]; simp only [e]; ring
      have key : zy (c l) t - 1 / e * (jet Rt (c l) t (j + 1) -
          (jet Rs (c l) s j - jet Rt (c l) t j) / (s - t)) =
          (e * zy (c l) t - (jet Rt (c l) t (j + 1) -
            (jet Rs (c l) s j - jet Rt (c l) t j) / (s - t))) / e := by
        field_simp
      rw [key, hXY, abs_div, abs_neg]
      have hH0 : 0 ≤ H := P.hH.le
      apply div_le_div₀ (by positivity) _ hδ'' hge
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      rw [abs_mul]
      have hA : |(s - t) * grad Rt Rs t s j + (j : ℝ) * (grad Rt Rs t s (j - 1) - Rt j)| ≤
          H * G + j * δ' := by
        calc _ ≤ |(s - t) * grad Rt Rs t s j| + |(j : ℝ) * (grad Rt Rs t s (j - 1) - Rt j)| :=
              abs_add_le _ _
          _ = |s - t| * |grad Rt Rs t s j| + (j : ℝ) * |grad Rt Rs t s (j - 1) - Rt j| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hj0]
          _ ≤ H * G + j * δ' := add_le_add (mul_le_mul P.gap_hi hG (abs_nonneg _) hH0)
              (mul_le_mul_of_nonneg_left hδ' hj0)
      calc |(s - t) * grad Rt Rs t s j + (j : ℝ) * (grad Rt Rs t s (j - 1) - Rt j)| * |c l 4|
          ≤ (H * G + j * δ') * K := mul_le_mul hA (hc 4) (abs_nonneg _) (by positivity)
        _ = K * (H * G + j * δ') := by ring
  have hmL := Determined.mass_le P.hSN P.hd1 hζq hq1 (by positivity) hdet
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
    {G δ' : ℝ} (hG : |grad Rt Rs t s m| ≤ G) (hδ' : |grad Rt Rs t s (m - 1) - Rt m| ≤ δ') :
    Determined E (St F c t) D t q
      (fun l => jet (Function.update Rt (m + 1) (grad Rt Rs t s m)) (c l) t (m + 1))
      ((δL + δL) / |s - t| + K * (H * G + m * δ'))
      (nGrad nL q (q + |s - t| * δL + errS K BR H eT)) := by
  have hK := P.K_nonneg
  have hgrad := P.grad_jet hq hδL hJ1 hJt hJs
  refine hgrad.perturb fun l hl hlt => ?_
  have hc : ∀ e, |c l e| ≤ K := P.hSN.coeff_le _ hlt
  have hid := P.grad_identity hm (c l)
  have hΔ := P.delta_ne
  have hjet : jet (Function.update Rt (m + 1) (grad Rt Rs t s m)) (c l) t (m + 1) =
      xder (c l) t (m + 1) - grad Rt Rs t s m * zy (c l) t - ((m : ℝ) + 1) * Rt m * c l 4 := by
    simp only [jet, Function.update_self]
    have : Function.update Rt (m + 1) (grad Rt Rs t s m) (m + 1 - 1) = Rt m := by
      simp
    rw [this]; push_cast; ring
  have key : jet (Function.update Rt (m + 1) (grad Rt Rs t s m)) (c l) t (m + 1) -
      (jet Rs (c l) s m - jet Rt (c l) t m) / (s - t) =
      ((s - t) * grad Rt Rs t s m + (m : ℝ) * (grad Rt Rs t s (m - 1) - Rt m)) * c l 4 := by
    rw [hjet, hid]
    have hgr : Rs m = Rt m + (s - t) * grad Rt Rs t s m := by
      simp only [grad]; field_simp; ring
    rw [hgr]
    ring
  rw [key, abs_mul]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hH0 : 0 ≤ H := P.hH.le
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) hG
  have hδ'0 : 0 ≤ δ' := le_trans (abs_nonneg _) hδ'
  have hA : |(s - t) * grad Rt Rs t s m + (m : ℝ) * (grad Rt Rs t s (m - 1) - Rt m)| ≤
      H * G + m * δ' := by
    calc _ ≤ |(s - t) * grad Rt Rs t s m| + |(m : ℝ) * (grad Rt Rs t s (m - 1) - Rt m)| :=
          abs_add_le _ _
      _ = |s - t| * |grad Rt Rs t s m| + (m : ℝ) * |grad Rt Rs t s (m - 1) - Rt m| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hm0]
      _ ≤ H * G + m * δ' := add_le_add (mul_le_mul P.gap_hi hG (abs_nonneg _) hH0)
          (mul_le_mul_of_nonneg_left hδ' hm0)
  calc |(s - t) * grad Rt Rs t s m + (m : ℝ) * (grad Rt Rs t s (m - 1) - Rt m)| * |c l 4|
      ≤ (H * G + m * δ') * K := mul_le_mul hA (hc 4) (abs_nonneg _) (by positivity)
    _ = K * (H * G + m * δ') := by ring

end PairData

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
