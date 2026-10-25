-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.NodeStep, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/NodeStep.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/NodeStep.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/NodeStep.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Combine
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Coarsen

set_option autoImplicit false

/-!
# The node step of the time tree, version 2

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `b03d2c4a`,
`Jets/NodeStep.lean` (updated to x0801's commit `ec0250f0`: scalar-bin width and jet precision
decoupled), for rows in `(ℝ²)^*`: the budget constants follow `Jets2/Combine.lean` (`4000 K⁶`
from the slab estimate, factors `2` from dot products) and `Jets2/Coarsen.lean` (`4800 K³`).

`NodeLists E F c D t R m w n`: at time `t`, with row sequence `R`, the jets `J_1, …, J_m` are
determined at width `w` by the `w`-bin of the scalar (up to `n` candidates) on `D`.

`coarsen_determined` turns a fine determination (precision `p` given the `q`-bin) into a coarse
one (precision `W` given the `W`-bin) outside a light set, using `coarsen_lists`.

`node_step` performs one pair of the time tree: from the lists of the two children (order `m`,
width `q`) it produces the lists of the parent (order `m + 1`, width `W`) with the new row
`g_m = (Rs m - Rt m)/(s - t)`, outside a light set.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The node invariant: the jets `J_1, …, J_m` at time `t` are determined within `δ` by the
`w`-bin of the scalar, up to `n` candidates, on `D`. -/
def NodeLists (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (c : Λ → Fin 7 → ℝ) (D : Set Λ) (t : ℝ)
    (R : ℕ → Fin 2 → ℝ) (m : ℕ) (w δ : ℝ) (n : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ m →
    Determined E (fun l => zS F (c l) t) D t w (fun l => jet R (c l) t j) δ n

theorem NodeLists.mono_set {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {c : Λ → Fin 7 → ℝ} {D D' : Set Λ}
    {t : ℝ} {R : ℕ → Fin 2 → ℝ} {m : ℕ} {w δ : ℝ} {n : ℕ} (h : NodeLists E F c D t R m w δ n)
    (hD : D' ⊆ D) : NodeLists E F c D' t R m w δ n :=
  fun j hj hjm => (h j hj hjm).mono_set hD

/-- From a determination to floor-bin lists. -/
theorem Determined.bins {E : Set (Λ × ℝ)} {S : Λ → ℝ} {D : Set Λ} {t q : ℝ} {J : Λ → ℝ}
    {p W : ℝ} {n : ℕ} (hW : 0 < W) (hp : 0 ≤ p) (h : Determined E S D t q J p n) :
    ∃ L : ℤ → Finset ℤ, (∀ σ, (L σ).card ≤ n * (⌊2 * p / W⌋₊ + 2)) ∧
      ∀ l ∈ D, (l, t) ∈ E → ⌊J l / W⌋ ∈ L ⌊S l / q⌋ := by
  classical
  obtain ⟨Y, hY, hmem⟩ := h
  let bins : ℝ → Finset ℤ := fun y => Finset.Icc ⌊(y - p) / W⌋ ⌊(y + p) / W⌋
  have hbins : ∀ y, (bins y).card ≤ ⌊2 * p / W⌋₊ + 2 := by
    intro y
    have := card_Icc_floor_le (y₀ := y) hW hp
    have h2 : (2 * p / W + 2 : ℝ) < (⌊2 * p / W⌋₊ + 2 : ℕ) + 1 := by
      push_cast; linarith [Nat.lt_floor_add_one (2 * p / W)]
    have : ((bins y).card : ℝ) < ((⌊2 * p / W⌋₊ + 2 : ℕ) : ℝ) + 1 := lt_of_le_of_lt this h2
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  refine ⟨fun σ => (Y σ).biUnion bins, fun σ => ?_, fun l hl hlt => ?_⟩
  · calc _ ≤ ∑ y ∈ Y σ, (bins y).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ Y σ, (⌊2 * p / W⌋₊ + 2) := Finset.sum_le_sum fun y _ => hbins y
      _ = (Y σ).card * (⌊2 * p / W⌋₊ + 2) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ n * (⌊2 * p / W⌋₊ + 2) := Nat.mul_le_mul_right _ (hY σ)
  · obtain ⟨y, hy, hd⟩ := hmem l hl hlt
    exact Finset.mem_biUnion.mpr ⟨y, hy, floor_mem_Icc_of_abs_le hW hd⟩

/-- From floor-bin lists to a determination at the bin width. -/
theorem determined_of_bins {E : Set (Λ × ℝ)} {S : Λ → ℝ} {D : Set Λ} {t r : ℝ} {J : Λ → ℝ}
    {W : ℝ} {n : ℕ} (hW : 0 < W) (L : ℤ → Finset ℤ) (hL : ∀ τ, (L τ).card ≤ n)
    (hmem : ∀ l ∈ D, (l, t) ∈ E → ⌊J l / W⌋ ∈ L ⌊S l / r⌋) :
    Determined E S D t r J W n := by
  classical
  refine ⟨fun τ => (L τ).image (fun v : ℤ => (v : ℝ) * W), fun τ => Finset.card_image_le.trans (hL τ),
    fun l hl hlt => ⟨⌊J l / W⌋ * W, Finset.mem_image.mpr ⟨_, hmem l hl hlt, rfl⟩, ?_⟩⟩
  have h1 := Int.floor_le (J l / W)
  have h2 := Int.lt_floor_add_one (J l / W)
  have h1' : (⌊J l / W⌋ : ℝ) * W ≤ J l := by
    have := mul_le_mul_of_nonneg_right h1 hW.le; rwa [div_mul_cancel₀ _ hW.ne'] at this
  have h2' : J l < (⌊J l / W⌋ : ℝ) * W + W := by
    have := mul_lt_mul_of_pos_right h2 hW; rw [div_mul_cancel₀ _ hW.ne'] at this; linarith
  rw [abs_le]; constructor <;> linarith

/-- **Coarsening a determination.**  From precision `p` given the `q`-bin, to precision `w` given
the `W`-bin, outside a light set (coefficient pieces at scale `W`). -/
theorem coarsen_determined {ν : Measure Λ} {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ}
    (hSN : ScalarNormal ν c E F piece K ζ d)
    {t q W w : ℝ} (hζq : ζ ≤ q) (hqW : q ≤ W) (hW1 : W ≤ 1) (hw : 0 < w) {D : Set Λ}
    {J : Λ → ℝ} {p : ℝ} {n : ℕ} (hp : 0 ≤ p) (h : Determined E (fun l => zS F (c l) t) D t q J p n)
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hJlip : ∀ l ∈ D, ∀ l' ∈ D, (l, t) ∈ E → (l', t) ∈ E → piece W l = piece W l' →
      |J l - J l'| ≤ CJ * W)
    (Kpop : ℝ) (hKpop : 0 < Kpop) :
    ∃ Good : Set Λ,
      ν {l | l ∈ D ∧ (l, t) ∈ E ∧ l ∉ Good} ≤
        ENNReal.ofReal (4800 * K ^ 3 * (CJ * W / w + 1) / Kpop) ∧
      Determined E (fun l => zS F (c l) t) (D ∩ Good) t W J w
        ⌊3 * K * ((n * (⌊2 * p / w⌋₊ + 2) : ℕ) : ℝ) * Kpop⌋₊ ∧
      (Measurable J → MeasurableSet Good) := by
  classical
  have hq : 0 < q := lt_of_lt_of_le hSN.zeta_pos hζq
  have hW : 0 < W := lt_of_lt_of_le hq hqW
  obtain ⟨Lf, hLf, hLmem⟩ := h.bins hw hp
  obtain ⟨Lc, hLc, hbad⟩ := coarsen_lists hSN t q W w hζq hqW hW1 hw D J Lf _ hLf hLmem CJ hCJ
    hJlip Kpop hKpop
  refine ⟨{l | (l, t) ∈ E → ⌊J l / w⌋ ∈ Lc ⌊zS F (c l) t / W⌋}, ?_, ?_, ?_⟩
  · refine (measure_mono ?_).trans hbad
    rintro l ⟨hl, hlt, hnot⟩
    exact ⟨hl, hlt, fun hmem => hnot fun _ => hmem⟩
  · refine determined_of_bins hw Lc (fun τ => ?_) (fun l hl hlt => hl.2 hlt)
    exact Nat.le_floor (hLc τ)
  · intro hJ
    have hS : Measurable (fun l => zS F (c l) t) := by
      have hc := hSN.measurable_c
      have hcomp : ∀ e : Fin 7, Measurable (fun l => c l e) :=
        fun e => (measurable_pi_apply e).comp hc
      have h0 := hcomp 0; have h1 := hcomp 1; have h2 := hcomp 2; have h3 := hcomp 3
      have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
      simp only [zS, zx, dot_two, zy_zero, zy_one]
      fun_prop
    have hsec : MeasurableSet {l : Λ | (l, t) ∈ E} := measurable_prodMk_right hSN.measurableSet_E
    have hfl1 : Measurable (fun l => ⌊J l / w⌋) := Int.measurable_floor.comp (hJ.div_const w)
    have hfl2 : Measurable (fun l => ⌊zS F (c l) t / W⌋) :=
      Int.measurable_floor.comp (hS.div_const W)
    have hpair : Measurable (fun l => (⌊J l / w⌋, ⌊zS F (c l) t / W⌋)) := hfl1.prodMk hfl2
    have hset : MeasurableSet {l : Λ | ⌊J l / w⌋ ∈ Lc ⌊zS F (c l) t / W⌋} :=
      hpair (MeasurableSet.of_discrete (s := {z : ℤ × ℤ | z.1 ∈ Lc z.2}))
    have : {l | (l, t) ∈ E → ⌊J l / w⌋ ∈ Lc ⌊zS F (c l) t / W⌋} =
        {l : Λ | (l, t) ∈ E}ᶜ ∪ {l : Λ | ⌊J l / w⌋ ∈ Lc ⌊zS F (c l) t / W⌋} := by
      ext l; simp only [mem_ofPred_eq, mem_union, mem_compl_iff]; tauto
    rw [this]
    exact hsec.compl.union hset

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set

noncomputable section

open PairData

variable {Λ : Type*} [MeasurableSpace Λ]

theorem nGrad_mono {nL : ℕ} {q δ1 δ1' : ℝ} (hq : 0 < q) (h : δ1 ≤ δ1') :
    nGrad nL q δ1 ≤ nGrad nL q δ1' := by
  unfold nGrad
  have : ⌊2 * δ1 / q⌋₊ ≤ ⌊2 * δ1' / q⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hq.le)
  gcongr

theorem le_nGrad {nL : ℕ} {q δ1 : ℝ} (hn : 1 ≤ nL) : nL ≤ nGrad nL q δ1 := by
  unfold nGrad
  calc nL = nL * 1 * 1 := by ring
    _ ≤ nL * ((1 * nL) * (⌊2 * δ1 / q⌋₊ + 2)) * nL := by
        gcongr
        · calc 1 ≤ 1 * 2 := by norm_num
            _ ≤ (1 * nL) * (⌊2 * δ1 / q⌋₊ + 2) := by gcongr <;> omega

/-- The thresholds of one pair: children read at scalar width `q` with jet precision `δL`, the
parent reads at scalar width `W` with jet precision `w`; `CJ` bounds the coefficient-Lipschitz
constant of the parent jets. -/
structure PairBudget (K ζ BR H Kg eT q δL W w mD CJ : ℝ) (nL m : ℕ) (Lam δc : ℕ → ℝ) : Prop where
  hζq : ζ ≤ q
  hqW : q ≤ W
  hW1 : W ≤ 1
  hnL : 1 ≤ nL
  hδL : 0 ≤ δL
  hw : 0 < w
  b0 : BR + eT * Kg / H ≤ Lam 0
  bpos : ∀ j, 0 < Lam j
  b1 : ∀ j, 1 ≤ j → j ≤ m →
    4000 * K ^ 6 * (nGrad nL q (q + H * δL + errS K BR H eT) : ℝ) *
      ((2 * δL * Kg / H + (3 * K + 2 * BR * K + 2 * j * Lam (j - 1) * K)) / Lam j + q) < mD
  c0 : eT * Kg / H ≤ δc 0
  cpos : ∀ j, 0 < δc j
  c1 : ∀ j, 1 ≤ j → j + 1 ≤ m →
    4000 * K ^ 6 * ((nGrad nL q (q + H * δL + errS K BR H eT) * nL : ℕ) : ℝ) *
      ((2 * δL * Kg / H + δL + 2 * K * (H * Lam j + j * δc (j - 1))) / δc j + q) < mD
  newP : 2 * δL * Kg / H + 2 * K * (H * Lam m + m * δc (m - 1)) ≤ w
  oldP : δL ≤ w
  hCJ : 3 + 4 * max BR (Lam m) + 2 * (m + 1) * max BR (Lam m) ≤ CJ
  hwCJ : CJ * W ≤ w

namespace PairData

variable {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
  {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ} {D : Set Λ}
  {t s H Kg : ℝ} {Rt Rs : ℕ → Fin 2 → ℝ} {BR eT : ℝ}

theorem abs_grad_zero_sub_le (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT) :
    ‖grad Rt Rs t s 0 - Rt 1‖ ≤ eT * Kg / H := by
  have hΔ := P.delta_pos
  have hH := P.hH
  have hKg : 0 < Kg := by linarith [P.hKg]
  have e : grad Rt Rs t s 0 - Rt 1 = (s - t)⁻¹ • (F s - F t - (s - t) • Rt 1) := by
    rw [smul_sub (s - t)⁻¹ (F s - F t) ((s - t) • Rt 1), smul_smul,
      inv_mul_cancel₀ P.delta_ne, one_smul]
    simp only [grad, P.Rt0, P.Rs0]
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv]
  have heT : 0 ≤ eT := P.eT_nonneg
  calc |s - t|⁻¹ * ‖F s - F t - (s - t) • Rt 1‖ ≤ |s - t|⁻¹ * eT :=
        mul_le_mul_of_nonneg_left P.taylor (by positivity)
    _ = eT / |s - t| := by field_simp
    _ ≤ eT / (H / Kg) := div_le_div_of_nonneg_left heT (by positivity) P.gap_lo
    _ = eT * Kg / H := by field_simp

/-- The bounds on the divided row differences and compatibility, from the budget. -/
theorem grad_compat_bounds (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL W w mD CJ : ℝ} {nL m : ℕ} {Lam δc : ℕ → ℝ}
    (B : PairBudget K ζ BR H Kg eT q δL W w mD CJ nL m Lam δc) (hm : 1 ≤ m)
    (hmass : ENNReal.ofReal mD ≤ ν D)
    (hL : NodeLists E F c D t Rt m q δL nL) (hLs : NodeLists E F c D s Rs m q δL nL) :
    (∀ j, j ≤ m → ‖grad Rt Rs t s j‖ ≤ Lam j) ∧
      (∀ j, j + 1 ≤ m → ‖grad Rt Rs t s j - Rt (j + 1)‖ ≤ δc j) := by
  have hq : 0 < q := lt_of_lt_of_le P.hSN.zeta_pos B.hζq
  have hq1 : q ≤ 1 := B.hqW.trans B.hW1
  have hK := P.K_nonneg
  have hBR := P.BR_nonneg
  have hΔ := P.delta_pos
  have hH := P.hH
  have hKg1 := P.hKg
  have hKg : 0 < Kg := by linarith
  have hδL := B.hδL
  have hΔH : |s - t| * δL ≤ H * δL := mul_le_mul_of_nonneg_right P.gap_hi hδL
  have hnG := nGrad_mono (nL := nL) hq
    (show q + |s - t| * δL + errS K BR H eT ≤ q + H * δL + errS K BR H eT by linarith)
  have hqΔ : (δL + δL) / |s - t| ≤ 2 * δL * Kg / H := by
    rw [div_le_div_iff₀ hΔ hH]
    have := P.gap_lo
    rw [div_le_iff₀ hKg] at this
    nlinarith
  have hJ1 := hL 1 le_rfl hm
  -- the divided differences
  have hgrad : ∀ j, j ≤ m → ‖grad Rt Rs t s j‖ ≤ Lam j := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 := P.abs_grad_zero_sub_le
      calc ‖grad Rt Rs t s 0‖ = ‖(grad Rt Rs t s 0 - Rt 1) + Rt 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖grad Rt Rs t s 0 - Rt 1‖ + ‖Rt 1‖ := norm_add_le _ _
        _ ≤ eT * Kg / H + BR := add_le_add h0 (P.Rt_le 1)
        _ ≤ Lam 0 := by linarith [B.b0]
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      refine (P.grad_lt (j := j + 1) (by omega) B.hζq hq1 hδL hJ1 (hL (j + 1) (by omega) hj)
        (hLs (j + 1) (by omega) hj) (by simpa using hprev) (B.bpos _) hmass ?_).le
      have hb := B.b1 (j + 1) (by omega) hj
      simp only [Nat.add_sub_cancel] at hb ⊢
      refine lt_of_le_of_lt ?_ hb
      have hΛ := B.bpos (j + 1)
      have hΛj := B.bpos j
      gcongr
  refine ⟨hgrad, ?_⟩
  -- compatibility
  intro j
  induction j with
  | zero => intro _; exact P.abs_grad_zero_sub_le.trans B.c0
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    refine (P.compat_lt (j := j + 1) (by omega) B.hζq hq1 hδL hJ1
      (hL (j + 1) (by omega) (by omega)) (hLs (j + 1) (by omega) (by omega))
      (hL (j + 1 + 1) (by omega) hj) (hgrad (j + 1) (by omega)) (by simpa using hprev)
      (B.cpos _) hmass ?_).le
    have hb := B.c1 (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at hb ⊢
    refine lt_of_le_of_lt ?_ hb
    have hδ := B.cpos (j + 1)
    have hδj := B.cpos j
    have hΛ := B.bpos (j + 1)
    have hnG' : ((nGrad nL q (q + |s - t| * δL + errS K BR H eT) * nL : ℕ) : ℝ) ≤
        ((nGrad nL q (q + H * δL + errS K BR H eT) * nL : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right _ hnG
    gcongr

/-- **The node step.** -/
theorem node_step (P : PairData ν c E F piece K ζ d D t s H Kg Rt Rs BR eT)
    {q δL W w mD CJ : ℝ} {nL m : ℕ} {Lam δc : ℕ → ℝ}
    (B : PairBudget K ζ BR H Kg eT q δL W w mD CJ nL m Lam δc) (hm : 1 ≤ m)
    (hmass : ENNReal.ofReal mD ≤ ν D)
    (hL : NodeLists E F c D t Rt m q δL nL) (hLs : NodeLists E F c D s Rs m q δL nL)
    (Kpop : ℝ) (hKpop : 0 < Kpop) :
    (∀ i, ‖Function.update Rt (m + 1) (grad Rt Rs t s m) i‖ ≤ max BR (Lam m)) ∧
    ∃ D' ⊆ D, ν (D \ D') ≤ ENNReal.ofReal ((m + 1) * (9600 * K ^ 3 / Kpop)) ∧
      NodeLists E F c D' t (Function.update Rt (m + 1) (grad Rt Rs t s m)) (m + 1) W w
        ⌊3 * K * ((4 * nGrad nL q (q + H * δL + errS K BR H eT) : ℕ) : ℝ) * Kpop⌋₊ ∧
      (MeasurableSet D → MeasurableSet D') := by
  classical
  have hq : 0 < q := lt_of_lt_of_le P.hSN.zeta_pos B.hζq
  have hW : 0 < W := lt_of_lt_of_le hq B.hqW
  have hζW : ζ ≤ W := B.hζq.trans B.hqW
  have hK := P.K_nonneg
  have hBR := P.BR_nonneg
  have hΔ := P.delta_pos
  have hH := P.hH
  have hKg : 0 < Kg := by linarith [P.hKg]
  have hδL := B.hδL
  have hw := B.hw
  obtain ⟨hgrad, hcompat⟩ := P.grad_compat_bounds B hm hmass hL hLs
  set R' := Function.update Rt (m + 1) (grad Rt Rs t s m) with hR'
  set BB := max BR (Lam m)
  have hBB : 0 ≤ BB := le_trans hBR (le_max_left _ _)
  have hR'le : ∀ i, ‖R' i‖ ≤ BB := by
    intro i
    by_cases hi : i = m + 1
    · subst hi; simp only [hR', Function.update_self]
      exact (hgrad m le_rfl).trans (le_max_right _ _)
    · simp only [hR', Function.update_of_ne hi]
      exact (P.Rt_le i).trans (le_max_left _ _)
  refine ⟨hR'le, ?_⟩
  have hR'eq : ∀ j, j ≤ m → ∀ cl, jet R' cl t j = jet Rt cl t j := by
    intro j hj cl
    simp only [jet, hR']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  -- the new jet
  have hJ1 := hL 1 le_rfl hm
  have hcm : ‖grad Rt Rs t s (m - 1) - Rt m‖ ≤ δc (m - 1) := by
    have := hcompat (m - 1) (by omega)
    rwa [Nat.sub_add_cancel hm] at this
  have hnew := P.new_jet hm hq hδL hJ1 (hL m hm le_rfl) (hLs m hm le_rfl) (hgrad m le_rfl) hcm
  set nG := nGrad nL q (q + H * δL + errS K BR H eT)
  have hnGact : nGrad nL q (q + |s - t| * δL + errS K BR H eT) ≤ nG :=
    nGrad_mono hq (by linarith [mul_le_mul_of_nonneg_right P.gap_hi hδL])
  have hqΔ : (δL + δL) / |s - t| ≤ 2 * δL * Kg / H := by
    rw [div_le_div_iff₀ hΔ hH]
    have := P.gap_lo
    rw [div_le_iff₀ hKg] at this
    nlinarith
  set Pn := (δL + δL) / |s - t| + 2 * K * (H * Lam m + m * δc (m - 1))
  have hPn : Pn ≤ w := le_trans (by simp only [Pn]; linarith) B.newP
  have hPn0 : 0 ≤ Pn := by
    have := B.bpos m; have := B.cpos (m - 1); simp only [Pn]; positivity
  -- the determinations to coarsen, for every `j ≤ m + 1`
  have hdet : ∀ j, 1 ≤ j → j ≤ m + 1 → ∃ (p : ℝ) (n : ℕ), 0 ≤ p ∧ p ≤ w ∧ n ≤ nG ∧
      Determined E (fun l => zS F (c l) t) D t q (fun l => jet R' (c l) t j) p n := by
    intro j hj1 hj2
    by_cases hjm : j ≤ m
    · refine ⟨δL, nL, hδL, B.oldP, le_nGrad B.hnL, ?_⟩
      exact (hL j hj1 hjm).congr fun l _ _ => (hR'eq j hjm (c l)).symm
    · have hj : j = m + 1 := by omega
      subst hj
      exact ⟨Pn, _, hPn0, hPn, hnGact, hnew⟩
  choose! pj nj hpj0 hpjW hnj hdetj using hdet
  have hCJ0 : 0 ≤ CJ := le_trans (by positivity) B.hCJ
  have hgood : ∀ j, 1 ≤ j → j ≤ m + 1 → ∃ Good : Set Λ,
      ν {l | l ∈ D ∧ (l, t) ∈ E ∧ l ∉ Good} ≤ ENNReal.ofReal (9600 * K ^ 3 / Kpop) ∧
      Determined E (fun l => zS F (c l) t) (D ∩ Good) t W (fun l => jet R' (c l) t j) w
        ⌊3 * K * ((4 * nG : ℕ) : ℝ) * Kpop⌋₊ ∧ MeasurableSet Good := by
    intro j hj1 hj2
    have hlip : ∀ l ∈ D, ∀ l' ∈ D, (l, t) ∈ E → (l', t) ∈ E → piece W l = piece W l' →
        |jet R' (c l) t j - jet R' (c l') t j| ≤ CJ * W := by
      intro l _ l' _ _ _ hpc
      have hdiam := P.hSN.piece_diam W hζW B.hW1 l l' hpc
      have := abs_jet_sub_le (R := R') (j := j) P.ht hR'le hdiam
      calc |jet R' (c l) t j - jet R' (c l') t j| ≤ (3 + 4 * BB + 2 * j * BB) * W := this
        _ ≤ CJ * W := by
            gcongr
            calc 3 + 4 * BB + 2 * (j : ℝ) * BB ≤ 3 + 4 * BB + 2 * (m + 1) * BB := by
                  gcongr; exact_mod_cast hj2
              _ ≤ CJ := B.hCJ
    obtain ⟨Good, hbad, hD, hmeas⟩ := coarsen_determined P.hSN B.hζq B.hqW B.hW1 hw
      (hpj0 j hj1 hj2) (hdetj j hj1 hj2) CJ hCJ0 hlip Kpop hKpop
    refine ⟨Good, hbad.trans (ENNReal.ofReal_le_ofReal ?_), hD.mono le_rfl (Nat.floor_mono ?_),
      hmeas (measurable_jet P.hSN.measurable_c R' t j)⟩
    · have : CJ * W / w ≤ 1 := (div_le_one hw).mpr B.hwCJ
      have hK3 : 0 ≤ 4800 * K ^ 3 / Kpop := by positivity
      calc 4800 * K ^ 3 * (CJ * W / w + 1) / Kpop = 4800 * K ^ 3 / Kpop * (CJ * W / w + 1) := by
            ring
        _ ≤ 4800 * K ^ 3 / Kpop * 2 := by gcongr; linarith
        _ = 9600 * K ^ 3 / Kpop := by ring
    · have hcount : (nj j * (⌊2 * pj j / w⌋₊ + 2) : ℕ) ≤ 4 * nG := by
        have hfl : ⌊2 * pj j / w⌋₊ ≤ 2 := by
          apply Nat.floor_le_of_le
          rw [div_le_iff₀ hw]; push_cast; linarith [hpjW j hj1 hj2]
        calc nj j * (⌊2 * pj j / w⌋₊ + 2) ≤ nG * (2 + 2) :=
              Nat.mul_le_mul (hnj j hj1 hj2) (by omega)
          _ = 4 * nG := by ring
      have : ((nj j * (⌊2 * pj j / w⌋₊ + 2) : ℕ) : ℝ) ≤ ((4 * nG : ℕ) : ℝ) := by
        exact_mod_cast hcount
      gcongr
  choose! Good hGbad hGdet hGmeas using hgood
  set I := Finset.Icc 1 (m + 1)
  refine ⟨D ∩ ⋂ j ∈ I, Good j, inter_subset_left, ?_, ?_, ?_⟩
  · -- the loss
    have hsub : D \ (D ∩ ⋂ j ∈ I, Good j) ⊆
        ⋃ j ∈ I, {l | l ∈ D ∧ (l, t) ∈ E ∧ l ∉ Good j} := by
      intro l ⟨hl, hnot⟩
      have : l ∉ ⋂ j ∈ I, Good j := fun h => hnot ⟨hl, h⟩
      simp only [mem_iInter, not_forall] at this
      obtain ⟨j, hj, hnj⟩ := this
      exact mem_iUnion₂.mpr ⟨j, hj, hl, (P.lab l hl).1, hnj⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc ∑ j ∈ I, ν {l | l ∈ D ∧ (l, t) ∈ E ∧ l ∉ Good j}
        ≤ ∑ _j ∈ I, ENNReal.ofReal (9600 * K ^ 3 / Kpop) :=
          Finset.sum_le_sum fun j hj => by
            obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj; exact hGbad j hj1 hj2
      _ = ENNReal.ofReal ((m + 1) * (9600 * K ^ 3 / Kpop)) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
            show (m + 1 + 1 - 1 : ℕ) = m + 1 by omega,
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (m:ℝ) + 1)]
          congr 1
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  · intro j hj1 hj2
    refine (hGdet j hj1 hj2).mono_set ?_
    intro l ⟨hl, hlG⟩
    exact ⟨hl, mem_iInter₂.mp hlG j (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)⟩
  · intro hD
    exact hD.inter (Finset.measurableSet_biInter _ fun j hj => by
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj; exact hGmeas j hj1 hj2)

end PairData

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
