-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepStruct.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 3be7d21a,
-- Submission/Obl/k4_terminal_time_extension/PrepStruct.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepHyp
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.Extrapolation
import Submission.Obl.k4_terminal_label_saturation.SatFormat
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat
import Submission.Lib.K4QuadraticSheets.QuadTest

/-!
# Structural fields of a tested sample

The source sets (format, whole-block confinement in the frame, base bounds), their
disjointness, the equations, the lists, and the pair masks with their tests (`tst`)
for the objects of `PrepDefs`.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MeasureTheory Set MvPolynomial Submission.Lib.K4VelocityStrips
open Submission.Obl.k4_terminal_label_saturation (fmt_of_atoms)

namespace PrepData

variable {D : PrepData} {N : ℝ} {M₀ D₀ : ℕ} {L : ℝ} {E : Fin D.W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}

/-! ### Source incidences -/

theorem Sb_sub (b : Fin D.C) : D.Sb b ⊆ D.F b := inter_subset_left

theorem Hyp.Sb_meas (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) : MeasurableSet (D.Sb b) :=
  (h.Fmeas b).inter (measurableSet_lt measurable_snd measurable_const)

/-- An old block lies in its coarse block. -/
theorem old_sub_blk (j : Fin (2 ^ (D.T + D.s))) :
    Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ (D.T + D.s)) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)) ⊆
      D.blk (coarseIdx j) := by
  obtain ⟨h1, h2⟩ := coarseIdx_bounds j
  intro t ht
  exact ⟨h1.trans ht.1, ht.2.trans h2⟩

theorem blk_meas (J₀ : Fin (2 ^ D.T)) : MeasurableSet (D.blk J₀) := measurableSet_Icc

theorem blk_sub_unit (J₀ : Fin (2 ^ D.T)) : D.blk J₀ ⊆ Icc 0 1 := by
  intro t ht
  have hpos : (0 : ℝ) < 2 ^ D.T := by positivity
  refine ⟨le_trans (by positivity) ht.1, ht.2.trans ?_⟩
  rw [div_le_one hpos]
  have : (J₀ : ℕ) + 1 ≤ 2 ^ D.T := J₀.isLt
  exact_mod_cast this

/-- The time of a source incidence. -/
theorem Hyp.Sb_time (h : D.Hyp N M₀ D₀ L E) {b : Fin D.C} {p : (ℕ × (Fin 6 → ℝ)) × ℝ}
    (hp : p ∈ D.Sb b) :
    ((D.j b : ℕ) : ℝ) / (2 : ℝ) ^ (D.T + D.s) ≤ p.2 ∧
      p.2 < (((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s) :=
  ⟨(h.sel b hp.1).2.2.1.1, hp.2⟩

/-- Format of the source incidences. -/
theorem Hyp.Sb_fmt (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) (i : ℕ) :
    fmt 7 (N ^ M₀ + 1) (max D₀ 1)
      {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ D.Sb b} := by
  have h1 := h.fmtF b i
  have h2 : fmt 7 1 1 {r : Fin 7 → ℝ | r 6 < (((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)} := by
    have := fmt_of_atoms (n := 7) (D := 1) (ι := Unit)
      (fun _ => MvPolynomial.X 6 - MvPolynomial.C ((((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)))
      (fun _ => by
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · simp [totalDegree_X]
        · simp)
      (fun v => !(v ()))
      {r : Fin 7 → ℝ | r 6 < (((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)}
      (fun z => by
        simp only [mem_ofPred_eq, map_sub, eval_X, eval_C, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, not_le, sub_neg])
    simpa [fmt, Submission.Obl.k4_terminal_label_saturation.fmt] using this
  have := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter h1 h2
  have e : {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ D.Sb b} =
      {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ D.F b} ∩
        {r : Fin 7 → ℝ | r 6 < (((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)} := by
    ext r
    simp [Sb]
  rw [e]
  exact this

/-- Source incidences of different charts of one world and coarse block are disjoint. -/
theorem Hyp.Sb_disjoint (h : D.Hyp N M₀ D₀ L E) {b b' : Fin D.C} (hne : b ≠ b')
    (hγ : D.γ b = D.γ b') : Disjoint (D.Sb b) (D.Sb b') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  by_cases hj : D.j b = D.j b'
  · exact Set.disjoint_left.mp (h.disj b b' hne hγ hj) (h.sel b hp.1).2.1 (h.sel b' hp'.1).2.1
  · obtain ⟨a1, a2⟩ := h.Sb_time hp
    obtain ⟨c1, c2⟩ := h.Sb_time hp'
    have hpos : (0 : ℝ) < 2 ^ (D.T + D.s) := by positivity
    rw [div_le_iff₀ hpos] at a1 c1
    rw [lt_div_iff₀ hpos] at a2 c2
    apply hj
    apply Fin.ext
    have e1 : ((D.j b : ℕ) : ℝ) < ((D.j b' : ℕ) : ℝ) + 1 := by nlinarith
    have e2 : ((D.j b' : ℕ) : ℝ) < ((D.j b : ℕ) : ℝ) + 1 := by nlinarith
    have f1 : (D.j b : ℕ) < (D.j b' : ℕ) + 1 := by exact_mod_cast e1
    have f2 : (D.j b' : ℕ) < (D.j b : ℕ) + 1 := by exact_mod_cast e2
    omega

/-! ### Frames of source entries -/

theorem fγ_of_src {i : Fin D.J} {b : Fin D.C} (hi : D.key i = D.src b) : D.fγ i = D.γ b := by
  rw [fγ, hi]; rfl

theorem fj_of_src {i : Fin D.J} {b : Fin D.C} (hi : D.key i = D.src b) :
    D.fj i = coarseIdx (D.j b) := by
  rw [fj, hi]; rfl

theorem fc_of_src {i : Fin D.J} {b : Fin D.C} (hi : D.key i = D.src b) :
    D.fc i = keyC D.g D.S₁ D.S₂ (D.src b) := by rw [fc, hi]

theorem fu_of_src {i : Fin D.J} {b : Fin D.C} (hi : D.key i = D.src b) :
    D.fu i = keyU D.g D.S₁ D.S₂ (D.src b) := by rw [fu, hi]

theorem fQ_of_src {i : Fin D.J} {b : Fin D.C} (hi : D.key i = D.src b) :
    D.fQ i = keyQ D.g D.S₁ D.S₂ D.Afr (D.src b) := by rw [fQ, hi]

/-- Whole-block confinement of a trajectory of the source chart in the frame of a source
entry. -/
theorem Hyp.conf_src (h : D.Hyp N M₀ D₀ L E) {i : Fin D.J} {b : Fin D.C}
    (hi : D.key i = D.src b) {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ D.A b) {t : ℝ}
    (ht : t ∈ D.blk (D.fj i)) :
    ‖Matrix.toEuclideanLin (D.fQ i)⁻¹ (y l t - D.fc i - t • D.fu i)‖ ≤ 2 := by
  rw [fQ_of_src hi, fc_of_src hi, fu_of_src hi]
  rw [fj_of_src hi] at ht
  exact h.frame_conf b hl ht

/-- **The source sets.** -/
theorem Hyp.S_props (h : D.Hyp N M₀ D₀ L E) {κ : ℝ} (hκ : 2 ≤ κ) (s : Fin D.m) :
    MeasurableSet (D.S s) ∧
    (∀ i : ℕ, fmt 7 (N ^ M₀ + 1) (max D₀ 1)
      {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ D.S s}) ∧
    ∀ p ∈ D.S s, p ∈ E (D.fγ (D.frame s)) ∧ (p.1.1 : ℝ) ≤ N ^ M₀ ∧
      (∀ d, |p.1.2 d| ≤ N ^ M₀) ∧ p.2 ∈ D.blk (D.fj (D.frame s)) ∧
      ∀ t ∈ D.blk (D.fj (D.frame s)),
        ‖Matrix.toEuclideanLin (D.fQ (D.frame s))⁻¹
          (y p.1 t - D.fc (D.frame s) - t • D.fu (D.frame s))‖ ≤ κ ∧
        |D.B (D.fγ (D.frame s)) * (x p.1 t) 3| ≤ D.B (D.fγ (D.frame s)) * (2 * N ^ M₀) ∧
        ‖base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.fc (D.frame s)) (D.fu (D.frame s))
          (D.fQ (D.frame s)) p.1 t‖ ≤ 1 / 8 ∧
        ∀ t' ∈ D.blk (D.fj (D.frame s)),
          ‖base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.fc (D.frame s)) (D.fu (D.frame s))
              (D.fQ (D.frame s)) p.1 t -
            base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.fc (D.frame s)) (D.fu (D.frame s))
              (D.fQ (D.frame s)) p.1 t'‖ ≤ (2 : ℝ) ^ D.T * |t - t'| := by
  classical
  by_cases hsrc : D.key (D.frame s) = D.src (D.chartOf s)
  · have hS : D.S s = D.Sb (D.chartOf s) := by simp [S, hsrc]
    set b := D.chartOf s with hb
    rw [hS]
    refine ⟨h.Sb_meas b, fun i => h.Sb_fmt b i, ?_⟩
    intro p hp
    obtain ⟨hpE, hpA, hpt, -⟩ := h.sel b hp.1
    obtain ⟨hl1, hl2, -⟩ := h.whole b hpA
    have hconf : ∀ t ∈ D.blk (D.fj (D.frame s)),
        ‖Matrix.toEuclideanLin (D.fQ (D.frame s))⁻¹
          (y p.1 t - D.fc (D.frame s) - t • D.fu (D.frame s))‖ ≤ κ :=
      fun t ht => (h.conf_src hsrc hpA ht).trans (by linarith)
    have hκ1 : 1 ≤ κ := by linarith
    refine ⟨?_, hl1, hl2, ?_, ?_⟩
    · rw [fγ_of_src hsrc]; exact hpE
    · rw [fj_of_src hsrc]; exact old_sub_blk _ hpt
    · intro t ht
      refine ⟨hconf t ht, ?_, base_norm_le hκ1 ht (hconf t ht), ?_⟩
      · have hB := (h.Bpos (D.fγ (D.frame s))).le
        rw [abs_mul, abs_of_nonneg hB]
        apply mul_le_mul_of_nonneg_left _ hB
        have ht01 := blk_sub_unit _ ht
        have h2 := hl2 2
        have h5 := hl2 5
        simp only [x, Matrix.cons_val_three, Matrix.cons_val_two, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons]
        calc |p.1.2 2 + t * p.1.2 5| ≤ |p.1.2 2| + |t| * |p.1.2 5| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ N ^ M₀ + 1 * N ^ M₀ := by
              have : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht01.1, ht01.2]
              gcongr
          _ = 2 * N ^ M₀ := by ring
      · intro t' _
        have hpos : (0 : ℝ) < 2 ^ D.T := by positivity
        have hlo : ((D.fj (D.frame s) : ℕ) : ℝ) / (2 : ℝ) ^ D.T ∈ D.blk (D.fj (D.frame s)) :=
          ⟨le_rfl, by gcongr; linarith⟩
        have hhi : (((D.fj (D.frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T ∈
            D.blk (D.fj (D.frame s)) := ⟨by gcongr; linarith, le_rfl⟩
        exact base_lipschitz hκ1 (hconf _ hlo) (hconf _ hhi) t t'
  · have hS : D.S s = ∅ := by simp [S, hsrc]
    rw [hS]
    refine ⟨MeasurableSet.empty, fun i => ?_, fun p hp => absurd hp (Set.notMem_empty p)⟩
    have := fmt_of_atoms (n := 7) (D := max D₀ 1) (ι := Empty) (fun e => e.elim)
      (fun e => e.elim) (fun _ => false) {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ (∅ : Set _)}
      (fun z => by simp)
    refine Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono this ?_ le_rfl
    simp only [Fintype.card_eq_zero, Nat.cast_zero]
    have := h.N2
    positivity

/-- **Disjointness of the source sets.** -/
theorem Hyp.S_disj (h : D.Hyp N M₀ D₀ L E) (s s' : Fin D.m) (hne : s ≠ s')
    (hγ : D.fγ (D.frame s) = D.fγ (D.frame s')) : Disjoint (D.S s) (D.S s') := by
  classical
  by_cases h1 : D.key (D.frame s) = D.src (D.chartOf s)
  · by_cases h2 : D.key (D.frame s') = D.src (D.chartOf s')
    · have hS : D.S s = D.Sb (D.chartOf s) := by simp [S, h1]
      have hS' : D.S s' = D.Sb (D.chartOf s') := by simp [S, h2]
      rw [hS, hS']
      have hb : D.chartOf s ≠ D.chartOf s' := by
        intro hc
        apply hne
        rw [D.eq_srcEnt h1, D.eq_srcEnt h2, hc]
      apply h.Sb_disjoint hb
      rw [← fγ_of_src h1, ← fγ_of_src h2, hγ]
    · have hS' : D.S s' = ∅ := by simp [S, h2]
      rw [hS']; exact disjoint_empty _
  · have hS : D.S s = ∅ := by simp [S, h1]
    rw [hS]; exact empty_disjoint _

/-! ### Equations -/

/-- **The equations.** -/
theorem Hyp.P_props (h : D.Hyp N M₀ D₀ L E) (κ : ℝ) (s : Fin D.m) :
    (D.P κ s).totalDegree ≤ 2 ∧ ∀ d, |(D.P κ s).coeff d| ≤
      81 * N ^ M₀ * physScale D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.B (D.fγ (D.frame s)))
        (D.fc (D.frame s)) (D.fu (D.frame s)) (D.fQ (D.frame s)) ^ 2 :=
  ⟨(totalDegree_transport_le _ _ _ _ _ _ _ _).trans (h.Rdeg _),
    abs_coeff_transport_le _ _ _ _ _ _ _ _ (h.Rdeg _) (h.Rcoeff _)⟩

/-- A bound on the substitution scale of a frame. -/
theorem physScale_le {T : ℕ} {j κ B : ℝ} (hj0 : 0 ≤ j) (hj : j + 1 ≤ 2 ^ T) (hκ : 0 ≤ κ)
    (hB : 0 < B) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    physScale T j κ B c u Q ≤
      1 + (1 + 100 * κ) * (1 + 2 * (‖c‖ + ‖u‖)) + 2 * (‖c‖ + ‖u‖) +
        100 * κ * (∑ i : Fin 2, ∑ i' : Fin 2, |Q i i'|) + B⁻¹ := by
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  have h1 : |(j + 1 / 2) / (2 : ℝ) ^ T| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hpos]; linarith
  have hpT : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  have h2 : |100 * κ / (2 : ℝ) ^ T| ≤ 100 * κ := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self (by positivity) hpT
  have hu0 := abs_coord_le_norm u 0
  have hu1 := abs_coord_le_norm u 1
  have hc0 := abs_coord_le_norm c 0
  have hc1 := abs_coord_le_norm c 1
  have hQ : |Q 0 0| + |Q 0 1| + |Q 1 0| + |Q 1 1| = ∑ i : Fin 2, ∑ i' : Fin 2, |Q i i'| := by
    simp [Fin.sum_univ_two]; ring
  unfold physScale
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 100 * κ), abs_of_pos (inv_pos.mpr hB), hQ]
  have hcn := norm_nonneg c
  have hun := norm_nonneg u
  have hsum : 0 ≤ ∑ i : Fin 2, ∑ i' : Fin 2, |Q i i'| := by positivity
  have e1 : (|(j + 1 / 2) / (2 : ℝ) ^ T| + |100 * κ / (2 : ℝ) ^ T|) * (1 + |u 0| + |u 1|) ≤
      (1 + 100 * κ) * (1 + 2 * (‖c‖ + ‖u‖)) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  linarith

/-! ### Lists -/

theorem card_charts_le (b : Fin D.C) :
    (Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b)).card ≤
      98 * (2 * D.Kb + 1) ^ 4 + 1 := by
  classical
  have hinj : Set.InjOn (fun s : Fin D.m => D.key (D.frame s))
      (Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b) : Set (Fin D.m)) := by
    intro s hs s' hs' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at hs hs'
    apply D.ent_injective
    have hf : D.frame s = D.frame s' := D.key_injective heq
    exact Prod.ext (by rw [← chartOf, ← chartOf, hs, hs']) hf
  have hmaps : ∀ s ∈ Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b),
      D.key (D.frame s) ∈ D.compat b := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [← hs]; exact D.key_frame_mem_compat s
  calc (Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b)).card
      ≤ (D.compat b).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ (compatKeys D.γ D.j D.c D.u D.Qf D.g D.S₁ D.S₂ D.Kb b).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ 98 * (2 * D.Kb + 1) ^ 4 + 1 := by
        have := compatKeys_card_le D.γ D.j D.c D.u D.Qf D.g D.S₁ D.S₂ D.Kb b
        omega

/-- **List sizes.** -/
theorem lst'_card_le (γ₀ : Fin D.W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    (D.lst' γ₀ o).card ≤ (D.lst γ₀ o).card * (98 * (2 * D.Kb + 1) ^ 4 + 1) := by
  classical
  unfold lst'
  have hsub : Finset.univ.filter (fun s => D.chartOf s ∈ D.lst γ₀ o) ⊆
      (D.lst γ₀ o).biUnion (fun b => Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b)) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨D.chartOf s, hs, rfl⟩
  calc (Finset.univ.filter (fun s => D.chartOf s ∈ D.lst γ₀ o)).card
      ≤ ((D.lst γ₀ o).biUnion
          (fun b => Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ b ∈ D.lst γ₀ o, (Finset.univ.filter (fun s : Fin D.m => D.chartOf s = b)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ D.lst γ₀ o, (98 * (2 * D.Kb + 1) ^ 4 + 1) :=
        Finset.sum_le_sum (fun b _ => card_charts_le b)
    _ = (D.lst γ₀ o).card * (98 * (2 * D.Kb + 1) ^ 4 + 1) := by
        rw [Finset.sum_const, smul_eq_mul]

theorem mem_lst' {γ₀ : Fin D.W} {o : EuclideanSpace ℝ (Fin 3) × ℤ} {s : Fin D.m} :
    s ∈ D.lst' γ₀ o ↔ D.chartOf s ∈ D.lst γ₀ o := by
  classical
  simp [lst']

/-! ### Pair masks -/

theorem Hyp.H_meas (h : D.Hyp N M₀ D₀ L E) (s s' : Fin D.m) : MeasurableSet (D.H s s') := by
  classical
  have h1 : Measurable fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => (p.1, p.2.1) :=
    measurable_fst.prodMk measurable_snd.fst
  have h2 : Measurable fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => (p.1, p.2.2) :=
    measurable_fst.prodMk measurable_snd.snd
  have hcont : Continuous fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) =>
      |eval (x p.1 p.2.1) (pderiv 3 (D.R (D.chartOf s')))| := by
    apply Continuous.abs
    apply (MvPolynomial.continuous_eval _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [x] <;> fun_prop
  have e : D.H s s' = {_p | D.key (D.frame s) = D.src (D.chartOf s) ∧ D.frame s' = D.frame s} ∩
      ((fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => (p.1, p.2.1)) ⁻¹' D.Sb (D.chartOf s) ∩
      ((fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => p.2.2) ⁻¹' D.blk (D.fj (D.frame s)) ∩
      ((fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => (p.1, p.2.2)) ⁻¹' D.Sb (D.chartOf s') ∩
      ((fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => (p.1, p.2.1)) ⁻¹' D.Good (D.γ (D.chartOf s)) ∩
      {p | D.dfl * D.B (D.γ (D.chartOf s)) ≤
        |eval (x p.1 p.2.1) (pderiv 3 (D.R (D.chartOf s')))|})))) := by
    ext p
    simp only [H, mem_setOf_eq, mem_inter_iff, mem_preimage]
    tauto
  rw [e]
  refine MeasurableSet.inter ?_ ((h1 (h.Sb_meas _)).inter ((measurable_snd.snd (blk_meas _)).inter
    ((h2 (h.Sb_meas _)).inter ((h1 (h.Good_meas _)).inter
      (measurableSet_le measurable_const hcont.measurable)))))
  by_cases hc : D.key (D.frame s) = D.src (D.chartOf s) ∧ D.frame s' = D.frame s
  · simp [hc]
  · simp [hc]

/-- The coarse block of a witness chart listing the frame of an entry. -/
theorem witness_block {s s' : Fin D.m} (hf : D.frame s' = D.frame s) :
    coarseIdx (D.j (D.chartOf s')) = D.fj (D.frame s) := by
  rw [← hf, D.frame_block s']

theorem witness_world {s s' : Fin D.m} (hf : D.frame s' = D.frame s) :
    D.γ (D.chartOf s') = D.fγ (D.frame s) := by
  rw [← hf, D.frame_world s']

/-- Extrapolation of an old test over the coarse block of its chart. -/
theorem Hyp.extrap (h : D.Hyp N M₀ D₀ L E) (b : Fin D.C) {l : ℕ × (Fin 6 → ℝ)}
    (hl : l ∈ D.A b) {t : ℝ} (ht : t ∈ D.blk (coarseIdx (D.j b))) :
    |eval (x l t) (D.R b)| ≤ 12 * (D.κ₀ * δ N L) * (2 ^ D.s + 1) ^ 2 ∧
    |eval (x l t) (pderiv 3 (D.R b))| ≤ 12 * (D.κ₀ * D.B (D.γ b)) * (2 ^ D.s + 1) ^ 2 := by
  obtain ⟨-, -, hw⟩ := h.whole b hl
  obtain ⟨c1, c2⟩ := coarseIdx_bounds (D.j b)
  have hpT : (0 : ℝ) < 2 ^ D.T := by positivity
  have hab : ((coarseIdx (D.j b) : ℕ) : ℝ) / 2 ^ D.T + 1 / 2 ^ D.T =
      (((coarseIdx (D.j b) : ℕ) : ℝ) + 1) / 2 ^ D.T := by rw [add_div]
  have ht' : t ∈ Icc (((coarseIdx (D.j b) : ℕ) : ℝ) / 2 ^ D.T)
      (((coarseIdx (D.j b) : ℕ) : ℝ) / 2 ^ D.T + 1 / 2 ^ D.T) := by
    rw [hab]; exact ht
  have hb' : (((D.j b : ℕ) : ℝ) + 1) / 2 ^ (D.T + D.s) ≤
      ((coarseIdx (D.j b) : ℕ) : ℝ) / 2 ^ D.T + 1 / 2 ^ D.T := by rw [hab]; exact c2
  have hℓ : 1 / (2 : ℝ) ^ D.T * 2 ^ (D.T + D.s) = 2 ^ D.s := by
    rw [pow_add]; field_simp
  constructor
  · have := test_extrapolate_block (D.R b) (h.Rdeg b) l (fun t ht => (hw t ht).2.1) c1 hb' ht'
    rwa [hℓ] at this
  · have hd : (pderiv 3 (D.R b)).totalDegree ≤ 2 :=
      (Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' (D.R b) 3 (d := 1)
        (h.Rdeg b)).trans (by norm_num)
    have := test_extrapolate_block (pderiv 3 (D.R b)) hd l (fun t ht => (hw t ht).2.2.1) c1 hb' ht'
    rwa [hℓ] at this

/-- **The pair masks.** -/
theorem Hyp.H_props (h : D.Hyp N M₀ D₀ L E) {κ a : ℝ} (hκ : 2 ≤ κ)
    (ha1 : 12 * D.κ₀ * (2 ^ D.s + 1) ^ 2 ≤ N ^ a) (hdfl : N ^ (-a) ≤ D.dfl)
    (s s' : Fin D.m) (p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) (hp : p ∈ D.H s s') :
    (p.1, p.2.1) ∈ D.S s ∧ p.2.2 ∈ D.blk (D.fj (D.frame s)) ∧
    (p.1, p.2.2) ∈ E (D.fγ (D.frame s)) ∧
    s' ∈ D.lst' (D.fγ (D.frame s)) (obs (D.B (D.fγ (D.frame s))) (δ N L) (p.1, p.2.2)) ∧
    D.frame s' = D.frame s ∧
    tst N a (δ N L) (D.P κ s) (D.P κ s')
      (base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.fc (D.frame s)) (D.fu (D.frame s))
        (D.fQ (D.frame s)) p.1)
      (fun t => D.B (D.fγ (D.frame s)) * (x p.1 t) 3) p.2.1 (D.blk (D.fj (D.frame s))) False := by
  classical
  obtain ⟨hsrc, hf, hS0, hblk, hS1, -, hder⟩ := hp
  set b := D.chartOf s with hb
  set b' := D.chartOf s' with hb'
  have hS : D.S s = D.Sb b := by simp [S, hsrc, hb]
  have hγ' : D.γ b' = D.fγ (D.frame s) := witness_world hf
  have hγ : D.fγ (D.frame s) = D.γ b := fγ_of_src hsrc
  have hJ' : coarseIdx (D.j b') = D.fj (D.frame s) := witness_block hf
  have hJ : D.fj (D.frame s) = coarseIdx (D.j b) := fj_of_src hsrc
  obtain ⟨hE0, hA0, ht0, hd0⟩ := h.sel b hS0.1
  obtain ⟨hE1, hA1, -, -⟩ := h.sel b' hS1.1
  have hB : 0 < D.B (D.fγ (D.frame s)) := h.Bpos _
  have hδ : 0 < δ N L := by unfold δ; positivity
  have hκ0 : (κ : ℝ) ≠ 0 := by linarith
  have hκ₀ := h.κ₀one
  have hNa : 0 < N ^ a := lt_of_lt_of_le (by positivity) ha1
  have hs1 : (1 : ℝ) ≤ 12 * (2 ^ D.s + 1) ^ 2 := by
    have : (1 : ℝ) ≤ 2 ^ D.s + 1 := by have := (pow_pos (by norm_num : (0:ℝ) < 2) D.s); linarith
    nlinarith
  have hκa : D.κ₀ ≤ N ^ a := by nlinarith
  have hQ := (h.frame_bounds (D.frame s)).1
  -- the transported tests evaluate to the old tests
  have hevP (R : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
      eval (Fin.snoc (fun i : Fin 3 => base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ
          (D.fc (D.frame s)) (D.fu (D.frame s)) (D.fQ (D.frame s)) p.1 t i)
          (D.B (D.fγ (D.frame s)) * (x p.1 t) 3))
        (transport D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.B (D.fγ (D.frame s)))
          (D.fc (D.frame s)) (D.fu (D.frame s)) (D.fQ (D.frame s)) R) = eval (x p.1 t) R :=
    eval_transport hκ0 hB.ne' hQ R p.1 t
  have hevD (R : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
      eval (Fin.snoc (fun i : Fin 3 => base D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ
          (D.fc (D.frame s)) (D.fu (D.frame s)) (D.fQ (D.frame s)) p.1 t i)
          (D.B (D.fγ (D.frame s)) * (x p.1 t) 3))
        (pderiv 3 (transport D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.B (D.fγ (D.frame s)))
          (D.fc (D.frame s)) (D.fu (D.frame s)) (D.fQ (D.frame s)) R)) =
        (D.B (D.fγ (D.frame s)))⁻¹ * eval (x p.1 t) (pderiv 3 R) :=
    eval_pderiv_transport hκ0 hB.ne' hQ R p.1 t
  have hPs : D.P κ s = transport D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.B (D.fγ (D.frame s)))
      (D.fc (D.frame s)) (D.fu (D.frame s)) (D.fQ (D.frame s)) (D.R b) := rfl
  have hPs' : D.P κ s' = transport D.T (((D.fj (D.frame s) : ℕ) : ℝ)) κ (D.B (D.fγ (D.frame s)))
      (D.fc (D.frame s)) (D.fu (D.frame s)) (D.fQ (D.frame s)) (D.R b') := by
    rw [P, hf]
  -- the coarse block of both charts
  have ht0blk : p.2.1 ∈ D.blk (coarseIdx (D.j b')) := by
    rw [hJ', hJ]; exact old_sub_blk _ ht0
  have hBb : D.B (D.γ b) = D.B (D.fγ (D.frame s)) := by rw [hγ]
  have hBb' : D.B (D.γ b') = D.B (D.fγ (D.frame s)) := by rw [hγ']
  refine ⟨by rw [hS]; exact hS0, hblk, by rw [← hγ']; exact hE1, ?_, hf, ?_, ?_⟩
  · rw [mem_lst', ← hγ']
    exact h.knows b' hS1.1
  · intro R hR
    rcases hR with rfl | rfl
    · rw [hPs, hevP, hevD]
      obtain ⟨-, -, hw⟩ := h.whole b hA0
      obtain ⟨-, hv, hd, -⟩ := hw p.2.1 ht0
      rw [hBb] at hd hd0
      refine ⟨hv.trans (by nlinarith), ?_, ?_, fun hf => hf.elim⟩
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
        have hN0 : 0 < N := by linarith [h.N2]
        have h1 : N ^ (-a) ≤ D.κ₀⁻¹ := by
          rw [Real.rpow_neg hN0.le]; exact inv_anti₀ (by linarith) hκa
        have h2 : D.κ₀⁻¹ = (D.B (D.fγ (D.frame s)))⁻¹ * (D.B (D.fγ (D.frame s)) / D.κ₀) := by
          field_simp
        calc N ^ (-a) ≤ D.κ₀⁻¹ := h1
          _ = (D.B (D.fγ (D.frame s)))⁻¹ * (D.B (D.fγ (D.frame s)) / D.κ₀) := h2
          _ ≤ (D.B (D.fγ (D.frame s)))⁻¹ * |eval (x p.1 p.2.1) (pderiv 3 (D.R b))| :=
            mul_le_mul_of_nonneg_left hd0 (inv_nonneg.mpr hB.le)
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
        rw [inv_mul_le_iff₀ hB]
        nlinarith
    · rw [hPs', hevP, hevD]
      obtain ⟨hv, hd⟩ := h.extrap b' hA1 ht0blk
      rw [hBb'] at hd
      refine ⟨hv.trans (by nlinarith), ?_, ?_, fun hf => hf.elim⟩
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
        rw [← hγ] at hder
        calc N ^ (-a) ≤ D.dfl := hdfl
          _ = (D.B (D.fγ (D.frame s)))⁻¹ * (D.dfl * D.B (D.fγ (D.frame s))) := by field_simp
          _ ≤ (D.B (D.fγ (D.frame s)))⁻¹ * |eval (x p.1 p.2.1) (pderiv 3 (D.R b'))| :=
            mul_le_mul_of_nonneg_left hder (inv_nonneg.mpr hB.le)
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
        rw [inv_mul_le_iff₀ hB]
        nlinarith
  · intro t ht
    rw [hPs, hevP, hevD]
    have htb : t ∈ D.blk (coarseIdx (D.j b)) := by rw [← hJ]; exact ht
    obtain ⟨hv, hd⟩ := h.extrap b hA0 htb
    rw [hBb] at hd
    refine ⟨hv.trans (by nlinarith), ?_⟩
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB)]
    rw [inv_mul_le_iff₀ hB]
    nlinarith

end PrepData

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
