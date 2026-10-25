-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Projection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Projection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/Projection.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Projection.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Cover
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Determined

set_option autoImplicit false

/-!
# The projection estimate, version 2 (deterministic replacement of `a04:projection-entropy`)

The `j = 2` form of `thin_y_mass` of o229 (session x0801, branch `x0801` at `b03d2c4a`,
`Jets/Projection.lean`).  At a fixed time, the labelled trajectories whose tangential projection
`e · y` lies within `L` of one of at most `KY` values prescribed by the `q`-bin of their scalar
`S` carry prior mass at most `4000 K⁶ KY (L + q)`, for a row `e` normalized by its largest
coordinate (`e k = 1`, `|e k'| ≤ 1`).  The scalar has an upper `d`-dimensional support count
(`SS`), so there are at most `≈ K q^{-d}` occupied scalar bins; each `q`-bin of `S` times a slab
of width `L` is covered by `≈ K (L/q + 1) (K/q)` cubes of side `q` in `(x, y)`, each of mass
`≤ K q^{2+d}` (`AC`).

`exists_normalized_row`: every nonzero row is a positive multiple of a normalized one, through
its largest coordinate; this is how the tail, compatibility and final tests divide by a row.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- The sup norm of a vector of `ℝ²` is attained at a coordinate. -/
theorem exists_norm_eq_abs (g : Fin 2 → ℝ) : ∃ k, ‖g‖ = |g k| := by
  rcases le_total |g 1| |g 0| with h | h
  · refine ⟨0, le_antisymm (norm_le_of_abs_le (abs_nonneg _) fun i => ?_) (abs_le_norm g 0)⟩
    fin_cases i
    · exact le_rfl
    · exact h
  · refine ⟨1, le_antisymm (norm_le_of_abs_le (abs_nonneg _) fun i => ?_) (abs_le_norm g 1)⟩
    fin_cases i
    · exact h
    · exact le_rfl

/-- Normalization of a nonzero row by its largest coordinate. -/
theorem exists_normalized_row {g : Fin 2 → ℝ} (hg : 0 < ‖g‖) :
    ∃ k, |g k| = ‖g‖ ∧ ((g k)⁻¹ • g) k = 1 ∧ |((g k)⁻¹ • g) (Fin.rev k)| ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_norm_eq_abs g
  have hgk : g k ≠ 0 := by
    intro h; rw [h, abs_zero] at hk; linarith
  refine ⟨k, hk.symm, ?_, ?_⟩
  · simp [hgk]
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv]
    rw [← hk, inv_mul_le_iff₀ hg, mul_one]
    exact abs_le_norm g _

/-- **Projection estimate** (slab form). -/
theorem thin_slab_mass {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ}
    (hSN : ScalarNormal ν c E F piece K ζ d) (hd1 : d ≤ 1) (t q L : ℝ)
    (hζq : ζ ≤ q) (hq1 : q ≤ 1) (hL : 0 ≤ L) {e : Fin 2 → ℝ} {k : Fin 2} (hek : e k = 1)
    (he' : |e (Fin.rev k)| ≤ 1) (Y : ℤ → Finset ℝ) (KY : ℕ) (hY : ∀ σ, (Y σ).card ≤ KY) :
    ν {l | (l, t) ∈ E ∧ ∃ y₀ ∈ Y ⌊zS F (c l) t / q⌋, |e ⬝ᵥ zy (c l) t - y₀| ≤ L} ≤
      ENNReal.ofReal (4000 * K ^ 6 * KY * (L + q)) := by
  classical
  have hK := hSN.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 < q := lt_of_lt_of_le hSN.zeta_pos hζq
  by_cases hex : ∃ l₀, (l₀, t) ∈ E
  swap
  · push Not at hex
    have : {l | (l, t) ∈ E ∧ ∃ y₀ ∈ Y ⌊zS F (c l) t / q⌋, |e ⬝ᵥ zy (c l) t - y₀| ≤ L} = ∅ := by
      ext l; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd h (hex l)
    rw [this, measure_empty]; exact bot_le
  obtain ⟨l₀, hl₀⟩ := hex
  have ht : t ∈ Icc (0 : ℝ) 1 := hSN.time_mem _ hl₀
  have hFt : ‖F t‖ ≤ K := hSN.row_le _ hl₀
  set A : ℝ := 4 * K ^ 2 + 3 * K with hA
  have hA7 : 7 ≤ A := by rw [hA]; nlinarith
  have hsub : {s | ∃ l, (l, t) ∈ E ∧ zS F (c l) t = s} ⊆ Icc (-A) A := by
    rintro s ⟨l, hl, rfl⟩
    exact abs_le.mp (abs_zS_le (hSN.coeff_le _ hl) ht hFt)
  obtain ⟨B, hBcard, hBmem⟩ := occupied_bins_le (hSN.support t) hζq hq (by linarith) hsub
  set n' : ℕ := ⌊2 * (2 * K) / q⌋₊ + 1 with hn'
  set n : ℕ := ⌊(2 * L + 2 * q) / q⌋₊ + 1 with hn
  set nx : ℕ := ⌊4 * K + 1⌋₊ + 1 with hnx
  let corner : ℝ → ℕ → ℕ → Fin 2 → ℝ := fun y₀ j' j =>
    slabCorner k (slabLo y₀ L q (e (Fin.rev k)) (-(2 * K) + j' * q) + j * q) (-(2 * K) + j' * q)
  let Sq : ℤ → ℝ → ℕ → ℕ → ℕ → Set Λ := fun σ y₀ j' j i =>
    {l | (l, t) ∈ E ∧ InCube (c l) t (colA (σ * q) (F t) (corner y₀ j' j) q + i * q)
      (corner y₀ j' j) q}
  have hcover : {l | (l, t) ∈ E ∧ ∃ y₀ ∈ Y ⌊zS F (c l) t / q⌋, |e ⬝ᵥ zy (c l) t - y₀| ≤ L} ⊆
      ⋃ σ ∈ B, ⋃ y₀ ∈ Y σ, ⋃ j' ∈ Finset.range n', ⋃ j ∈ Finset.range n,
        ⋃ i ∈ Finset.range nx, Sq σ y₀ j' j i := by
    rintro l ⟨hl, y₀, hy₀, hyL⟩
    set σ := ⌊zS F (c l) t / q⌋ with hσ
    have hσB : σ ∈ B := hBmem _ ⟨l, hl, rfl⟩
    have hc := hSN.coeff_le _ hl
    have hyb : |zy (c l) t (Fin.rev k)| ≤ 2 * K := abs_zy_le hc ht _
    obtain ⟨j', hj', j, hj, hbox⟩ := slab_cover hq hek he' hyb hyL
    have hS1 : (σ : ℝ) * q ≤ zS F (c l) t := by
      have := Int.floor_le (zS F (c l) t / q)
      calc (σ : ℝ) * q ≤ zS F (c l) t / q * q := by gcongr
        _ = zS F (c l) t := by field_simp
    have hS2 : zS F (c l) t < σ * q + q := by
      have := Int.lt_floor_add_one (zS F (c l) t / q)
      calc zS F (c l) t = zS F (c l) t / q * q := by field_simp
        _ < ((σ : ℝ) + 1) * q := by gcongr
        _ = σ * q + q := by ring
    obtain ⟨i, hi, hx⟩ := col_cover (s₀ := σ * q) (x := zx (c l) t) (y := zy (c l) t)
      (b := corner y₀ j' j) hq hFt (by simpa [zS] using hS1) (by simpa [zS] using hS2) hbox
    simp only [mem_iUnion, exists_prop, Finset.mem_range]
    exact ⟨σ, hσB, y₀, hy₀, j', hj', j, hj, i, hi, hl, hx, hbox⟩
  -- measure of each cube
  have hsq : ∀ σ y₀ j' j i, ν (Sq σ y₀ j' j i) ≤ ENNReal.ofReal (K * q ^ (2 + d)) := by
    intro σ y₀ j' j i
    exact hSN.abs_cap t _ _ q hζq hq1
  have hsum : ν {l | (l, t) ∈ E ∧ ∃ y₀ ∈ Y ⌊zS F (c l) t / q⌋, |e ⬝ᵥ zy (c l) t - y₀| ≤ L} ≤
      ∑ σ ∈ B, ∑ y₀ ∈ Y σ, ∑ j' ∈ Finset.range n', ∑ j ∈ Finset.range n,
        ∑ i ∈ Finset.range nx, ENNReal.ofReal (K * q ^ (2 + d)) := by
    refine (measure_mono hcover).trans ?_
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun y₀ _ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j' _ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact hsq σ y₀ j' j i
  refine hsum.trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hYle : ∀ σ ∈ B, ((Y σ).card : ENNReal) *
      (n' * (n * (nx * ENNReal.ofReal (K * q ^ (2 + d))))) ≤
      (KY : ENNReal) * (n' * (n * (nx * ENNReal.ofReal (K * q ^ (2 + d))))) := by
    intro σ _; gcongr; exact_mod_cast hY σ
  refine (Finset.sum_le_sum hYle).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hconv : (B.card : ENNReal) *
      ((KY : ENNReal) * (n' * (n * (nx * ENNReal.ofReal (K * q ^ (2 + d)))))) =
      ENNReal.ofReal (B.card * (KY * (n' * (n * (nx * (K * q ^ (2 + d))))))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  -- bounds on the counts
  have hn'' : (n' : ℝ) ≤ (4 * K + q) / q := by
    have := floor_add_one_le (B := 2 * (2 * K) / q) (by positivity)
    rw [hn']
    calc _ ≤ 2 * (2 * K) / q + 1 := this
      _ = (4 * K + q) / q := by field_simp; ring
  have hn2 : (n : ℝ) ≤ (2 * L + 3 * q) / q := by
    have := floor_add_one_le (B := (2 * L + 2 * q) / q) (by positivity)
    rw [hn]
    calc _ ≤ (2 * L + 2 * q) / q + 1 := this
      _ = (2 * L + 3 * q) / q := by field_simp; ring
  have hnx' : (nx : ℝ) ≤ 4 * K + 2 := by
    have := floor_add_one_le (B := 4 * K + 1) (by positivity)
    rw [hnx]; linarith
  have hpow : (2 * A / q) ^ d * q ^ (2 + d) = (2 * A) ^ d * q ^ 2 := by
    rw [Real.div_rpow (by positivity) hq.le, Real.rpow_add hq]
    have : q ^ (2 : ℝ) = q ^ 2 := by exact_mod_cast Real.rpow_natCast q 2
    rw [this]
    have hqd : 0 < q ^ d := Real.rpow_pos_of_pos hq d
    field_simp
  have hAd : (2 * A) ^ d ≤ 2 * A := by
    calc (2 * A) ^ d ≤ (2 * A) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hd1
      _ = 2 * A := Real.rpow_one _
  have hA' : 2 * A ≤ 14 * K ^ 2 := by rw [hA]; nlinarith
  have hBc : (B.card : ℝ) ≤ 3 * (K * (2 * A / q) ^ d) := hBcard
  have hKY : (0 : ℝ) ≤ KY := Nat.cast_nonneg _
  have hKq : 0 ≤ K * q ^ (2 + d) := by positivity
  calc (B.card : ℝ) * (KY * (n' * (n * (nx * (K * q ^ (2 + d))))))
      ≤ 3 * (K * (2 * A / q) ^ d) * (KY * ((4 * K + q) / q * ((2 * L + 3 * q) / q *
          ((4 * K + 2) * (K * q ^ (2 + d)))))) := by
        gcongr
    _ = 3 * K ^ 2 * KY * (4 * K + 2) * ((2 * A / q) ^ d * q ^ (2 + d)) *
          ((4 * K + q) * (2 * L + 3 * q) / q ^ 2) := by
        field_simp
    _ = 3 * K ^ 2 * KY * (4 * K + 2) * ((2 * A) ^ d * q ^ 2) *
          ((4 * K + q) * (2 * L + 3 * q) / q ^ 2) := by rw [hpow]
    _ = 3 * K ^ 2 * KY * (4 * K + 2) * (2 * A) ^ d * ((4 * K + q) * (2 * L + 3 * q)) := by
        field_simp
    _ ≤ 3 * K ^ 2 * KY * (6 * K) * (14 * K ^ 2) * ((5 * K) * (3 * (L + q))) := by
        gcongr
        · linarith
        · exact hAd.trans hA'
        · linarith
        · linarith
    _ = 3780 * K ^ 6 * KY * (L + q) := by ring
    _ ≤ 4000 * K ^ 6 * KY * (L + q) := by
        have : 0 ≤ K ^ 6 * KY * (L + q) := by positivity
        nlinarith

/-- **Projection estimate, `Determined` form.**  If a normalized tangential projection at time
`t` is determined within `L` by the `q`-bin of the scalar (up to `n` candidates) on the labelled
trajectories of `D`, these carry prior mass at most `4000 K⁶ n (L + q)`. -/
theorem Determined.mass_le {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 7 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {piece : ℝ → Λ → Fin 7 → ℤ} {K ζ d : ℝ}
    (hSN : ScalarNormal ν c E F piece K ζ d) (hd1 : d ≤ 1) {D : Set Λ} {t q L : ℝ} {n : ℕ}
    (hζq : ζ ≤ q) (hq1 : q ≤ 1) (hL : 0 ≤ L) {e : Fin 2 → ℝ} {k : Fin 2} (hek : e k = 1)
    (he' : |e (Fin.rev k)| ≤ 1)
    (h : Determined E (fun l => zS F (c l) t) D t q (fun l => e ⬝ᵥ zy (c l) t) L n) :
    ν {l | l ∈ D ∧ (l, t) ∈ E} ≤ ENNReal.ofReal (4000 * K ^ 6 * n * (L + q)) := by
  obtain ⟨Y, hY, hmem⟩ := h
  refine (measure_mono ?_).trans (thin_slab_mass hSN hd1 t q L hζq hq1 hL hek he' Y n hY)
  rintro l ⟨hl, hlt⟩
  obtain ⟨y, hy, hd⟩ := hmem l hl hlt
  exact ⟨hlt, y, hy, hd⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
