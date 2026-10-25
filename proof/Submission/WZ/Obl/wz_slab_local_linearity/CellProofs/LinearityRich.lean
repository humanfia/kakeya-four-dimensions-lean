-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityRich.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityQuads

/-!
# Rich blocks of cells are aligned (sticky Lemma 5.3, Step 1 assembled)

Cells `q = (i, j, k)` of `P` are grouped into blocks `j / M` (slabs of `M` rows of the lattice
`ρ ℤ³`, of width `s = M ρ`).  Blocks with at least `#P / (2 NB)` cells carry half of `P`, and at
every cell `q` of such a block the local grain normal `V q` has `|V q 0| ≥ κ / 8`.

We also record `card_floor_image_le_of_assouad_affine`: values `(u - c) / λ` with `u` in an
Assouad-type set fall into at most `C (R / r)^α (2 / |λ| + 3)` classes of width `r`.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric
open scoped RealInnerProductSpace

noncomputable section

theorem norm_le_abs_add_abs_add_abs (v : Space) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have hsq : ‖v‖ ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2), sq_abs (v 0), sq_abs (v 1),
      sq_abs (v 2), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq

theorem abs_apply_le_norm (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  rwa [Real.norm_eq_abs] at this

/-- **Classes after an affine change.** -/
theorem card_floor_image_le_of_assouad_affine {β : Type*} {d α C r R x c lam : ℝ} {B : Set ℝ}
    (hB : Assouad d α C B) (hdr : d ≤ r) (hrR : r ≤ R) (hr : 0 < r) (hlam : lam ≠ 0)
    (s : Finset β) (u : β → ℝ) (huB : ∀ a ∈ s, u a ∈ B) (huI : ∀ a ∈ s, u a ∈ Icc x (x + R)) :
    (#(s.image fun a => ⌊(u a - c) / lam / r⌋) : ℝ) ≤ C * (R / r) ^ α * (2 / |lam| + 3) := by
  classical
  obtain ⟨m, cc, hcov, hm⟩ := hB r R x hdr hrR
  set N : ℕ := ⌈1 / |lam|⌉₊ with hN
  have hlampos : 0 < |lam| := abs_pos.mpr hlam
  have hcl : ∀ a ∈ s, ∃ j : Fin m × Fin (2 * N + 1),
      ⌊(u a - c) / lam / r⌋ = (fun j : Fin m × Fin (2 * N + 1) =>
        ⌊(cc j.1 - c) / lam / r⌋ - N + (j.2 : ℤ)) j := by
    intro a ha
    have hmem : u a ∈ B ∩ Icc x (x + R) := ⟨huB a ha, huI a ha⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hmem)
    rw [mem_closedBall, Real.dist_eq] at hj
    -- the two scaled values differ by at most `1 / |lam|`
    have hdiff : |(u a - c) / lam / r - (cc j - c) / lam / r| ≤ 1 / |lam| := by
      have : (u a - c) / lam / r - (cc j - c) / lam / r = (u a - cc j) / lam / r := by
        field_simp; ring
      rw [this, abs_div, abs_div, abs_of_pos hr]
      rw [div_div, div_le_div_iff₀ (by positivity) hlampos]
      nlinarith [abs_nonneg (u a - cc j)]
    have hNge : 1 / |lam| ≤ N := Nat.le_ceil _
    set t := (u a - c) / lam / r
    set t0 := (cc j - c) / lam / r
    rw [abs_le] at hdiff
    have hlo : ⌊t0⌋ - (N : ℤ) ≤ ⌊t⌋ := by
      have : t0 - N ≤ t := by linarith
      have h := Int.floor_le_floor this
      rwa [Int.floor_sub_natCast] at h
    have hhi : ⌊t⌋ ≤ ⌊t0⌋ + (N : ℤ) := by
      have : t ≤ t0 + N := by linarith
      have h := Int.floor_le_floor this
      rwa [Int.floor_add_natCast] at h
    refine ⟨(j, ⟨(⌊t⌋ - (⌊t0⌋ - N)).toNat, ?_⟩), ?_⟩
    · have : (⌊t⌋ - (⌊t0⌋ - N)).toNat ≤ 2 * N := by omega
      omega
    · simp only
      have h0 : (0 : ℤ) ≤ ⌊t⌋ - (⌊t0⌋ - N) := by omega
      rw [Int.toNat_of_nonneg h0]
      ring
  have hcard := card_image_le_of_forall_exists s _ _ hcl
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  have hNle : (N : ℝ) ≤ 1 / |lam| + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hC0 : 0 ≤ C * (R / r) ^ α := le_trans (Nat.cast_nonneg m) hm
  calc (#(s.image fun a => ⌊(u a - c) / lam / r⌋) : ℝ) ≤ ((m * (2 * N + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = m * (2 * N + 1) := by push_cast; ring
    _ ≤ (C * (R / r) ^ α) * (2 * (1 / |lam| + 1) + 1) := by gcongr
    _ = C * (R / r) ^ α * (2 / |lam| + 3) := by ring

/-- The block of a cell: `j / M`. -/
def blockOf (M : ℕ) (q : ℤ × ℤ × ℤ) : ℤ := q.2.1 / (M : ℤ)

/-- **Rich blocks.** The cells lying in blocks with at least `#P / (2 NB)` cells are at least
half of `P`, when there are at most `NB` blocks. -/
theorem card_rich_ge {α β : Type*} [DecidableEq β] (P : Finset α) (b : α → β) {NB : ℝ}
    (hNB : (#(P.image b) : ℝ) ≤ NB) (hNBpos : 0 < NB) :
    (#P : ℝ) / 2 ≤ #(P.filter fun q => (#P : ℝ) / (2 * NB) ≤ #{q' ∈ P | b q' = b q}) := by
  classical
  have hτ : (0 : ℝ) ≤ (#P : ℝ) / (2 * NB) := by positivity
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => (#P : ℝ) / (2 * NB) ≤ (#{q' ∈ P | b q' = b q} : ℝ))
  have hsplitR : (#(P.filter fun q => (#P : ℝ) / (2 * NB) ≤ #{q' ∈ P | b q' = b q}) : ℝ) +
      #(P.filter fun q => ¬ ((#P : ℝ) / (2 * NB) ≤ #{q' ∈ P | b q' = b q})) = #P := by
    exact_mod_cast hsplit
  -- the poor cells: fewer than `τ` per block
  have hpoor : (#(P.filter fun q => ¬ ((#P : ℝ) / (2 * NB) ≤ #{q' ∈ P | b q' = b q})) : ℝ) ≤
      #(P.image b) * ((#P : ℝ) / (2 * NB)) := by
    generalize hPp : P.filter (fun q => ¬ ((#P : ℝ) / (2 * NB) ≤ #{q' ∈ P | b q' = b q})) = Pp
    have hPpsub : Pp ⊆ P := by rw [← hPp]; exact Finset.filter_subset _ _
    have hPpmem : ∀ q ∈ Pp, (#{q' ∈ P | b q' = b q} : ℝ) < (#P : ℝ) / (2 * NB) := by
      intro q hq
      rw [← hPp, Finset.mem_filter] at hq
      exact lt_of_not_ge hq.2
    have h1 : (#Pp : ℝ) = ∑ v ∈ Pp.image b, (#{q ∈ Pp | b q = v} : ℝ) := by
      rw [card_eq_sum_card_image b Pp]; push_cast; rfl
    have h2 : ∀ v ∈ Pp.image b, (#{q ∈ Pp | b q = v} : ℝ) ≤ (#P : ℝ) / (2 * NB) := by
      intro v hv
      obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hv
      have hlt := hPpmem q0 hq0
      have hsub : Pp.filter (fun q => b q = b q0) ⊆ P.filter (fun q' => b q' = b q0) := by
        intro q hq
        rw [Finset.mem_filter] at hq ⊢
        exact ⟨hPpsub hq.1, hq.2⟩
      have h3 : (#(Pp.filter fun q => b q = b q0) : ℝ) ≤ #(P.filter fun q' => b q' = b q0) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith
    have h3 : #(Pp.image b) ≤ #(P.image b) :=
      Finset.card_le_card (Finset.image_subset_image hPpsub)
    rw [h1]
    calc ∑ v ∈ Pp.image b, (#{q ∈ Pp | b q = v} : ℝ) ≤ ∑ _v ∈ Pp.image b, (#P : ℝ) / (2 * NB) :=
          Finset.sum_le_sum h2
      _ = #(Pp.image b) * ((#P : ℝ) / (2 * NB)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ #(P.image b) * ((#P : ℝ) / (2 * NB)) := by gcongr
  have hτNB : (#(P.image b) : ℝ) * ((#P : ℝ) / (2 * NB)) ≤ #P / 2 := by
    calc (#(P.image b) : ℝ) * ((#P : ℝ) / (2 * NB)) ≤ NB * ((#P : ℝ) / (2 * NB)) := by gcongr
      _ = #P / 2 := by field_simp
  linarith

end

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
