-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityAlign.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityClasses
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.Grains

/-!
# Step 1 of sticky Lemma 5.3: the local grain normal is aligned with the global one

We work with cells of the lattice `ρ ℤ³`.  A cell `q = (i, j, k)` sits at `cellPos ρ q`.
For a block `B` of cells whose local grain values `⟪W, cellPos ρ q⟫` lie in an Assouad-type
set (one local grain structure, normal `W`), and whose global grain values
`ρ i + f (ρ k) ρ j` lie in Assouad-type sets (one per layer `k`), the block is small unless
`W` is nearly parallel to `(1, f (ρ k), 0)` horizontally:
`#B ≤ N_loc · M · N_glob · (4 / |W 1 - f (ρ k) W 0| + 1)` for some layer `k` of the block.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric
open scoped RealInnerProductSpace

noncomputable section

/-- The position of a lattice cell. -/
def cellPos (ρ : ℝ) (q : ℤ × ℤ × ℤ) : Space :=
  WithLp.toLp 2 ![ρ * q.1, ρ * q.2.1, ρ * q.2.2]

@[simp] theorem cellPos_zero (ρ : ℝ) (q : ℤ × ℤ × ℤ) : cellPos ρ q 0 = ρ * q.1 := by
  simp [cellPos]

@[simp] theorem cellPos_one (ρ : ℝ) (q : ℤ × ℤ × ℤ) : cellPos ρ q 1 = ρ * q.2.1 := by
  simp [cellPos]

@[simp] theorem cellPos_two (ρ : ℝ) (q : ℤ × ℤ × ℤ) : cellPos ρ q 2 = ρ * q.2.2 := by
  simp [cellPos]

theorem inner_cellPos (ρ : ℝ) (W : Space) (q : ℤ × ℤ × ℤ) :
    ⟪W, cellPos ρ q⟫ = ρ * (W 0 * q.1 + W 1 * q.2.1 + W 2 * q.2.2) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, cellPos_zero, cellPos_one, cellPos_two,
    RCLike.inner_apply, conj_trivial]
  ring

/-- The global grain value of a cell for the slope `f`. -/
def globalValue (ρ : ℝ) (f : ℝ → ℝ) (q : ℤ × ℤ × ℤ) : ℝ :=
  ρ * q.1 + f (ρ * q.2.2) * (ρ * q.2.1)

/-- **Step 1 block bound.** -/
theorem block_bound {ρ α K Rl Rg : ℝ} (hρ : 0 < ρ) (hRl : ρ ≤ Rl) (hRg : ρ ≤ Rg)
    (f : ℝ → ℝ) (W : Space) (hW0 : |W 0| ≤ 1)
    (B : Finset (ℤ × ℤ × ℤ)) (hB : B.Nonempty) (M : ℕ) (Ks : Finset ℤ) (hKs : #Ks ≤ M)
    (hlayer : ∀ q ∈ B, q.2.2 ∈ Ks)
    (A : ℤ → Set ℝ) (hA : ∀ k, Assouad ρ α K (A k)) (xg : ℤ → ℝ)
    (hglob : ∀ q ∈ B, globalValue ρ f q ∈ A q.2.2 ∧
      globalValue ρ f q ∈ Icc (xg q.2.2) (xg q.2.2 + Rg))
    (AL : Set ℝ) (hAL : Assouad ρ α K AL) (xl : ℝ)
    (hloc : ∀ q ∈ B, ⟪W, cellPos ρ q⟫ ∈ AL ∧ ⟪W, cellPos ρ q⟫ ∈ Icc xl (xl + Rl)) :
    ∃ k1 ∈ Ks, |W 1 - f (ρ * k1) * W 0| = 0 ∨
      (#B : ℝ) ≤ (3 * (K * (Rl / ρ) ^ α)) * M *
        ((3 * (K * (Rg / ρ) ^ α)) * (4 / |W 1 - f (ρ * k1) * W 0| + 1)) := by
  classical
  set NL := 3 * (K * (Rl / ρ) ^ α) with hNL
  set NG := 3 * (K * (Rg / ρ) ^ α) with hNG
  -- local classes
  have hcardL : (#(B.image fun q => ⌊⟪W, cellPos ρ q⟫ / ρ⌋) : ℝ) ≤ NL :=
    card_floor_image_le_of_assouad hAL le_rfl hRl hρ B _ (fun q hq => (hloc q hq).1)
      (fun q hq => (hloc q hq).2)
  obtain ⟨κ, -, hκ⟩ := exists_card_fiber_ge B _ hB hcardL
  set B1 := B.filter fun q => ⌊⟪W, cellPos ρ q⟫ / ρ⌋ = κ with hB1
  have hNLpos : 0 < NL := lt_of_lt_of_le (by exact_mod_cast card_pos.mpr (hB.image _)) hcardL
  have hB1pos : (0 : ℝ) < #B1 := lt_of_lt_of_le (div_pos (by exact_mod_cast hB.card_pos) hNLpos) hκ
  have hB1ne : B1.Nonempty := by
    rw [← card_pos]; exact_mod_cast hB1pos
  -- layers
  have hcardK : (#(B1.image fun q => q.2.2) : ℝ) ≤ M := by
    have : #(B1.image fun q => q.2.2) ≤ #Ks := by
      apply Finset.card_le_card
      intro k hk
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
      exact hlayer q (Finset.mem_filter.mp hq).1
    exact_mod_cast this.trans hKs
  obtain ⟨k1, hk1, hS⟩ := exists_card_fiber_ge B1 _ hB1ne hcardK
  set S := B1.filter fun q => q.2.2 = k1 with hSdef
  have hk1Ks : k1 ∈ Ks := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk1
    exact hlayer q (Finset.mem_filter.mp hq).1
  refine ⟨k1, hk1Ks, ?_⟩
  by_cases hD : |W 1 - f (ρ * k1) * W 0| = 0
  · exact Or.inl hD
  right
  have hDpos : 0 < |W 1 - f (ρ * k1) * W 0| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hD)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by exact_mod_cast card_pos.mpr (hB1ne.image _))
    hcardK
  -- membership facts for `S`
  have hSmem : ∀ q ∈ S, q ∈ B ∧ ⌊⟪W, cellPos ρ q⟫ / ρ⌋ = κ ∧ q.2.2 = k1 := by
    intro q hq
    rw [hSdef, Finset.mem_filter, hB1, Finset.mem_filter] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2⟩
  -- global classes on `S`
  have hcardG : (#(S.image fun q => ⌊globalValue ρ f q / ρ⌋) : ℝ) ≤ NG := by
    apply card_floor_image_le_of_assouad (hA k1) le_rfl hRg hρ S _ (x := xg k1)
    · intro q hq
      obtain ⟨hqB, -, hqk⟩ := hSmem q hq
      have := (hglob q hqB).1
      rwa [hqk] at this
    · intro q hq
      obtain ⟨hqB, -, hqk⟩ := hSmem q hq
      have := (hglob q hqB).2
      rwa [hqk] at this
  -- each global class within `S` is small
  have hfib : ∀ w : ℤ, (#{q ∈ S | ⌊globalValue ρ f q / ρ⌋ = w} : ℝ) ≤
      4 / |W 1 - f (ρ * k1) * W 0| + 1 := by
    intro w
    set Sw := S.filter fun q => ⌊globalValue ρ f q / ρ⌋ = w
    have hinj : Set.InjOn (fun q : ℤ × ℤ × ℤ => (q.1, q.2.1)) (Sw : Set (ℤ × ℤ × ℤ)) := by
      intro q hq q' hq' h
      have hk : q.2.2 = q'.2.2 := by
        rw [(hSmem q (Finset.mem_filter.mp hq).1).2.2,
          (hSmem q' (Finset.mem_filter.mp hq').1).2.2]
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2 hk)
    have hcard_eq : #(Sw.image fun q : ℤ × ℤ × ℤ => (q.1, q.2.1)) = #Sw :=
      card_image_of_injOn hinj
    rw [← hcard_eq]
    apply card_lattice_fibre_le (c := κ - W 2 * k1) hW0 hDpos
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hqS := (Finset.mem_filter.mp hq).1
    have hqw := (Finset.mem_filter.mp hq).2
    obtain ⟨-, hqκ, hqk⟩ := hSmem q hqS
    refine ⟨?_, ?_, ?_⟩
    · have : globalValue ρ f q / ρ = (q.1 : ℝ) + f (ρ * k1) * q.2.1 := by
        rw [globalValue, hqk]; field_simp
      rw [← this]; exact hqw
    · have h1 := Int.floor_le (⟪W, cellPos ρ q⟫ / ρ)
      rw [hqκ, inner_cellPos, mul_div_cancel_left₀ _ hρ.ne', hqk] at h1
      simp only
      linarith
    · have h2 := Int.lt_floor_add_one (⟪W, cellPos ρ q⟫ / ρ)
      rw [hqκ, inner_cellPos, mul_div_cancel_left₀ _ hρ.ne', hqk] at h2
      simp only
      linarith
  have hScard : (#S : ℝ) ≤ NG * (4 / |W 1 - f (ρ * k1) * W 0| + 1) := by
    have hsum : (#S : ℝ) = ∑ w ∈ S.image (fun q => ⌊globalValue ρ f q / ρ⌋),
        (#{q ∈ S | ⌊globalValue ρ f q / ρ⌋ = w} : ℝ) := by
      rw [card_eq_sum_card_image (fun q => ⌊globalValue ρ f q / ρ⌋) S]; push_cast; rfl
    rw [hsum]
    calc ∑ w ∈ S.image (fun q => ⌊globalValue ρ f q / ρ⌋),
          (#{q ∈ S | ⌊globalValue ρ f q / ρ⌋ = w} : ℝ)
        ≤ ∑ _w ∈ S.image (fun q => ⌊globalValue ρ f q / ρ⌋),
          (4 / |W 1 - f (ρ * k1) * W 0| + 1) := sum_le_sum fun w _ => hfib w
      _ = #(S.image fun q => ⌊globalValue ρ f q / ρ⌋) *
          (4 / |W 1 - f (ρ * k1) * W 0| + 1) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ NG * (4 / |W 1 - f (ρ * k1) * W 0| + 1) := by gcongr
  -- combine
  have h1 : (#B : ℝ) / NL ≤ #B1 := hκ
  have h2 : (#B1 : ℝ) / M ≤ #S := hS
  have h3 : (#B : ℝ) ≤ NL * #B1 := by rwa [div_le_iff₀' hNLpos] at h1
  have h4 : (#B1 : ℝ) ≤ M * #S := by rwa [div_le_iff₀' hMpos] at h2
  calc (#B : ℝ) ≤ NL * #B1 := h3
    _ ≤ NL * (M * #S) := by gcongr
    _ ≤ NL * (M * (NG * (4 / |W 1 - f (ρ * k1) * W 0| + 1))) := by gcongr
    _ = NL * M * (NG * (4 / |W 1 - f (ρ * k1) * W 0| + 1)) := by ring

end

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
