-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityQuads.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityAlign

/-!
# Steps 1 (numerics), 3 and 4 of sticky Lemma 5.3

* `abs_zero_ge_of_cross_small`: a horizontal vector `(W0, W1)` of length at least `κ` with
  `|W1 - F W0| ≤ κ / 4` and `|F| ≤ 4` has `|W0| ≥ κ / 8`.
* `abs_zero_ge_of_block`: the block bound of `LinearityAlign` turns a heavy block into this
  alignment.
* `exists_quadruples`: two Cauchy–Schwarz collision counts and one pigeonhole produce many
  "paths of length three" `p1 —local— p2 —global— p3 —local— p4` with `p1`, `p4` in a common
  layer and `p1` in a fixed global class.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset

/-- Alignment from a small cross term. -/
theorem abs_zero_ge_of_cross_small {W0 W1 F κ : ℝ} (hκ : 0 < κ) (hF : |F| ≤ 4)
    (hh : κ ^ 2 ≤ W0 ^ 2 + W1 ^ 2) (hD : |W1 - F * W0| ≤ κ / 4) : κ / 8 ≤ |W0| := by
  by_contra hlt
  push Not at hlt
  have h1 : |W1| ≤ |W1 - F * W0| + |F| * |W0| := by
    calc |W1| = |(W1 - F * W0) + F * W0| := by ring_nf
      _ ≤ |W1 - F * W0| + |F * W0| := abs_add_le _ _
      _ = |W1 - F * W0| + |F| * |W0| := by rw [abs_mul]
  have h2 : |F| * |W0| ≤ 4 * (κ / 8) := by
    gcongr
  have hW1 : |W1| < 3 * κ / 4 + κ / 4 := by linarith
  have hW1' : |W1| ≤ 3 * κ / 4 := by linarith
  have hsq0 : W0 ^ 2 < (κ / 8) ^ 2 := by
    rw [← sq_abs W0]; exact pow_lt_pow_left₀ hlt (abs_nonneg _) (by norm_num)
  have hsq1 : W1 ^ 2 ≤ (3 * κ / 4) ^ 2 := by
    rw [← sq_abs W1]; exact pow_le_pow_left₀ (abs_nonneg _) hW1' 2
  nlinarith

/-- **Step 1, numerics.** If a block of cells satisfies the hypotheses of `block_bound`, has at
least `τ ≥ N_loc M N_glob (1 + 16 / κ)` cells, the slope is bounded by `4` on its layers, and the
horizontal part of `W` has length at least `κ`, then `|W 0| ≥ κ / 8`. -/
theorem abs_zero_ge_of_block {ρ α K Rl Rg κ τ : ℝ} (hρ : 0 < ρ) (hRl : ρ ≤ Rl) (hRg : ρ ≤ Rg)
    (hK : 0 ≤ K) (hκ : 0 < κ) (f : ℝ → ℝ) (W : Space) (hW0 : |W 0| ≤ 1)
    (hWh : κ ^ 2 ≤ W 0 ^ 2 + W 1 ^ 2)
    (B : Finset (ℤ × ℤ × ℤ)) (hB : B.Nonempty) (M : ℕ) (Ks : Finset ℤ) (hKs : #Ks ≤ M)
    (hlayer : ∀ q ∈ B, q.2.2 ∈ Ks) (hf4 : ∀ k ∈ Ks, |f (ρ * k)| ≤ 4)
    (A : ℤ → Set ℝ) (hA : ∀ k, Assouad ρ α K (A k)) (xg : ℤ → ℝ)
    (hglob : ∀ q ∈ B, globalValue ρ f q ∈ A q.2.2 ∧
      globalValue ρ f q ∈ Set.Icc (xg q.2.2) (xg q.2.2 + Rg))
    (AL : Set ℝ) (hAL : Assouad ρ α K AL) (xl : ℝ)
    (hloc : ∀ q ∈ B, inner ℝ W (cellPos ρ q) ∈ AL ∧
      inner ℝ W (cellPos ρ q) ∈ Set.Icc xl (xl + Rl))
    (hτB : τ ≤ #B)
    (hτ : (3 * (K * (Rl / ρ) ^ α)) * M * (3 * (K * (Rg / ρ) ^ α)) * (1 + 16 / κ) < τ) :
    κ / 8 ≤ |W 0| := by
  obtain ⟨k1, hk1, hcase⟩ := block_bound hρ hRl hRg f W hW0 B hB M Ks hKs hlayer A hA xg
    hglob AL hAL xl hloc
  apply abs_zero_ge_of_cross_small hκ (hf4 k1 hk1) hWh
  set D := |W 1 - f (ρ * k1) * W 0|
  rcases hcase with h0 | hle
  · rw [h0]; positivity
  · by_contra hD
    push Not at hD
    set N := (3 * (K * (Rl / ρ) ^ α)) * M * (3 * (K * (Rg / ρ) ^ α))
    have hDpos : 0 < D := lt_trans (by positivity) hD
    have h4 : 4 / D < 16 / κ := by
      rw [div_lt_div_iff₀ hDpos hκ]; linarith
    have hNnn : 0 ≤ N := by
      have h1 : 0 ≤ Rl / ρ := div_nonneg (le_trans hρ.le hRl) hρ.le
      have h2 : 0 ≤ Rg / ρ := div_nonneg (le_trans hρ.le hRg) hρ.le
      positivity
    have : (#B : ℝ) ≤ N * (1 + 16 / κ) := by
      calc (#B : ℝ) ≤ (3 * (K * (Rl / ρ) ^ α)) * M * ((3 * (K * (Rg / ρ) ^ α)) * (4 / D + 1)) :=
            hle
        _ = N * (4 / D + 1) := by ring
        _ ≤ N * (1 + 16 / κ) := mul_le_mul_of_nonneg_left (by linarith) hNnn
    linarith

/-- **Steps 3 and 4: quadruples.** Pairs in a common local grain (key `lk`), then pairs of such
pairs with equal `(layer p, layer p', global class p')`, then a popular `(layer p1, class p1)`. -/
theorem exists_quadruples {α : Type*} [DecidableEq α] (P1 : Finset α) (hP1 : P1.Nonempty)
    (lk : α → ℤ × ℤ) (zl gc : α → ℤ) {NLoc NS NZW : ℝ}
    (hloc : (#(P1.image lk) : ℝ) ≤ NLoc)
    (hS : (#((keyPairs P1 lk).image fun pp => (zl pp.1, zl pp.2, gc pp.2)) : ℝ) ≤ NS)
    (hZW : (#(P1.image fun p => (zl p, gc p)) : ℝ) ≤ NZW) :
    ∃ k0 w : ℤ, ∃ Q0 : Finset ((α × α) × (α × α)),
      (∀ x ∈ Q0, x.1.1 ∈ P1 ∧ x.1.2 ∈ P1 ∧ x.2.1 ∈ P1 ∧ x.2.2 ∈ P1 ∧
        lk x.1.1 = lk x.1.2 ∧ lk x.2.1 = lk x.2.2 ∧
        zl x.1.1 = k0 ∧ zl x.2.1 = k0 ∧ zl x.1.2 = zl x.2.2 ∧ gc x.1.2 = gc x.2.2 ∧
        gc x.1.1 = w) ∧
      (#P1 : ℝ) ^ 4 ≤ NLoc ^ 2 * NS * NZW * #Q0 := by
  classical
  set LP := keyPairs P1 lk
  set sk : α × α → ℤ × ℤ × ℤ := fun pp => (zl pp.1, zl pp.2, gc pp.2)
  set Quad := keyPairs LP sk
  have hLP : (#P1 : ℝ) ^ 2 ≤ NLoc * #LP := card_sq_le_mul_card_keyPairs P1 lk hloc
  have hQuad : (#LP : ℝ) ^ 2 ≤ NS * #Quad := card_sq_le_mul_card_keyPairs LP sk hS
  have hP1pos : (0 : ℝ) < #P1 := by exact_mod_cast hP1.card_pos
  have hNLoc : 0 < NLoc := by
    have : (0 : ℝ) < #(P1.image lk) := by exact_mod_cast (hP1.image lk).card_pos
    linarith
  -- `Quad` is nonempty
  have hLPpos : (0 : ℝ) < #LP := by
    have : (0 : ℝ) < NLoc * #LP := lt_of_lt_of_le (by positivity) hLP
    exact pos_of_mul_pos_right this hNLoc.le
  have hNS : 0 < NS := by
    have hne : LP.Nonempty := by rw [← card_pos]; exact_mod_cast hLPpos
    have : (0 : ℝ) < #(LP.image sk) := by exact_mod_cast (hne.image sk).card_pos
    linarith
  have hQuadpos : (0 : ℝ) < #Quad := by
    have : (0 : ℝ) < NS * #Quad := lt_of_lt_of_le (by positivity) hQuad
    exact pos_of_mul_pos_right this hNS.le
  have hQne : Quad.Nonempty := by rw [← card_pos]; exact_mod_cast hQuadpos
  -- pigeonhole the layer and global class of `p1`
  set key : (α × α) × (α × α) → ℤ × ℤ := fun x => (zl x.1.1, gc x.1.1)
  have hkeys : (#(Quad.image key) : ℝ) ≤ NZW := by
    have : #(Quad.image key) ≤ #(P1.image fun p => (zl p, gc p)) := by
      apply Finset.card_le_card
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      have hx1 := (mem_keyPairs.mp hx).1
      exact Finset.mem_image.mpr ⟨x.1.1, (mem_keyPairs.mp hx1).1, rfl⟩
    exact le_trans (by exact_mod_cast this) hZW
  obtain ⟨⟨k0, w⟩, -, hbig⟩ := exists_card_fiber_ge Quad key hQne hkeys
  refine ⟨k0, w, Quad.filter fun x => key x = (k0, w), ?_, ?_⟩
  · intro x hx
    obtain ⟨hxQ, hxk⟩ := Finset.mem_filter.mp hx
    obtain ⟨h1, h2, hs⟩ := mem_keyPairs.mp hxQ
    obtain ⟨a1, a2, hl1⟩ := mem_keyPairs.mp h1
    obtain ⟨b1, b2, hl2⟩ := mem_keyPairs.mp h2
    simp only [sk, Prod.mk.injEq] at hs
    simp only [key, Prod.mk.injEq] at hxk
    exact ⟨a1, a2, b1, b2, hl1, hl2, hxk.1, hs.1 ▸ hxk.1, hs.2.1, hs.2.2, hxk.2⟩
  · have hNZW : 0 < NZW := by
      have : (0 : ℝ) < #(Quad.image key) := by exact_mod_cast (hQne.image key).card_pos
      linarith
    have h3 : (#Quad : ℝ) ≤ NZW * #(Quad.filter fun x => key x = (k0, w)) := by
      rwa [div_le_iff₀' hNZW] at hbig
    have hLP2 : (#P1 : ℝ) ^ 4 ≤ NLoc ^ 2 * (#LP : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hLP 2
      calc (#P1 : ℝ) ^ 4 = ((#P1 : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ (NLoc * #LP) ^ 2 := this
        _ = NLoc ^ 2 * (#LP : ℝ) ^ 2 := by ring
    calc (#P1 : ℝ) ^ 4 ≤ NLoc ^ 2 * (#LP : ℝ) ^ 2 := hLP2
      _ ≤ NLoc ^ 2 * (NS * #Quad) := by gcongr
      _ ≤ NLoc ^ 2 * (NS * (NZW * #(Quad.filter fun x => key x = (k0, w)))) := by gcongr
      _ = NLoc ^ 2 * NS * NZW * #(Quad.filter fun x => key x = (k0, w)) := by ring

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
