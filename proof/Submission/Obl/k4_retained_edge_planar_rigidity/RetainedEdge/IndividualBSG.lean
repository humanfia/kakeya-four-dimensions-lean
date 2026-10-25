-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/IndividualBSG.lean;
-- only the namespace and module paths were renamed to o071's.
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.CellRuzsa
import Submission.Obl.k4_graph_bsg

/-!
# Rounding and graph BSG for one parameter (paper display `re:individual-bsg`)

For one represented parameter `κ`, round `A` and `κ B` to grid cells, apply the graph
Balog–Szemerédi–Gowers lemma with retained edges (paper Lemma 7.1 = accepted o005) to the image
graph in `ℤ × ℤ`, and pull the selected cells back. Lattice endpoint sets have at most one point
per cell, and the points of `B` in one cell of `κ B` are at most `(2|κ⁻¹| + 2)²`, so all losses are
polynomial in the subpower `K`.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

noncomputable section

/-- The graph BSG statement (T5) with explicit constants. -/
def GraphBSG (c C₀ : ℝ) : Prop :=
  ∀ (G : Type) [AddCommGroup G] [DecidableEq G] (A B : Finset G) (E : Finset (G × G)) (θ : ℝ),
    A.Nonempty → B.Nonempty → E ⊆ A ×ˢ B → 0 < θ → θ ≤ 1 →
    θ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) → ∃ A' : Finset G, ∃ B' : Finset G, A' ⊆ A ∧
    B' ⊆ B ∧ c * θ * (A.card : ℝ) ≤ (A'.card : ℝ) ∧ c * θ * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
    c * θ ^ 2 * (A.card : ℝ) * (B.card : ℝ) ≤ ((E ∩ A' ×ˢ B').card : ℝ) ∧
    (((A' ×ˢ B').image (fun p : G × G => p.1 + p.2)).card : ℝ) ≤
      C₀ * (θ ^ 5)⁻¹ * ((E.image (fun p : G × G => p.1 + p.2)).card : ℝ) ^ 3 /
        ((A.card : ℝ) * (B.card : ℝ))

theorem graphBSG_exists : ∃ c C₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ GraphBSG c C₀ :=
  Submission.k4_graph_bsg

/-- A finite set of points of the lattice `hℤ²`. -/
def OnLattice (h : ℝ) (U : Finset (ℝ × ℝ)) : Prop := ∀ x ∈ U, ∃ a b : ℤ, x = (h * a, h * b)

theorem OnLattice.mono {h : ℝ} {U V : Finset (ℝ × ℝ)} (hV : OnLattice h V) (hUV : U ⊆ V) :
    OnLattice h U := fun x hx => hV x (hUV hx)

theorem cell_lattice {h : ℝ} (hh : 0 < h) (a b : ℤ) : cell h (h * a, h * b) = (a, b) := by
  simp [cell, mul_div_cancel_left₀ _ hh.ne']

theorem cell_injOn_lattice {h : ℝ} (hh : 0 < h) {U : Finset (ℝ × ℝ)} (hU : OnLattice h U) :
    Set.InjOn (cell h) U := by
  intro x hx y hy hxy
  obtain ⟨a, b, rfl⟩ := hU x hx
  obtain ⟨a', b', rfl⟩ := hU y hy
  rw [cell_lattice hh, cell_lattice hh] at hxy
  simp only [Prod.mk.injEq] at hxy
  rw [hxy.1, hxy.2]

theorem card_cells_lattice {h : ℝ} (hh : 0 < h) {U : Finset (ℝ × ℝ)} (hU : OnLattice h U) :
    (cells h U).card = U.card :=
  Finset.card_image_of_injOn (cell_injOn_lattice hh hU)

theorem card_lattice_le_smul {h : ℝ} (hh : 0 < h) {U : Finset (ℝ × ℝ)} (hU : OnLattice h U)
    {κ : ℝ} (hκ : κ ≠ 0) :
    (U.card : ℝ) ≤ (2 * |κ⁻¹| + 2) ^ 2 * (cells h (κ • U)).card := by
  have := card_cells_le_smul (h := h) hκ U
  rwa [card_cells_lattice hh hU] at this

theorem card_cells_le_card' (h : ℝ) (U : Finset (ℝ × ℝ)) (κ : ℝ) :
    (cells h (κ • U)).card ≤ U.card :=
  (card_cells_le h _).trans Finset.card_image_le

/-- The lattice points of `U` whose `κ`-dilates share one cell are at most `(2|κ⁻¹| + 2)²`. -/
theorem fiber_smul_le {h : ℝ} (hh : 0 < h) {U : Finset (ℝ × ℝ)} (hU : OnLattice h U) {κ : ℝ}
    (hκ : κ ≠ 0) (z : ℤ × ℤ) :
    ((U.filter (fun y => cell h (κ • y) = z)).card : ℝ) ≤ (2 * |κ⁻¹| + 2) ^ 2 := by
  classical
  set Y := U.filter (fun y => cell h (κ • y) = z)
  have hY : OnLattice h Y := hU.mono (Finset.filter_subset _ _)
  have h1 := card_lattice_le_smul hh hY hκ
  have h2 : (cells h (κ • Y)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := mem_cells.mp ha
    obtain ⟨v, hv, rfl⟩ := mem_cells.mp hb
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hu
    obtain ⟨y', hy', rfl⟩ := Finset.mem_smul_finset.mp hv
    rw [(Finset.mem_filter.mp hy).2, (Finset.mem_filter.mp hy').2]
  have h2' : ((cells h (κ • Y)).card : ℝ) ≤ 1 := by exact_mod_cast h2
  calc (Y.card : ℝ) ≤ (2 * |κ⁻¹| + 2) ^ 2 * (cells h (κ • Y)).card := h1
    _ ≤ (2 * |κ⁻¹| + 2) ^ 2 * 1 := by gcongr
    _ = (2 * |κ⁻¹| + 2) ^ 2 := mul_one _


/-- Rounding an edge `(x, y)` to the pair of cells of `x` and `κ y`. -/
def roundPair (h κ : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : (ℤ × ℤ) × (ℤ × ℤ) :=
  (cell h p.1, cell h (κ • p.2))

set_option maxHeartbeats 1000000 in
/-- **Rounding and graph BSG for one parameter** (paper display `re:individual-bsg`). -/
theorem individual_bsg {c C₀ : ℝ} (hc : 0 < c) (hC₀ : 0 < C₀) (hT5 : GraphBSG c C₀)
    {h K L : ℝ} (hh : 0 < h) (hL : 0 < L) (hK : 2 ^ 20 ≤ K) (hKc : 1 / c ≤ K) (hKC : C₀ ≤ K)
    {A B : Finset (ℝ × ℝ)} (hAlat : OnLattice h A) (hBlat : OnLattice h B)
    (hA1 : L / K ≤ A.card) (hA2 : (A.card : ℝ) ≤ K * L) (hB1 : L / K ≤ B.card)
    (hB2 : (B.card : ℝ) ≤ K * L) {κ : ℝ} (hκ : κ ≠ 0) (hκinv : |κ⁻¹| ≤ K)
    {G : Finset ((ℝ × ℝ) × (ℝ × ℝ))} (hG : G ⊆ A ×ˢ B) (hGc : L ^ 2 / K ≤ G.card)
    (hsum : ((cells h (G.image (fun p => p.1 + κ • p.2))).card : ℝ) ≤ K * L) :
    ∃ A₁ B₁ : Finset (ℝ × ℝ), A₁ ⊆ A ∧ B₁ ⊆ B ∧ L / K ^ 40 ≤ (A₁.card : ℝ) ∧
      L / K ^ 40 ≤ ((cells h (κ • B₁)).card : ℝ) ∧
      ((cells h (A₁ + κ • B₁)).card : ℝ) ≤ K ^ 40 * L ∧
      L ^ 2 / K ^ 40 ≤ ((G.filter (fun p => p.1 ∈ A₁ ∧ p.2 ∈ B₁)).card : ℝ) := by
  classical
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have h16 : (16 : ℝ) ≤ K := le_trans (by norm_num) hK
  set A' := cells h A with hA'
  set B' := cells h (κ • B) with hB'
  set G' := G.image (roundPair h κ) with hG'
  have hG'sub : G' ⊆ A' ×ˢ B' := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hp' := Finset.mem_product.mp (hG hp)
    exact Finset.mem_product.mpr ⟨cell_mem_cells hp'.1,
      cell_mem_cells (Finset.smul_mem_smul_finset hp'.2)⟩
  -- sizes of the rounded vertex sets
  have hA'c : (A'.card : ℝ) = A.card := by rw [hA', card_cells_lattice hh hAlat]
  have hB'up : (B'.card : ℝ) ≤ B.card := by exact_mod_cast card_cells_le_card' h B κ
  have hκ4 : 2 * |κ⁻¹| + 2 ≤ 4 * K := by linarith
  have hB'low : (B.card : ℝ) / (16 * K ^ 2) ≤ B'.card := by
    have h1 := card_lattice_le_smul hh hBlat hκ
    rw [div_le_iff₀ (by positivity)]
    calc (B.card : ℝ) ≤ (2 * |κ⁻¹| + 2) ^ 2 * (cells h (κ • B)).card := h1
      _ ≤ (4 * K) ^ 2 * B'.card := by gcongr
      _ = B'.card * (16 * K ^ 2) := by ring
  -- the image graph keeps a polynomial fraction of the edges
  have hfib : ∀ q ∈ G', (G.filter (fun p => roundPair h κ p = q)).card ≤ ⌊(2 * |κ⁻¹| + 2) ^ 2⌋₊ := by
    intro q _
    apply Nat.le_floor
    have hinj : Set.InjOn (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2) (G.filter (fun p => roundPair h κ p = q)) := by
      intro p hp p' hp' heq
      have hp1 := Finset.mem_filter.mp hp
      have hp1' := Finset.mem_filter.mp hp'
      have e1 : cell h p.1 = cell h p'.1 := by
        have := hp1.2.trans hp1'.2.symm
        exact (Prod.mk.injEq _ _ _ _).mp this |>.1
      have hx := cell_injOn_lattice hh hAlat (Finset.mem_product.mp (hG hp1.1)).1
        (Finset.mem_product.mp (hG hp1'.1)).1 e1
      exact Prod.ext hx heq
    have hsub : (G.filter (fun p => roundPair h κ p = q)).image (fun p => p.2) ⊆
        B.filter (fun y => cell h (κ • y) = q.2) := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      have hp1 := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (hG hp1.1)).2, ?_⟩
      have := hp1.2
      exact ((Prod.mk.injEq _ _ _ _).mp this).2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj] at h1
    calc ((G.filter (fun p => roundPair h κ p = q)).card : ℝ) ≤
          (B.filter (fun y => cell h (κ • y) = q.2)).card := by exact_mod_cast h1
      _ ≤ (2 * |κ⁻¹| + 2) ^ 2 := fiber_smul_le hh hBlat hκ q.2
  have hGG' := Finset.card_le_mul_card_image G _ hfib
  have hG'low : (G.card : ℝ) / (16 * K ^ 2) ≤ G'.card := by
    have hfl : (⌊(2 * |κ⁻¹| + 2) ^ 2⌋₊ : ℝ) ≤ 16 * K ^ 2 := by
      calc (⌊(2 * |κ⁻¹| + 2) ^ 2⌋₊ : ℝ) ≤ (2 * |κ⁻¹| + 2) ^ 2 := Nat.floor_le (by positivity)
        _ ≤ (4 * K) ^ 2 := by gcongr
        _ = 16 * K ^ 2 := by ring
    have h1 : (G.card : ℝ) ≤ ⌊(2 * |κ⁻¹| + 2) ^ 2⌋₊ * G'.card := by exact_mod_cast hGG'
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) G'.card]
  -- the density of the image graph
  have hApos : (0 : ℝ) < A.card := lt_of_lt_of_le (by positivity) hA1
  have hB'low' : L / (16 * K ^ 3) ≤ B'.card := by
    calc L / (16 * K ^ 3) = (L / K) / (16 * K ^ 2) := by field_simp <;> ring
      _ ≤ (B.card : ℝ) / (16 * K ^ 2) := by gcongr
      _ ≤ B'.card := hB'low
  have hBpos : (0 : ℝ) < B'.card := lt_of_lt_of_le (by positivity) hB'low'
  have hG'low' : L ^ 2 / (16 * K ^ 3) ≤ G'.card := by
    calc L ^ 2 / (16 * K ^ 3) = (L ^ 2 / K) / (16 * K ^ 2) := by field_simp <;> ring
      _ ≤ (G.card : ℝ) / (16 * K ^ 2) := by gcongr
      _ ≤ G'.card := hG'low
  have hG'pos : (0 : ℝ) < G'.card := lt_of_lt_of_le (by positivity) hG'low'
  have hAB : (A'.card : ℝ) * B'.card ≤ K ^ 2 * L ^ 2 := by
    rw [hA'c]
    calc (A.card : ℝ) * B'.card ≤ (K * L) * (K * L) := by
          gcongr; exact hB'up.trans hB2
      _ = K ^ 2 * L ^ 2 := by ring
  have hABlow : L ^ 2 / (16 * K ^ 4) ≤ (A'.card : ℝ) * B'.card := by
    rw [hA'c]
    calc L ^ 2 / (16 * K ^ 4) = (L / K) * (L / (16 * K ^ 3)) := by field_simp <;> ring
      _ ≤ (A.card : ℝ) * B'.card := by gcongr
  set θ := (G'.card : ℝ) / ((A'.card : ℝ) * B'.card) with hθ
  have hABpos : (0 : ℝ) < (A'.card : ℝ) * B'.card := by rw [hA'c]; positivity
  have hθpos : 0 < θ := div_pos hG'pos hABpos
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hABpos]
    have := Finset.card_le_card hG'sub
    rw [Finset.card_product] at this
    exact_mod_cast this
  have hθlow : 1 / K ^ 6 ≤ θ := by
    rw [hθ, div_le_div_iff₀ (by positivity) hABpos, one_mul]
    calc (A'.card : ℝ) * B'.card ≤ K ^ 2 * L ^ 2 := hAB
      _ = (L ^ 2 / (16 * K ^ 3)) * (16 * K ^ 5) := by field_simp <;> ring
      _ ≤ G'.card * K ^ 6 := by
          gcongr
          nlinarith [pow_pos hK0 5]
  have hθeq : θ * (A'.card : ℝ) * B'.card ≤ G'.card := by
    rw [hθ, mul_assoc, div_mul_cancel₀ _ hABpos.ne']
  have hA'ne : A'.Nonempty := Finset.card_pos.mp (by rw [← Nat.cast_pos (α := ℝ), hA'c]; exact hApos)
  have hB'ne : B'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hBpos)
  obtain ⟨A'', B'', hA''sub, hB''sub, hA''c, hB''c, hE'', hsumset⟩ :=
    hT5 (ℤ × ℤ) A' B' G' θ hA'ne hB'ne hG'sub hθpos hθ1 hθeq
  -- pull back the selected cells
  set A₁ := A.filter (fun x => cell h x ∈ A'') with hA₁
  set B₁ := B.filter (fun y => cell h (κ • y) ∈ B'') with hB₁
  have hcA : cells h A₁ = A'' := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := mem_cells.mp hz
      exact (Finset.mem_filter.mp hx).2
    · intro hz
      obtain ⟨x, hx, rfl⟩ := mem_cells.mp (hA''sub hz)
      exact cell_mem_cells (Finset.mem_filter.mpr ⟨hx, hz⟩)
  have hcB : cells h (κ • B₁) = B'' := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hu, rfl⟩ := mem_cells.mp hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hu
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      obtain ⟨u, hu, rfl⟩ := mem_cells.mp (hB''sub hz)
      obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hu
      exact cell_mem_cells (Finset.smul_mem_smul_finset (Finset.mem_filter.mpr ⟨hy, hz⟩))
  have hA₁c : (A₁.card : ℝ) = A''.card := by
    rw [← hcA, card_cells_lattice hh (hAlat.mono (Finset.filter_subset _ _))]
  have hcK : 1 / K ≤ c := by
    rw [div_le_iff₀ hK0]; rw [div_le_iff₀ hc] at hKc; linarith
  have hK40 : ∀ e : ℕ, e ≤ 40 → K ^ e ≤ K ^ 40 := fun e he => pow_le_pow_right₀ hK1 he
  refine ⟨A₁, B₁, Finset.filter_subset _ _, Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · -- the endpoint set `A₁` is large
    rw [hA₁c]
    calc L / K ^ 40 ≤ L / K ^ 8 := by gcongr <;> norm_num
      _ = (1 / K) * (1 / K ^ 6) * (L / K) := by field_simp <;> ring
      _ ≤ c * θ * A'.card := by rw [hA'c]; gcongr
      _ ≤ A''.card := hA''c
  · -- the dilated endpoint set `κ B₁` is large
    rw [hcB]
    calc L / K ^ 40 ≤ L / (16 * K ^ 10) := by
          gcongr
          calc 16 * K ^ 10 ≤ K * K ^ 10 := by gcongr
            _ = K ^ 11 := by ring
            _ ≤ K ^ 40 := hK40 11 (by norm_num)
      _ = (1 / K) * (1 / K ^ 6) * (L / (16 * K ^ 3)) := by field_simp <;> ring
      _ ≤ c * θ * B'.card := by gcongr
      _ ≤ B''.card := hB''c
  · -- the restricted sumset is small
    have hC' : ((G'.image (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1 + q.2)).card : ℝ) ≤ 4 * (K * L) := by
      have hsub : G'.image (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1 + q.2) ⊆
          cells h (G.image (fun p => p.1 + κ • p.2)) - ebox 0 1 := by
        intro z hz
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
        show cell h p.1 + cell h (κ • p.2) ∈ _
        have hmem := cell_add_sub_mem h p.1 (κ • p.2)
        exact Finset.mem_sub.mpr ⟨cell h (p.1 + κ • p.2),
          cell_mem_cells (Finset.mem_image_of_mem _ hp), _, hmem, sub_sub_cancel _ _⟩
      have h1 := (Finset.card_le_card hsub).trans Finset.card_sub_le
      rw [card_ebox01] at h1
      have h1' : ((G'.image (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1 + q.2)).card : ℝ) ≤
          (cells h (G.image (fun p => p.1 + κ • p.2))).card * 4 := by exact_mod_cast h1
      linarith
    have hθ5 : (θ ^ 5)⁻¹ ≤ K ^ 30 := by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      calc (K ^ 30)⁻¹ = (1 / K ^ 6) ^ 5 := by field_simp <;> ring
        _ ≤ θ ^ 5 := by gcongr
    have hsumset' : ((A'' + B'').card : ℝ) ≤ C₀ * (θ ^ 5)⁻¹ *
        ((G'.image (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1 + q.2)).card : ℝ) ^ 3 /
          ((A'.card : ℝ) * (B'.card : ℝ)) := by
      rw [← Finset.image_add_product]; exact hsumset
    have h4 := card_cells_add_le h A₁ (κ • B₁)
    rw [hcA, hcB] at h4
    have h4' : ((cells h (A₁ + κ • B₁)).card : ℝ) ≤ ((A'' + B'').card : ℝ) * 4 := by
      exact_mod_cast h4
    calc ((cells h (A₁ + κ • B₁)).card : ℝ) ≤ ((A'' + B'').card : ℝ) * 4 := h4'
      _ ≤ (C₀ * (θ ^ 5)⁻¹ * ((G'.image (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1 + q.2)).card : ℝ) ^ 3 /
          ((A'.card : ℝ) * (B'.card : ℝ))) * 4 := by gcongr
      _ ≤ (K * K ^ 30 * (4 * (K * L)) ^ 3 / (L ^ 2 / (16 * K ^ 4))) * 4 := by
          gcongr
      _ = 4096 * K ^ 38 * L := by field_simp <;> ring
      _ ≤ K ^ 40 * L := by
          have : (4096 : ℝ) ≤ K ^ 2 :=
            le_trans (le_trans (by norm_num) hK) (le_self_pow₀ hK1 (by norm_num))
          have : (4096 : ℝ) * K ^ 38 ≤ K ^ 40 := by
            calc (4096 : ℝ) * K ^ 38 ≤ K ^ 2 * K ^ 38 := by gcongr
              _ = K ^ 40 := by ring
          gcongr
  · -- many original edges are retained
    have hA₁mem : ∀ x ∈ A, cell h x ∈ A'' → x ∈ A₁ := fun x hx hc => Finset.mem_filter.mpr ⟨hx, hc⟩
    have hB₁mem : ∀ y ∈ B, cell h (κ • y) ∈ B'' → y ∈ B₁ := fun y hy hc =>
      Finset.mem_filter.mpr ⟨hy, hc⟩
    clear_value θ A₁ B₁ G' A' B'
    have hsurj : Set.SurjOn (roundPair h κ) ↑(G.filter (fun p => p.1 ∈ A₁ ∧ p.2 ∈ B₁))
        ↑(G' ∩ A'' ×ˢ B'') := by
      intro q hq
      rw [Finset.mem_coe, Finset.mem_inter, Finset.mem_product] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      rw [hG'] at hq1
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq1
      have hpAB := Finset.mem_product.mp (hG hp)
      exact ⟨p, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hp, hA₁mem _ hpAB.1 hq2,
        hB₁mem _ hpAB.2 hq3⟩), rfl⟩
    have h1 := Finset.card_le_card_of_surjOn (roundPair h κ) hsurj
    have h1' : ((G' ∩ A'' ×ˢ B'').card : ℝ) ≤
        ((G.filter (fun p => p.1 ∈ A₁ ∧ p.2 ∈ B₁)).card : ℝ) := by exact_mod_cast h1
    have e1 : L ^ 2 / K ^ 40 ≤ (1 / K) * (1 / K ^ 6) ^ 2 * (L ^ 2 / (16 * K ^ 4)) := by
      have hK18 : 16 * K ^ 17 ≤ K ^ 40 := by
        calc 16 * K ^ 17 ≤ K * K ^ 17 := mul_le_mul_of_nonneg_right h16 (by positivity)
          _ = K ^ 18 := by ring
          _ ≤ K ^ 40 := hK40 18 (by norm_num)
      have : (1 / K) * (1 / K ^ 6) ^ 2 * (L ^ 2 / (16 * K ^ 4)) = L ^ 2 / (16 * K ^ 17) := by
        field_simp
      rw [this]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hK18
    have e2 : (1 / K) * (1 / K ^ 6) ^ 2 * (L ^ 2 / (16 * K ^ 4)) ≤
        c * θ ^ 2 * ((A'.card : ℝ) * B'.card) := by
      have hθ2 : (1 / K ^ 6) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (by positivity) hθlow 2
      exact mul_le_mul (mul_le_mul hcK hθ2 (by positivity) hc.le) hABlow (by positivity)
        (by positivity)
    calc L ^ 2 / K ^ 40 ≤ (1 / K) * (1 / K ^ 6) ^ 2 * (L ^ 2 / (16 * K ^ 4)) := e1
      _ ≤ c * θ ^ 2 * ((A'.card : ℝ) * B'.card) := e2
      _ = c * θ ^ 2 * (A'.card : ℝ) * B'.card := by ring
      _ ≤ ((G' ∩ A'' ×ˢ B'').card : ℝ) := hE''
      _ ≤ _ := h1'

end

end Submission.Obl.k4_retained_edge_planar_rigidity
