-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityExtract.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityCells

/-!
# Extraction of dot-product triples (sticky Lemma 5.3, Steps 2–5 before Theorem 5.2)

From the cell hypotheses `CellHyp` we extract a layer `k0`, a class `w`, rows `j` (one lattice
row `M j + r0` per block, at height-independent position `Y j = ρ (M j + r0)`), a local grain
tilt `g j` per row, and many triples `(k2, j1, j3)` with

  `(ρ k2 - ρ k0) (g j3 - g j1) + (f (ρ k2) - f (ρ k0)) (Y j1 - Y j3) ∈ A k0 - w ρ + [-4ρ, 4ρ]`.

This is identity (5.16) of the sticky paper, obtained here without the skew transform.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric
open scoped RealInnerProductSpace

noncomputable section

/-- The four-step identity behind (5.16). -/
theorem dot_identity {x1 x2 x3 x4 Y1 Y3 z0 z2 g1 g3 F0 F2 ρ : ℝ}
    (h12 : |(x2 + g1 * z2) - (x1 + g1 * z0)| < ρ)
    (h23 : |(x3 + F2 * Y3) - (x2 + F2 * Y1)| < ρ)
    (h34 : |(x4 + g3 * z0) - (x3 + g3 * z2)| < ρ) :
    |((z2 - z0) * (g3 - g1) + (F2 - F0) * (Y1 - Y3)) -
      ((x4 + F0 * Y3) - (x1 + F0 * Y1))| < 3 * ρ := by
  rw [abs_lt] at h12 h23 h34 ⊢
  constructor <;> nlinarith

/-- Floors of `ρ i + c` divided by `ρ` determine the integer `i`. -/
theorem int_eq_of_floor_eq {ρ c c' : ℝ} (hρ : 0 < ρ) {i i' : ℤ}
    (h : ⌊(ρ * i + c) / ρ⌋ = ⌊(ρ * i' + c') / ρ⌋) (hc : c = c') : i = i' := by
  subst hc
  have e : ∀ n : ℤ, (ρ * n + c) / ρ = (n : ℝ) + c / ρ := by
    intro n; field_simp
  rw [e, e, Int.floor_intCast_add, Int.floor_intCast_add] at h
  omega

theorem abs_sub_lt_of_floor_div_eq {ρ a b : ℝ} (hρ : 0 < ρ) (h : ⌊a / ρ⌋ = ⌊b / ρ⌋) :
    |a - b| < ρ := by
  have h1 := Int.floor_le (a / ρ)
  have h2 := Int.lt_floor_add_one (a / ρ)
  have h3 := Int.floor_le (b / ρ)
  have h4 := Int.lt_floor_add_one (b / ρ)
  rw [h] at h1 h2
  have : |a / ρ - b / ρ| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hρ, div_lt_one hρ] at this
  exact this

/-- The output of the extraction: dot-product triples. -/
structure DotTriples (ρ : ℝ) (M : ℕ) (κ : ℝ) (f : ℝ → ℝ) (A : ℤ → Set ℝ)
    (k0 w : ℤ) (Y g : ℤ → ℝ) (R : Finset ℤ) (T : Finset (ℤ × ℤ × ℤ)) : Prop where
  k0_mem : 0 ≤ k0 ∧ k0 < M
  T_mem : ∀ t ∈ T, (0 ≤ t.1 ∧ t.1 < M) ∧ t.2.1 ∈ R ∧ t.2.2 ∈ R
  Y_bound : ∀ j ∈ R, |Y j| ≤ 1
  Y_sep : ∀ j ∈ R, ∀ j' ∈ R, j ≠ j' → M * ρ ≤ |Y j - Y j'|
  Y_lin : ∀ j j' : ℤ, Y j - Y j' = M * ρ * (j - j')
  g_bound : ∀ j ∈ R, |g j| ≤ 8 / κ
  g_lip : ∀ j ∈ R, ∀ j' ∈ R, |g j - g j'| ≤ 1400 / κ ^ 2 * |Y j - Y j'|
  dot_mem : ∀ t ∈ T, ∃ v ∈ A k0,
    |((ρ * t.1 - ρ * k0) * (g t.2.2 - g t.2.1) + (f (ρ * t.1) - f (ρ * k0)) * (Y t.2.1 - Y t.2.2))
      - (v - w * ρ)| ≤ 4 * ρ

namespace CellHyp

variable {ρ : ℝ} {M : ℕ} {α K κ β : ℝ} {f : ℝ → ℝ} {V : Space → Space}
  {P : Finset (ℤ × ℤ × ℤ)} {A : ℤ → Set ℝ} {AL : ℤ × ℤ × ℤ → Set ℝ}

/-- Row decomposition of the second lattice coordinate. -/
theorem row_eq (_hM : 0 < M) (q : ℤ × ℤ × ℤ) :
    q.2.1 = (M : ℤ) * blockOf M q + q.2.1 % (M : ℤ) := by
  have := Int.mul_ediv_add_emod q.2.1 (M : ℤ)
  simp only [blockOf]
  omega

set_option maxHeartbeats 1000000 in
/-- **Extraction of dot-product triples.** -/
theorem exists_dotTriples (h : CellHyp ρ M α K κ β f V P A AL) (hP : P.Nonempty) {NB : ℝ}
    (hNB : (#(P.image (blockOf M)) : ℝ) ≤ NB) (hNBpos : 0 < NB)
    (hτ : (3 * (K * ((40 * (M * ρ)) / ρ) ^ α)) * M * (3 * (K * ((12 * (M * ρ)) / ρ) ^ α)) *
      (1 + 16 / κ) < (#P : ℝ) / (2 * NB)) :
    ∃ (k0 w : ℤ) (Y g : ℤ → ℝ) (R : Finset ℤ) (T : Finset (ℤ × ℤ × ℤ)),
      DotTriples ρ M κ f A k0 w Y g R T ∧
      (∀ t ∈ T, t.1 ∈ P.image (fun q => q.2.2)) ∧
      ((#P : ℝ) / (2 * M)) ^ 4 ≤
        (NB * (K * ((40 * (M * ρ)) / ρ) ^ α * (16 / κ + 3))) ^ 2 *
          (M * (M * (3 * (K * ((12 * (M * ρ)) / ρ) ^ α)))) *
          (M * (3 * (K * ((12 * (M * ρ)) / ρ) ^ α))) * #T := by
  classical
  have hρ := h.hρ
  have hMpos : (0 : ℝ) < M := by exact_mod_cast h.hM
  have hMZ : (0 : ℤ) < M := by exact_mod_cast h.hM
  have hκ := h.hκ
  have hK := h.hK
  have hρs : ρ ≤ (M : ℝ) * ρ := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast h.hM
    nlinarith
  -- rich cells
  set Prich := P.filter fun q => (#P : ℝ) / (2 * NB) ≤ #{q' ∈ P | blockOf M q' = blockOf M q}
    with hPrich
  have hPrich_card : (#P : ℝ) / 2 ≤ #Prich := card_rich_ge P (blockOf M) hNB hNBpos
  have hPrich_sub : Prich ⊆ P := Finset.filter_subset _ _
  have hal : ∀ q ∈ Prich, κ / 8 ≤ |V (cellPos ρ q) 0| := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact h.aligned_of_rich hτ hq'.1 hq'.2
  have hPpos : (0 : ℝ) < #P := by exact_mod_cast hP.card_pos
  have hPrich_ne : Prich.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < #Prich := lt_of_lt_of_le (by positivity) hPrich_card
    exact_mod_cast this
  -- a residue class of rows
  have hres_card : (#(Prich.image fun q => q.2.1 % (M : ℤ)) : ℝ) ≤ M := by
    have : #(Prich.image fun q => q.2.1 % (M : ℤ)) ≤ #(Finset.Ico 0 (M : ℤ)) := by
      apply Finset.card_le_card
      intro r hr
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hMZ.ne', Int.emod_lt_of_pos _ hMZ⟩
    simp only [Int.card_Ico, sub_zero, Int.toNat_natCast] at this
    exact_mod_cast this
  obtain ⟨r0, -, hr0⟩ := exists_card_fiber_ge Prich _ hPrich_ne hres_card
  set P1 := Prich.filter fun q => q.2.1 % (M : ℤ) = r0 with hP1
  have hP1_sub : P1 ⊆ P := (Finset.filter_subset _ _).trans hPrich_sub
  have hP1mem : ∀ q ∈ P1, q ∈ P ∧ κ / 8 ≤ |V (cellPos ρ q) 0| ∧
      q.2.1 = (M : ℤ) * blockOf M q + r0 := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    refine ⟨hPrich_sub hq'.1, hal q hq'.1, ?_⟩
    have := row_eq h.hM q
    rw [hq'.2] at this
    exact this
  have hP1card : (#P : ℝ) / (2 * M) ≤ #P1 := by
    have : (#Prich : ℝ) / M ≤ #P1 := hr0
    calc (#P : ℝ) / (2 * M) = (#P / 2) / M := by ring
      _ ≤ #Prich / M := by gcongr
      _ ≤ #P1 := this
  have hP1ne : P1.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < #P1 := lt_of_lt_of_le (by positivity) hP1card
    exact_mod_cast this
  -- representatives and tilts
  have hrep_ex : ∀ j : ℤ, ∃ p : ℤ × ℤ × ℤ, (∃ q ∈ P1, blockOf M q = j) →
      p ∈ P1 ∧ blockOf M p = j := by
    intro j
    by_cases hj : ∃ q ∈ P1, blockOf M q = j
    · obtain ⟨q, hq, hqj⟩ := hj
      exact ⟨q, fun _ => ⟨hq, hqj⟩⟩
    · exact ⟨(0, 0, 0), fun h' => absurd h' hj⟩
  choose rep hrep using hrep_ex
  set Wr : ℤ → Space := fun j => V (cellPos ρ (rep j)) with hWr
  set g : ℤ → ℝ := fun j => Wr j 2 / Wr j 0 with hg
  set Y : ℤ → ℝ := fun j => ρ * ((M : ℤ) * j + r0) with hY
  set R := P1.image (blockOf M) with hR
  have hrepR : ∀ j ∈ R, rep j ∈ P1 ∧ blockOf M (rep j) = j := by
    intro j hj
    obtain ⟨q, hq, hqj⟩ := Finset.mem_image.mp hj
    exact hrep j ⟨q, hq, hqj⟩
  -- the value `v` of the local grain of row `j`
  set vloc : ℤ × ℤ × ℤ → ℝ := fun q => ρ * q.1 + g (blockOf M q) * (ρ * q.2.2) with hvloc
  set lk : ℤ × ℤ × ℤ → ℤ × ℤ := fun q => (blockOf M q, ⌊vloc q / ρ⌋) with hlk
  set gc : ℤ × ℤ × ℤ → ℤ := fun q => ⌊globalValue ρ f q / ρ⌋ with hgc
  set zl : ℤ × ℤ × ℤ → ℤ := fun q => q.2.2 with hzl
  -- `vloc` is an affine function of the local value of the representative
  have hvloc_eq : ∀ q ∈ P1, vloc q = (⟪Wr (blockOf M q), cellPos ρ q⟫ -
      Wr (blockOf M q) 1 * (ρ * (M * blockOf M q + r0))) / Wr (blockOf M q) 0 := by
    intro q hq
    obtain ⟨-, hW0, hrow⟩ := hP1mem q hq
    have hjR : blockOf M q ∈ R := Finset.mem_image_of_mem _ hq
    obtain ⟨hrepP1, hrepj⟩ := hrepR _ hjR
    have hW0' : κ / 8 ≤ |Wr (blockOf M q) 0| := (hP1mem _ hrepP1).2.1
    have hne : Wr (blockOf M q) 0 ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hW0'; linarith
    rw [inner_cellPos, hrow]
    simp only [hvloc, hg]
    push_cast
    field_simp
    ring
  -- local classes: at most `NB K (40 M)^α (16/κ + 3)`
  set NLoc := NB * (K * ((40 * (M * ρ)) / ρ) ^ α * (16 / κ + 3)) with hNLoc
  have hloc_card : (#(P1.image lk) : ℝ) ≤ NLoc := by
    have hsub : P1.image lk ⊆ R.biUnion fun j => (P1.filter fun q => blockOf M q = j).image lk := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_biUnion.mpr ⟨blockOf M q, Finset.mem_image_of_mem _ hq,
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq, rfl⟩)⟩
    have hper : ∀ j ∈ R, (#((P1.filter fun q => blockOf M q = j).image lk) : ℝ) ≤
        K * ((40 * (M * ρ)) / ρ) ^ α * (16 / κ + 3) := by
      intro j hj
      obtain ⟨hrepP1, hrepj⟩ := hrepR j hj
      obtain ⟨hrepP, hrepal, -⟩ := hP1mem _ hrepP1
      set Pj := P1.filter fun q => blockOf M q = j
      have himg : Pj.image lk = (Pj.image fun q => ⌊(⟪Wr j, cellPos ρ q⟫ -
          Wr j 1 * (ρ * (M * j + r0))) / Wr j 0 / ρ⌋).image (fun c => (j, c)) := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro q hq
        have hq' := Finset.mem_filter.mp hq
        simp only [Function.comp, hlk, Prod.mk.injEq]
        refine ⟨hq'.2, ?_⟩
        rw [hvloc_eq q hq'.1, hq'.2]
      rw [himg]
      have hW0ne : Wr j 0 ≠ 0 := by
        intro h0; simp only [hWr] at h0; rw [h0, abs_zero] at hrepal; linarith
      calc (#((Pj.image fun q => ⌊(⟪Wr j, cellPos ρ q⟫ - Wr j 1 * (ρ * (M * j + r0))) /
              Wr j 0 / ρ⌋).image fun c => (j, c)) : ℝ)
          ≤ #(Pj.image fun q => ⌊(⟪Wr j, cellPos ρ q⟫ - Wr j 1 * (ρ * (M * j + r0))) /
              Wr j 0 / ρ⌋) := by exact_mod_cast Finset.card_image_le
        _ ≤ K * ((40 * (M * ρ)) / ρ) ^ α * (2 / |Wr j 0| + 3) := by
            apply card_floor_image_le_of_assouad_affine (h.locAD _ hrepP) le_rfl
              (by nlinarith) hρ hW0ne Pj (fun q => ⟪Wr j, cellPos ρ q⟫)
              (x := ⟪Wr j, cellPos ρ (rep j)⟫ - 20 * (M * ρ))
            · intro q hq
              have hq' := Finset.mem_filter.mp hq
              have hqP := (hP1mem q hq'.1).1
              apply h.locMem _ hrepP q hqP
              apply h.dist_cell_le_of_block hqP hrepP
              rw [hq'.2, hrepj]
            · intro q hq
              have hq' := Finset.mem_filter.mp hq
              have hqP := (hP1mem q hq'.1).1
              have hd : ‖cellPos ρ q - cellPos ρ (rep j)‖ ≤ 20 * (M * ρ) :=
                h.dist_cell_le_of_block hqP hrepP (by rw [hq'.2, hrepj])
              have hW : ‖Wr j‖ = 1 := h.Vunit _ hrepP
              have hin : |⟪Wr j, cellPos ρ q⟫ - ⟪Wr j, cellPos ρ (rep j)⟫| ≤ 20 * (M * ρ) := by
                rw [← inner_sub_right]
                calc |⟪Wr j, cellPos ρ q - cellPos ρ (rep j)⟫|
                    ≤ ‖Wr j‖ * ‖cellPos ρ q - cellPos ρ (rep j)‖ := abs_real_inner_le_norm _ _
                  _ ≤ 1 * (20 * (M * ρ)) := by rw [hW]; gcongr
                  _ = 20 * (M * ρ) := one_mul _
              rw [abs_le] at hin
              constructor <;> linarith
        _ ≤ K * ((40 * (M * ρ)) / ρ) ^ α * (16 / κ + 3) := by
            have hpos : 0 < |Wr j 0| := lt_of_lt_of_le (by positivity) hrepal
            have h2 : 2 / |Wr j 0| ≤ 16 / κ := by
              rw [div_le_div_iff₀ hpos hκ]; linarith
            have hC : 0 ≤ K * ((40 * (M * ρ)) / ρ) ^ α := by positivity
            gcongr
    have hRcard : (#R : ℝ) ≤ NB := by
      have : #R ≤ #(P.image (blockOf M)) := Finset.card_le_card (Finset.image_subset_image hP1_sub)
      exact le_trans (by exact_mod_cast this) hNB
    calc (#(P1.image lk) : ℝ) ≤ #(R.biUnion fun j => (P1.filter fun q => blockOf M q = j).image lk) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ j ∈ R, (#((P1.filter fun q => blockOf M q = j).image lk) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ R, K * ((40 * (M * ρ)) / ρ) ^ α * (16 / κ + 3) := Finset.sum_le_sum hper
      _ = #R * (K * ((40 * (M * ρ)) / ρ) ^ α * (16 / κ + 3)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ NLoc := by
          have hC : 0 ≤ K * ((40 * (M * ρ)) / ρ) ^ α * (16 / κ + 3) := by positivity
          rw [hNLoc]; gcongr
  -- global classes per layer and the keys `(layer, class)`
  set NG := 3 * (K * ((12 * (M * ρ)) / ρ) ^ α) with hNG
  set NZW := (M : ℝ) * NG with hNZW
  have hzw_card : (#(P1.image fun p => (zl p, gc p)) : ℝ) ≤ NZW := by
    set Ks := P1.image zl
    have hsub : (P1.image fun p => (zl p, gc p)) ⊆
        Ks.biUnion fun k => (P1.filter fun q => zl q = k).image fun p => (zl p, gc p) := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_biUnion.mpr ⟨zl q, Finset.mem_image_of_mem _ hq,
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq, rfl⟩)⟩
    have hKs : (#Ks : ℝ) ≤ M := by
      have : #Ks ≤ #(Finset.Ico 0 (M : ℤ)) := by
        apply Finset.card_le_card
        intro k hk
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_Ico.mpr (h.layer q (hP1mem q hq).1)
      simp only [Int.card_Ico, sub_zero, Int.toNat_natCast] at this
      exact_mod_cast this
    have hper : ∀ k ∈ Ks, (#((P1.filter fun q => zl q = k).image fun p => (zl p, gc p)) : ℝ)
        ≤ NG := by
      intro k hk
      set Pk := P1.filter fun q => zl q = k
      have himg : (Pk.image fun p => (zl p, gc p)) = (Pk.image gc).image fun c => (k, c) := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro q hq
        simp only [Function.comp, Prod.mk.injEq, and_true]
        exact (Finset.mem_filter.mp hq).2
      rw [himg]
      calc (#((Pk.image gc).image fun c => (k, c)) : ℝ) ≤ #(Pk.image gc) := by
            exact_mod_cast Finset.card_image_le
        _ ≤ NG := by
            apply card_floor_image_le_of_assouad (h.globAD k) le_rfl (by nlinarith) hρ Pk
              (fun q => globalValue ρ f q) (x := β - 6 * (M * ρ))
            · intro q hq
              have hq' := Finset.mem_filter.mp hq
              have := h.globMem q (hP1mem q hq'.1).1
              simp only [hzl] at hq'
              rwa [hq'.2] at this
            · intro q hq
              have hq' := Finset.mem_filter.mp hq
              have := h.region q (hP1mem q hq'.1).1
              rw [abs_le] at this
              constructor <;> linarith
    calc (#(P1.image fun p => (zl p, gc p)) : ℝ)
        ≤ #(Ks.biUnion fun k => (P1.filter fun q => zl q = k).image fun p => (zl p, gc p)) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ k ∈ Ks, (#((P1.filter fun q => zl q = k).image fun p => (zl p, gc p)) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Ks, NG := Finset.sum_le_sum hper
      _ = #Ks * NG := by rw [sum_const, nsmul_eq_mul]
      _ ≤ NZW := by
          have : 0 ≤ NG := by positivity
          rw [hNZW]; gcongr
  have hS_card : (#((keyPairs P1 lk).image fun pp => (zl pp.1, zl pp.2, gc pp.2)) : ℝ) ≤
      M * NZW := by
    have hsub : ((keyPairs P1 lk).image fun pp => (zl pp.1, zl pp.2, gc pp.2)) ⊆
        (Finset.Ico 0 (M : ℤ)) ×ˢ (P1.image fun p => (zl p, gc p)) := by
      intro x hx
      obtain ⟨pp, hpp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨h1, h2, -⟩ := mem_keyPairs.mp hpp
      exact Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr (h.layer _ (hP1mem _ h1).1),
        Finset.mem_image_of_mem _ h2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_product] at this
    simp only [Int.card_Ico, sub_zero, Int.toNat_natCast] at this
    calc (#((keyPairs P1 lk).image fun pp => (zl pp.1, zl pp.2, gc pp.2)) : ℝ)
        ≤ (M : ℝ) * #(P1.image fun p => (zl p, gc p)) := by exact_mod_cast this
      _ ≤ M * NZW := by gcongr
  -- quadruples
  obtain ⟨k0, w, Q0, hQ0, hQ0card⟩ :=
    exists_quadruples P1 hP1ne lk zl gc hloc_card hS_card hzw_card
  -- the triples
  set tr : ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) → ℤ × ℤ × ℤ :=
    fun x => (zl x.1.2, blockOf M x.1.1, blockOf M x.2.2) with htr
  set T := Q0.image tr with hT
  -- a cell of `P1` is determined by its block, layer and the floor of a value `ρ i + c`
  have hcell : ∀ q ∈ P1, ∀ q' ∈ P1, blockOf M q = blockOf M q' → q.2.2 = q'.2.2 →
      ∀ c : ℝ, ⌊(ρ * q.1 + c) / ρ⌋ = ⌊(ρ * q'.1 + c) / ρ⌋ → q = q' := by
    intro q hq q' hq' hb hk c hc
    have hy : q.2.1 = q'.2.1 := by
      rw [(hP1mem q hq).2.2, (hP1mem q' hq').2.2, hb]
    have hx : q.1 = q'.1 := int_eq_of_floor_eq hρ hc rfl
    exact Prod.ext hx (Prod.ext hy hk)
  have hgv : ∀ q : ℤ × ℤ × ℤ, globalValue ρ f q = ρ * q.1 + f (ρ * q.2.2) * (ρ * q.2.1) :=
    fun q => rfl
  have hinj : Set.InjOn tr (Q0 : Set _) := by
    intro x hx x' hx' hxx
    obtain ⟨a1, a2, b1, b2, hl1, hl2, hz1, hz4, hz23, hg23, hw1⟩ := hQ0 x hx
    obtain ⟨a1', a2', b1', b2', hl1', hl2', hz1', hz4', hz23', hg23', hw1'⟩ := hQ0 x' hx'
    simp only [htr, Prod.mk.injEq] at hxx
    obtain ⟨hk2, hj1, hj3⟩ := hxx
    simp only [hlk, Prod.mk.injEq] at hl1 hl2 hl1' hl2'
    simp only [hzl] at hz1 hz4 hz23 hk2 hz1' hz4' hz23'
    -- `p1`
    have hp1 : x.1.1 = x'.1.1 := by
      apply hcell _ a1 _ a1' hj1 (by rw [hz1, hz1'])
        (f (ρ * x.1.1.2.2) * (ρ * x.1.1.2.1))
      have hy : x.1.1.2.1 = x'.1.1.2.1 := by
        rw [(hP1mem _ a1).2.2, (hP1mem _ a1').2.2, hj1]
      have e1 : ⌊(ρ * x.1.1.1 + f (ρ * x.1.1.2.2) * (ρ * x.1.1.2.1)) / ρ⌋ = w := hw1
      have e2 : ⌊(ρ * x'.1.1.1 + f (ρ * x.1.1.2.2) * (ρ * x.1.1.2.1)) / ρ⌋ = w := by
        rw [← hw1', hgc]; simp only [globalValue]; rw [hy, hz1, hz1']
      rw [e1, e2]
    -- `p2`
    have hp2 : x.1.2 = x'.1.2 := by
      have hb : blockOf M x.1.2 = blockOf M x'.1.2 := by rw [← hl1.1, ← hl1'.1, hp1]
      apply hcell _ a2 _ a2' hb hk2 (g (blockOf M x.1.2) * (ρ * x.1.2.2.2))
      have e1 := hl1.2
      have e2 := hl1'.2
      rw [hp1] at e1
      simp only [hvloc] at e1 e2
      rw [← hb, ← hk2] at e2
      rw [← e1, e2]
    -- `p3`
    have hp3 : x.2.2 = x'.2.2 := by
      have hk3 : x.2.2.2.2 = x'.2.2.2.2 := by rw [← hz23, ← hz23', hk2]
      apply hcell _ b2 _ b2' hj3 hk3 (f (ρ * x.2.2.2.2) * (ρ * x.2.2.2.1))
      have hy : x.2.2.2.1 = x'.2.2.2.1 := by
        rw [(hP1mem _ b2).2.2, (hP1mem _ b2').2.2, hj3]
      have e1 : ⌊(ρ * x.2.2.1 + f (ρ * x.2.2.2.2) * (ρ * x.2.2.2.1)) / ρ⌋ = gc x.1.2 :=
        hg23.symm
      have e2 : ⌊(ρ * x'.2.2.1 + f (ρ * x.2.2.2.2) * (ρ * x.2.2.2.1)) / ρ⌋ = gc x'.1.2 := by
        rw [hg23', hgc]; simp only [globalValue]; rw [hy, hk3]
      rw [e1, e2, hp2]
    -- `p4`
    have hp4 : x.2.1 = x'.2.1 := by
      have hb : blockOf M x.2.1 = blockOf M x'.2.1 := by rw [hl2.1, hl2'.1, hp3]
      have hk4 : x.2.1.2.2 = x'.2.1.2.2 := by rw [hz4, hz4']
      apply hcell _ b1 _ b1' hb hk4 (g (blockOf M x.2.1) * (ρ * x.2.1.2.2))
      have e1 := hl2.2
      have e2 := hl2'.2
      rw [← hp3] at e2
      simp only [hvloc] at e1 e2
      rw [← hb, ← hk4] at e2
      rw [e1, ← e2]
    exact Prod.ext (Prod.ext hp1 hp2) (Prod.ext hp4 hp3)
  have hTcard : #T = #Q0 := Finset.card_image_of_injOn hinj
  -- `Q0` is nonempty
  have hQ0ne : Q0.Nonempty := by
    have hP1pos : (0 : ℝ) < #P1 := by exact_mod_cast hP1ne.card_pos
    have h4 : (0 : ℝ) < (#P1 : ℝ) ^ 4 := pow_pos hP1pos 4
    have hQ0pos : (0 : ℝ) < #Q0 := by
      by_contra h0
      have h0' : (#Q0 : ℝ) = 0 := le_antisymm (not_lt.mp h0) (Nat.cast_nonneg _)
      rw [h0', mul_zero] at hQ0card
      linarith
    exact Finset.card_pos.mp (by exact_mod_cast hQ0pos)
  obtain ⟨x0, hx0⟩ := hQ0ne
  -- tilt bounds
  have hWbd : ∀ j ∈ R, |Wr j 2| ≤ 1 ∧ κ / 8 ≤ |Wr j 0| := by
    intro j hj
    have hrP1 := (hrepR j hj).1
    refine ⟨?_, (hP1mem _ hrP1).2.1⟩
    rw [← h.Vunit _ (hP1mem _ hrP1).1]
    exact abs_apply_le_norm _ 2
  have hYrep : ∀ j ∈ R, Y j = ρ * (rep j).2.1 := by
    intro j hj
    obtain ⟨hrP1, hrj⟩ := hrepR j hj
    rw [(hP1mem _ hrP1).2.2, hrj]
    simp only [hY]
    push_cast
    ring
  refine ⟨k0, w, Y, g, R, T, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- `k0` is a layer
    obtain ⟨a1, -, -, -, -, -, hz1, -⟩ := hQ0 x0 hx0
    rw [← hz1]
    exact h.layer _ (hP1mem _ a1).1
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨a1, a2, b1, b2, -⟩ := hQ0 x hx
    exact ⟨h.layer _ (hP1mem _ a2).1, Finset.mem_image_of_mem _ a1, Finset.mem_image_of_mem _ b2⟩
  · intro j hj
    rw [hYrep j hj]
    exact h.ybound _ (hP1mem _ (hrepR j hj).1).1
  · intro j hj j' hj' hjj
    simp only [hY]
    push_cast
    have : (1 : ℝ) ≤ |((j - j' : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |j - j'| := Int.one_le_abs (sub_ne_zero.mpr hjj)
      exact_mod_cast this
    push_cast at this
    have e : ρ * ((M : ℝ) * j + r0) - ρ * ((M : ℝ) * j' + r0) = (M * ρ) * (j - j') := by ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < M * ρ)]
    nlinarith
  · intro j j'
    simp only [hY]
    push_cast
    ring
  · intro j hj
    obtain ⟨h2, h0⟩ := hWbd j hj
    simp only [hg]
    rw [abs_div]
    have hpos : 0 < |Wr j 0| := lt_of_lt_of_le (by positivity) h0
    rw [div_le_div_iff₀ hpos hκ]
    nlinarith
  · intro j hj j' hj'
    obtain ⟨h2, h0⟩ := hWbd j hj
    obtain ⟨h2', h0'⟩ := hWbd j' hj'
    have hp0 : 0 < |Wr j 0| := lt_of_lt_of_le (by positivity) h0
    have hp0' : 0 < |Wr j' 0| := lt_of_lt_of_le (by positivity) h0'
    obtain ⟨hrP1, -⟩ := hrepR j hj
    obtain ⟨hrP1', -⟩ := hrepR j' hj'
    have hlip := h.Vlip _ (hP1mem _ hrP1).1 _ (hP1mem _ hrP1').1
    have hdist := h.dist_cell_le (hP1mem _ hrP1).1 (hP1mem _ hrP1').1
    rw [← hYrep j hj, ← hYrep j' hj'] at hdist
    set Δ := ‖Wr j - Wr j'‖ with hΔ
    have hΔ0 : |Wr j 0 - Wr j' 0| ≤ Δ := by
      have := abs_apply_le_norm (Wr j - Wr j') 0
      simpa [PiLp.sub_apply] using this
    have hΔ2 : |Wr j 2 - Wr j' 2| ≤ Δ := by
      have := abs_apply_le_norm (Wr j - Wr j') 2
      simpa [PiLp.sub_apply] using this
    -- `|a/b - c/d| ≤ 72 Δ / κ²`
    have hkey : |g j - g j'| ≤ 72 / κ ^ 2 * Δ := by
      simp only [hg]
      have hne : Wr j 0 ≠ 0 := abs_pos.mp hp0
      have hne' : Wr j' 0 ≠ 0 := abs_pos.mp hp0'
      have e : Wr j 2 / Wr j 0 - Wr j' 2 / Wr j' 0 =
          (Wr j 2 - Wr j' 2) / Wr j 0 + Wr j' 2 * (Wr j' 0 - Wr j 0) / (Wr j 0 * Wr j' 0) := by
        field_simp; ring
      rw [e]
      calc |(Wr j 2 - Wr j' 2) / Wr j 0 + Wr j' 2 * (Wr j' 0 - Wr j 0) / (Wr j 0 * Wr j' 0)|
          ≤ |(Wr j 2 - Wr j' 2) / Wr j 0| +
            |Wr j' 2 * (Wr j' 0 - Wr j 0) / (Wr j 0 * Wr j' 0)| := abs_add_le _ _
        _ = |Wr j 2 - Wr j' 2| / |Wr j 0| +
            |Wr j' 2| * |Wr j' 0 - Wr j 0| / (|Wr j 0| * |Wr j' 0|) := by
            rw [abs_div, abs_div, abs_mul, abs_mul]
        _ ≤ Δ / (κ / 8) + 1 * Δ / ((κ / 8) * (κ / 8)) := by
            gcongr
            rw [abs_sub_comm]; exact hΔ0
        _ = 8 / κ * Δ + 64 / κ ^ 2 * Δ := by field_simp; ring
        _ ≤ 72 / κ ^ 2 * Δ := by
            have hΔnn : 0 ≤ Δ := norm_nonneg _
            have h8 : 8 / κ ≤ 8 / κ ^ 2 := by
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              nlinarith [h.hκ1]
            calc 8 / κ * Δ + 64 / κ ^ 2 * Δ ≤ 8 / κ ^ 2 * Δ + 64 / κ ^ 2 * Δ := by gcongr
              _ = 72 / κ ^ 2 * Δ := by ring
    by_cases hjj : j = j'
    · subst hjj; simp
    · have hsep : M * ρ ≤ |Y j - Y j'| := by
        simp only [hY]
        push_cast
        have : (1 : ℝ) ≤ |((j - j' : ℤ) : ℝ)| := by
          have : (1 : ℤ) ≤ |j - j'| := Int.one_le_abs (sub_ne_zero.mpr hjj)
          exact_mod_cast this
        push_cast at this
        have e : ρ * ((M : ℝ) * j + r0) - ρ * ((M : ℝ) * j' + r0) = (M * ρ) * (j - j') := by ring
        rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < M * ρ)]
        nlinarith
      have hΔle : Δ ≤ 19 * |Y j - Y j'| := by
        have : ‖cellPos ρ (rep j) - cellPos ρ (rep j')‖ ≤ 19 * |Y j - Y j'| := by linarith
        exact le_trans hlip this
      calc |g j - g j'| ≤ 72 / κ ^ 2 * Δ := hkey
        _ ≤ 72 / κ ^ 2 * (19 * |Y j - Y j'|) := by gcongr
        _ ≤ 1400 / κ ^ 2 * |Y j - Y j'| := by
            have : 0 ≤ |Y j - Y j'| := abs_nonneg _
            have : 0 < κ ^ 2 := by positivity
            rw [← mul_assoc]
            gcongr
            rw [div_mul_eq_mul_div]
            gcongr
            norm_num
  · -- the dot relation
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨a1, a2, b1, b2, hl1, hl2, hz1, hz4, hz23, hg23, hw1⟩ := hQ0 x hx
    simp only [hlk, Prod.mk.injEq] at hl1 hl2
    simp only [hzl] at hz1 hz4 hz23
    have hfinal : ∀ D gv4 gv1 : ℝ, |D - (gv4 - gv1)| < 3 * ρ → (w : ℝ) * ρ ≤ gv1 →
        gv1 < w * ρ + ρ → |D - (gv4 - w * ρ)| ≤ 4 * ρ := by
      intro D gv4 gv1 h1 h2 h3
      rw [abs_lt] at h1
      rw [abs_le]
      constructor <;> linarith
    refine ⟨globalValue ρ f x.2.1, ?_, ?_⟩
    · have := h.globMem _ (hP1mem _ b1).1
      rwa [hz4] at this
    · -- rows and layers of the four cells
      have hy1 : ρ * (x.1.1.2.1 : ℝ) = Y (blockOf M x.1.1) := by
        rw [(hP1mem _ a1).2.2]; simp only [hY]; push_cast; ring
      have hy2 : ρ * (x.1.2.2.1 : ℝ) = Y (blockOf M x.1.1) := by
        rw [(hP1mem _ a2).2.2, ← hl1.1]; simp only [hY]; push_cast; ring
      have hy3 : ρ * (x.2.2.2.1 : ℝ) = Y (blockOf M x.2.2) := by
        rw [(hP1mem _ b2).2.2]; simp only [hY]; push_cast; ring
      have hy4 : ρ * (x.2.1.2.1 : ℝ) = Y (blockOf M x.2.2) := by
        rw [(hP1mem _ b1).2.2, hl2.1]; simp only [hY]; push_cast; ring
      have h12 : |(ρ * (x.1.2.1 : ℝ) + g (blockOf M x.1.1) * (ρ * (x.1.2.2.2 : ℝ))) -
          (ρ * (x.1.1.1 : ℝ) + g (blockOf M x.1.1) * (ρ * (k0 : ℝ)))| < ρ := by
        have := abs_sub_lt_of_floor_div_eq hρ hl1.2.symm
        simp only [hvloc] at this
        rw [← hl1.1, hz1] at this
        exact this
      have h34 : |(ρ * (x.2.1.1 : ℝ) + g (blockOf M x.2.2) * (ρ * (k0 : ℝ))) -
          (ρ * (x.2.2.1 : ℝ) + g (blockOf M x.2.2) * (ρ * (x.1.2.2.2 : ℝ)))| < ρ := by
        have := abs_sub_lt_of_floor_div_eq hρ hl2.2
        simp only [hvloc] at this
        rw [hl2.1, hz4, ← hz23] at this
        exact this
      have h23 : |(ρ * (x.2.2.1 : ℝ) + f (ρ * (x.1.2.2.2 : ℝ)) * Y (blockOf M x.2.2)) -
          (ρ * (x.1.2.1 : ℝ) + f (ρ * (x.1.2.2.2 : ℝ)) * Y (blockOf M x.1.1))| < ρ := by
        have := abs_sub_lt_of_floor_div_eq hρ hg23.symm
        rw [hgv, hgv, ← hz23, hy2, hy3] at this
        exact this
      have hid := dot_identity (F0 := f (ρ * k0)) h12 h23 h34
      have hgv1 : globalValue ρ f x.1.1 =
          ρ * (x.1.1.1 : ℝ) + f (ρ * (k0 : ℝ)) * Y (blockOf M x.1.1) := by
        rw [hgv, hz1, hy1]
      have hgv4 : globalValue ρ f x.2.1 =
          ρ * (x.2.1.1 : ℝ) + f (ρ * (k0 : ℝ)) * Y (blockOf M x.2.2) := by
        rw [hgv, hz4, hy4]
      have hfl1 := Int.floor_le (globalValue ρ f x.1.1 / ρ)
      have hfl2 := Int.lt_floor_add_one (globalValue ρ f x.1.1 / ρ)
      have hw1' : ⌊globalValue ρ f x.1.1 / ρ⌋ = w := hw1
      rw [hw1'] at hfl1 hfl2
      have hg1 : (w : ℝ) * ρ ≤ globalValue ρ f x.1.1 := by
        rwa [le_div_iff₀ hρ] at hfl1
      have hg2 : globalValue ρ f x.1.1 < (w : ℝ) * ρ + ρ := by
        rw [div_lt_iff₀ hρ] at hfl2; linarith
      rw [hgv4]
      rw [hgv1] at hg1 hg2
      exact hfinal _ _ _ hid hg1 hg2
  · -- every retained height is occupied by an original cell
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨_, a2, _⟩ := hQ0 x hx
    exact Finset.mem_image_of_mem (fun q => q.2.2) (hP1mem _ a2).1
  · -- the count
    rw [hTcard]
    have h1 : ((#P : ℝ) / (2 * M)) ^ 4 ≤ (#P1 : ℝ) ^ 4 := by
      apply pow_le_pow_left₀ (by positivity) hP1card
    calc ((#P : ℝ) / (2 * M)) ^ 4 ≤ (#P1 : ℝ) ^ 4 := h1
      _ ≤ NLoc ^ 2 * (M * NZW) * NZW * #Q0 := hQ0card
      _ = _ := by rw [hNLoc, hNZW, hNG]

end CellHyp

end

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
