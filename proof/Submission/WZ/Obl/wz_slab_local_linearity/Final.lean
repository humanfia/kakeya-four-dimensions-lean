-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.Final.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellModel
import Submission.WZ.Obl.wz_slab_local_linearity.CellDichotomy
import Submission.WZ.Obl.wz_slab_local_linearity.LocalProjectionCover
import Submission.WZ.Obl.wz_slab_local_linearity.GlobalProjectionCover
import Submission.WZ.Obl.wz_slab_local_linearity.QuarterCells
import Submission.WZ.Obl.wz_slab_local_linearity.SlabCoordinates
import Submission.WZ.Obl.wz_slab_local_linearity.SlabHyp
import Submission.WZ.Obl.wz_slab_local_linearity.Clamp

/-!
# Assembly of the slab theorem

The frozen hypotheses on a union of grid cubes are moved to the cell form of sticky
Lemma 5.3 (`finite_cell_linearity`): the vertical index is shifted so that the layers
start at `0`, the slope is clamped outside the slab, the global grain values are the
horizontal slices, and the local grain values are the projections onto the normal at the
centre cell, covered through the local projection-volume bound.  The affine fit at the
occupied layers is then spread over lower quarter cells.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric MeasureTheory CellProofs
open scoped RealInnerProductSpace

/-- Translating a set translates its covers. -/
lemma CoverUpper.translate {A : Set ℝ} {r N : ℝ} (b : ℝ) (h : CoverUpper A r N) :
    CoverUpper ((fun x => x + b) '' A) r N := by
  obtain ⟨m, c, hc, hm⟩ := h
  refine ⟨m, fun j => c j + b, ?_, hm⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
  refine mem_iUnion.mpr ⟨j, ?_⟩
  simpa only [mem_closedBall, Real.dist_eq, add_sub_add_right_eq_sub] using hj

/-- The empty set is AD with any nonnegative constant. -/
lemma intervalAD_empty {d α C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) : IntervalAD d α C ∅ := by
  intro r R a hdr hrR
  refine ⟨0, Fin.elim0, by simp, ?_⟩
  simp only [Nat.cast_zero]
  exact mul_nonneg hC (Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _)

lemma coverUpper_empty {r N : ℝ} (hN : 0 ≤ N) : CoverUpper (∅ : Set ℝ) r N :=
  ⟨0, Fin.elim0, by simp, by simpa using hN⟩

/-- `(4 √ρ / ρ) ^ (1 - σ) ≤ 4 ρ ^ (-(1 - σ) / 2)`. -/
lemma global_power_bound {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) :
    (4 * Real.sqrt ρ / ρ) ^ (1 - σ) ≤ 4 * ρ ^ (-(1 - σ) / 2) := by
  have he : 4 * Real.sqrt ρ / ρ = 4 * ρ ^ (-(1 : ℝ) / 2) := by
    rw [mul_div_assoc, Real.sqrt_eq_rpow,
      show (-(1 : ℝ) / 2) = 1 / 2 - 1 by norm_num, Real.rpow_sub hρ, Real.rpow_one]
  rw [he, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
  have h4 : (4 : ℝ) ^ (1 - σ) ≤ 4 := by
    calc (4 : ℝ) ^ (1 - σ) ≤ 4 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  rw [show -(1 : ℝ) / 2 * (1 - σ) = -(1 - σ) / 2 by ring]
  exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hρ.le _)

/-- The local volume exponent, divided by one power of `ρ`. -/
lemma local_power_eq {ρ σ η : ℝ} (hρ : 0 < ρ) (C : ℝ) :
    C * ρ ^ ((1 + σ) / 2 - η) / ρ = C * ρ ^ (-(1 - σ) / 2 - η) := by
  rw [mul_div_assoc]
  congr 1
  rw [show -(1 - σ) / 2 - η = ((1 + σ) / 2 - η) - 1 by ring,
    Real.rpow_sub hρ ((1 + σ) / 2 - η) 1, Real.rpow_one]

/-- **The slab theorem**, in the named form of the frozen statement. -/
theorem slab_local_linearity (hproj : ProjectionDichotomy) {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η ρ₀ : ℝ, 0 < η ∧ 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∀ (z₀ c₀ : ℝ) (Z : Set ℝ) (f : ℝ → ℝ) (K : Finset (Fin 3 → ℤ))
        (V : Space3 → Space3),
      SlabHyp ρ σ η z₀ c₀ Z f K V →
      ∃ Zl : Set ℝ, Zl ⊆ Z ∧ ENNReal.ofReal (ρ ^ ((1 : ℝ) / 2 + ε)) ≤ volume Zl ∧
        ∃ a b : ℝ, ∀ z ∈ Zl, |f z - (a + b * z)| ≤ ρ := by
  classical
  have hfin := finiteDichotomy_of_projection hproj hσ hσ1
  set C₀ : ℝ := 38 * (802 : ℝ) ^ 3 with hC₀def
  have hC₀ : 0 < C₀ := by positivity
  obtain ⟨η, ρ₁, hη, hρ₁, hcell⟩ := finite_cell_linearity hσ hσ1 hfin hC₀ ε hε
  obtain ⟨ρ₂, hρ₂, hquarter⟩ := quarter_cell_measure_budget hε
  refine ⟨η, min ρ₁ (min ρ₂ (1 / 100)), hη, by positivity, ?_⟩
  intro ρ hρ hρ₀ z₀ c₀ Z f K V h
  have hρ₁' : ρ ≤ ρ₁ := hρ₀.trans (min_le_left _ _)
  have hρ₂' : ρ ≤ ρ₂ := hρ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ100 : ρ ≤ 1 / 100 := hρ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρ1 : ρ ≤ 1 := by linarith
  set s := Real.sqrt ρ with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hρ
  have hs2 : s * s = ρ := Real.mul_self_sqrt hρ.le
  have hρs : ρ ≤ 4 * s := by nlinarith
  have hzs : z₀ ≤ z₀ + s := by linarith
  set k₀ : ℤ := slabBase ρ z₀ with hk₀
  set M : ℕ := slabLayers ρ with hMdef
  obtain ⟨hMlo, hMhi, hMρ1⟩ := slabLayers_bounds hρ hρ100
  obtain ⟨hsMρ, hMρs⟩ := cell_layer_scale hρ hMlo hMhi
  set P : Finset (ℤ × ℤ × ℤ) := shiftCells k₀ K with hPdef
  set g : ℝ → ℝ := fun z => clampSlope f z₀ (z₀ + s) hzs (z + ρ * k₀) with hgdef
  set W : Space → Space := fun x => V (x + heightShift ρ k₀) with hWdef
  -- the corner of a shifted cell
  have hcorner : ∀ q ∈ P, cellPos ρ q + heightShift ρ k₀ ∈ gridCubes ρ K :=
    fun q hq => shifted_corner_mem hρ hq
  have hheight : ∀ p ∈ gridCubes ρ K, p 2 ∈ Icc z₀ (z₀ + s) :=
    fun p hp => h.heights (h.region p hp).2.2.1
  have hcornerZ : ∀ q ∈ P, ρ * (q.2.2 : ℝ) + ρ * k₀ ∈ Icc z₀ (z₀ + s) := by
    intro q hq
    have := hheight _ (hcorner q hq)
    rwa [shifted_corner_two] at this
  have hgq : ∀ q ∈ P, g (ρ * (q.2.2 : ℝ)) = f (ρ * (q.2.2 : ℝ) + ρ * k₀) := by
    intro q hq
    simp only [hgdef]
    exact clampSlope_eq hzs (hcornerZ q hq)
  -- global grain sets: the horizontal slices
  set A : ℤ → Set ℝ := fun k => {u : ℝ | ∃ p ∈ gridCubes ρ K,
      p 2 = ρ * (k : ℝ) + ρ * k₀ ∧ u = p 0 + f (ρ * (k : ℝ) + ρ * k₀) * p 1} with hAdef
  have hAempty : ∀ k : ℤ, ρ * (k : ℝ) + ρ * k₀ ∉ Z → A k = ∅ := by
    intro k hk
    ext u
    simp only [hAdef, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨p, hp, hp2, -⟩
    exact hk (hp2 ▸ (h.region p hp).2.2.1)
  have hAAD : ∀ k : ℤ, Assouad ρ (1 - σ) (ρ ^ (-η)) (A k) := by
    intro k
    by_cases hk : ρ * (k : ℝ) + ρ * k₀ ∈ Z
    · exact h.global_AD _ hk
    · rw [hAempty k hk]
      exact intervalAD_empty hρ (Real.rpow_nonneg hρ.le _)
  have hAcover : ∀ k : ℤ, CoverUpper (A k) ρ (C₀ * ρ ^ (-(1 - σ) / 2 - η)) := by
    intro k
    have hbound : ρ ^ (-η) * (4 * s / ρ) ^ (1 - σ) ≤ C₀ * ρ ^ (-(1 - σ) / 2 - η) := by
      have hp := global_power_bound hρ hσ
      calc ρ ^ (-η) * (4 * s / ρ) ^ (1 - σ) ≤ ρ ^ (-η) * (4 * ρ ^ (-(1 - σ) / 2)) :=
            mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hρ.le _)
        _ = 4 * ρ ^ (-(1 - σ) / 2 - η) := by
            rw [show -(1 - σ) / 2 - η = -(1 - σ) / 2 + -η by ring, Real.rpow_add hρ]
            ring
        _ ≤ C₀ * ρ ^ (-(1 - σ) / 2 - η) :=
            mul_le_mul_of_nonneg_right (by rw [hC₀def]; norm_num) (Real.rpow_nonneg hρ.le _)
    by_cases hk : ρ * (k : ℝ) + ρ * k₀ ∈ Z
    · have hc := global_slice_cover (ρ := ρ) (s := s) (z₀ := z₀) (c₀ := c₀)
        (z := ρ * (k : ℝ) + ρ * k₀) (E := gridCubes ρ K) (f := f)
        hρs h.f_lip
        (fun p hp => ⟨(h.region p hp).2.1, hheight p hp, (h.region p hp).2.2.2⟩)
        (h.global_AD _ hk)
      exact hc.mono_bound hbound
    · rw [hAempty k hk]
      exact coverUpper_empty (by positivity)
  -- local grain sets: projections onto the normal at the centre cell
  set AL : ℤ × ℤ × ℤ → Set ℝ := fun p => {x : ℝ | ∃ q ∈ P,
      ‖cellPos ρ q - cellPos ρ p‖ ≤ 20 * (M * ρ) ∧ x = ⟪W (cellPos ρ p), cellPos ρ q⟫}
    with hALdef
  have hALcover : ∀ p ∈ P, CoverUpper (AL p) ρ (C₀ * ρ ^ (-(1 - σ) / 2 - η)) := by
    intro p hp
    set pc := cellPos ρ p + heightShift ρ k₀ with hpc
    have hpcE : pc ∈ gridCubes ρ K := hcorner p hp
    have hloc := local_projection_cover hρ hρ100 (Real.rpow_nonneg hρ.le ((1 + σ) / 2 - η))
      K V (fun q hq => (h.normals q hq).1) h.normal_lip h.local_volume hpcE
    have htr := CoverUpper.translate (-⟪V pc, heightShift ρ k₀⟫) hloc
    rw [local_power_eq hρ] at htr
    apply htr.mono_set
    rintro x ⟨q, hq, hd, rfl⟩
    have hk := mem_shiftCells_iff.mp hq
    refine ⟨⟪V pc, gridCorner ρ ((shiftIndex k₀).symm q)⟫,
      ⟨(shiftIndex k₀).symm q, ?_, rfl⟩, ?_⟩
    · refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hk, ?_⟩)
      rw [← cellPos_add_heightShift, hpc, dist_eq_norm, add_sub_add_right_eq_sub]
      linarith
    · simp only [hWdef]
      rw [← cellPos_add_heightShift, inner_add_right]
      ring
  -- the cell hypotheses
  have hL := clampSlope_lipschitz hzs h.f_lip
  have hglip : ∀ z z' : ℝ, |g z - g z'| ≤ |z - z'| := by
    intro z z'
    have hd := hL.dist_le_mul (z + ρ * k₀) (z' + ρ * k₀)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, add_sub_add_right_eq_sub] at hd
    exact hd
  have hcellhyp : CellHyp ρ M 0 (C₀ * ρ ^ (-(1 - σ) / 2 - η)) (ρ ^ η) c₀ g W P A AL :=
    { hρ := hρ
      hM := slabLayers_pos ρ
      hs := hMρ1
      hK := by positivity
      hκ := Real.rpow_pos_of_pos hρ η
      hκ1 := Real.rpow_le_one hρ.le hρ1 hη.le
      hf_lip := fun z z' _ _ _ _ => hglip z z'
      hf4 := fun z _ _ => clampSlope_bound hzs h.f_bound _
      layer := fun q hq => shifted_layer_mem hρ hheight hq
      ybound := by
        intro q hq
        have := (h.region _ (hcorner q hq)).2.1
        rwa [shifted_corner_one] at this
      region := by
        intro q hq
        have hpE := hcorner q hq
        have hr := h.region _ hpE
        have hz := hheight _ hpE
        have hb := global_projection_bound hr.2.1 hz
          (h.f_lip _ hz _ ⟨le_rfl, hzs⟩) hr.2.2.2
        rw [shifted_corner_zero, shifted_corner_one, shifted_corner_two] at hb
        simp only [globalValue]
        rw [hgq q hq]
        linarith
      Vunit := fun q hq => (h.normals _ (hcorner q hq)).1
      Vhor := by
        intro q hq
        have := (h.normals _ (hcorner q hq)).2
        rw [show (ρ ^ η) ^ 2 = ρ ^ (2 * η) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; ring_nf]
        exact this
      Vlip := by
        intro q hq q' hq'
        have := h.normal_lip _ (hcorner q hq) _ (hcorner q' hq')
        rwa [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub] at this
      globAD := fun k => assouad_zero_of_cover (hAcover k)
      globMem := by
        intro q hq
        refine ⟨cellPos ρ q + heightShift ρ k₀, hcorner q hq, shifted_corner_two ρ k₀ q, ?_⟩
        simp only [globalValue]
        rw [hgq q hq, shifted_corner_zero, shifted_corner_one]
      locAD := fun p hp => assouad_zero_of_cover (hALcover p hp)
      locMem := fun p _ q hq hd => ⟨q, hq, hd, rfl⟩ }
  have hPcard : ρ ^ (-2 + σ / 2 + η) ≤ (P.card : ℝ) := by
    rw [hPdef, card_shiftCells]
    have := gridCubes_card_lower hρ K h.mass
    rwa [show 1 + σ / 2 + η - 3 = -2 + σ / 2 + η by ring] at this
  obtain ⟨a, b, hb, S, hSP, hScard, hfS⟩ :=
    hcell ρ hρ hρ₁' M c₀ g W P A AL hMlo hMhi hcellhyp hPcard hAAD
  -- back to the original heights
  set S' := S.image (fun k => k + k₀) with hS'def
  have hS'K : S' ⊆ K.image (fun k => k 2) := shiftCells_height_image hSP
  have hZcells : heightCells ρ S' ⊆ Z :=
    (heightCells_mono ρ hS'K).trans
      (grid_heightCells_subset hρ (fun p hp => (h.region p hp).2.2.1))
  have hfZ : ∀ x ∈ Z, ∀ y ∈ Z, |f x - f y| ≤ |x - y| :=
    fun x hx y hy => h.f_lip x (h.heights hx) y (h.heights hy)
  have hanchor : ∀ k ∈ S', |f (ρ * k) - ((a - b * (ρ * k₀)) + b * (ρ * k))| ≤ ρ / 8 := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨q, hq, hqj⟩ := Finset.mem_image.mp (hSP hj)
    have hfj := hfS j hj
    have hgj : g (ρ * (j : ℝ)) = f (ρ * (j : ℝ) + ρ * k₀) := by
      rw [← hqj]
      exact hgq q hq
    rw [hgj] at hfj
    have he : ρ * ((j + k₀ : ℤ) : ℝ) = ρ * (j : ℝ) + ρ * k₀ := by push_cast; ring
    rw [he]
    have he2 : (a - b * (ρ * k₀)) + b * (ρ * (j : ℝ) + ρ * k₀) = a + b * (ρ * j) := by ring
    rw [he2]
    exact hfj
  obtain ⟨Zl, hZl, hvol, haff⟩ := quarter_height_extraction hρ hZcells hb hfZ hanchor
  refine ⟨Zl, hZl, le_trans ?_ hvol, a - b * (ρ * k₀), b, haff⟩
  apply ENNReal.ofReal_le_ofReal
  rw [hS'def, shifted_height_card]
  calc ρ ^ ((1 : ℝ) / 2 + ε) ≤ ρ ^ ((ε - 1) / 2) * ρ / 4 := hquarter ρ hρ hρ₂'
    _ ≤ (S.card : ℝ) * ρ / 4 := by gcongr

end WangZahlLot.Obl.wz_slab_local_linearity
