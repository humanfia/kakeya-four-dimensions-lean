-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.PerTube.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Cordoba

/-!
The filling of the box of one flat tube (WZ Lemma 7.14, Step 3), for the proof of
`WangZahlLot.wz_flat_cluster_slab_filling`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

/-- The final real inequality of `per_tube`. -/
lemma pt_final_real {δ ρ L θ κ lam' P Λ Λm F V D b : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 0 < L) (hP : 0 ≤ P) (hΛ : 1 ≤ Λ) (hΛm : Λm ≤ Λ)
    (hF : 0 ≤ F) (hV : 0 ≤ V) (hD : D = 32 * δ / θ) (hb : b = 32 * ρ * L)
    (ha : lam' * δ ^ 2 ≤ 128 * (2 * (D + 2 * δ) + δ) * δ ^ 2 * F)
    (hc : (κ * (L * δ ^ 2 / 8)) ^ 2 * F ≤ 20000 * L * δ ^ 2 * Λm * V)
    (hnum : P * (10 ^ 13 * (ρ / θ) * Λ) ≤ κ ^ 2 * lam') :
    P * (10 * δ * b * 2) ≤ V := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hδθ : δ ≤ δ / θ := by
    rw [le_div_iff₀ hθ]
    nlinarith
  have hDle : 2 * (D + 2 * δ) + δ ≤ 69 * (δ / θ) := by
    have e : 2 * (D + 2 * δ) + δ = 64 * (δ / θ) + 5 * δ := by
      rw [hD]; ring
    rw [e]
    linarith
  have ha' : lam' ≤ 8832 * (δ / θ) * F := by
    have h1 : lam' * δ ^ 2 ≤ (8832 * (δ / θ) * F) * δ ^ 2 := by
      calc lam' * δ ^ 2 ≤ 128 * (2 * (D + 2 * δ) + δ) * δ ^ 2 * F := ha
        _ ≤ 128 * (69 * (δ / θ)) * δ ^ 2 * F := by gcongr
        _ = (8832 * (δ / θ) * F) * δ ^ 2 := by ring
    exact le_of_mul_le_mul_right h1 hδ2
  have hd' : P * 10 ^ 13 * ρ * Λ ≤ 8832 * κ ^ 2 * δ * F := by
    have h1 : P * (10 ^ 13 * (ρ / θ) * Λ) ≤ κ ^ 2 * (8832 * (δ / θ) * F) :=
      hnum.trans (mul_le_mul_of_nonneg_left ha' (sq_nonneg κ))
    have e1 : P * (10 ^ 13 * (ρ / θ) * Λ) = (P * 10 ^ 13 * ρ * Λ) * (1 / θ) := by ring
    have e2 : κ ^ 2 * (8832 * (δ / θ) * F) = (8832 * κ ^ 2 * δ * F) * (1 / θ) := by ring
    rw [e1, e2] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hc' : κ ^ 2 * L * δ ^ 2 * F ≤ 1280000 * Λ * V := by
    have h1 : (κ * (L * δ ^ 2 / 8)) ^ 2 * F ≤ 20000 * L * δ ^ 2 * Λ * V := by
      refine hc.trans ?_
      have h0 : 0 ≤ 20000 * L * δ ^ 2 := by positivity
      have h2 := mul_le_mul_of_nonneg_left hΛm h0
      have h3 := mul_le_mul_of_nonneg_right h2 hV
      simpa only [mul_assoc] using h3
    have e : (κ * (L * δ ^ 2 / 8)) ^ 2 * F = (κ ^ 2 * L * δ ^ 2 * F) * (L * δ ^ 2 / 64) := by
      ring
    have e2 : 20000 * L * δ ^ 2 * Λ * V = (1280000 * Λ * V) * (L * δ ^ 2 / 64) := by ring
    rw [e, e2] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hX : P * 10 ^ 13 * ρ * Λ * (L * δ) ≤ 8832 * 1280000 * Λ * V := by
    calc P * 10 ^ 13 * ρ * Λ * (L * δ) ≤ 8832 * κ ^ 2 * δ * F * (L * δ) :=
          mul_le_mul_of_nonneg_right hd' (by positivity)
      _ = 8832 * (κ ^ 2 * L * δ ^ 2 * F) := by ring
      _ ≤ 8832 * (1280000 * Λ * V) := by gcongr
      _ = 8832 * 1280000 * Λ * V := by ring
  have hX' : P * 10 ^ 13 * ρ * L * δ ≤ 8832 * 1280000 * V := by
    have e1 : P * 10 ^ 13 * ρ * Λ * (L * δ) = (P * 10 ^ 13 * ρ * L * δ) * Λ := by ring
    have e2 : 8832 * 1280000 * Λ * V = (8832 * 1280000 * V) * Λ := by ring
    rw [e1, e2] at hX
    exact le_of_mul_le_mul_right hX (by linarith)
  have e3 : P * (10 * δ * b * 2) = 640 * (P * ρ * L * δ) := by rw [hb]; ring
  have e4 : P * 10 ^ 13 * ρ * L * δ = 10 ^ 13 * (P * ρ * L * δ) := by ring
  rw [e3]
  rw [e4] at hX'
  have hpos : 0 ≤ P * ρ * L * δ := by positivity
  nlinarith

/-- The number of axial cells is at most `1/δ`, so its logarithm is at most `log (1/δ)`. -/
lemma pt_log_cells {δ θ D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hD : D = 32 * δ / θ) :
    1 + 2 * δ ≤ ((⌈(1 + 2 * δ) / D⌉₊ : ℕ) : ℝ) * D ∧
      Real.log ((⌈(1 + 2 * δ) / D⌉₊ : ℕ) : ℝ) ≤ Real.log (1 / δ) := by
  have hD0 : 0 < D := by rw [hD]; positivity
  have hMD : 1 + 2 * δ ≤ ((⌈(1 + 2 * δ) / D⌉₊ : ℕ) : ℝ) * D := by
    have := Nat.le_ceil ((1 + 2 * δ) / D)
    rwa [div_le_iff₀ hD0] at this
  refine ⟨hMD, ?_⟩
  have hMpos : (0 : ℝ) < ((⌈(1 + 2 * δ) / D⌉₊ : ℕ) : ℝ) := by
    rcases (Nat.cast_nonneg (α := ℝ) ⌈(1 + 2 * δ) / D⌉₊).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hMD
      linarith
  have h1 : ((⌈(1 + 2 * δ) / D⌉₊ : ℕ) : ℝ) < (1 + 2 * δ) / D + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hD32 : 32 * δ ≤ D := by
    rw [hD, le_div_iff₀ hθ]
    nlinarith
  have h3 : (1 + 2 * δ) / D ≤ (1 + 2 * δ) / (32 * δ) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hD32
  have h4 : (1 + 2 * δ) / (32 * δ) = (1 / δ) / 32 + 1 / 16 := by
    field_simp
    ring
  have hs : 100 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  exact Real.log_le_log hMpos (by linarith)

/-- The box of one flat tube is filled. The tube `i` lies in the slab `Slab u t r` of
half-width `r ≤ θ/32`; through every point `p` of a set `Z3` of mass `lam' δ²` in the tube
passes a tube `j` of the family lying in the same slab, at angle in `(θ, 8ρ]` with the tube
`i`, whose regular shading `Z2 j ⊆ Y j` contains `p` and fills a `κ`-share of the
`L`-neighbourhood of `p` in that tube. Then the `10δ × b × 2` box around the tube `i`, with
`b = 32 ρ L`, is filled to a `δ^e` share by `⋃ Y`. -/
theorem per_tube {n : ℕ} {δ ρ b L θ κ lam' e : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hκ : 0 ≤ κ) (hlam' : 0 ≤ lam')
    (hb : b = 32 * ρ * L) (hL3 : 3 * δ ≤ L) (hL : 1 / 2 + δ + L ≤ 1) (hbδ : 2 * δ ≤ b)
    (x v : Fin n → Space) (Y : Fin n → Set Space) (hv : ∀ j, ‖v j‖ = 1)
    (hYm : ∀ j, MeasurableSet (Y j)) (hYT : ∀ j, Y j ⊆ Tube δ (x j) (v j))
    (i : Fin n) (u : Space) (t r : ℝ) (hu : ‖u‖ = 1)
    (hslab : Tube δ (x i) (v i) ⊆ Slab u t r)
    (hr32 : 32 * r ≤ θ) (hr : 3 * δ + 8 * r * (L + 2 * δ) ≤ 5 * δ)
    (hρL : 3 * δ + 8 * ρ * (L + 2 * δ) ≤ b / 2)
    (Z3 : Set Space) (hZ3m : MeasurableSet Z3) (hZ3 : Z3 ⊆ Tube δ (x i) (v i))
    (hZ3mass : ENNReal.ofReal (lam' * δ ^ 2) ≤ volume Z3)
    (Z2 : Fin n → Set Space) (hZ2m : ∀ j, MeasurableSet (Z2 j)) (hZ2Y : ∀ j, Z2 j ⊆ Y j)
    (hcross : ∀ p ∈ Z3, ∃ j, p ∈ Z2 j ∧ Tube δ (x j) (v j) ⊆ Slab u t r ∧
        θ < angle (v j) (v i) ∧ angle (v j) (v i) ≤ 8 * ρ ∧
        ENNReal.ofReal κ * volume (Tube δ (x j) (v j) ∩ ball p L) ≤ volume (Z2 j ∩ ball p L))
    (hnum : δ ^ e * (10 ^ 13 * (ρ / θ) * (1 + Real.log (1 / δ))) ≤ κ ^ 2 * lam') :
    ∃ (z : Space) (g : Space ≃ₗᵢ[ℝ] Space), Tube δ (x i) (v i) ⊆ Box (10 * δ) b 2 z g ∧
      ENNReal.ofReal (δ ^ e) * volume (Box (10 * δ) b 2 z g) ≤
        volume (Box (10 * δ) b 2 z g ∩ ⋃ j, Y j) := by
  have _ := hlam'
  -- Step 1: the frame adapted to the tube `i` and the slab
  have hu' : |inner ℝ u (v i)| ≤ 2 * r := slab_inner_dir hδ hslab
  have huv : |inner ℝ u (v i)| ≤ 1 / 2 := by linarith
  obtain ⟨g, hg2, hg0⟩ := adapted_frame hu (hv i) huv
  refine ⟨x i + (1 / 2 : ℝ) • v i, g, tube_subset_box hδ (hv i) hbδ (by linarith) hg2, ?_⟩
  -- Step 2: the axial cells
  set D : ℝ := 32 * δ / θ with hD
  have hD0 : 0 < D := by positivity
  obtain ⟨hMD, hlogM⟩ := pt_log_cells hδ hδ1 hθ hθ1 hD
  set M : ℕ := ⌈(1 + 2 * δ) / D⌉₊ with hM
  set F : Finset (Fin M) :=
    Finset.univ.filter (fun m : Fin M => (Z3 ∩ cell δ D (x i) (v i) m).Nonempty) with hF
  have hcells : lam' * δ ^ 2 ≤ 128 * (2 * (D + 2 * δ) + δ) * δ ^ 2 * (F.card : ℝ) :=
    many_cells hδ (hv i) hD0 Z3 hZ3m hZ3 hZ3mass M hMD
  -- Step 3: a point of `Z3` in each occupied cell, and a crossing tube through it
  have hex : ∀ m ∈ F, ∃ p, p ∈ Z3 ∧ p ∈ cell δ D (x i) (v i) m := by
    intro m hm
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hm).2
    exact ⟨p, hp.1, hp.2⟩
  choose! pt hptZ3 hptcell using hex
  have : Nonempty (Fin n) := ⟨i⟩
  choose! jf hjZ2 hjslab hjθ hjρ hjκ using hcross
  -- the box and the set `E`
  set B : Set Space := Box (10 * δ) b 2 (x i + (1 / 2 : ℝ) • v i) g with hB
  have hBvol : volume B = ENNReal.ofReal (10 * δ * b * 2) :=
    box_volume (by positivity) (by linarith) (by norm_num) _ g
  set E : Set Space := B ∩ ⋃ j, Y j with hE
  have hEm : MeasurableSet E := (box_measurable _ _ _ _ _).inter (MeasurableSet.iUnion hYm)
  have hEfin : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    rw [hBvol]
    exact ENNReal.ofReal_ne_top
  -- Step 4: the hypotheses of Córdoba's estimate
  have hpTi : ∀ m ∈ F, pt m ∈ Tube δ (x i) (v i) := fun m hm => hZ3 (hptZ3 m hm)
  have hpTj : ∀ m ∈ F, pt m ∈ Tube δ (x (jf (pt m))) (v (jf (pt m))) := fun m hm =>
    hYT _ (hZ2Y _ (hjZ2 _ (hptZ3 m hm)))
  have h0 : ∀ m ∈ F, |g (v (jf (pt m))) 0| ≤ 8 * r := by
    intro m hm
    have h := hg0 (v (jf (pt m)))
    rw [hv] at h
    have hj := slab_inner_dir hδ (hjslab _ (hptZ3 m hm))
    linarith
  have h1 : ∀ m ∈ F, |g (v (jf (pt m))) 1| ≤ 8 * ρ := fun m hm =>
    (frame_coord_le_angle (hv i) hg2 (v (jf (pt m))) 1 (by decide)).trans
      (hjρ _ (hptZ3 m hm))
  have hcr : ∀ m ∈ F, θ / 2 ≤ |g (v (jf (pt m))) 1| := fun m hm =>
    inplane_large (hv i) (hv _) hg2 hθ.le (hjθ _ (hptZ3 m hm)) (by linarith [h0 m hm])
  have hAm : ∀ m ∈ F, MeasurableSet (Z2 (jf (pt m)) ∩ ball (pt m) L) := fun m _ =>
    (hZ2m _).inter measurableSet_ball
  have hA : ∀ m ∈ F, Z2 (jf (pt m)) ∩ ball (pt m) L ⊆
      Tube δ (x (jf (pt m))) (v (jf (pt m))) ∩ ball (pt m) L := fun m _ =>
    inter_subset_inter_left _ ((hZ2Y _).trans (hYT _))
  have hmass : ∀ m ∈ F, ENNReal.ofReal (κ * (L * δ ^ 2 / 8)) ≤
      volume (Z2 (jf (pt m)) ∩ ball (pt m) L) := by
    intro m hm
    rw [ENNReal.ofReal_mul hκ]
    calc ENNReal.ofReal κ * ENNReal.ofReal (L * δ ^ 2 / 8)
        ≤ ENNReal.ofReal κ * volume (Tube δ (x (jf (pt m))) (v (jf (pt m))) ∩ ball (pt m) L) := by
          gcongr
          exact tube_ball_volume_lower hδ (hv _) hL3 (by linarith) (hpTj m hm)
      _ ≤ volume (Z2 (jf (pt m)) ∩ ball (pt m) L) := hjκ _ (hptZ3 m hm)
  have hAE : ∀ m ∈ F, Z2 (jf (pt m)) ∩ ball (pt m) L ⊆ E := by
    intro m hm q hq
    have hpiece := piece_subset_box hδ (hv i) (hv _) hg2 (hpTi m hm) (hpTj m hm) (h0 m hm)
      (h1 m hm) hr hρL hL
    exact ⟨hpiece (hA m hm hq), mem_iUnion.mpr ⟨_, hZ2Y _ hq.1⟩⟩
  have hu0 : 0 ≤ κ * (L * δ ^ 2 / 8) :=
    mul_nonneg hκ (div_nonneg (mul_nonneg (by linarith) (sq_nonneg δ)) (by norm_num))
  have hcor := cordoba_box (u := κ * (L * δ ^ 2 / 8)) (x := x i) (v := v i) hδ (by linarith)
    hθ hθ1 (by linarith) hD hu0 (hv i) hg2 F pt (fun m => x (jf (pt m)))
    (fun m => v (jf (pt m))) (fun m => Z2 (jf (pt m)) ∩ ball (pt m) L) (fun m => hv _)
    hpTi hptcell hpTj hcr hAm hA hmass E hEm hEfin hAE
  -- Step 5: the numerics
  have hreal : δ ^ e * (10 * δ * b * 2) ≤ (volume E).toReal :=
    pt_final_real hδ hρ hθ hθ1 (by linarith) (Real.rpow_nonneg hδ.le e)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 / δ by rw [le_div_iff₀ hδ]; linarith)])
      (by linarith) (Nat.cast_nonneg _) ENNReal.toReal_nonneg hD hb hcells hcor hnum
  rw [hBvol, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le e)]
  exact (ENNReal.ofReal_le_iff_le_toReal hEfin).mpr hreal

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
