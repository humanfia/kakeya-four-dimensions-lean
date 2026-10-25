-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_prism_fan_avoidance.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_prism_fan_avoidance.Defs

/-!
# A Córdoba-type overlap row for same-coarse prisms

For a prism `U j₀ = P a (ρc) c (z j₀) (e j₀)` of an `NData`, the prisms `U j` of the same coarse
tube (`γ j = γ j₀`) overlap `U j₀` in total volume `≲ (K + 2) δ^{-h} vol (U j₀)`, where
`K = dyExp 1 (a / ρc) ≤ log₂ (1/δ)`. Prisms meeting `U j₀` lie in an adapted window of
dimensions `1600ρc × 1600ρc × 6c`; those overlapping it in a share `τ ≥ a/ρc` lie (WZ Lemma 4.9)
moreover in its `24 a / τ`-neighbourhood across; the dense disjoint shadings of the same coarse
fibre count the prisms in any box.

Credit: the window lemma (`aligned_prism_coordinate`, `intersecting_prism_container`) is ported
from session x0570's `AlignedPrismGeometry.lean` on o198's branch x0570 (`PrismData` replaced by
`NData`), and the shading count follows its `intersecting_prism_count`
(`AlignedPrismSeparation.lean`). The dyadic structure follows o095's
`Parent.Factor.overlap_row` in `CordobaSlab.lean`.
-/

noncomputable section
namespace WangZahlLot.Obl.wz_move_two_prism_fan_avoidance
open Set MeasureTheory

/-- A prism adapted to a common axis stays transversely narrow in any other
frame adapted to that axis. (Ported from x0570, o198.) -/
theorem aligned_prism_coordinate {a ρ c : ℝ} {z p w : V}
    (hρ : 0 < ρ) (hc : 0 ≤ c) (ha : a ≤ ρ * c) (hrc : ρ * c ≤ c)
    (hw : ‖w‖ = 1) (e E : V ≃ₗᵢ[ℝ] V)
    (he : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2)
    (Ew : ∀ i : Fin 3, i < 2 → |E w i| ≤ 10 * ρ)
    (hp : p ∈ P a (ρ * c) c z e) (i : Fin 3) (hi : i < 2) :
    |E (p - z) i| ≤ 266 * ρ * c := by
  have hn : ‖p - z‖ ≤ c := by
    have hh := WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_subset_closedBall
      ha hrc hc z e hp
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hh
  by_cases hsmall : ρ ≤ 1 / 100
  · have hp' : p ∈ WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.P
        a (ρ * c) c z e := hp
    have hperp := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.prism_perpendicular_bound
      hρ hsmall hc ha (by nlinarith [mul_nonneg hρ.le hc]) hw e he hp'
    have hcoord := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.abs_rotated_coord_le
      E ((p - z) - (inner ℝ w (p - z)) • w) i
    have hinner : |inner ℝ w (p - z)| ≤ c :=
      (abs_real_inner_le_norm _ _).trans (by simpa only [hw, one_mul] using hn)
    have hdecomp : E (p - z) i =
        E ((p - z) - (inner ℝ w (p - z)) • w) i + inner ℝ w (p - z) * E w i := by
      simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hdecomp]
    calc
      _ ≤ |E ((p - z) - (inner ℝ w (p - z)) • w) i| +
          |inner ℝ w (p - z) * E w i| := abs_add_le _ _
      _ ≤ 256 * ρ * c + c * (10 * ρ) :=
        add_le_add (hcoord.trans hperp) (by rw [abs_mul]; gcongr; exact Ew i hi)
      _ = _ := by ring
  · have hh := (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.abs_rotated_coord_le
      E (p - z) i).trans hn
    have hbig : 1 ≤ 266 * ρ := by linarith
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hbig hc])

/-- Prisms in one coarse fibre that meet a fixed prism fit in an adapted
window of volume proportional to rho squared times c cubed. (Ported from x0570, o198.) -/
theorem intersecting_prism_container {ω ζ δ h ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} (hδ : 0 < δ)
    (D : NData ω ζ δ h ρ c n x v Y) (j j₀ : Fin D.L)
    (hγ : D.γ j = D.γ j₀)
    (hmeet : (P D.a (ρ * c) c (D.z j) (D.e j) ∩
      P D.a (ρ * c) c (D.z j₀) (D.e j₀)).Nonempty) :
    P D.a (ρ * c) c (D.z j) (D.e j) ⊆
      P (1600 * ρ * c) (1600 * ρ * c) (6 * c) (D.z j₀) (D.e j₀) := by
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  have hρ : 0 < ρ := pos_of_mul_pos_left hrc hc.le
  have hE (i : Fin 3) (hi : i < 2) : |D.e j₀ (D.w (D.γ j₀)) i| ≤ 10 * ρ := by
    have hh := (D.geometry j₀).2
    fin_cases i
    · change |D.e j₀ (D.w (D.γ j₀)) 0| ≤ 10 * ρ
      dsimp only [ι] at hh
      nlinarith [sq_nonneg (D.e j₀ (D.w (D.γ j₀)) 1),
        sq_abs (D.e j₀ (D.w (D.γ j₀)) 0), abs_nonneg (D.e j₀ (D.w (D.γ j₀)) 0)]
    · change |D.e j₀ (D.w (D.γ j₀)) 1| ≤ 10 * ρ
      dsimp only [ι] at hh
      nlinarith [sq_nonneg (D.e j₀ (D.w (D.γ j₀)) 0),
        sq_abs (D.e j₀ (D.w (D.γ j₀)) 1), abs_nonneg (D.e j₀ (D.w (D.γ j₀)) 1)]
    · norm_num at hi
  have hcoord (l : Fin D.L) (hl : D.γ l = D.γ j₀) (p : V)
      (hp : p ∈ P D.a (ρ * c) c (D.z l) (D.e l)) (i : Fin 3) (hi : i < 2) :
      |D.e j₀ (p - D.z l) i| ≤ 266 * ρ * c := by
    apply aligned_prism_coordinate hρ hc.le D.middle D.upper (D.unit (D.γ l))
      (D.e l) (D.e j₀) (D.geometry l).2 _ hp i hi
    simpa only [hl] using hE
  have hnorm (l : Fin D.L) (p : V)
      (hp : p ∈ P D.a (ρ * c) c (D.z l) (D.e l)) : ‖p - D.z l‖ ≤ c := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using
      WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_subset_closedBall
        D.middle D.upper hc.le (D.z l) (D.e l) hp
  obtain ⟨q₀, hqj, hq₀⟩ := hmeet
  intro p hp
  have he (i : Fin 3) : D.e j₀ (p - D.z j₀) i =
      (D.e j₀ (p - D.z j) i - D.e j₀ (q₀ - D.z j) i) +
        D.e j₀ (q₀ - D.z j₀) i := by
    rw [show p - D.z j₀ = ((p - D.z j) - (q₀ - D.z j)) + (q₀ - D.z j₀) by abel,
      map_add, map_sub]
    rfl
  have htrans (i : Fin 3) (hi : i < 2) :
      |D.e j₀ (p - D.z j₀) i| ≤ 1600 * ρ * c / 2 := by
    rw [he]
    have hh := (abs_add_le (D.e j₀ (p - D.z j) i - D.e j₀ (q₀ - D.z j) i)
      (D.e j₀ (q₀ - D.z j₀) i)).trans
      (add_le_add (abs_sub (D.e j₀ (p - D.z j) i)
        (D.e j₀ (q₀ - D.z j) i)) le_rfl)
    have hp' := hcoord j hγ p hp i hi
    have hq' := hcoord j hγ q₀ hqj i hi
    have hq₀' := hcoord j₀ rfl q₀ hq₀ i hi
    nlinarith [mul_nonneg hρ.le hc.le]
  refine ⟨htrans 0 (by decide), htrans 1 (by decide), ?_⟩
  have habs := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.abs_rotated_coord_le
    (D.e j₀) (p - D.z j₀) 2
  have hn : ‖p - D.z j₀‖ ≤ 3 * c := by
    rw [show p - D.z j₀ = ((p - D.z j) - (q₀ - D.z j)) + (q₀ - D.z j₀) by abel]
    calc
      _ ≤ ‖(p - D.z j) - (q₀ - D.z j)‖ + ‖q₀ - D.z j₀‖ := norm_add_le _ _
      _ ≤ (‖p - D.z j‖ + ‖q₀ - D.z j‖) + ‖q₀ - D.z j₀‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (c + c) + c := add_le_add (add_le_add (hnorm j p hp)
        (hnorm j q₀ hqj)) (hnorm j₀ q₀ hq₀)
      _ = _ := by ring
  change |D.e j₀ (p - D.z j₀) 2| ≤ 6 * c / 2
  linarith

/-- The volume of a prism. -/
theorem prism_volume_le (a₁ a₂ a₃ : ℝ) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃) (z : V)
    (e : V ≃ₗᵢ[ℝ] V) : μ (P a₁ a₂ a₃ z e) ≤ O (a₁ * a₂ * a₃) :=
  (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume h₁ h₂ h₃ z e).le

/-- Counting with dense disjoint shadings: the prisms of one coarse fibre whose boxes lie in a
set `Z` of volume at most `VZ` number at most `VZ / (δ^h vol U)`. (The pattern of x0570's
`intersecting_prism_count`, o198.) -/
theorem shading_count {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (D : NData ω ζ δ h ρ c n x v Y) (k₀ : Fin D.N) (G : Finset (Fin D.L))
    (Z : Set V) (VZ : ℝ) (hVZ : 0 ≤ VZ) (hZ : μ Z ≤ O VZ)
    (hG : ∀ j ∈ G, D.γ j = k₀ ∧ P D.a (ρ * c) c (D.z j) (D.e j) ⊆ Z) :
    (G.card : ℝ) * (δ ^ h * (D.a * (ρ * c) * c)) ≤ VZ := by
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  have hd : 0 < δ ^ h := Real.rpow_pos_of_pos hδ h
  have hmass : O (G.card * (δ ^ h * (D.a * (ρ * c) * c))) ≤ O VZ := by
    calc
      _ = ∑ _j ∈ G, O (δ ^ h * (D.a * (ρ * c) * c)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, O,
          ENNReal.ofReal_mul (Nat.cast_nonneg G.card), ENNReal.ofReal_natCast]
      _ ≤ ∑ j ∈ G, μ (⋃ i, D.W i j) := by
        apply Finset.sum_le_sum
        intro j _
        have he : μ (P D.a (ρ * c) c (D.z j) (D.e j)) = O (D.a * (ρ * c) * c) :=
          WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha.le hrc.le hc.le _ _
        calc
          _ = O (δ ^ h) * μ (P D.a (ρ * c) c (D.z j) (D.e j)) := by
            rw [he]
            exact ENNReal.ofReal_mul hd.le
          _ ≤ _ := D.dense j
      _ = μ (⋃ j ∈ G, ⋃ i, D.W i j) := by
        symm
        apply measure_biUnion_finset
        · intro j hj j' hj' hne
          exact D.disjoint j j' hne ((hG j hj).1.trans (hG j' hj').1.symm)
        · intro j _
          exact MeasurableSet.iUnion (fun i => (D.pieces i j).1)
      _ ≤ μ Z := by
        apply measure_mono
        intro p hp
        obtain ⟨j, hp⟩ := Set.mem_iUnion.mp hp
        obtain ⟨hj, hp⟩ := Set.mem_iUnion.mp hp
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
        exact (hG j hj).2 ((D.pieces i j).2.1 hi).2
      _ ≤ O VZ := hZ
  exact (ENNReal.ofReal_le_ofReal_iff hVZ).mp hmass

open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor
  (dyExp dyUp le_dyUp dyUp_lt dyExp_le nrm coord_zero box_convex) in
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.ConvexSlab (slab subset_slab) in
/-- **Overlap row.** The prisms of the coarse fibre of `j₀` overlap `U j₀` in total volume at most
`15360000 (K + 2) δ^{-h} vol (U j₀)`, `K = dyExp 1 (a / ρc)`. -/
theorem overlap_row {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (D : NData ω ζ δ h ρ c n x v Y) (j₀ : Fin D.L) :
    ∑ j ∈ Finset.univ.filter (fun j => D.γ j = D.γ j₀),
        (μ (P D.a (ρ * c) c (D.z j₀) (D.e j₀) ∩ P D.a (ρ * c) c (D.z j) (D.e j))).toReal ≤
      15360000 * ((WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.dyExp 1
          (D.a / (ρ * c)) : ℝ) + 2) * δ ^ (-h) * (D.a * (ρ * c) * c) := by
  classical
  show ∑ j ∈ Finset.univ.filter (fun j => D.γ j = D.γ j₀),
      (volume (P D.a (ρ * c) c (D.z j₀) (D.e j₀) ∩ P D.a (ρ * c) c (D.z j) (D.e j))).toReal ≤ _
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  have hρ : 0 < ρ := pos_of_mul_pos_left hrc hc.le
  have hd : 0 < δ ^ h := Real.rpow_pos_of_pos hδ h
  have hτmin : 0 < D.a / (ρ * c) := div_pos ha hrc
  have hv0pos : 0 < D.a * (ρ * c) * c := by positivity
  set v0 : ℝ := D.a * (ρ * c) * c with hv0
  set K : ℕ := dyExp 1 (D.a / (ρ * c)) with hK
  set F : Finset (Fin D.L) := Finset.univ.filter (fun j => D.γ j = D.γ j₀) with hF
  let U : Fin D.L → Set V := fun j => P D.a (ρ * c) c (D.z j) (D.e j)
  let Win : Set V := P (1600 * ρ * c) (1600 * ρ * c) (6 * c) (D.z j₀) (D.e j₀)
  let Wk : ℕ → Set V := fun k => P (96 * D.a * 2 ^ k) (1600 * ρ * c) (6 * c) (D.z j₀) (D.e j₀)
  let term : Fin D.L → ℝ := fun j => (volume (U j₀ ∩ U j)).toReal
  have hvolU : ∀ j, volume (U j) = O v0 := fun j =>
    WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha.le hrc.le hc.le _ _
  have hterm_le : ∀ j, term j ≤ v0 := fun j => by
    have h1 : volume (U j₀ ∩ U j) ≤ O v0 :=
      (measure_mono inter_subset_right).trans (hvolU j).le
    exact ENNReal.toReal_le_of_le_ofReal hv0pos.le h1
  have hfin : ∀ j, volume (U j₀ ∩ U j) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (by rw [hvolU j]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  -- prisms with a nonzero overlap lie in the adapted window
  have hnonempty : ∀ j, term j ≠ 0 → (U j ∩ U j₀).Nonempty := by
    intro j hj
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hj
    show (volume (U j₀ ∩ U j)).toReal = 0
    rw [Set.inter_comm, hne, measure_empty, ENNReal.toReal_zero]
  have hwin : ∀ j ∈ F, term j ≠ 0 → U j ⊆ Win := fun j hj hne =>
    intersecting_prism_container hδ D j j₀ (Finset.mem_filter.mp hj).2 (hnonempty j hne)
  -- the first coordinate of `e j₀` is the slab coordinate
  have hslabcoord : ∀ p : V, D.e j₀ (p - D.z j₀) 0 =
      inner ℝ (nrm (D.e j₀)) p - inner ℝ (nrm (D.e j₀)) (D.z j₀) := by
    intro p
    rw [coord_zero, inner_sub_right]
  have hU₀slab : U j₀ ⊆ slab (nrm (D.e j₀)) (inner ℝ (nrm (D.e j₀)) (D.z j₀)) (D.a / 2) := by
    intro p hp
    show |inner ℝ (nrm (D.e j₀)) p - inner ℝ (nrm (D.e j₀)) (D.z j₀)| ≤ D.a / 2
    rw [← hslabcoord p]
    exact hp.1
  -- prisms with a large overlap lie in a thin window (WZ Lemma 4.9)
  have hthin : ∀ j ∈ F, D.a / (ρ * c) * v0 ≤ term j → U j ⊆ Wk (dyExp 1 (term j / v0)) := by
    intro j hjF hj
    have htpos : 0 < term j := lt_of_lt_of_le (by positivity) hj
    have hτpos : 0 < term j / v0 := div_pos htpos hv0pos
    have hconc : ENNReal.ofReal (term j / v0) * volume (U j) ≤
        volume (U j ∩ slab (nrm (D.e j₀)) (inner ℝ (nrm (D.e j₀)) (D.z j₀)) (D.a / 2)) := by
      calc ENNReal.ofReal (term j / v0) * volume (U j)
          = ENNReal.ofReal (term j / v0 * v0) := by
            rw [hvolU j, ENNReal.ofReal_mul hτpos.le]
        _ = ENNReal.ofReal (term j) := by rw [div_mul_cancel₀ _ hv0pos.ne']
        _ = volume (U j₀ ∩ U j) := ENNReal.ofReal_toReal (hfin j)
        _ ≤ _ := measure_mono (fun p hp => Set.mem_inter hp.2 (hU₀slab hp.1))
    have hsub : U j ⊆ slab (nrm (D.e j₀)) (inner ℝ (nrm (D.e j₀)) (D.z j₀))
        (48 * (D.a / 2) / (term j / v0)) :=
      subset_slab (show Convex ℝ (U j) from box_convex D.a (ρ * c) c (D.z j) (D.e j))
        (by rw [hvolU j]; exact ENNReal.ofReal_pos.mpr hv0pos)
        (by rw [hvolU j]; exact ENNReal.ofReal_ne_top) (by positivity) hτpos hconc
    have hW := hwin j hjF htpos.ne'
    have hlt := dyUp_lt (M := 1) hτpos one_pos
    have h2k : (0 : ℝ) < 2 ^ dyExp 1 (term j / v0) := by positivity
    unfold dyUp at hlt
    rw [div_lt_iff₀ h2k] at hlt
    intro p hp
    have h0 := hsub hp
    have hw : p ∈ Win := hW hp
    show |ι (D.e j₀ (p - D.z j₀)) 0| ≤ 96 * D.a * 2 ^ dyExp 1 (term j / v0) / 2 ∧
      |ι (D.e j₀ (p - D.z j₀)) 1| ≤ 1600 * ρ * c / 2 ∧ |ι (D.e j₀ (p - D.z j₀)) 2| ≤ 6 * c / 2
    refine ⟨?_, hw.2.1, hw.2.2⟩
    show |D.e j₀ (p - D.z j₀) 0| ≤ 96 * D.a * 2 ^ dyExp 1 (term j / v0) / 2
    have h0' : |D.e j₀ (p - D.z j₀) 0| ≤ 48 * (D.a / 2) / (term j / v0) := by
      rw [hslabcoord p]; exact h0
    refine h0'.trans ?_
    rw [div_le_iff₀ hτpos]
    nlinarith [mul_lt_mul_of_pos_left hlt ha]
  -- the per-term bound
  have hpointwise : ∀ j ∈ F, term j ≤ (if U j ⊆ Win then D.a / (ρ * c) * v0 else 0) +
      ∑ k ∈ Finset.range (K + 1), (if U j ⊆ Wk k then v0 / 2 ^ k else 0) := by
    intro j hjF
    have hsum_nn : 0 ≤ ∑ k ∈ Finset.range (K + 1), (if U j ⊆ Wk k then v0 / 2 ^ k else 0) :=
      Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
    have hfirst_nn : 0 ≤ (if U j ⊆ Win then D.a / (ρ * c) * v0 else 0) := by
      split_ifs <;> positivity
    by_cases hsmall : term j < D.a / (ρ * c) * v0
    · by_cases hz : term j = 0
      · rw [hz]; exact add_nonneg hfirst_nn hsum_nn
      · rw [if_pos (hwin j hjF hz)]
        linarith
    · have hsmall' : D.a / (ρ * c) * v0 ≤ term j := not_lt.mp hsmall
      have htpos : 0 < term j := lt_of_lt_of_le (by positivity) hsmall'
      have hτpos : 0 < term j / v0 := div_pos htpos hv0pos
      have hkK : dyExp 1 (term j / v0) ≤ K :=
        dyExp_le one_pos hτmin (by rw [le_div_iff₀ hv0pos]; exact hsmall')
      have hk_mem : dyExp 1 (term j / v0) ∈ Finset.range (K + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hkK)
      have hterm_k : term j ≤ v0 / 2 ^ dyExp 1 (term j / v0) := by
        have h1 := le_dyUp (M := 1) hτpos (by rw [div_le_one hv0pos]; exact hterm_le j)
        unfold dyUp at h1
        rw [div_le_iff₀ hv0pos] at h1
        calc term j ≤ 1 / 2 ^ dyExp 1 (term j / v0) * v0 := h1
          _ = v0 / 2 ^ dyExp 1 (term j / v0) := by ring
      have hsingle : (if U j ⊆ Wk (dyExp 1 (term j / v0)) then
            v0 / 2 ^ dyExp 1 (term j / v0) else 0) ≤
          ∑ k' ∈ Finset.range (K + 1), (if U j ⊆ Wk k' then v0 / 2 ^ k' else 0) :=
        Finset.single_le_sum (f := fun k' => if U j ⊆ Wk k' then v0 / 2 ^ k' else 0)
          (fun k' _ => by split_ifs <;> positivity) hk_mem
      rw [if_pos (hthin j hjF hsmall')] at hsingle
      linarith
  -- the counts
  have h_win : ((F.filter fun j => U j ⊆ Win).card : ℝ) * (D.a / (ρ * c) * v0) ≤
      15360000 * (δ ^ h)⁻¹ * v0 := by
    have h1 : ((F.filter fun j => U j ⊆ Win).card : ℝ) * (δ ^ h * v0) ≤
        (1600 * ρ * c) * (1600 * ρ * c) * (6 * c) :=
      shading_count hδ D (D.γ j₀) (F.filter fun j => U j ⊆ Win) Win
        ((1600 * ρ * c) * (1600 * ρ * c) * (6 * c)) (by positivity)
        (prism_volume_le _ _ _ (by positivity) (by positivity) (by positivity) _ _)
        (fun j hj => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2,
          (Finset.mem_filter.mp hj).2⟩)
    have h2 : (1600 * ρ * c) * (1600 * ρ * c) * (6 * c) * (D.a / (ρ * c)) = 15360000 * v0 := by
      calc (1600 * ρ * c) * (1600 * ρ * c) * (6 * c) * (D.a / (ρ * c))
          = 15360000 * (ρ * c) * c * (D.a / (ρ * c) * (ρ * c)) := by ring
        _ = 15360000 * v0 := by rw [div_mul_cancel₀ D.a hrc.ne', hv0]; ring
    rw [show (15360000 : ℝ) * (δ ^ h)⁻¹ * v0 = 15360000 * v0 / δ ^ h by ring, le_div_iff₀ hd]
    calc ((F.filter fun j => U j ⊆ Win).card : ℝ) * (D.a / (ρ * c) * v0) * δ ^ h
        = ((F.filter fun j => U j ⊆ Win).card : ℝ) * (δ ^ h * v0) * (D.a / (ρ * c)) := by ring
      _ ≤ (1600 * ρ * c) * (1600 * ρ * c) * (6 * c) * (D.a / (ρ * c)) :=
        mul_le_mul_of_nonneg_right h1 hτmin.le
      _ = 15360000 * v0 := h2
  have h_k : ∀ k ∈ Finset.range (K + 1),
      ((F.filter fun j => U j ⊆ Wk k).card : ℝ) * (v0 / 2 ^ k) ≤ 921600 * (δ ^ h)⁻¹ * v0 := by
    intro k _
    have h1 : ((F.filter fun j => U j ⊆ Wk k).card : ℝ) * (δ ^ h * v0) ≤
        (96 * D.a * 2 ^ k) * (1600 * ρ * c) * (6 * c) :=
      shading_count hδ D (D.γ j₀) (F.filter fun j => U j ⊆ Wk k) (Wk k)
        ((96 * D.a * 2 ^ k) * (1600 * ρ * c) * (6 * c)) (by positivity)
        (prism_volume_le _ _ _ (by positivity) (by positivity) (by positivity) _ _)
        (fun j hj => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2,
          (Finset.mem_filter.mp hj).2⟩)
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rw [show (921600 : ℝ) * (δ ^ h)⁻¹ * v0 = 921600 * v0 / δ ^ h by ring, le_div_iff₀ hd,
      show ((F.filter fun j => U j ⊆ Wk k).card : ℝ) * (v0 / 2 ^ k) * δ ^ h =
        ((F.filter fun j => U j ⊆ Wk k).card : ℝ) * (δ ^ h * v0) / 2 ^ k by ring,
      div_le_iff₀ h2k]
    calc _ ≤ (96 * D.a * 2 ^ k) * (1600 * ρ * c) * (6 * c) := h1
      _ = 921600 * v0 * 2 ^ k := by rw [hv0]; ring
  -- summing the per-term bound
  calc ∑ j ∈ F, term j
      ≤ ∑ j ∈ F, ((if U j ⊆ Win then D.a / (ρ * c) * v0 else 0) +
          ∑ k ∈ Finset.range (K + 1), (if U j ⊆ Wk k then v0 / 2 ^ k else 0)) :=
        Finset.sum_le_sum fun j hj => hpointwise j hj
    _ = ((F.filter fun j => U j ⊆ Win).card : ℝ) * (D.a / (ρ * c) * v0) +
          ∑ k ∈ Finset.range (K + 1),
            ((F.filter fun j => U j ⊆ Wk k).card : ℝ) * (v0 / 2 ^ k) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        · apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 15360000 * (δ ^ h)⁻¹ * v0 + ∑ _k ∈ Finset.range (K + 1), 921600 * (δ ^ h)⁻¹ * v0 :=
        add_le_add h_win (Finset.sum_le_sum h_k)
    _ ≤ 15360000 * ((K : ℝ) + 2) * (δ ^ h)⁻¹ * v0 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        have hX : 0 ≤ (δ ^ h)⁻¹ * v0 := by positivity
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        nlinarith [mul_nonneg hK0 hX]
    _ = _ := by rw [Real.rpow_neg hδ.le]

/-- The dyadic exponent of the overlap row is at most `log₂ (1/δ)`. -/
theorem overlap_exp_le {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (D : NData ω ζ δ h ρ c n x v Y) :
    ((WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.dyExp 1
        (D.a / (ρ * c)) : ℕ) : ℝ) ≤ Real.logb 2 (1 / δ) := by
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hrc1 : ρ * c ≤ 1 := D.upper.trans D.length
  have hδ1 : δ ≤ 1 := D.lower.trans (D.middle.trans hrc1)
  have hle : δ ≤ D.a / (ρ * c) := by
    rw [le_div_iff₀ hrc]
    calc δ * (ρ * c) ≤ δ * 1 := mul_le_mul_of_nonneg_left hrc1 hδ.le
      _ = δ := mul_one δ
      _ ≤ D.a := D.lower
  have h1 := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.dyExp_le one_pos hδ hle
  have hlog : 0 ≤ Real.logb 2 (1 / δ) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  calc ((WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.dyExp 1
        (D.a / (ρ * c)) : ℕ) : ℝ)
      ≤ (WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.dyExp 1 δ : ℝ) := by
        exact_mod_cast h1
    _ ≤ Real.logb 2 (1 / δ) := Nat.floor_le hlog

end WangZahlLot.Obl.wz_move_two_prism_fan_avoidance
