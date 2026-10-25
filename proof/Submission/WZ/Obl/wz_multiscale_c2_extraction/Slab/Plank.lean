-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Plank.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Select

/-!
# A plank piece carrying a fair share of the kept mass

The kept points of a window are aligned with the global grain set at the kept height, which is
covered by few intervals of length `2 √s` (Assouad regularity at scale `√s`). Cutting the
neighbourhoods of these intervals into planks of width `√s` and the box into ten strips in the
second coordinate gives few pieces; one of them carries a fair share of the kept mass. A piece
lies in a ball of radius `1/3`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- A plank piece: twisted coordinate within `√s / 2` of `c`, second coordinate in a strip of
width `1/5`, height in the window. -/
def plankRegion (f : ℝ → ℝ) (z₀ c y₀ s : ℝ) : Set Space :=
  {p | |p 0 + f z₀ * p 1 - c| ≤ Real.sqrt s / 2 ∧ y₀ ≤ p 1 ∧ p 1 ≤ y₀ + 1 / 5 ∧
    z₀ ≤ p 2 ∧ p 2 ≤ z₀ + Real.sqrt s}

lemma measurableSet_plankRegion (f : ℝ → ℝ) (z₀ c y₀ s : ℝ) :
    MeasurableSet (plankRegion f z₀ c y₀ s) := by
  have h0 : Continuous fun p : Space => p 0 := by fun_prop
  have h1 : Continuous fun p : Space => p 1 := by fun_prop
  have h2 : Continuous fun p : Space => p 2 := by fun_prop
  have hu : Continuous fun p : Space => |p 0 + f z₀ * p 1 - c| := by fun_prop
  apply IsClosed.measurableSet
  simp only [plankRegion, Set.ofPred_and]
  refine IsClosed.inter (isClosed_le hu continuous_const) ?_
  refine IsClosed.inter (isClosed_le continuous_const h1) ?_
  refine IsClosed.inter (isClosed_le h1 continuous_const) ?_
  exact IsClosed.inter (isClosed_le continuous_const h2) (isClosed_le h2 continuous_const)

/-- The centre of a plank piece. -/
noncomputable def plankCentre (f : ℝ → ℝ) (z₀ c y₀ s : ℝ) : Space :=
  pt (c - f z₀ * (y₀ + 1 / 10)) (y₀ + 1 / 10) (z₀ + Real.sqrt s / 2)

lemma dist_plankCentre_le {f : ℝ → ℝ} {z₀ c y₀ s : ℝ} (hfz : |f z₀| ≤ 3)
    (hs : 0 ≤ s) (hs1 : Real.sqrt s ≤ 1 / 1000) {q : Space}
    (hq : q ∈ plankRegion f z₀ c y₀ s) : dist q (plankCentre f z₀ c y₀ s) ≤ 1 / 3 := by
  obtain ⟨hu, hy1, hy2, hz1, hz2⟩ := hq
  have hsp : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  unfold plankCentre
  rw [dist_eq_norm]
  have hn := norm_sq_eq_three
    (q - pt (c - f z₀ * (y₀ + 1 / 10)) (y₀ + 1 / 10) (z₀ + Real.sqrt s / 2))
  simp only [PiLp.sub_apply, pt_zero, pt_one, pt_two] at hn
  have e0 : q 0 - (c - f z₀ * (y₀ + 1 / 10)) =
      (q 0 + f z₀ * q 1 - c) - f z₀ * (q 1 - (y₀ + 1 / 10)) := by ring
  have a1 : |q 1 - (y₀ + 1 / 10)| ≤ 1 / 10 := abs_le.mpr ⟨by linarith, by linarith⟩
  have a0 : |q 0 - (c - f z₀ * (y₀ + 1 / 10))| ≤ 1 / 2000 + 3 / 10 := by
    rw [e0]
    calc |(q 0 + f z₀ * q 1 - c) - f z₀ * (q 1 - (y₀ + 1 / 10))|
        ≤ |q 0 + f z₀ * q 1 - c| + |f z₀| * |q 1 - (y₀ + 1 / 10)| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 1 / 2000 + 3 * (1 / 10) := by
          gcongr
          linarith
      _ = 1 / 2000 + 3 / 10 := by ring
  have a2 : |q 2 - (z₀ + Real.sqrt s / 2)| ≤ 1 / 2000 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have b0 := sq_le_sq' (abs_le.mp a0).1 (abs_le.mp a0).2
  have b1 := sq_le_sq' (abs_le.mp a1).1 (abs_le.mp a1).2
  have b2 := sq_le_sq' (abs_le.mp a2).1 (abs_le.mp a2).2
  have hsq : ‖q - pt (c - f z₀ * (y₀ + 1 / 10)) (y₀ + 1 / 10) (z₀ + Real.sqrt s / 2)‖ ^ 2 ≤
      (1 / 3) ^ 2 := by
    rw [hn]; nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hsq

section

variable {σ δ s θ K N : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
  {Eo : Set Space} {f : ℝ → ℝ} {P : Space → Space}

/-- One plank piece carries a fair share of the kept mass. -/
theorem exists_plank_piece (hS : FineSetup σ δ s θ K N x v Y Eo f P) {z₀ zs H : ℝ}
    (hz₀ : z₀ ∈ Icc (-1 : ℝ) 1) (hzs : zs ∈ Icc (-1 : ℝ) 1) (hH : 0 ≤ H)
    (hzz : |z₀ - zs| ≤ H) {ZR : Set ℝ}
    (hZR : ∀ z ∈ ZR, |z - zs| ≤ H ∧ z₀ ≤ z ∧ z ≤ z₀ + Real.sqrt s) :
    ∃ (c y₀ : ℝ) (NP : ℕ),
      (NP : ℝ) ≤ 10 * (K * (8 / Real.sqrt s) ^ (1 - σ)) *
        (2 * (Real.sqrt s + (4 * ((H + 2 * δ) / θ + 2 * δ) + H)) / Real.sqrt s + 2) ∧
      ∑ i ∈ keptAt Y zs, volume (Y i ∩ (fun p : Space => p 2) ⁻¹' ZR) ≤
        (NP : ℝ≥0∞) * ∑ i ∈ keptAt Y zs,
          volume (Y i ∩ plankRegion f z₀ c y₀ s ∩ (fun p : Space => p 2) ⁻¹' ZR) := by
  classical
  have hs := s_pos hS
  have hb := sqrt_s_bounds hS
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  set D := 4 * ((H + 2 * δ) / θ + 2 * δ) + H with hD
  have hD0 : 0 ≤ D := by
    have := hS.θ_pos; have := hS.δ_pos
    positivity
  -- the covering of the global grain set at the kept height
  have hδs : δ ≤ Real.sqrt s := by
    have : s ≤ Real.sqrt s := by nlinarith
    linarith [hS.δ_le]
  obtain ⟨mc, cc, hcov, hmc⟩ := hS.glob zs hzs (Real.sqrt s) 8 (-4) hδs (by linarith)
  set J : ℕ := ⌈2 * (Real.sqrt s + D) / Real.sqrt s⌉₊ + 1 with hJ
  -- the pieces
  set centre : Fin mc → Fin J → ℝ := fun l j =>
    cc l - (Real.sqrt s + D) + Real.sqrt s / 2 * (2 * (j : ℝ) + 1)
  set ystrip : Fin 10 → ℝ := fun t => -1 + (t : ℝ) / 5
  set g : Fin mc × Fin J × Fin 10 → ℝ≥0∞ := fun π => ∑ i ∈ keptAt Y zs,
    volume (Y i ∩ plankRegion f z₀ (centre π.1 π.2.1) (ystrip π.2.2) s ∩
      (fun p : Space => p 2) ⁻¹' ZR)
  -- every kept point lies in a piece
  have hpiece : ∀ i ∈ keptAt Y zs, Y i ∩ (fun p : Space => p 2) ⁻¹' ZR ⊆
      ⋃ π ∈ (Finset.univ : Finset (Fin mc × Fin J × Fin 10)),
        Y i ∩ plankRegion f z₀ (centre π.1 π.2.1) (ystrip π.2.2) s ∩
          (fun p : Space => p 2) ⁻¹' ZR := by
    intro i hi p hp
    obtain ⟨hpY, hpZ⟩ := hp
    obtain ⟨hpz, hz0, hz1⟩ := hZR (p 2) hpZ
    obtain ⟨u, hu, hpu⟩ := kept_aligned hS hz₀ hi hpY hpz hzz
    have hfz : |f zs| ≤ 3 := hS.f_bound zs hzs
    have hu4 : u ∈ Icc (-4 : ℝ) (-4 + 8) := by
      have := projectedSlice_subset_Icc hS.Eo_ball hfz hu
      constructor <;> linarith [this.1, this.2]
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hcov ⟨hu, hu4⟩)
    rw [mem_closedBall, Real.dist_eq] at hl
    set w := p 0 + f z₀ * p 1 - (cc l - (Real.sqrt s + D)) with hw
    have hw0 : 0 ≤ w := by
      have := (abs_le.mp hl).1; have := (abs_le.mp hpu).1; linarith
    have hw1 : w ≤ 2 * (Real.sqrt s + D) := by
      have := (abs_le.mp hl).2; have := (abs_le.mp hpu).2; linarith
    set jn : ℕ := ⌊w / Real.sqrt s⌋₊ with hjn
    have hjlt : jn < J := by
      have h1 : (jn : ℝ) ≤ w / Real.sqrt s := Nat.floor_le (div_nonneg hw0 hsp.le)
      have h2 : w / Real.sqrt s ≤ 2 * (Real.sqrt s + D) / Real.sqrt s :=
        div_le_div_of_nonneg_right hw1 hsp.le
      have h3 : 2 * (Real.sqrt s + D) / Real.sqrt s ≤ ⌈2 * (Real.sqrt s + D) / Real.sqrt s⌉₊ :=
        Nat.le_ceil _
      have : (jn : ℝ) < J := by rw [hJ]; push_cast; linarith
      exact_mod_cast this
    have hp1 := abs_coord_lt_one (hS.Eo_ball (hS.sub_Eo i hpY)) 1
    set tn : ℕ := ⌊(p 1 + 1) * 5⌋₊ with htn
    have htlt : tn < 10 := by
      have h1 : (tn : ℝ) ≤ (p 1 + 1) * 5 :=
        Nat.floor_le (by linarith [(abs_lt.mp hp1).1])
      have : (tn : ℝ) < 10 := by linarith [(abs_lt.mp hp1).2]
      exact_mod_cast this
    refine mem_iUnion₂.mpr ⟨(l, ⟨jn, hjlt⟩, ⟨tn, htlt⟩), Finset.mem_univ _, ⟨hpY, ?_⟩, hpZ⟩
    refine ⟨?_, ?_, ?_, hz0, hz1⟩
    · -- the twisted coordinate is in the plank
      have h1 : (jn : ℝ) ≤ w / Real.sqrt s := Nat.floor_le (div_nonneg hw0 hsp.le)
      have h2 : w / Real.sqrt s < jn + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hsp] at h1
      rw [div_lt_iff₀ hsp] at h2
      simp only [centre]
      rw [abs_le]
      constructor <;> nlinarith
    · have h1 : (tn : ℝ) ≤ (p 1 + 1) * 5 :=
        Nat.floor_le (by linarith [(abs_lt.mp hp1).1])
      simp only [ystrip]; linarith
    · have h2 : (p 1 + 1) * 5 < tn + 1 := Nat.lt_floor_add_one _
      simp only [ystrip]; linarith
  have hsum : ∑ i ∈ keptAt Y zs, volume (Y i ∩ (fun p : Space => p 2) ⁻¹' ZR) ≤
      ∑ π : Fin mc × Fin J × Fin 10, g π := by
    calc ∑ i ∈ keptAt Y zs, volume (Y i ∩ (fun p : Space => p 2) ⁻¹' ZR)
        ≤ ∑ i ∈ keptAt Y zs, ∑ π : Fin mc × Fin J × Fin 10,
            volume (Y i ∩ plankRegion f z₀ (centre π.1 π.2.1) (ystrip π.2.2) s ∩
              (fun p : Space => p 2) ⁻¹' ZR) := by
          apply Finset.sum_le_sum
          intro i hi
          exact (measure_mono (hpiece i hi)).trans (measure_biUnion_finset_le _ _)
      _ = ∑ π : Fin mc × Fin J × Fin 10, g π := Finset.sum_comm
  have hNPb : ((Fintype.card (Fin mc × Fin J × Fin 10) : ℕ) : ℝ) ≤
      10 * (K * (8 / Real.sqrt s) ^ (1 - σ)) *
        (2 * (Real.sqrt s + D) / Real.sqrt s + 2) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    have hJr : (J : ℝ) ≤ 2 * (Real.sqrt s + D) / Real.sqrt s + 2 := by
      rw [hJ]; push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * (Real.sqrt s + D) / Real.sqrt s by positivity)
      linarith
    have hmc' : (mc : ℝ) ≤ K * (8 / Real.sqrt s) ^ (1 - σ) := hmc
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    calc (mc : ℝ) * (J * 10) = 10 * (mc * J) := by ring
      _ ≤ 10 * ((K * (8 / Real.sqrt s) ^ (1 - σ)) *
          (2 * (Real.sqrt s + D) / Real.sqrt s + 2)) := by
          gcongr
          · exact (Nat.cast_nonneg _).trans hmc'
      _ = _ := by ring
  by_cases hne : (Finset.univ : Finset (Fin mc × Fin J × Fin 10)).Nonempty
  · obtain ⟨π, -, hπ⟩ := Finset.exists_max_image Finset.univ g hne
    refine ⟨centre π.1 π.2.1, ystrip π.2.2, Fintype.card (Fin mc × Fin J × Fin 10), hNPb, ?_⟩
    calc _ ≤ ∑ π : Fin mc × Fin J × Fin 10, g π := hsum
      _ ≤ ∑ _π' : Fin mc × Fin J × Fin 10, g π := Finset.sum_le_sum fun π' _ => hπ π' (Finset.mem_univ _)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨0, 0, 0, by simp only [Nat.cast_zero]; exact (Nat.cast_nonneg _).trans hNPb, ?_⟩
    calc _ ≤ ∑ π : Fin mc × Fin J × Fin 10, g π := hsum
      _ = 0 := by rw [hne, Finset.sum_empty]
      _ ≤ _ := zero_le

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
