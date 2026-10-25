-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormCenter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDefs
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

/-!
# Choice of the zoom centre

Centres run over the grid `s ℤ³ ∩ [-M s, M s]³` with `s = 1 / (8 lam)`. Every shaded point of a
tube lies in the original piece of that tube about a grid centre within `1 / (4 lam)` of its axis,
and every unit segment has at most `2058 lam` grid points within `1 / (4 lam)`. Averaging gives
a centre through which many tubes pass, with a good shading mass ratio.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal

/-- Abstract pigeonhole over a finite set of centres. -/
theorem exists_good_center {ι : Type*} (S : Finset ι) (A : ι → ℝ) (N : ι → ℕ) {T B amax : ℝ}
    {n₀ : ℕ} (hA : ∀ m ∈ S, A m ≤ N m * amax) (hT : T ≤ ∑ m ∈ S, A m)
    (hB : (∑ m ∈ S, (N m : ℝ)) ≤ B) (hBpos : 0 < B) (hTpos : 0 < T)
    (hlight : (S.card : ℝ) * n₀ * amax ≤ T / 2) (hamax : 0 ≤ amax) :
    ∃ m ∈ S, n₀ ≤ N m ∧ T / (4 * B) * N m < A m := by
  classical
  set κ := T / (4 * B) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  let H := S.filter (fun m => n₀ ≤ N m)
  have hlightsum : ∑ m ∈ S.filter (fun m => ¬ n₀ ≤ N m), A m ≤ T / 2 := by
    calc ∑ m ∈ S.filter (fun m => ¬ n₀ ≤ N m), A m ≤
          ∑ m ∈ S.filter (fun m => ¬ n₀ ≤ N m), (n₀ : ℝ) * amax := by
          apply sum_le_sum
          intro m hm
          obtain ⟨hmS, hmN⟩ := mem_filter.mp hm
          calc A m ≤ N m * amax := hA m hmS
            _ ≤ n₀ * amax := by
                apply mul_le_mul_of_nonneg_right _ hamax
                exact_mod_cast (le_of_lt (not_le.mp hmN))
      _ = ((S.filter (fun m => ¬ n₀ ≤ N m)).card : ℝ) * n₀ * amax := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ (S.card : ℝ) * n₀ * amax := by
          apply mul_le_mul_of_nonneg_right _ hamax
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact_mod_cast card_filter_le _ _
      _ ≤ T / 2 := hlight
  have hheavy : T / 2 ≤ ∑ m ∈ H, A m := by
    have hsplit := sum_filter_add_sum_filter_not S (fun m => n₀ ≤ N m) A
    linarith
  have hNH : ∑ m ∈ H, (N m : ℝ) ≤ B := by
    refine le_trans ?_ hB
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro _ _ _; exact Nat.cast_nonneg _
  by_contra hno
  push Not at hno
  have hle : ∑ m ∈ H, A m ≤ ∑ m ∈ H, κ * N m := by
    apply sum_le_sum
    intro m hm
    obtain ⟨hmS, hmN⟩ := mem_filter.mp hm
    exact hno m hmS hmN
  have h2 : ∑ m ∈ H, κ * (N m : ℝ) ≤ κ * B := by
    rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hNH hκ0
  have h3 : κ * B = T / 4 := by rw [hκ]; field_simp
  linarith

/-- Integer points of a coordinate interval of length `6`. -/
theorem card_int_near_le {s : ℝ} (hs : 0 < s) (y : ℝ) :
    ((Finset.Icc (⌈y / s⌉ - 3) (⌈y / s⌉ + 3)).card = 7) ∧
      ∀ m : ℤ, |s * m - y| ≤ 3 * s → m ∈ Finset.Icc (⌈y / s⌉ - 3) (⌈y / s⌉ + 3) := by
  constructor
  · simp only [Int.card_Icc]
    omega
  · intro m hm
    rw [Finset.mem_Icc]
    obtain ⟨h1, h2⟩ := abs_le.mp hm
    have hlo : y / s - 3 ≤ m := by
      rw [div_sub' (ne_of_gt hs), div_le_iff₀ hs]; linarith
    have hhi : (m : ℝ) ≤ y / s + 3 := by
      rw [div_add' _ _ _ (ne_of_gt hs), le_div_iff₀ hs]; linarith
    have hc1 : (⌈y / s⌉ : ℝ) - 1 < y / s := by
      have := Int.ceil_lt_add_one (y / s); linarith
    have hc2 : y / s ≤ ⌈y / s⌉ := Int.le_ceil _
    constructor
    · have : ((⌈y / s⌉ - 3 : ℤ) : ℝ) < m + 1 := by push_cast; linarith
      exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
    · have : (m : ℝ) ≤ ((⌈y / s⌉ + 3 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this

/-- The grid point with integer coordinates `m` and spacing `s`. -/
noncomputable def gridPt (s : ℝ) (m : Fin 3 → ℤ) : Space :=
  s • WithLp.toLp 2 (fun k => (m k : ℝ))

theorem gridPt_apply (s : ℝ) (m : Fin 3 → ℤ) (k : Fin 3) : gridPt s m k = s * m k := by
  simp [gridPt]

/-- At most `343` grid points lie within `3 s` of any point. -/
theorem card_grid_near_le {s : ℝ} (hs : 0 < s) (y : Space) (S : Finset (Fin 3 → ℤ)) :
    (S.filter (fun m => ‖gridPt s m - y‖ ≤ 3 * s)).card ≤ 343 := by
  classical
  let P := Fintype.piFinset (fun k : Fin 3 => Finset.Icc (⌈y k / s⌉ - 3) (⌈y k / s⌉ + 3))
  have hsub : S.filter (fun m => ‖gridPt s m - y‖ ≤ 3 * s) ⊆ P := by
    intro m hm
    have hm' := (mem_filter.mp hm).2
    rw [Fintype.mem_piFinset]
    intro k
    apply (card_int_near_le hs (y k)).2
    have hc : |(gridPt s m - y) k| ≤ ‖gridPt s m - y‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gridPt s m - y) k
    have : (gridPt s m - y) k = s * m k - y k := by simp [gridPt_apply]
    rw [this] at hc
    exact hc.trans hm'
  calc _ ≤ P.card := card_le_card hsub
    _ = 343 := by
        simp only [P, Fintype.card_piFinset, (card_int_near_le hs _).1]
        simp


open scoped Classical in
/-- Grid points within `2 s` of a unit segment: at most `343 (1 / s + 2)`. -/
theorem card_grid_near_segment_le {s : ℝ} (hs : 0 < s) {x v : Space} (hv : ‖v‖ = 1)
    (S : Finset (Fin 3 → ℤ)) :
    ((S.filter (fun m => ∃ t ∈ Icc (0 : ℝ) 1, ‖gridPt s m - (x + t • v)‖ ≤ 2 * s)).card : ℝ) ≤
      343 * (1 / s + 2) := by
  classical
  set K := ⌈1 / s⌉₊ with hK
  have hKpos : 0 < K := Nat.ceil_pos.mpr (by positivity)
  have hKs : 1 / s ≤ K := Nat.le_ceil _
  have hKs' : (K : ℝ) ≤ 1 / s + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hsub : S.filter (fun m => ∃ t ∈ Icc (0 : ℝ) 1, ‖gridPt s m - (x + t • v)‖ ≤ 2 * s) ⊆
      (Finset.range (K + 1)).biUnion
        (fun k => S.filter (fun m => ‖gridPt s m - (x + ((k : ℝ) / K) • v)‖ ≤ 3 * s)) := by
    intro m hm
    obtain ⟨hmS, t, ht, hmt⟩ := mem_filter.mp hm
    rw [Finset.mem_biUnion]
    refine ⟨⌈t * K⌉₊, ?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      apply Nat.ceil_le.mpr
      have : t * K ≤ 1 * K := mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg _)
      simpa using this
    · rw [mem_filter]
      refine ⟨hmS, ?_⟩
      have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
      have hc1 : t * K ≤ ⌈t * K⌉₊ := Nat.le_ceil _
      have hc2 : (⌈t * K⌉₊ : ℝ) < t * K + 1 :=
        Nat.ceil_lt_add_one (mul_nonneg ht.1 (Nat.cast_nonneg _))
      have hdiff : |(⌈t * K⌉₊ : ℝ) / K - t| ≤ s := by
        rw [abs_le]
        constructor
        · rw [le_sub_iff_add_le, le_div_iff₀ hK0]; nlinarith
        · rw [sub_le_iff_le_add, div_le_iff₀ hK0]
          have : 1 ≤ s * K := by rw [div_le_iff₀ hs] at hKs; linarith
          nlinarith
      calc ‖gridPt s m - (x + ((⌈t * K⌉₊ : ℝ) / K) • v)‖ =
            ‖(gridPt s m - (x + t • v)) - (((⌈t * K⌉₊ : ℝ) / K - t) • v)‖ := by
            congr 1; module
        _ ≤ ‖gridPt s m - (x + t • v)‖ + ‖((⌈t * K⌉₊ : ℝ) / K - t) • v‖ := norm_sub_le _ _
        _ ≤ 2 * s + s := by
            rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
            linarith
        _ = 3 * s := by ring
  calc ((S.filter (fun m => ∃ t ∈ Icc (0 : ℝ) 1, ‖gridPt s m - (x + t • v)‖ ≤ 2 * s)).card : ℝ)
      ≤ ((Finset.range (K + 1)).biUnion
          (fun k => S.filter (fun m => ‖gridPt s m - (x + ((k : ℝ) / K) • v)‖ ≤ 3 * s))).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (K + 1),
          ((S.filter (fun m => ‖gridPt s m - (x + ((k : ℝ) / K) • v)‖ ≤ 3 * s)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range (K + 1), (343 : ℝ) := by
        apply sum_le_sum; intro k _
        exact_mod_cast card_grid_near_le hs _ S
    _ = 343 * (K + 1) := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ 343 * (1 / s + 2) := by linarith

/-- Rounding a point of the unit ball to the grid. -/
theorem exists_grid_near {s : ℝ} (hs : 0 < s) {p : Space} (hp : ‖p‖ < 1) :
    ∃ m ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(⌈1 / s⌉₊ + 1 : ℤ)) (⌈1 / s⌉₊ + 1)),
      ‖gridPt s m - p‖ ≤ s := by
  refine ⟨fun k => round (p k / s), ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_Icc]
    have hpk : |p k| ≤ ‖p‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p k
    have hr := abs_sub_round (p k / s)
    have hpks : |p k / s| ≤ 1 / s := by
      rw [abs_div, abs_of_pos hs]
      exact div_le_div_of_nonneg_right (by linarith) hs.le
    have hceil : 1 / s ≤ (⌈1 / s⌉₊ : ℝ) := Nat.le_ceil _
    obtain ⟨h1, h2⟩ := abs_le.mp hpks
    obtain ⟨h3, h4⟩ := abs_le.mp hr
    constructor
    · have : (-(⌈1 / s⌉₊ + 1 : ℤ) : ℝ) ≤ round (p k / s) := by push_cast; linarith
      exact_mod_cast this
    · have : (round (p k / s) : ℝ) ≤ ((⌈1 / s⌉₊ + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · have hcoord : ∀ k, |(gridPt s (fun k => round (p k / s)) - p) k| ≤ s / 2 := by
      intro k
      have : (gridPt s (fun k => round (p k / s)) - p) k = s * (round (p k / s) - p k / s) := by
        simp only [PiLp.sub_apply, gridPt_apply]; field_simp
      rw [this, abs_mul, abs_of_pos hs, abs_sub_comm]
      have := abs_sub_round (p k / s)
      nlinarith
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨hs.le, ?_⟩
    rw [Fin.sum_univ_three]
    have h0 := hcoord 0
    have h1 := hcoord 1
    have h2 := hcoord 2
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_abs ((gridPt s (fun k => round (p k / s)) - p) 0),
      sq_abs ((gridPt s (fun k => round (p k / s)) - p) 1),
      sq_abs ((gridPt s (fun k => round (p k / s)) - p) 2),
      abs_nonneg ((gridPt s (fun k => round (p k / s)) - p) 0),
      abs_nonneg ((gridPt s (fun k => round (p k / s)) - p) 1),
      abs_nonneg ((gridPt s (fun k => round (p k / s)) - p) 2)]

/-- A shaded point of a tube lies in the original piece about some nearby grid centre. -/
theorem mem_subTube_of_near {c : Space} {lam δ : ℝ} (hlam : 0 < lam) {x v p : Space}
    (hv : ‖v‖ = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hpt : ‖p - (x + t • v)‖ < δ)
    (hc : ‖c - (x + t • v)‖ ≤ 1 / (2 * lam)) : p ∈ subTube c lam δ x v := by
  set τ := inner ℝ (c - x) v with hτ
  have hτt : |τ - t| ≤ 1 / (2 * lam) := (abs_param_sub_le hv t).trans hc
  refine mem_tube_iff.mpr ⟨(t - τ) * lam + 1 / 2, ⟨?_, ?_⟩, ?_⟩
  · have := (abs_le.mp hτt).2
    have h3 : -(1 / (2 * lam)) * lam ≤ (t - τ) * lam :=
      mul_le_mul_of_nonneg_right (by linarith) hlam.le
    have h2 : -(1 / (2 * lam)) * lam = -(1 / 2) := by field_simp
    linarith
  · have := (abs_le.mp hτt).1
    have h3 : (t - τ) * lam ≤ (1 / (2 * lam)) * lam :=
      mul_le_mul_of_nonneg_right (by linarith) hlam.le
    have h2 : (1 / (2 * lam)) * lam = 1 / 2 := by field_simp
    linarith
  · have he : foot c x v - (1 / (2 * lam)) • v + ((t - τ) * lam + 1 / 2) • (1 / lam) • v =
        x + t • v := by
      simp only [foot, ← hτ, smul_smul]
      rw [show ((t - τ) * lam + 1 / 2) * (1 / lam) = (t - τ) + 1 / (2 * lam) by field_simp]
      module
    rwa [he]


theorem subTube_eq (c : Space) (lam δ : ℝ) (x v : Space) :
    subTube c lam δ x v = thickening δ (segment ℝ (foot c x v - (1 / (2 * lam)) • v)
      (foot c x v - (1 / (2 * lam)) • v + (1 / lam) • v)) := rfl

theorem segment_subTube_subset {c : Space} {lam : ℝ} (hlam : 1 ≤ lam) (x v : Space) :
    segment ℝ (foot c x v - (1 / (2 * lam)) • v)
      (foot c x v - (1 / (2 * lam)) • v + (1 / lam) • v) ⊆
      (fun t : ℝ => (foot c x v - (1 / (2 * lam)) • v) + t • v) '' Icc 0 (1 / lam) := by
  have hlam0 : 0 < lam := by linarith
  rw [segment_eq_image']
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨t * (1 / lam), ⟨mul_nonneg ht.1 (by positivity), ?_⟩, ?_⟩
  · calc t * (1 / lam) ≤ 1 * (1 / lam) := mul_le_mul_of_nonneg_right ht.2 (by positivity)
      _ = 1 / lam := one_mul _
  · simp only [add_sub_cancel_left, smul_smul]

theorem volume_piece_image_le {lam δ : ℝ} (hlam : 1 ≤ lam) (hδ : 0 < δ) {a v : Space}
    (hv : ‖v‖ = 1) :
    volume (thickening δ ((fun t : ℝ => a + t • v) '' Icc 0 (1 / lam))) ≤
      ENNReal.ofReal (128 * (2 * (1 / lam) + δ) * δ ^ 2) := by
  have hlam0 : 0 < lam := by linarith
  have hT : Icc (0 : ℝ) (1 / lam) ⊆ Icc 0 1 := by
    intro t ht; exact ⟨ht.1, ht.2.trans (by rw [div_le_one hlam0]; exact hlam)⟩
  exact WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    a v hv hT hδ (by positivity) (by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])

theorem piece_volume_arith {lam δ : ℝ} (hδl : δ ≤ 1 / lam) :
    128 * (2 * (1 / lam) + δ) * δ ^ 2 ≤ 384 * δ ^ 2 / lam := by
  have h3 : 128 * (2 * (1 / lam) + δ) * δ ^ 2 ≤ 128 * (3 * (1 / lam)) * δ ^ 2 := by
    gcongr; linarith
  calc 128 * (2 * (1 / lam) + δ) * δ ^ 2 ≤ 128 * (3 * (1 / lam)) * δ ^ 2 := h3
    _ = 384 * δ ^ 2 / lam := by ring

theorem volume_subTube_le {c : Space} {lam δ : ℝ} (hlam : 1 ≤ lam) (hδ : 0 < δ)
    (hδl : δ ≤ 1 / lam) {x v : Space} (hv : ‖v‖ = 1) :
    volume (subTube c lam δ x v) ≤ ENNReal.ofReal (384 * δ ^ 2 / lam) := by
  rw [subTube_eq]
  have h1 := measure_mono (μ := volume) (thickening_subset_of_subset δ
    (segment_subTube_subset (c := c) hlam x v))
  have h2 := volume_piece_image_le (a := foot c x v - (1 / (2 * lam)) • v) hlam hδ hv
  exact h1.trans (h2.trans (ENNReal.ofReal_le_ofReal (piece_volume_arith hδl)))

open scoped Classical in
/-- The tubes passing within `1 / (4 lam)` of `c`. -/
noncomputable def zoomThrough {n : ℕ} (c : Space) (lam : ℝ) (x v : Fin n → Space) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ t ∈ Icc (0 : ℝ) 1, ‖c - (x i + t • v i)‖ ≤ 1 / (4 * lam))

theorem mem_zoomThrough {n : ℕ} {c : Space} {lam : ℝ} {x v : Fin n → Space} {i : Fin n} :
    i ∈ zoomThrough c lam x v ↔ ∃ t ∈ Icc (0 : ℝ) 1, ‖c - (x i + t • v i)‖ ≤ 1 / (4 * lam) := by
  classical
  simp [zoomThrough]

/-- Choice of the zoom centre. -/
theorem exists_center {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space} {δ lam Mtot : ℝ}
    {n₀ : ℕ} (hδ : 0 < δ) (hlam : 1 ≤ lam) (hδs : δ ≤ 1 / (8 * lam))
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, tube δ (x i) (v i) ⊆ ball 0 1)
    (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hM : Mtot ≤ ∑ i, (volume (Y i)).toReal) (hMpos : 0 < Mtot)
    (hlight : (21 * lam) ^ 3 * n₀ * (384 * δ ^ 2 / lam) ≤ Mtot / 2) :
    ∃ c : Space, n₀ ≤ (zoomThrough c lam x v).card ∧
      Mtot / (4 * (3430 * lam * n)) * (zoomThrough c lam x v).card <
        ∑ i ∈ zoomThrough c lam x v, (volume (Y i ∩ subTube c lam δ (x i) (v i))).toReal := by
  classical
  have hlam0 : 0 < lam := by linarith
  set s := 1 / (8 * lam) with hs
  have hs0 : 0 < s := by positivity
  set Mb : ℤ := ⌈1 / s⌉₊ + 1 with hMb
  set box := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-Mb) Mb) with hbox
  have hδl : δ ≤ 1 / lam := hδs.trans (by
    rw [div_le_div_iff₀ (by positivity) hlam0]; nlinarith)
  have hamax : ∀ (c : Space) i, (volume (Y i ∩ subTube c lam δ (x i) (v i))).toReal ≤
      384 * δ ^ 2 / lam := by
    intro c i
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    exact (measure_mono inter_subset_right).trans (volume_subTube_le hlam hδ hδl (hv i))
  set A : (Fin 3 → ℤ) → ℝ := fun m => ∑ i ∈ zoomThrough (gridPt s m) lam x v,
    (volume (Y i ∩ subTube (gridPt s m) lam δ (x i) (v i))).toReal with hA
  set N : (Fin 3 → ℤ) → ℕ := fun m => (zoomThrough (gridPt s m) lam x v).card with hN
  -- (a) pointwise bound
  have hAN : ∀ m ∈ box, A m ≤ N m * (384 * δ ^ 2 / lam) := by
    intro m _
    calc A m ≤ ∑ _i ∈ zoomThrough (gridPt s m) lam x v, (384 * δ ^ 2 / lam) :=
          sum_le_sum fun i _ => hamax _ i
      _ = N m * (384 * δ ^ 2 / lam) := by rw [sum_const, nsmul_eq_mul]
  -- (b) total mass
  have hcover : ∀ i, (volume (Y i)).toReal ≤ ∑ m ∈ box.filter (fun m => i ∈ zoomThrough (gridPt s m) lam x v),
      (volume (Y i ∩ subTube (gridPt s m) lam δ (x i) (v i))).toReal := by
    intro i
    have hsub : Y i ⊆ ⋃ m ∈ box.filter (fun m => i ∈ zoomThrough (gridPt s m) lam x v),
        (Y i ∩ subTube (gridPt s m) lam δ (x i) (v i)) := by
      intro p hp
      obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp (hYT i hp)
      have hpb : ‖p‖ < 1 := by simpa using hball i (hYT i hp)
      obtain ⟨m, hm, hmp⟩ := exists_grid_near hs0 hpb
      have hnear : ‖gridPt s m - (x i + t • v i)‖ ≤ 1 / (4 * lam) := by
        calc ‖gridPt s m - (x i + t • v i)‖ ≤ ‖gridPt s m - p‖ + ‖p - (x i + t • v i)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ s + δ := by linarith
          _ ≤ 1 / (4 * lam) := by
              rw [hs]
              have : 1 / (8 * lam) + 1 / (8 * lam) = 1 / (4 * lam) := by field_simp; ring
              linarith
      refine mem_iUnion₂.mpr ⟨m, mem_filter.mpr ⟨hm, mem_zoomThrough.mpr ⟨t, ht, hnear⟩⟩, hp, ?_⟩
      exact mem_subTube_of_near hlam0 (hv i) ht hpt (hnear.trans (by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith))
    have hfin : ∀ m, volume (Y i ∩ subTube (gridPt s m) lam δ (x i) (v i)) ≠ ∞ := fun m =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((measure_mono inter_subset_right).trans (volume_subTube_le hlam hδ hδl (hv i)))
    have h1 := (measure_mono hsub).trans (measure_biUnion_finset_le (μ := volume) _ _)
    rw [← ENNReal.toReal_sum (fun m _ => hfin m)]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun m _ => hfin m) h1
  have hT : Mtot ≤ ∑ m ∈ box, A m := by
    refine hM.trans ?_
    calc ∑ i, (volume (Y i)).toReal ≤ ∑ i, ∑ m ∈ box.filter (fun m => i ∈ zoomThrough (gridPt s m) lam x v),
          (volume (Y i ∩ subTube (gridPt s m) lam δ (x i) (v i))).toReal := sum_le_sum fun i _ => hcover i
      _ = ∑ m ∈ box, A m := by
          rw [hA]
          simp_rw [sum_filter]
          rw [sum_comm]
          refine sum_congr rfl fun m _ => ?_
          rw [← sum_filter]
          congr 1
          ext a; simp
  -- (c) total count
  have hcount : (∑ m ∈ box, (N m : ℝ)) ≤ 3430 * lam * n := by
    have h1 : (∑ m ∈ box, (N m : ℝ)) = ∑ i : Fin n,
        ((box.filter (fun m => i ∈ zoomThrough (gridPt s m) lam x v)).card : ℝ) := by
      rw [hN]
      simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      simp_rw [sum_filter]
      rw [sum_comm]
      simp [zoomThrough]
    rw [h1]
    calc ∑ i : Fin n, ((box.filter (fun m => i ∈ zoomThrough (gridPt s m) lam x v)).card : ℝ) ≤
          ∑ _i : Fin n, (3430 * lam) := by
          apply sum_le_sum
          intro i _
          have hfil : box.filter (fun m => i ∈ zoomThrough (gridPt s m) lam x v) =
              box.filter (fun m => ∃ t ∈ Icc (0 : ℝ) 1, ‖gridPt s m - (x i + t • v i)‖ ≤ 2 * s) := by
            apply filter_congr
            intro m _
            rw [mem_zoomThrough]
            have : 2 * s = 1 / (4 * lam) := by rw [hs]; field_simp; ring
            rw [this]
          rw [hfil]
          refine (card_grid_near_segment_le hs0 (hv i) box).trans ?_
          rw [hs, one_div_one_div]
          nlinarith
      _ = 3430 * lam * n := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- (d) number of centres
  have hbox : (box.card : ℝ) ≤ (21 * lam) ^ 3 := by
    rw [hbox, Fintype.card_piFinset]
    simp only [Int.card_Icc, prod_const, card_univ, Fintype.card_fin]
    have hceil : (⌈1 / s⌉₊ : ℝ) ≤ 1 / s + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    rw [hs, one_div_one_div] at hceil
    have hcast : (((Mb + 1 - -Mb).toNat : ℕ) : ℝ) ≤ 16 * lam + 5 := by
      have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
      have hpos : 0 ≤ Mb + 1 - -Mb := by omega
      rw [show ((Mb + 1 - -Mb).toNat : ℝ) = ((Mb + 1 - -Mb : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg hpos]
      rw [hMb]; push_cast
      rw [hs, one_div_one_div]
      linarith
    calc ((((Mb + 1 - -Mb).toNat ^ 3 : ℕ)) : ℝ) = ((Mb + 1 - -Mb).toNat : ℝ) ^ 3 := by push_cast; ring
      _ ≤ (16 * lam + 5) ^ 3 := by gcongr
      _ ≤ (21 * lam) ^ 3 := by gcongr; linarith
  -- (e) the pigeonhole
  have hnpos : 0 < n := by
    by_contra h0
    push Not at h0
    have : n = 0 := by omega
    subst this
    simp at hM; linarith
  have hBpos : 0 < 3430 * lam * n := by positivity
  obtain ⟨m, hm, hn₀, hgood⟩ := exists_good_center box A N hAN hT hcount hBpos hMpos
    (by
      calc (box.card : ℝ) * n₀ * (384 * δ ^ 2 / lam) ≤ (21 * lam) ^ 3 * n₀ * (384 * δ ^ 2 / lam) := by
            gcongr
        _ ≤ Mtot / 2 := hlight)
    (by positivity)
  exact ⟨gridPt s m, hn₀, hgood⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
