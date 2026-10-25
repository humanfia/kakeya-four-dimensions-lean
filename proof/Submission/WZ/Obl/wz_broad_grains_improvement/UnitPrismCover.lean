-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.UnitPrismCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/- Adapted from this workspace: o196/x0579, commit5ac3173, UnitCover.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.RawPrismData
import Submission.WZ.Obl.wz_broad_grains_improvement.UnitPrismGeometry
import Submission.WZ.Obl.wz_coarse_tube_grains.Geom
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (G)
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData G_iff_data)

/-- Every dense small prism can be widened to a square-ended prism lying in
one of three centered unit tubes. -/
theorem RawPrismData.widened_unitCarrier {ω ζ δ h ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (D : RawPrismData ω ζ δ h ρ c n x v Y) (hδ : 0 < δ) (hcsmall : c ≤ 1 / 40)
    (hYball : ∀ i, Y i ⊆ I) (j : Fin D.L) :
    ∃ k : Fin 3, P D.a c c (D.z j) (D.e j) ⊆ unitCarrier k := by
  have ha : 0 < D.a := hδ.trans_le D.shape.1
  have hb : 0 < ρ * c := ha.trans_le D.shape.2.1
  have hc : 0 < c := hb.trans_le D.shape.2.2.1
  have hvol : μ (P D.a (ρ * c) c (D.z j) (D.e j)) =
      O (D.a * (ρ * c) * c) :=
    WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha.le hb.le hc.le _ _
  have hpositive : 0 < μ (⋃ i, D.W i j) := by
    apply lt_of_lt_of_le _ (D.dense j)
    rw [hvol]
    exact ENNReal.mul_pos (by simp [O]; positivity) (by simp [O]; positivity)
  obtain ⟨q, hq⟩ := nonempty_of_measure_ne_zero hpositive.ne'
  obtain ⟨i, hqi⟩ := mem_iUnion.mp hq
  have hqP := (D.pieces i j).2.1 hqi
  have hqball : ‖q‖ ≤ 1 := by
    have hh := hYball i hqP.1
    exact (show ‖q‖ < 1 by simpa only [I, mem_ball, dist_zero_right] using hh).le
  obtain ⟨k, hk⟩ := exists_unitCarrier_of_small_ball hqball
  refine ⟨k, fun p hp => hk ?_⟩
  have hpz := WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_subset_closedBall
    (D.shape.2.1.trans D.shape.2.2.1) le_rfl hc.le (D.z j) (D.e j) hp
  have hqz := WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_subset_closedBall
    D.shape.2.1 D.shape.2.2.1 hc.le (D.z j) (D.e j) hqP.2
  have hpz' : dist p (D.z j) ≤ c := hpz
  have hqz' : dist (D.z j) q ≤ c := by simpa only [mem_closedBall, dist_comm] using hqz
  have htriangle := dist_triangle p (D.z j) q
  change dist p q ≤ 1 / 20
  linarith

/-- Passing from angular scale `ρ` to unit scale costs at most `ρ⁻¹` when
the angular exponent is between zero and one. -/
theorem RawPrismData.broad_at_one {ω ζ δ h ε ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (D : RawPrismData ω ζ δ h ρ c n x v Y) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hh : 0 ≤ h) (hβ : 0 ≤ ω * ζ / 100) (hβ1 : ω * ζ / 100 ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hloss : δ ^ ε ≤ δ ^ h * ρ)
    (j : Fin D.L) (p u : V) (r : ℝ) (hu : ‖u‖ = 1) (hdr : δ ≤ r) (hr1 : r ≤ 1) :
    q n {i | p ∈ D.W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-ε) * (r / 1) ^ (ω * ζ / 100) * q n {i | p ∈ D.W i j} := by
  have hr : 0 < r := hδ.trans_le hdr
  have hρβ : ρ ≤ ρ ^ (ω * ζ / 100) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 hβ1
  have hhpow : δ ^ h ≤ 1 := Real.rpow_le_one hδ.le hδ1 hh
  have hcoeff : δ ^ (-h) / ρ ^ (ω * ζ / 100) ≤ δ ^ (-ε) := by
    rw [Real.rpow_neg hδ.le, Real.rpow_neg hδ.le, div_eq_mul_inv, ← mul_inv]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact hloss.trans (mul_le_mul_of_nonneg_left hρβ (by positivity))
  by_cases hrρ : r ≤ ρ
  · have hb := D.broad j p u r hu hdr hrρ
    refine hb.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [div_one, Real.div_rpow hr.le hρ.le]
    calc
      δ ^ (-h) * (r ^ (ω * ζ / 100) / ρ ^ (ω * ζ / 100)) =
          (δ ^ (-h) / ρ ^ (ω * ζ / 100)) * r ^ (ω * ζ / 100) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)
  · have hsub : q n {i | p ∈ D.W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        q n {i | p ∈ D.W i j} := by
      exact_mod_cast Set.ncard_le_ncard
        (show {i | p ∈ D.W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ⊆
          {i | p ∈ D.W i j} from fun _ hi => hi.1)
    have hpow : δ ^ ε ≤ r ^ (ω * ζ / 100) := by
      calc
        _ ≤ δ ^ h * ρ := hloss
        _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hhpow hρ.le
        _ = ρ := one_mul _
        _ ≤ ρ ^ (ω * ζ / 100) := hρβ
        _ ≤ _ := Real.rpow_le_rpow hρ.le (le_of_not_ge hrρ) hβ
    have hone : 1 ≤ δ ^ (-ε) * (r / 1) ^ (ω * ζ / 100) := by
      rw [div_one, Real.rpow_neg hδ.le, ← div_eq_inv_mul]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr (by simpa using hpow)
    exact hsub.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hone)

/-- A macroscopic broad prism family admits a single exact coarse tube.
Only whole prism labels are discarded, so their density and all directional
proportions survive. -/
theorem RawPrismData.stage_one_at_one_data {ω ζ δ h ε ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (D : RawPrismData ω ζ δ h ρ c n x v Y) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hh : 0 ≤ h) (hβ : 0 ≤ ω * ζ / 100) (hβ1 : ω * ζ / 100 ≤ 1)
    (hcsmall : c ≤ 1 / 40) (hball : ∀ i, T δ (x i) (v i) ⊆ I)
    (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmassloss : 3 * δ ^ ε ≤ δ ^ h) (hdenseloss : δ ^ ε ≤ δ ^ h * ρ) :
    ∃ D' : PrismData n, D'.Valid ω ζ δ ε 1 c x v Y 1 ∧ D'.a = D.a ∧
      ∃ τ : Fin D'.L → Fin D.L, Function.Injective τ ∧
        D'.z = D.z ∘ τ ∧ D'.e = D.e ∘ τ ∧ ∀ i, D'.W i = D.W i ∘ τ := by
  classical
  have ha : 0 < D.a := hδ.trans_le D.shape.1
  have hb : 0 < ρ * c := ha.trans_le D.shape.2.1
  have hc : 0 < c := hb.trans_le D.shape.2.2.1
  have hρ : 0 < ρ := pos_of_mul_pos_left hb hc.le
  have hρ1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hc).mp (by simpa using D.shape.2.2.1)
  choose label hlabel using D.widened_unitCarrier hδ hcsmall
    (fun i => (hYT i).trans (hball i))
  let weight : Fin D.L → ENNReal := fun j => ∑ i, μ (D.W i j)
  let mass : Fin 3 → ENNReal := fun k => ∑ j ∈ Finset.univ.filter (label · = k), weight j
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ mass Finset.univ_nonempty
  let S : Finset (Fin D.L) := Finset.univ.filter (label · = k)
  let g : Fin S.card ↪o Fin D.L := S.orderEmbOfFin rfl
  have hgS (j : Fin S.card) : g j ∈ S := S.orderEmbOfFin_mem rfl j
  have hglabel (j : Fin S.card) : label (g j) = k := (Finset.mem_filter.mp (hgS j)).2
  have hsum : (∑ i, ∑ j, μ (D.W i j)) ≤ 3 * ∑ j ∈ S, weight j := by
    rw [Finset.sum_comm]
    change (∑ j, weight j) ≤ 3 * mass k
    have he : ∑ k, mass k = ∑ j, weight j :=
      Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) weight
    rw [← he]
    calc
      ∑ k', mass k' ≤ ∑ _k' : Fin 3, mass k := Finset.sum_le_sum (fun k' hk' => hk k' hk')
      _ = _ := by simp [nsmul_eq_mul]
  have hsumg : ∑ j, weight (g j) = ∑ j ∈ S, weight j := by
    calc
      _ = ∑ j : S, weight j :=
        Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _
          (fun j => by simp [g, Finset.coe_orderIsoOfFin_apply])
      _ = _ := Finset.sum_coe_sort S weight
  let D' : PrismData n := ⟨D.a, 1, S.card, 1, D.z ∘ g, D.e ∘ g,
    (fun i j => D.W i (g j)), (fun _ => -(1 / 2 : ℝ) • unitAxis k),
    (fun _ => unitAxis k), (fun _ => 0)⟩
  refine ⟨D', ?_, rfl, g, g.injective, rfl, rfl, fun _ => rfl⟩
  refine ⟨D.shape.1, ?_, ?_, D.shape.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul] using D.shape.2.1.trans D.shape.2.2.1
  · simp
  · intro i j
    refine ⟨(D.pieces i (g j)).1, ?_, fun j' hjj' =>
      (D.pieces i (g j)).2.2 (g j') (fun he => hjj' (g.injective he))⟩
    intro p hp
    have hh := (D.pieces i (g j)).2.1 hp
    have hmid : (ρ * c) / 2 ≤ (1 * c) / 2 := by
      simpa only [one_mul] using
        div_le_div_of_nonneg_right D.shape.2.2.1 (by norm_num : (0 : ℝ) ≤ 2)
    exact ⟨hh.1, hh.2.1, hh.2.2.1.trans hmid, hh.2.2.2⟩
  · have htot : (3 : ENNReal) * (O (δ ^ ε) * ∑ i, μ (Y i)) ≤
        3 * ∑ j ∈ S, weight j := by
      calc
        _ = O (3 * δ ^ ε) * ∑ i, μ (Y i) := by
          simp only [O, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
            ENNReal.ofReal_ofNat, mul_assoc]
        _ ≤ O (δ ^ h) * ∑ i, μ (Y i) := mul_le_mul' (ENNReal.ofReal_le_ofReal hmassloss) le_rfl
        _ ≤ _ := D.mass.trans hsum
    have hdiv : (3 : ENNReal)⁻¹ * (3 * (O (δ ^ ε) * ∑ i, μ (Y i))) ≤
        (3 : ENNReal)⁻¹ * (3 * ∑ j ∈ S, weight j) := mul_le_mul' le_rfl htot
    have hthree : (3 : ENNReal)⁻¹ * 3 = 1 := by
      rw [mul_comm]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    simp only [← mul_assoc, hthree, one_mul] at hdiv
    rw [Finset.sum_comm]
    change O (δ ^ ε) * ∑ i, μ (Y i) ≤ ∑ j, weight (g j)
    rw [hsumg]
    exact hdiv
  · intro j
    refine le_trans ?_ (D.dense (g j))
    simp only [Function.comp_apply, one_mul]
    have hnewvol : μ (P D.a c c (D.z (g j)) (D.e (g j))) = O (D.a * c * c) :=
      WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha.le hc.le hc.le _ _
    have holdvol : μ (P D.a (ρ * c) c (D.z (g j)) (D.e (g j))) = O (D.a * (ρ * c) * c) :=
      WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha.le hb.le hc.le _ _
    change O (δ^ε)*μ (P D.a c c (D.z (g j)) (D.e (g j))) ≤
      O (δ^h)*μ (P D.a (ρ*c) c (D.z (g j)) (D.e (g j)))
    rw [hnewvol, holdvol]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_right hdenseloss (show 0 ≤ D.a * c * c by positivity)
    nlinarith
  · intro i j hij
    have hcross := D.crossing i (g j) hij
    refine ⟨(hball i).trans (ball_zero_subset_unitCarrier k), ?_, ?_⟩
    · have hne : (T δ (x i) (v i) ∩ P D.a (ρ * c) c (D.z (g j)) (D.e (g j))).Nonempty := by
        obtain ⟨p, hp, _⟩ := hcross.2 (c / 2) (by simp)
        exact ⟨p, hp⟩
      exact (WangZahlLot.Obl.wz_coarse_tube_grains.Geom.crossing_widen
        Metric.isOpen_thickening ((convex_segment _ _).thickening δ) hc
        (by simpa only [one_mul] using D.shape.2.2.1) hne hcross.1).1
    · intro t ht
      obtain ⟨p, hp, hpt⟩ := hcross.2 t ht
      refine ⟨p, ⟨hp.1, hp.2.1, hp.2.2.1.trans ?_, hp.2.2.2⟩, hpt⟩
      simpa only [one_mul] using div_le_div_of_nonneg_right D.shape.2.2.1 (by norm_num : (0 : ℝ) ≤ 2)
  · intro j p u r hu hdr hr1
    exact D.broad_at_one hδ hδ1 hh hβ hβ1 hρ hρ1 hdenseloss (g j) p u r hu hdr hr1
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro _
    exact norm_unitAxis k
  · intro _
    refine ⟨rfl, ?_⟩
    intro j
    refine ⟨?_, ?_⟩
    · change P D.a (1 * c) c (D.z (g j)) (D.e (g j)) ⊆ unitCarrier k
      rw [one_mul, ← hglabel j]
      exact hlabel (g j)
    ·
      have hnorm : ‖D.e (g j) (unitAxis k)‖ = 1 := by simp [norm_unitAxis]
      have h0 := PiLp.norm_apply_le (D.e (g j) (unitAxis k)) (0 : Fin 3)
      have h1 := PiLp.norm_apply_le (D.e (g j) (unitAxis k)) (1 : Fin 3)
      rw [hnorm, Real.norm_eq_abs] at h0 h1
      have hs0 := (sq_le_one_iff_abs_le_one _).mpr h0
      have hs1 := (sq_le_one_iff_abs_le_one _).mpr h1
      change (D.e (g j) (unitAxis k)) 0 ^ 2 +
        (D.e (g j) (unitAxis k)) 1 ^ 2 ≤ (10*1)^2
      linarith
  · omega

/-- The unit-scale cover with the selection witnesses omitted. -/
theorem RawPrismData.stage_one_at_one {ω ζ δ h ε ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (D : RawPrismData ω ζ δ h ρ c n x v Y) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hh : 0 ≤ h) (hβ : 0 ≤ ω * ζ / 100) (hβ1 : ω * ζ / 100 ≤ 1)
    (hcsmall : c ≤ 1 / 40) (hball : ∀ i, T δ (x i) (v i) ⊆ I)
    (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmassloss : 3 * δ ^ ε ≤ δ ^ h) (hdenseloss : δ ^ ε ≤ δ ^ h * ρ) :
    G ω ζ δ ε 1 c n x v Y 1 := by
  obtain ⟨D', H, _⟩ := D.stage_one_at_one_data hδ hδ1 hh hβ hβ1 hcsmall hball hYT
    hmassloss hdenseloss
  exact G_iff_data.mpr ⟨D', H⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
