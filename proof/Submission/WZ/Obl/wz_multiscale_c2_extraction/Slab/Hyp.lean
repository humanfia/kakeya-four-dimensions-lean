-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Hyp.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Setup

/-!
# The hypotheses of the slab lemma for a coarse set built at representative heights

A coarse set `E` is a union of grid cubes of side `s` in rows `m ∈ R`; every cube of row `m`
contains a fine point of a plank region `PR` at the representative height `zrep m` of its row.
This file checks all the hypotheses of `SlabLinearity` except the volume lower bound:

* the box and plank containment;
* the unit plane field `unitField P pc s` is exactly 1-Lipschitz with a large horizontal part;
* every horizontal slice of `E` projects into the `9 s`-neighbourhood of the global grain set
  at the representative height, hence is Assouad-regular at scale `s`;
* the local projections of `E` are covered by the local grains of the fine set at scale `4 s`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- A coarse configuration in one window. -/
structure CoarseConfig (s : ℝ) {n : ℕ} (Y : Fin n → Set Space) (f : ℝ → ℝ)
    (R : Finset ℤ) (zrep : ℤ → ℝ) (Kc : Finset (Fin 3 → ℤ)) (PR : Set Space)
    (z₀ c₀ : ℝ) (pc : Space) : Prop where
  zrep_mem : ∀ m ∈ R, zrep m ∈ Ico (s * m) (s * (m + 1))
  rows : ∀ m ∈ R, ∀ z ∈ Ico (s * m) (s * (m + 1)), 2 * Real.sqrt s ≤ |z| ∧ z ∈ Icc (-1 : ℝ) 1
  cube_row : ∀ k ∈ Kc, k 2 ∈ R
  cube_pt : ∀ k ∈ Kc, ∃ i, ∃ q ∈ Y i, q ∈ PR ∧ q 2 = zrep (k 2) ∧ q ∈ Coarse.gridCube s k
  PR_plank : ∀ q ∈ PR, |q 0 + f z₀ * q 1 - c₀| ≤ Real.sqrt s / 2
  PR_ball : ∀ q ∈ PR, dist q pc ≤ 1 / 3
  z₀_mem : z₀ ∈ Icc (-1 : ℝ) 1

/-- The union of the cubes of a configuration. -/
def cubeUnion (s : ℝ) (Kc : Finset (Fin 3 → ℤ)) : Set Space :=
  ⋃ k ∈ Kc, Coarse.gridCube s k

/-- The heights of the rows of a configuration. -/
def rowUnion (s : ℝ) (R : Finset ℤ) : Set ℝ :=
  ⋃ m ∈ R, Ico (s * m) (s * (m + 1))

lemma row_eq_of_mem {s : ℝ} (hs : 0 < s) {m m' : ℤ} {z : ℝ}
    (hz : z ∈ Ico (s * m) (s * (m + 1))) (hz' : z ∈ Ico (s * m') (s * (m' + 1))) : m = m' := by
  have h1 : (m : ℝ) ≤ z / s := by rw [le_div_iff₀ hs]; linarith [hz.1]
  have h2 : z / s < m + 1 := by rw [div_lt_iff₀ hs]; linarith [hz.2]
  have h1' : (m' : ℝ) ≤ z / s := by rw [le_div_iff₀ hs]; linarith [hz'.1]
  have h2' : z / s < m' + 1 := by rw [div_lt_iff₀ hs]; linarith [hz'.2]
  have a : m ≤ m' := by
    have : (m : ℝ) < m' + 1 := by linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
  have b : m' ≤ m := by
    have : (m' : ℝ) < m + 1 := by linarith
    exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
  omega

lemma height_mem_row {s : ℝ} {k : Fin 3 → ℤ} {p : Space} (hp : p ∈ Coarse.gridCube s k) :
    p 2 ∈ Ico (s * k 2) (s * (k 2 + 1)) :=
  ⟨(hp 2).1, (hp 2).2⟩

section

variable {σ δ s θ K N : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
  {Eo : Set Space} {f : ℝ → ℝ} {P : Space → Space}
  {R : Finset ℤ} {zrep : ℤ → ℝ} {Kc : Finset (Fin 3 → ℤ)} {PR : Set Space}
  {z₀ c₀ : ℝ} {pc : Space}

lemma s_pos (hS : FineSetup σ δ s θ K N x v Y Eo f P) : 0 < s := hS.δ_pos.trans_le hS.δ_le

lemma sqrt_s_bounds (hS : FineSetup σ δ s θ K N x v Y Eo f P) :
    16 * s ≤ Real.sqrt s ∧ Real.sqrt s ≤ 1 / 1000 := by
  have hs := s_pos hS
  have hs1 := hS.s_small
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hle : Real.sqrt s ≤ 1 / 1000 := by
    rw [show (1 : ℝ) / 1000 = Real.sqrt (1 / 10 ^ 6) by
      rw [show (1 : ℝ) / 10 ^ 6 = (1 / 1000) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hs1
  refine ⟨?_, hle⟩
  nlinarith

/-- A fine point at height at least `2 √s` is at distance at least `2 s` from the vertical
faces of the box. -/
lemma coord_le_of_height (hS : FineSetup σ δ s θ K N x v Y Eo f P) {q : Space} (hq : q ∈ Eo)
    (hq2 : 2 * Real.sqrt s ≤ |q 2|) : |q 0| ≤ 1 - 2 * s ∧ |q 1| ≤ 1 - 2 * s := by
  have hs := s_pos hS
  have hball := mem_ball_zero_iff.mp (hS.Eo_ball hq)
  have hn := norm_sq_eq_three q
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have h2 : 4 * s ≤ q 2 ^ 2 := by
    have : (2 * Real.sqrt s) ^ 2 ≤ |q 2| ^ 2 :=
      pow_le_pow_left₀ (by positivity) hq2 2
    rw [sq_abs, mul_pow, hsq] at this
    linarith
  have hnorm : ‖q‖ ^ 2 < 1 := by
    have := pow_lt_pow_left₀ hball (norm_nonneg q) (two_ne_zero)
    simpa using this
  have hs1 := hS.s_small
  have h3 : (1 - 4 * s) ≤ (1 - 2 * s) ^ 2 := by nlinarith
  have h5 : 0 ≤ 1 - 2 * s := by
    have : s ≤ 1 / 2 := hs1.trans (by norm_num)
    linarith
  have hq0 : q 0 ^ 2 ≤ (1 - 2 * s) ^ 2 := by nlinarith [sq_nonneg (q 1)]
  have hq1 : q 1 ^ 2 ≤ (1 - 2 * s) ^ 2 := by nlinarith [sq_nonneg (q 0)]
  exact ⟨abs_le.mpr (abs_le_of_sq_le_sq' hq0 h5), abs_le.mpr (abs_le_of_sq_le_sq' hq1 h5)⟩

theorem hyp_box (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    (hC : CoarseConfig s Y f R zrep Kc PR z₀ c₀ pc) :
    ∀ p ∈ cubeUnion s Kc, |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ p 2 ∈ rowUnion s R ∧
      |p 0 + f z₀ * p 1 - c₀| ≤ Real.sqrt s := by
  intro p hp
  obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp hp
  obtain ⟨i, q, hqY, hqPR, hq2, hqk⟩ := hC.cube_pt k hk
  have hs := s_pos hS
  have hpq : dist p q < 2 * s := Coarse.diam_le_of_mem_gridCube hs hpk hqk
  have hqE : q ∈ Eo := hS.sub_Eo i hqY
  have hrow := hC.cube_row k hk
  have hzr := hC.zrep_mem _ hrow
  have hqh : 2 * Real.sqrt s ≤ |q 2| := by rw [hq2]; exact (hC.rows _ hrow _ hzr).1
  obtain ⟨h0, h1⟩ := coord_le_of_height hS hqE hqh
  have d0 := abs_coord_sub_le p q 0
  have d1 := abs_coord_sub_le p q 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub (p 0) (q 0); linarith
  · have := abs_sub_abs_le_abs_sub (p 1) (q 1); linarith
  · exact mem_iUnion₂.mpr ⟨k 2, hrow, height_mem_row hpk⟩
  · have hfz : |f z₀| ≤ 3 := hS.f_bound z₀ hC.z₀_mem
    have hplank := hC.PR_plank q hqPR
    have e : p 0 + f z₀ * p 1 - c₀ = (q 0 + f z₀ * q 1 - c₀) + ((p 0 - q 0) + f z₀ * (p 1 - q 1)) := by
      ring
    have hb := sqrt_s_bounds hS
    rw [e]
    calc |(q 0 + f z₀ * q 1 - c₀) + ((p 0 - q 0) + f z₀ * (p 1 - q 1))|
        ≤ |q 0 + f z₀ * q 1 - c₀| + (|p 0 - q 0| + |f z₀| * |p 1 - q 1|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Real.sqrt s / 2 + (dist p q + 3 * dist p q) := by gcongr
      _ ≤ Real.sqrt s := by linarith

lemma rowUnion_subset_Icc (hC : CoarseConfig s Y f R zrep Kc PR z₀ c₀ pc) :
    rowUnion s R ⊆ Icc (-1 : ℝ) 1 := by
  intro z hz
  obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
  exact (hC.rows m hm z hzm).2

lemma norm_le_two_of_box {p : Space} (h0 : |p 0| ≤ 1) (h1 : |p 1| ≤ 1) (h2 : |p 2| ≤ 1) :
    ‖p‖ ≤ 2 := by
  have hn := norm_sq_eq_three p
  have a0 : p 0 ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (p 0)]
  have a1 : p 1 ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (p 1)]
  have a2 : p 2 ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (p 2)]
  have : ‖p‖ ^ 2 ≤ 2 ^ 2 := by rw [hn]; nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp this

/-- Every coarse point is within `2 s` of a fine point of its cube. -/
lemma near_fine (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    (hC : CoarseConfig s Y f R zrep Kc PR z₀ c₀ pc) :
    ∀ p ∈ cubeUnion s Kc, ∃ i, ∃ q ∈ Y i, q ∈ PR ∧ dist p q < 2 * s := by
  intro p hp
  obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp hp
  obtain ⟨i, q, hqY, hqPR, -, hqk⟩ := hC.cube_pt k hk
  exact ⟨i, q, hqY, hqPR, Coarse.diam_le_of_mem_gridCube (s_pos hS) hpk hqk⟩

lemma cubeUnion_subset_ball (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    (hC : CoarseConfig s Y f R zrep Kc PR z₀ c₀ pc) :
    cubeUnion s Kc ⊆ ball pc (2 / 5) := by
  intro p hp
  obtain ⟨i, q, -, hqPR, hpq⟩ := near_fine hS hC p hp
  have h := hC.PR_ball q hqPR
  have hs1 := hS.s_small
  rw [mem_ball]
  calc dist p pc ≤ dist p q + dist q pc := dist_triangle _ _ _
    _ < 2 * s + 1 / 3 := by linarith
    _ ≤ 2 / 5 := by linarith

/-- The plane field hypotheses. -/
theorem hyp_V (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    (hC : CoarseConfig s Y f R zrep Kc PR z₀ c₀ pc) {η : ℝ}
    (hη : s ^ η ≤ (θ - δ) / 2 - 8 * s) :
    (∀ p ∈ cubeUnion s Kc, ‖unitField P pc s p‖ = 1 ∧
      s ^ (2 * η) ≤ (unitField P pc s p 0) ^ 2 + (unitField P pc s p 1) ^ 2) ∧
    (∀ p ∈ cubeUnion s Kc, ∀ q ∈ cubeUnion s Kc,
      dist (unitField P pc s p) (unitField P pc s q) ≤ dist p q) := by
  have hs := s_pos hS
  have hs1 : s ≤ 1 / 20 := hS.s_small.trans (by norm_num)
  have hnear : ∀ p ∈ cubeUnion s Kc, ∃ p', ‖P p'‖ = 1 ∧ dist p p' ≤ 2 * s := by
    intro p hp
    obtain ⟨i, q, hqY, -, hpq⟩ := near_fine hS hC p hp
    exact ⟨q, hS.unit q (hS.sub_Eo i hqY), hpq.le⟩
  obtain ⟨hunit, hlip, hclose⟩ :=
    unitField_spec hS.P_lip hs hs1 (cubeUnion_subset_ball hS hC) hnear
  refine ⟨fun p hp => ⟨hunit p hp, ?_⟩, hlip⟩
  obtain ⟨i, q, hqY, -, hpq⟩ := near_fine hS hC p hp
  have hqE := hS.sub_Eo i hqY
  have hd := hclose p hp q (hS.unit q hqE) hpq.le
  have hvθ := hS.vert i ⟨q, hqY⟩
  have hh := norm_horiz_ge_of_perp (hS.v_unit i) (hS.unit q hqE) hS.θ_pos.le hvθ hS.θ_le
    (hS.perp i q hqY)
  have hsub : ‖horiz (unitField P pc s p)‖ ≥ ‖horiz (P q)‖ - 8 * s := by
    have h1 : ‖horiz (unitField P pc s p) - horiz (P q)‖ ≤ 8 * s := by
      rw [← horiz_sub]
      exact (norm_horiz_le _).trans (by rw [← dist_eq_norm]; exact hd)
    have h2 := norm_sub_norm_le (horiz (P q)) (horiz (unitField P pc s p))
    rw [norm_sub_rev] at h2
    linarith
  have hpos : 0 ≤ s ^ η := Real.rpow_nonneg hs.le _
  have hge : s ^ η ≤ ‖horiz (unitField P pc s p)‖ := by linarith
  rw [← norm_horiz_sq, show s ^ (2 * η) = (s ^ η) ^ 2 by
    rw [mul_comm, Real.rpow_mul hs.le]; norm_num]
  exact pow_le_pow_left₀ hpos hge 2

/-- The slices of the coarse set are Assouad-regular at the coarse scale. -/
theorem hyp_slice (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    (hC : CoarseConfig s Y f R zrep Kc PR z₀ c₀ pc) :
    ∀ z ∈ rowUnion s R, Reg.Assouad s (1 - σ) (162 * K)
      {u : ℝ | ∃ p ∈ cubeUnion s Kc, p 2 = z ∧ u = p 0 + f z * p 1} := by
  intro z hz
  obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
  have hs := s_pos hS
  have hzr := hC.zrep_mem m hm
  have hzr1 : zrep m ∈ Icc (-1 : ℝ) 1 := (hC.rows m hm _ hzr).2
  have hB := (hS.glob (zrep m) hzr1).mono_scale hS.δ_le
  have h := Reg.Assouad.perturb_mul (K := 9) hs (by linarith [hS.σ_lt]) (by linarith [hS.σ_pos])
    (by linarith [hS.K_one]) (by norm_num) hB
    (A := {u : ℝ | ∃ p ∈ cubeUnion s Kc, p 2 = z ∧ u = p 0 + f z * p 1}) ?_
  · convert h using 1; ring
  rintro u ⟨p, hp, hp2, rfl⟩
  obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp hp
  obtain ⟨i, q, hqY, -, hq2, hqk⟩ := hC.cube_pt k hk
  have hkm : k 2 = m := row_eq_of_mem hs (hp2 ▸ height_mem_row hpk) hzm
  have hqE := hS.sub_Eo i hqY
  refine ⟨q 0 + f (q 2) * q 1, ?_, ?_⟩
  · rw [show zrep m = q 2 by rw [hq2, hkm]]
    exact mem_projectedSlice hqE
  · have hpq : dist p q < 2 * s := Coarse.diam_le_of_mem_gridCube hs hpk hqk
    have hfz : |f z| ≤ 3 := hS.f_bound z (hC.rows m hm z hzm).2
    have hq1 : |q 1| ≤ 1 := (abs_coord_lt_one (hS.Eo_ball hqE) 1).le
    have h1 := twist_sub_le (p := p) (q := q) (G := f (q 2)) hfz hq1
    have hlip : |f z - f (q 2)| ≤ |z - q 2| := by
      have := hS.f_lip.dist_le_mul z (q 2)
      simpa [Real.dist_eq] using this
    have hzq : |z - q 2| ≤ s := by
      rw [hq2, hkm]
      rw [abs_le]
      constructor <;> linarith [hzm.1, hzm.2, hzr.1, hzr.2]
    linarith

/-- The 1-dimensional measure of a union of `m` closed intervals of radius `r`. -/
lemma volume_iUnion_closedBall_le {m : ℕ} (c : Fin m → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (⋃ j, closedBall (c j) r) ≤ ENNReal.ofReal (m * (2 * r)) := by
  calc volume (⋃ j, closedBall (c j) r) ≤ ∑ j, volume (closedBall (c j) r) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _j : Fin m, ENNReal.ofReal (2 * r) := by
        congr 1; funext j; rw [Real.volume_closedBall]
    _ = ENNReal.ofReal (m * (2 * r)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The local projections of the coarse set are small. -/
theorem hyp_local (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    (hC : CoarseConfig s Y f R zrep Kc PR z₀ c₀ pc) :
    ∀ p ∈ cubeUnion s Kc, volume ((fun q : Space => ⟪unitField P pc s p, q⟫) ''
        (cubeUnion s Kc ∩ ball p (Real.sqrt s))) ≤
      ENNReal.ofReal (44 * K * s ^ ((1 + σ) / 2)) := by
  intro p hp
  have hs := s_pos hS
  have hb := sqrt_s_bounds hS
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  obtain ⟨i, qk, hqkY, -, hpqk⟩ := near_fine hS hC p hp
  have hqkE := hS.sub_Eo i hqkY
  have hs1 : s ≤ 1 / 20 := hS.s_small.trans (by norm_num)
  have hnear : ∀ p ∈ cubeUnion s Kc, ∃ p', ‖P p'‖ = 1 ∧ dist p p' ≤ 2 * s := by
    intro p hp
    obtain ⟨i, q, hqY, -, hpq⟩ := near_fine hS hC p hp
    exact ⟨q, hS.unit q (hS.sub_Eo i hqY), hpq.le⟩
  obtain ⟨-, -, hclose⟩ :=
    unitField_spec hS.P_lip hs hs1 (cubeUnion_subset_ball hS hC) hnear
  have hVq : dist (unitField P pc s p) (P qk) ≤ 8 * s :=
    hclose p hp qk (hS.unit qk hqkE) hpqk.le
  -- the local grains of the fine set at scale `4 s`
  have h4s : Real.sqrt (4 * s) = 2 * Real.sqrt s := by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hloc := hS.loc (4 * s) (by linarith [hS.δ_le]) (by linarith) qk hqkE
  set A := (fun q : Space => ⟪P qk, q⟫) '' (Eo ∩ ball qk (Real.sqrt (4 * s)))
  obtain ⟨m, c, hcov, hm⟩ := hloc (4 * s) (4 * Real.sqrt s) (⟪P qk, qk⟫ - 2 * Real.sqrt s)
    le_rfl (by nlinarith)
  -- every projected coarse point is near a projected fine point
  have hsub : (fun q : Space => ⟪unitField P pc s p, q⟫) ''
      (cubeUnion s Kc ∩ ball p (Real.sqrt s)) ⊆ ⋃ j, closedBall (c j) (22 * s) := by
    rintro w ⟨y, ⟨hyE, hyb⟩, rfl⟩
    obtain ⟨i', q', hq'Y, -, hyq'⟩ := near_fine hS hC y hyE
    have hq'E := hS.sub_Eo i' hq'Y
    have hyp : dist y p < Real.sqrt s := mem_ball.mp hyb
    have hq'qk : dist q' qk < 2 * Real.sqrt s := by
      calc dist q' qk ≤ dist q' y + dist y p + dist p qk := dist_triangle4 _ _ _ _
        _ < 2 * s + Real.sqrt s + 2 * s := by
            rw [dist_comm q' y]; linarith
        _ ≤ 2 * Real.sqrt s := by linarith
    have hA : ⟪P qk, q'⟫ ∈ A ∩ Icc (⟪P qk, qk⟫ - 2 * Real.sqrt s)
        (⟪P qk, qk⟫ - 2 * Real.sqrt s + 4 * Real.sqrt s) := by
      refine ⟨⟨q', ⟨hq'E, ?_⟩, rfl⟩, ?_⟩
      · rw [mem_ball, h4s]; exact hq'qk
      · have hcs : |⟪P qk, q' - qk⟫| ≤ ‖P qk‖ * ‖q' - qk‖ := abs_real_inner_le_norm _ _
        rw [hS.unit qk hqkE, one_mul, ← dist_eq_norm] at hcs
        rw [inner_sub_right] at hcs
        constructor <;> linarith [(abs_le.mp hcs).1, (abs_le.mp hcs).2]
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov hA)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    rw [mem_closedBall, Real.dist_eq] at hj ⊢
    have hbox := hyp_box hS hC y hyE
    have hy2 : |y 2| ≤ 1 := abs_le.mpr (rowUnion_subset_Icc hC hbox.2.2.1)
    have hny : ‖y‖ ≤ 2 := norm_le_two_of_box hbox.1 hbox.2.1 hy2
    have e : ⟪unitField P pc s p, y⟫ - c j =
        (⟪P qk, q'⟫ - c j) + ⟪unitField P pc s p - P qk, y⟫ + ⟪P qk, y - q'⟫ := by
      rw [inner_sub_left, inner_sub_right]; ring
    have t1 : |⟪unitField P pc s p - P qk, y⟫| ≤ 16 * s := by
      calc |⟪unitField P pc s p - P qk, y⟫| ≤ ‖unitField P pc s p - P qk‖ * ‖y‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (8 * s) * 2 := by
            rw [← dist_eq_norm]
            exact mul_le_mul hVq hny (norm_nonneg _) (by linarith)
        _ = 16 * s := by ring
    have t2 : |⟪P qk, y - q'⟫| ≤ 2 * s := by
      calc |⟪P qk, y - q'⟫| ≤ ‖P qk‖ * ‖y - q'‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * (2 * s) := by
            rw [hS.unit qk hqkE, ← dist_eq_norm]
            exact mul_le_mul le_rfl hyq'.le dist_nonneg (by norm_num)
        _ = 2 * s := by ring
    rw [e]
    calc |(⟪P qk, q'⟫ - c j) + ⟪unitField P pc s p - P qk, y⟫ + ⟪P qk, y - q'⟫|
        ≤ |⟪P qk, q'⟫ - c j| + |⟪unitField P pc s p - P qk, y⟫| + |⟪P qk, y - q'⟫| :=
          abs_add_three _ _ _
      _ ≤ 4 * s + 16 * s + 2 * s := by linarith
      _ = 22 * s := by ring
  have hratio : 4 * Real.sqrt s / (4 * s) = (Real.sqrt s)⁻¹ := by
    field_simp
    nlinarith
  rw [hratio] at hm
  calc volume ((fun q : Space => ⟪unitField P pc s p, q⟫) ''
        (cubeUnion s Kc ∩ ball p (Real.sqrt s)))
      ≤ volume (⋃ j, closedBall (c j) (22 * s)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (m * (2 * (22 * s))) := volume_iUnion_closedBall_le c (by linarith)
    _ ≤ ENNReal.ofReal (44 * K * s ^ ((1 + σ) / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have hpow : (Real.sqrt s)⁻¹ ^ (1 - σ) * s = s ^ ((1 + σ) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le, ← Real.rpow_mul hs.le,
            ← Real.rpow_add_one hs.ne']
          congr 1; ring
        calc (m : ℝ) * (2 * (22 * s)) = 44 * ((m : ℝ) * s) := by ring
          _ ≤ 44 * (K * (Real.sqrt s)⁻¹ ^ (1 - σ) * s) := by
              gcongr
          _ = 44 * K * s ^ ((1 + σ) / 2) := by rw [← hpow]; ring

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
