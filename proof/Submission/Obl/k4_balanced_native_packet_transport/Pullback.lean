import Submission.Obl.k4_balanced_native_packet_transport.CPF.OriginalPacketCoverage
import Submission.Obl.k4_remainder_pure_profile_normalization.ObservationImages

/-!
# Pulling a saturated normalized child atlas back to native depth-zero charts

A depth-zero parent known atlas `P` (with one time block, `P.T = 0`, and native tests
`P.R b = p.P (P.γ b)`) normalizes the original problem into `normalizedData q`.  A
saturated child atlas `a` of the normalized problem is pulled back chart by chart:
the assignment and the event are the original ones (`originalAssignment`,
`originalEvent`), the frame is the composed frame, the center and the velocity are
the affine images of the child ones, and the test is the native test of the world at
depth zero.  Terminal lists are the observation images of the pulled-back events;
their cardinality is controlled through the parent terminal lists and the child
own-depth lists, since the normalized depth-`r` observation is a function of the
original terminal observation (`normObs`).

The format computations follow `ChartSystem.lift_assignment_format` and
`ChartSystem.lift_event_format` of this tree's accepted o184
(`Submission/Obl/k4_remainder_pure_profile_normalization/Normalization/Lift.lean`), and the
measurability of observation images is o184's `measurableSet_obs_image`.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.Pullback

open MeasureTheory Set
open Submission.Obl.k4_remainder_pure_profile_normalization
open Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedPacketSystems
open Submission.Obl.k4_balanced_native_packet_transport.CPF.OriginalPacketCoverage

/-! ### Dyadic depths -/

/-- The number of halvings between the depth-`r` and the depth-one dyadic thickness. -/
noncomputable def dyadicGap (N r : ℝ) : ℕ :=
  (⌊1 * Real.log N / Real.log 2⌋ - ⌊r * Real.log N / Real.log 2⌋).toNat

theorem delta_zero (N : ℝ) : δ N 0 = 1 := by
  simp [δ]

theorem delta_eq_pow_mul {N r : ℝ} (hN : 1 ≤ N) (hr : r ≤ 1) :
    δ N r = (2 : ℝ) ^ dyadicGap N r * δ N 1 := by
  have hlog : 0 ≤ Real.log N / Real.log 2 :=
    div_nonneg (Real.log_nonneg hN) (Real.log_nonneg one_le_two)
  have hle : ⌊r * Real.log N / Real.log 2⌋ ≤ ⌊1 * Real.log N / Real.log 2⌋ := by
    apply Int.floor_mono
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hr hlog
  unfold δ dyadicGap
  rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_add₀ two_ne_zero]
  congr 1
  ring

/-- Floors at depth `r ≤ 1` are integer quotients of floors at depth one. -/
theorem floor_div_delta {N r : ℝ} (hN : 1 ≤ N) (hr : r ≤ 1) (X : ℝ) :
    ⌊X / δ N r⌋ = ⌊X / δ N 1⌋ / ((2 ^ dyadicGap N r : ℕ) : ℤ) := by
  rw [← Int.floor_div_natCast, delta_eq_pow_mul hN hr]
  congr 1
  push_cast
  rw [div_div, mul_comm]

/-! ### Normalized observations -/

/-- The normalized depth-`r` observation (with `g = dyadicGap N r`) of an original
terminal observation, through a parent chart with frame `Q`, center `c` and velocity
`u` on the single time block `[0, 1]`. -/
noncomputable def normObs (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : Spatial) (g : ℕ)
    (o : Observation) : Observation :=
  (WithLp.toLp 2 ![o.1 0,
      Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![o.1 1, o.1 2] - c - o.1 0 • u) 0,
      Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![o.1 1, o.1 2] - c - o.1 0 • u) 1],
    o.2 / ((2 ^ g : ℕ) : ℤ))

/-- Through a parent frame on the unit time block, the normalized depth-`r` observation
of a normalized incidence is a function of the original terminal observation. -/
theorem obs_normalize (F : Normalization.Frame) (ht₀ : F.t₀ = 0) (hq : F.q = 1)
    {N r : ℝ} (hN : 1 ≤ N) (hr : r ≤ 1) (B : ℝ) (z : Incidence) :
    obs (B / δ N 0) (δ N r) (F.normTraj z.1, (z.2 - F.t₀) / F.q) =
      normObs F.D F.c F.u (dyadicGap N r) (obs B (δ N 1) z) := by
  have hpl := F.planarPoint_normTraj (by rw [hq]; exact one_ne_zero) z.1 z.2
  rw [ht₀, hq, sub_zero, div_one] at hpl ⊢
  have h3 : x (F.normTraj z.1) z.2 3 = x z.1 z.2 3 := by
    simp [x, Normalization.Frame.normTraj, Normalization.Frame.normCoeff, ht₀, hq]
  refine Prod.ext ?_ ?_
  · show WithLp.toLp 2 ![z.2, Normalization.planarPoint (F.normTraj z.1) z.2 0,
        Normalization.planarPoint (F.normTraj z.1) z.2 1] =
      WithLp.toLp 2 ![z.2,
        Matrix.toEuclideanLin F.D⁻¹ (Normalization.planarPoint z.1 z.2 - F.c - z.2 • F.u) 0,
        Matrix.toEuclideanLin F.D⁻¹ (Normalization.planarPoint z.1 z.2 - F.c - z.2 • F.u) 1]
    rw [hpl]
  · show ⌊B / δ N 0 * x (F.normTraj z.1) z.2 3 / δ N r⌋ =
      ⌊B * x z.1 z.2 3 / δ N 1⌋ / ((2 ^ dyadicGap N r : ℕ) : ℤ)
    rw [h3, delta_zero, div_one, floor_div_delta hN hr]

/-! ### Unit parent blocks -/

theorem frameOf_unit {p : Data} {k : ℕ} (P : Atlas p k) (hT : P.T = 0) (b : Fin P.C) :
    (P.system.frameOf b).t₀ = 0 ∧ (P.system.frameOf b).q = 1 := by
  have hj : (P.j b : ℕ) = 0 := by
    have h1 : (P.j b : ℕ) < 2 ^ P.T := (P.j b).isLt
    have h2 : (2 : ℕ) ^ P.T = 1 := by rw [hT]; rfl
    omega
  constructor
  · show ((P.j b : ℕ) : ℝ) / (2 : ℝ) ^ P.T = 0
    rw [hj]
    simp
  · show 1 / (2 : ℝ) ^ P.T = 1
    rw [hT]
    simp

theorem parent_block_eq {p : Data} {k : ℕ} (P : Atlas p k) (hT : P.T = 0) (b : Fin P.C) :
    Icc (((P.j b : ℕ) : ℝ) / (2 : ℝ) ^ P.T) ((((P.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ P.T) =
      Icc 0 1 := by
  have hj : (P.j b : ℕ) = 0 := by
    have h1 : (P.j b : ℕ) < 2 ^ P.T := (P.j b).isLt
    have h2 : (2 : ℕ) ^ P.T = 1 := by rw [hT]; rfl
    omega
  rw [hj, hT]
  norm_num

theorem block_subset_unit {T : ℕ} (j : Fin (2 ^ T)) :
    Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) ⊆ Icc 0 1 := by
  rintro t ⟨h1, h2⟩
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  have hj' : (j : ℕ) + 1 ≤ 2 ^ T := j.isLt
  have hj : ((j : ℕ) : ℝ) + 1 ≤ 2 ^ T := by exact_mod_cast hj'
  exact ⟨le_trans (by positivity) h1, h2.trans ((div_le_one hT).mpr hj)⟩

/-! ### The pulled-back charts -/

section Setting

variable {p : SourceData} (q : Certificate p) (k : ℕ) (a : CPF.Atlas (normalizedData q) k)

/-- The original world of a pulled-back chart. -/
def pullWorld (c : Fin a.C) : Fin (p.W (q.sequence.index k)) :=
  (q.sequence.atlas k).γ (a.γ c)

/-- The original center: the parent center plus the parent frame image of the child
center. -/
noncomputable def pullCenter (c : Fin a.C) : Spatial :=
  (q.sequence.atlas k).c (a.γ c) +
    Matrix.toEuclideanLin ((q.sequence.atlas k).Q (a.γ c)) (a.c c)

/-- The original velocity: the parent velocity plus the parent frame image of the child
velocity. -/
noncomputable def pullVelocity (c : Fin a.C) : Spatial :=
  (q.sequence.atlas k).u (a.γ c) +
    Matrix.toEuclideanLin ((q.sequence.atlas k).Q (a.γ c)) (a.u c)

/-- Terminal lists of the pulled-back charts: the terminal observation images of their
original events. -/
noncomputable def pullList (γ : Fin (p.W (q.sequence.index k))) (o : Observation) :
    Finset (Fin a.C) :=
  @Finset.filter (Fin a.C)
    (fun c => pullWorld q k a c = γ ∧
      o ∈ obs (p.B (q.sequence.index k) γ) (δ (p.N (q.sequence.index k)) 1) ''
        originalEvent q k a c)
    (fun _ => Classical.propDecidable _) Finset.univ

theorem mem_pullList (γ : Fin (p.W (q.sequence.index k))) (o : Observation) (c : Fin a.C) :
    c ∈ pullList q k a γ o ↔ pullWorld q k a c = γ ∧
      o ∈ obs (p.B (q.sequence.index k) γ) (δ (p.N (q.sequence.index k)) 1) ''
        originalEvent q k a c := by
  unfold pullList
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem composedFrame_eq (c : Fin a.C) :
    composedFrame q k a c = (q.sequence.atlas k).Q (a.γ c) * a.Q c := rfl

theorem pull_det {M₁ D₁ : ℕ} {r : ℝ} (ha : a.TrueAt M₁ D₁ r) (c : Fin a.C) :
    (composedFrame q k a c).det ≠ 0 := by
  rw [composedFrame_eq, Matrix.det_mul]
  exact mul_ne_zero (parent_det_ne_zero q k (a.γ c)) (ha.2.2.1 c).1

theorem pull_center_bound (hp : p.Valid) {M₁ D₁ : ℕ} {r : ℝ} (ha : a.TrueAt M₁ D₁ r)
    (c : Fin a.C) :
    ‖pullCenter q k a c‖ + ‖pullVelocity q k a c‖ ≤
      p.N (q.sequence.index k) ^ (q.M + M₁ + 1) := by
  obtain ⟨_, _, _, _, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨_, hPcu, hPfr, _⟩ := hPchart (a.γ c)
  obtain ⟨_, hacu, _⟩ := ha.2.2.1 c
  change ‖a.c c‖ + ‖a.u c‖ ≤ p.N (q.sequence.index k) ^ M₁ at hacu
  have hN : 2 ≤ p.N (q.sequence.index k) := hp.1 _
  have hS : (∑ e : Fin 2, ∑ e' : Fin 2, |(q.sequence.atlas k).Q (a.γ c) e e'|) ≤
      p.N (q.sequence.index k) ^ q.M := by
    refine le_trans (Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun e' _ =>
      le_add_of_nonneg_right (abs_nonneg (((q.sequence.atlas k).Q (a.γ c))⁻¹ e e'))) hPfr
  have hS0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |(q.sequence.atlas k).Q (a.γ c) e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc := Normalization.norm_toEuclideanLin_le ((q.sequence.atlas k).Q (a.γ c)) (a.c c)
  have hu := Normalization.norm_toEuclideanLin_le ((q.sequence.atlas k).Q (a.γ c)) (a.u c)
  have h1 := norm_add_le ((q.sequence.atlas k).c (a.γ c))
    (Matrix.toEuclideanLin ((q.sequence.atlas k).Q (a.γ c)) (a.c c))
  have h2 := norm_add_le ((q.sequence.atlas k).u (a.γ c))
    (Matrix.toEuclideanLin ((q.sequence.atlas k).Q (a.γ c)) (a.u c))
  have hN1 : (1 : ℝ) ≤ p.N (q.sequence.index k) ^ M₁ := one_le_pow₀ (by linarith)
  have hP0 : (0 : ℝ) ≤ p.N (q.sequence.index k) ^ q.M := by positivity
  have hcu0 : 0 ≤ ‖a.c c‖ + ‖a.u c‖ := by positivity
  have hprod : (∑ e : Fin 2, ∑ e' : Fin 2, |(q.sequence.atlas k).Q (a.γ c) e e'|) *
      (‖a.c c‖ + ‖a.u c‖) ≤
        p.N (q.sequence.index k) ^ q.M * p.N (q.sequence.index k) ^ M₁ :=
    mul_le_mul hS hacu hcu0 hP0
  have e : p.N (q.sequence.index k) ^ (q.M + M₁ + 1) =
      p.N (q.sequence.index k) ^ q.M * p.N (q.sequence.index k) ^ M₁ *
        p.N (q.sequence.index k) := by
    rw [pow_add, pow_add, pow_one]
  unfold pullCenter pullVelocity
  rw [e]
  have hA0 : 0 ≤ p.N (q.sequence.index k) ^ q.M * p.N (q.sequence.index k) ^ M₁ := by
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hN1 hP0]

theorem pull_frame_bound (hp : p.Valid) {M₁ D₁ : ℕ} {r : ℝ} (ha : a.TrueAt M₁ D₁ r)
    (c : Fin a.C) :
    (∑ e : Fin 2, ∑ e' : Fin 2,
      (|composedFrame q k a c e e'| + |(composedFrame q k a c)⁻¹ e e'|)) ≤
      p.N (q.sequence.index k) ^ (q.M + M₁ + 1) := by
  obtain ⟨_, _, _, _, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨_, _, hPfr, _⟩ := hPchart (a.γ c)
  obtain ⟨_, _, hafr, _⟩ := ha.2.2.1 c
  exact Normalization.lift_frame_bounds _ _ (hp.1 _) hPfr hafr

theorem pull_thin {M₁ D₁ : ℕ} {r κout : ℝ} (hT : (q.sequence.atlas k).T = 0)
    (ha : a.TrueAt M₁ D₁ r) (hκout : (q.sequence.atlas k).κ * a.κ ≤ κout) (c : Fin a.C) :
    (∑ e : Fin 2, ∑ e' : Fin 2, |composedFrame q k a c e e'|) ≤ κout / (2 : ℝ) ^ a.T := by
  obtain ⟨_, _, _, _, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨_, _, _, hPthin, _⟩ := hPchart (a.γ c)
  obtain ⟨_, _, _, hathin, _⟩ := ha.2.2.1 c
  rw [hT, pow_zero, div_one] at hPthin
  have hκP : 0 ≤ (q.sequence.atlas k).κ := by linarith [q.sequence.slack_one k]
  have hS0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |a.Q c e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [composedFrame_eq]
  refine (Normalization.matrix_l1_mul_le _ _).trans ?_
  calc _ ≤ (q.sequence.atlas k).κ * (a.κ / (2 : ℝ) ^ a.T) := mul_le_mul hPthin hathin hS0 hκP
    _ = (q.sequence.atlas k).κ * a.κ / (2 : ℝ) ^ a.T := by ring
    _ ≤ κout / (2 : ℝ) ^ a.T := div_le_div_of_nonneg_right hκout (by positivity)

theorem pull_assignment_fmt {M₁ D₁ : ℕ} {r : ℝ} (ha : a.TrueAt M₁ D₁ r) (c : Fin a.C)
    (i : ℕ) :
    Normalization.Fmt (p.N (q.sequence.index k) ^ q.M + p.N (q.sequence.index k) ^ M₁)
      (max q.D D₁) {x | (i, x) ∈ originalAssignment q k a c} := by
  obtain ⟨_, _, _, _, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨_, _, _, _, _, _, _, _, hPfmt, _⟩ := hPchart (a.γ c)
  obtain ⟨_, _, _, _, _, _, _, _, hafmt, _⟩ := ha.2.2.1 c
  have h₀ : Normalization.Fmt (p.N (q.sequence.index k) ^ q.M) q.D
      {x | (i, x) ∈ (q.sequence.atlas k).A (a.γ c)} := (hPfmt i).1
  have h' : Normalization.Fmt (p.N (q.sequence.index k) ^ M₁) D₁ {x | (i, x) ∈ a.A c} :=
    (hafmt i).1
  have hpre := h'.preimage ((q.sequence.atlas k).system.frameOf (a.γ c)).normCoeffPoly
    ((q.sequence.atlas k).system.frameOf (a.γ c)).totalDegree_normCoeffPoly_le
  refine (h₀.inter hpre).congr ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    ((q.sequence.atlas k).system.frameOf (a.γ c)).eval_normCoeffPoly]
  rfl

theorem pull_event_fmt {M₁ D₁ : ℕ} {r : ℝ} (ha : a.TrueAt M₁ D₁ r) (c : Fin a.C) (i : ℕ) :
    Normalization.Fmt (p.N (q.sequence.index k) ^ q.M + p.N (q.sequence.index k) ^ M₁)
      (max q.D D₁) {x₁ : Fin 7 → ℝ |
        ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ originalEvent q k a c} := by
  obtain ⟨_, _, _, _, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨_, _, _, _, _, _, _, _, hPfmt, _⟩ := hPchart (a.γ c)
  obtain ⟨_, _, _, _, _, _, _, _, hafmt, _⟩ := ha.2.2.1 c
  have h₀ : Normalization.Fmt (p.N (q.sequence.index k) ^ q.M) q.D
      {x | (i, x) ∈ (q.sequence.atlas k).A (a.γ c)} := (hPfmt i).1
  have h' : Normalization.Fmt (p.N (q.sequence.index k) ^ M₁) D₁
      {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ a.F c} :=
    (hafmt i).2
  have hA := h₀.preimage
    (fun j : Fin 6 => (MvPolynomial.X j.castSucc : MvPolynomial (Fin 7) ℝ))
    (fun j => Normalization.deg1_X _)
  have hF := h'.preimage ((q.sequence.atlas k).system.frameOf (a.γ c)).normIncPoly
    ((q.sequence.atlas k).system.frameOf (a.γ c)).totalDegree_normIncPoly_le
  refine (hA.inter hF).congr ?_
  rw [originalEvent_eq_pullback q ha c]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    ((q.sequence.atlas k).system.frameOf (a.γ c)).eval_normIncPoly,
    MvPolynomial.eval_X, Fin.lastCases_castSucc]
  have h6 : (6 : Fin 7) = Fin.last 6 := rfl
  rw [h6, Fin.lastCases_last]
  simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_preimage]
  rfl

theorem pull_geometry {M₁ D₁ : ℕ} {r : ℝ} (hT : (q.sequence.atlas k).T = 0)
    (ha : a.TrueAt M₁ D₁ r) (c : Fin a.C) (l : Trajectory)
    (hl : l ∈ originalAssignment q k a c) (t : ℝ)
    (ht : t ∈ Icc (((a.j c : ℕ) : ℝ) / (2 : ℝ) ^ a.T)
      ((((a.j c : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T)) :
    ‖Matrix.toEuclideanLin (composedFrame q k a c)⁻¹
      (y l t - pullCenter q k a c - t • pullVelocity q k a c)‖ ≤ a.κ := by
  obtain ⟨ht₀, hq⟩ := frameOf_unit (q.sequence.atlas k) hT (a.γ c)
  obtain ⟨_, _, _, _, _, _, _, _, _, haA, _⟩ := ha.2.2.1 c
  obtain ⟨_, _, hgeo⟩ :=
    haA (((q.sequence.atlas k).system.frameOf (a.γ c)).normTraj l) hl.2
  have hg := (hgeo t ht).1
  have hD : IsUnit ((q.sequence.atlas k).system.frameOf (a.γ c)).D.det :=
    isUnit_iff_ne_zero.mpr (parent_det_ne_zero q k (a.γ c))
  have hfl := ((q.sequence.atlas k).system.frameOf (a.γ c)).frame_lift
    (by rw [hq]; exact one_ne_zero) hD (a.Q c) (a.c c) (a.u c) l t
  rw [ht₀, hq, sub_zero, div_one] at hfl
  have hc : ((q.sequence.atlas k).system.frameOf (a.γ c)).liftCenter (a.c c) (a.u c) =
      pullCenter q k a c := by
    rw [Normalization.Frame.liftCenter, ht₀, zero_div, zero_smul, sub_zero]
    rfl
  have hu : ((q.sequence.atlas k).system.frameOf (a.γ c)).liftSpeed (a.u c) =
      pullVelocity q k a c := by
    rw [Normalization.Frame.liftSpeed, hq, inv_one, one_smul]
    rfl
  rw [hc, hu] at hfl
  rw [composedFrame_eq]
  exact (congrArg norm hfl).le.trans hg

theorem pull_native (hT : (q.sequence.atlas k).T = 0)
    (hR : ∀ b, (q.sequence.atlas k).R b = p.P (q.sequence.index k) ((q.sequence.atlas k).γ b))
    (c : Fin a.C) (l : Trajectory) (hl : l ∈ originalAssignment q k a c) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |MvPolynomial.eval (x l t) (p.P (q.sequence.index k) (pullWorld q k a c))| ≤
        (q.sequence.atlas k).κ * δ (p.N (q.sequence.index k)) 0 ∧
      |MvPolynomial.eval (x l t)
          (MvPolynomial.pderiv (3 : Fin 4) (p.P (q.sequence.index k) (pullWorld q k a c)))| ≤
        (q.sequence.atlas k).κ * p.B (q.sequence.index k) (pullWorld q k a c) ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
          (MvPolynomial.pderiv (3 : Fin 4) (p.P (q.sequence.index k) (pullWorld q k a c))))| ≤
        (q.sequence.atlas k).κ * p.B (q.sequence.index k) (pullWorld q k a c) ^ 2 /
          δ (p.N (q.sequence.index k)) 0 := by
  obtain ⟨_, _, _, _, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨_, _, _, _, _, _, _, _, _, hPA, _⟩ := hPchart (a.γ c)
  have ht' : t ∈ Icc ((((q.sequence.atlas k).j (a.γ c) : ℕ) : ℝ) /
      (2 : ℝ) ^ (q.sequence.atlas k).T)
      (((((q.sequence.atlas k).j (a.γ c) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (q.sequence.atlas k).T) := by
    rw [parent_block_eq (q.sequence.atlas k) hT (a.γ c)]
    exact ht
  obtain ⟨_, h0, h1, h2⟩ := (hPA l hl.1).2.2 t ht'
  rw [hR (a.γ c)] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem pull_event_time {M₁ D₁ : ℕ} {r : ℝ} (hT : (q.sequence.atlas k).T = 0)
    (ha : a.TrueAt M₁ D₁ r) (c : Fin a.C) (z : Incidence) (hz : z ∈ originalEvent q k a c) :
    z.2 ∈ Icc (((a.j c : ℕ) : ℝ) / (2 : ℝ) ^ a.T) ((((a.j c : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T) := by
  obtain ⟨ht₀, hq⟩ := frameOf_unit (q.sequence.atlas k) hT (a.γ c)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, haF, _⟩ := ha.2.2.1 c
  obtain ⟨w, hw, rfl⟩ := hz
  show ((q.sequence.atlas k).system.frameOf (a.γ c)).t₀ +
    ((q.sequence.atlas k).system.frameOf (a.γ c)).q * w.2 ∈ _
  rw [ht₀, hq, zero_add, one_mul]
  exact (haF w hw).2.2.1

theorem pull_event_lower {M₁ D₁ : ℕ} {r : ℝ}
    (hR : ∀ b, (q.sequence.atlas k).R b = p.P (q.sequence.index k) ((q.sequence.atlas k).γ b))
    (ha : a.TrueAt M₁ D₁ r) (c : Fin a.C) (z : Incidence) (hz : z ∈ originalEvent q k a c) :
    p.B (q.sequence.index k) (pullWorld q k a c) / (q.sequence.atlas k).κ ≤
      |MvPolynomial.eval (x z.1 z.2)
        (MvPolynomial.pderiv (3 : Fin 4) (p.P (q.sequence.index k) (pullWorld q k a c)))| := by
  obtain ⟨_, _, _, _, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hPF, _⟩ := hPchart (a.γ c)
  have h := (hPF z (originalEvent_subset_parent q ha c hz)).2.2.2
  rw [hR (a.γ c)] at h
  exact h

theorem pow_add_pow_le {N : ℝ} (hN : 2 ≤ N) {M₀ M₁ M : ℕ} (hM : M₀ + M₁ + 1 ≤ M) :
    N ^ M₀ + N ^ M₁ ≤ N ^ M := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have h0 : (1 : ℝ) ≤ N ^ M₀ := one_le_pow₀ hN1
  have h1 : (1 : ℝ) ≤ N ^ M₁ := one_le_pow₀ hN1
  have e : N ^ (M₀ + M₁ + 1) = N ^ M₀ * N ^ M₁ * N := by rw [pow_add, pow_add, pow_one]
  have hle : N ^ (M₀ + M₁ + 1) ≤ N ^ M := pow_le_pow_right₀ hN1 hM
  rw [e] at hle
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ N ^ M₀),
    mul_le_mul_of_nonneg_right h0 (by linarith : (0 : ℝ) ≤ N ^ M₁)]

/-- **The pulled-back native chart.** Every child chart of a saturated normalized atlas
gives an original depth-zero chart with the native test, the original assignment and the
original event, at slack `κout ≥ κ_P κ_a`; its terminal observations are listed by
`pullList`. -/
theorem pull_chart (hp : p.Valid) (hT : (q.sequence.atlas k).T = 0)
    (hR : ∀ b, (q.sequence.atlas k).R b = p.P (q.sequence.index k) ((q.sequence.atlas k).γ b))
    {M₁ D₁ : ℕ} {r : ℝ} (ha : a.TrueAt M₁ D₁ r) (hκ : 1 ≤ a.κ)
    {κout : ℝ} (hκout : (q.sequence.atlas k).κ * a.κ ≤ κout)
    {Mout Dout : ℕ} (hM : q.M + M₁ + 1 ≤ Mout) (hD : max q.D D₁ ≤ Dout) (c : Fin a.C) :
    Chart (p.N (q.sequence.index k)) Mout Dout κout a.T ((a.j c : ℕ) : ℝ) 0
      (p.B (q.sequence.index k) (pullWorld q k a c))
      (p.E (q.sequence.index k) (pullWorld q k a c))
      (pullCenter q k a c) (pullVelocity q k a c) (composedFrame q k a c)
      (p.P (q.sequence.index k) (pullWorld q k a c))
      (originalAssignment q k a c) (originalEvent q k a c)
      (∀ z ∈ originalEvent q k a c, c ∈ pullList q k a (pullWorld q k a c)
        (obs (p.B (q.sequence.index k) (pullWorld q k a c))
          (δ (p.N (q.sequence.index k)) 1) z)) := by
  have hN : 2 ≤ p.N (q.sequence.index k) := hp.1 _
  have hN1 : (1 : ℝ) ≤ p.N (q.sequence.index k) := by linarith
  have hMle : ∀ m, m ≤ Mout →
      p.N (q.sequence.index k) ^ m ≤ p.N (q.sequence.index k) ^ Mout :=
    fun m hm => pow_le_pow_right₀ hN1 hm
  have hκP : 1 ≤ (q.sequence.atlas k).κ := q.sequence.slack_one k
  have hPκ : (q.sequence.atlas k).κ ≤ κout := by nlinarith
  have haκ : a.κ ≤ κout := by nlinarith
  have hB : 0 < p.B (q.sequence.index k) (pullWorld q k a c) := by
    obtain ⟨_, _, hs⟩ := hp.sampleProblem
    exact (hs _).scale_pos _
  have hδ : 0 < δ (p.N (q.sequence.index k)) 0 := by rw [delta_zero]; exact one_pos
  have hsum := pow_add_pow_le hN hM
  obtain ⟨_, _, _, _, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨_, _, _, _, hPdeg, hPcoef, hPAm, _, _, hPA, _, _⟩ := hPchart (a.γ c)
  obtain ⟨_, _, _, _, _, _, haAm, _, _, _, _, _⟩ := ha.2.2.1 c
  rw [hR (a.γ c)] at hPdeg hPcoef
  refine ⟨pull_det q k a ha c, (pull_center_bound q k a hp ha c).trans (hMle _ hM),
    (pull_frame_bound q k a hp ha c).trans (hMle _ hM), pull_thin q k a hT ha hκout c,
    hPdeg, fun e => (hPcoef e).trans (hMle _ (by omega)),
    CPF.NormalizedAssignments.measurableSet_originalAssignment _ _ _ hPAm _ haAm,
    measurableSet_originalEvent q ha c,
    fun i => ⟨(pull_assignment_fmt q k a ha c i).mono hsum hD,
      (pull_event_fmt q k a ha c i).mono hsum hD⟩, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨hl1, hl2, _⟩ := hPA l hl.1
    refine ⟨hl1.trans (hMle _ (by omega)), fun e => (hl2 e).trans (hMle _ (by omega)),
      fun t ht => ?_⟩
    obtain ⟨h0, h1, h2⟩ := pull_native q k a hT hR c l hl t (block_subset_unit (a.j c) ht)
    refine ⟨(pull_geometry q k a hT ha c l hl t ht).trans haκ, h0.trans ?_, h1.trans ?_,
      h2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hPκ hδ.le
    · exact mul_le_mul_of_nonneg_right hPκ hB.le
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hPκ (sq_nonneg _)) hδ.le
  · intro z hz
    refine ⟨originalEvent_subset_original q ha c hz,
      (originalEvent_subset_assignment q ha c hz).1, pull_event_time q k a hT ha c z hz, ?_⟩
    exact (div_le_div_of_nonneg_left hB.le (by linarith) hPκ).trans
      (pull_event_lower q k a hR ha c z hz)
  · intro z hz
    exact (mem_pullList q k a _ _ c).mpr ⟨rfl, z, hz, rfl⟩

/-- Separation: two pulled-back charts on one world and one block have disjoint original
assignments, by the child separation when they share a parent chart and by the parent
separation (one parent block) otherwise. -/
theorem pull_separated {M₁ D₁ : ℕ} {r : ℝ} (hT : (q.sequence.atlas k).T = 0)
    (ha : a.TrueAt M₁ D₁ r) (c c' : Fin a.C) (hcc : c ≠ c')
    (hγ : pullWorld q k a c = pullWorld q k a c') (hj : a.j c = a.j c') :
    Disjoint (originalAssignment q k a c) (originalAssignment q k a c') := by
  obtain ⟨_, _, hPsep, _, _, _⟩ := q.sequence.valid k
  by_cases hb : a.γ c = a.γ c'
  · have hd := ha.2.1 c c' hcc hb hj
    rw [Set.disjoint_left]
    rintro l ⟨_, hl⟩ ⟨_, hl'⟩
    change ((q.sequence.atlas k).system.frameOf (a.γ c)).normTraj l ∈ a.A c at hl
    change ((q.sequence.atlas k).system.frameOf (a.γ c')).normTraj l ∈ a.A c' at hl'
    rw [← hb] at hl'
    exact Set.disjoint_left.mp hd hl hl'
  · have hPj : (q.sequence.atlas k).j (a.γ c) = (q.sequence.atlas k).j (a.γ c') := by
      apply Fin.ext
      have h1 := ((q.sequence.atlas k).j (a.γ c)).isLt
      have h2 := ((q.sequence.atlas k).j (a.γ c')).isLt
      have h3 : (2 : ℕ) ^ (q.sequence.atlas k).T = 1 := by rw [hT]; rfl
      omega
    have hd := hPsep _ _ hb hγ hPj
    rw [Set.disjoint_left]
    rintro l ⟨hl, _⟩ ⟨hl', _⟩
    exact Set.disjoint_left.mp hd hl hl'

/-- The normalized own-depth observation of a pulled-back incidence is a function of its
original terminal observation. -/
theorem pull_obs {r : ℝ} (hT : (q.sequence.atlas k).T = 0) (b : Fin (q.sequence.atlas k).C)
    (hN : 1 ≤ p.N (q.sequence.index k)) (hr : r ≤ 1) (w : Incidence) :
    CPF.obs ((normalizedData q).B k b) (CPF.δ ((normalizedData q).N k) r) w =
      normObs ((q.sequence.atlas k).Q b) ((q.sequence.atlas k).c b) ((q.sequence.atlas k).u b)
        (dyadicGap (p.N (q.sequence.index k)) r)
        (obs (p.B (q.sequence.index k) ((q.sequence.atlas k).γ b))
          (δ (p.N (q.sequence.index k)) 1) ((incidenceEquiv q k b).symm w)) := by
  obtain ⟨ht₀, hq⟩ := frameOf_unit (q.sequence.atlas k) hT b
  have hew : (((q.sequence.atlas k).system.frameOf b).normTraj
      ((incidenceEquiv q k b).symm w).1,
      (((incidenceEquiv q k b).symm w).2 - ((q.sequence.atlas k).system.frameOf b).t₀) /
        ((q.sequence.atlas k).system.frameOf b).q) = w :=
    (incidenceEquiv q k b).apply_symm_apply w
  have h := obs_normalize ((q.sequence.atlas k).system.frameOf b) ht₀ hq hN hr
    (p.B (q.sequence.index k) ((q.sequence.atlas k).γ b)) ((incidenceEquiv q k b).symm w)
  rw [hew] at h
  exact h

/-- Cardinality of the pulled-back terminal lists: at most `κ_P` parent charts are listed
at an original terminal observation, and for each of them at most `κ_a` child charts are
listed at its normalized own-depth observation. -/
theorem pull_card (hp : p.Valid) (hL : p.L = 1) (hT : (q.sequence.atlas k).T = 0)
    {M₁ D₁ : ℕ} {r : ℝ} (ha : a.SaturatedAt M₁ D₁ r) (hr : r ≤ 1) (hκ : 0 ≤ a.κ)
    (γ : Fin (p.W (q.sequence.index k))) (o : Observation) :
    ((pullList q k a γ o).card : ℝ) ≤ (q.sequence.atlas k).κ * a.κ := by
  classical
  obtain ⟨old, _, _, hold, hPchart, _⟩ := q.sequence.valid k
  obtain ⟨hat, _, lstA, hlstAcard, hlstA, _⟩ := ha
  have hN1 : (1 : ℝ) ≤ p.N (q.sequence.index k) := by linarith [hp.1 (q.sequence.index k)]
  have hsub : pullList q k a γ o ⊆ (old γ o).biUnion (fun b => lstA b
      (normObs ((q.sequence.atlas k).Q b) ((q.sequence.atlas k).c b)
        ((q.sequence.atlas k).u b) (dyadicGap (p.N (q.sequence.index k)) r) o)) := by
    intro c hc
    obtain ⟨hw, z, hz, hzo⟩ := (mem_pullList q k a γ o c).mp hc
    subst hw hzo
    rw [Finset.mem_biUnion]
    refine ⟨a.γ c, ?_, ?_⟩
    · have h := (hPchart (a.γ c)).2.2.2.2.2.2.2.2.2.2.2 z
        (originalEvent_subset_parent q hat c hz)
      rw [hL] at h
      exact h
    · obtain ⟨w, hw, rfl⟩ := hz
      have h := hlstA c w hw
      rw [pull_obs q k hT (a.γ c) hN1 hr w] at h
      exact h
  calc ((pullList q k a γ o).card : ℝ)
      ≤ (((old γ o).biUnion (fun b => lstA b
          (normObs ((q.sequence.atlas k).Q b) ((q.sequence.atlas k).c b)
            ((q.sequence.atlas k).u b) (dyadicGap (p.N (q.sequence.index k)) r) o))).card :
            ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ b ∈ old γ o, ((lstA b
          (normObs ((q.sequence.atlas k).Q b) ((q.sequence.atlas k).c b)
            ((q.sequence.atlas k).u b) (dyadicGap (p.N (q.sequence.index k)) r) o)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ old γ o, a.κ := Finset.sum_le_sum fun b _ => hlstAcard b _
    _ = ((old γ o).card : ℝ) * a.κ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q.sequence.atlas k).κ * a.κ := mul_le_mul_of_nonneg_right (hold γ o) hκ

/-- The pulled-back terminal lists are measurable: they record observation images of
events in the polynomial sign format. -/
theorem pull_measurable {M₁ D₁ : ℕ} {r : ℝ} (ha : a.TrueAt M₁ D₁ r)
    (γ : Fin (p.W (q.sequence.index k))) (c : Fin a.C) :
    MeasurableSet {o | c ∈ pullList q k a γ o} := by
  by_cases hw : pullWorld q k a c = γ
  · have heq : {o | c ∈ pullList q k a γ o} =
        obs (p.B (q.sequence.index k) γ) (δ (p.N (q.sequence.index k)) 1) ''
          originalEvent q k a c := by
      ext o
      simp only [Set.mem_ofPred_eq, mem_pullList, hw, true_and]
    rw [heq]
    exact measurableSet_obs_image _ _ (fun i => pull_event_fmt q k a ha c i)
  · have heq : {o | c ∈ pullList q k a γ o} = ∅ := by
      ext o
      simp only [Set.mem_ofPred_eq, mem_pullList, hw, false_and, Set.mem_empty_iff_false]
    rw [heq]
    exact MeasurableSet.empty

theorem pull_count (hp : p.Valid) {M₁ D₁ : ℕ} {r : ℝ} (ha : a.TrueAt M₁ D₁ r) {Mout : ℕ}
    (hM : M₁ ≤ Mout) : (a.C : ℝ) ≤ p.N (q.sequence.index k) ^ Mout := by
  have hN : (1 : ℝ) ≤ p.N (q.sequence.index k) := by linarith [hp.1 (q.sequence.index k)]
  exact ha.1.trans (pow_le_pow_right₀ hN hM)

/-- **Pulled-back native systems.** For a depth-zero parent known atlas on one time block
with native tests, every saturated child atlas of the normalized problem (depth `r ≤ 1`,
slack `κ_a ≥ 1`) pulls back to original native depth-zero charts with terminal lists:
the chart count, separation, list cardinalities `≤ κ_P κ_a`, list measurability and
every chart at any slack `κout ≥ κ_P κ_a`, with formats `Mout ≥ M_P + M₁ + 1`,
`Dout ≥ max D_P D₁`. -/
theorem pullback_system (hp : p.Valid) (hL : p.L = 1) (hT : (q.sequence.atlas k).T = 0)
    (hR : ∀ b, (q.sequence.atlas k).R b = p.P (q.sequence.index k) ((q.sequence.atlas k).γ b))
    {M₁ D₁ : ℕ} {r : ℝ} (ha : a.SaturatedAt M₁ D₁ r) (hr : r ≤ 1) (hκ : 1 ≤ a.κ)
    {κout : ℝ} (hκout : (q.sequence.atlas k).κ * a.κ ≤ κout)
    {Mout Dout : ℕ} (hM : q.M + M₁ + 1 ≤ Mout) (hD : max q.D D₁ ≤ Dout) :
    (a.C : ℝ) ≤ p.N (q.sequence.index k) ^ Mout ∧
    (∀ c c', c ≠ c' → pullWorld q k a c = pullWorld q k a c' → a.j c = a.j c' →
      Disjoint (originalAssignment q k a c) (originalAssignment q k a c')) ∧
    (∀ γ o, ((pullList q k a γ o).card : ℝ) ≤ (q.sequence.atlas k).κ * a.κ) ∧
    (∀ γ c, MeasurableSet {o | c ∈ pullList q k a γ o}) ∧
    ∀ c, Chart (p.N (q.sequence.index k)) Mout Dout κout a.T ((a.j c : ℕ) : ℝ) 0
      (p.B (q.sequence.index k) (pullWorld q k a c))
      (p.E (q.sequence.index k) (pullWorld q k a c))
      (pullCenter q k a c) (pullVelocity q k a c) (composedFrame q k a c)
      (p.P (q.sequence.index k) (pullWorld q k a c))
      (originalAssignment q k a c) (originalEvent q k a c)
      (∀ z ∈ originalEvent q k a c, c ∈ pullList q k a (pullWorld q k a c)
        (obs (p.B (q.sequence.index k) (pullWorld q k a c))
          (δ (p.N (q.sequence.index k)) 1) z)) :=
  ⟨pull_count q k a hp ha.1 (by omega),
    fun c c' hcc hγ hj => pull_separated q k a hT ha.1 c c' hcc hγ hj,
    pull_card q k a hp hL hT ha hr (by linarith),
    fun γ c => pull_measurable q k a ha.1 γ c,
    pull_chart q k a hp hT hR ha.1 hκ hκout hM hD⟩

end Setting

end Submission.Obl.k4_balanced_native_packet_transport.Pullback
