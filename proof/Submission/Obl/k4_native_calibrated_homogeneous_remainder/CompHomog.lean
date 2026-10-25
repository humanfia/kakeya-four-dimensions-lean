/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompHomog.lean.
   Weakened weights to nonnegative; simp registrations are local to each module. -/
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompHomogSetup

/-!
# Multi-world homogenization

A sequence of finite world families (weights, priors, events, hidden scales) with tempered
data, native bounds and inverse-subpower mass admits a subsequence and incidence
selections on which every weighted world density of the joint observation is typical for one
common profile.  Proof: encode the worlds as one world (`CompWorlds`), apply accepted o075, and
decode through shifted hidden windows (`CompDecode`).  The world observations are at the
intrinsic dyadic thickness `dl N (ρ₀ + s) / dl N ρ₀` (equal to `dl N s` or half of it).
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_worlds (BoolFormat PriorFormat EventFormat)

/-- The intrinsic dyadic thickness of the encoded observation at depth `ρ₀ + s`. -/
noncomputable def theta (N ρ₀ s : ℝ) : ℝ := dl N (ρ₀ + s) / dl N ρ₀

theorem theta_pos (N ρ₀ s : ℝ) : 0 < theta N ρ₀ s := div_pos (dl_pos _ _) (dl_pos _ _)

theorem dl_eq_mul_theta (N ρ₀ s : ℝ) : dl N (ρ₀ + s) = dl N ρ₀ * theta N ρ₀ s := by
  unfold theta; field_simp [(dl_pos N ρ₀).ne']

theorem theta_inv_eq_two_pow {N ρ₀ s : ℝ} (hN : 1 ≤ N) (hs : 0 ≤ s) :
    ∃ m : ℕ, (theta N ρ₀ s)⁻¹ = (2 : ℝ) ^ m := by
  have hmono : ⌊ρ₀ * Real.log N / Real.log 2⌋ ≤ ⌊(ρ₀ + s) * Real.log N / Real.log 2⌋ := by
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg hN)
  refine ⟨(⌊(ρ₀ + s) * Real.log N / Real.log 2⌋ - ⌊ρ₀ * Real.log N / Real.log 2⌋).toNat, ?_⟩
  unfold theta dl
  rw [inv_div, ← zpow_natCast, Int.toNat_of_nonneg (by omega), div_eq_mul_inv,
    ← zpow_neg, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

theorem theta_le_one {N ρ₀ s : ℝ} (hN : 1 ≤ N) (hs : 0 ≤ s) : theta N ρ₀ s ≤ 1 := by
  obtain ⟨m, hm⟩ := theta_inv_eq_two_pow (ρ₀ := ρ₀) hN hs
  have h1 : (1 : ℝ) ≤ (theta N ρ₀ s)⁻¹ := by rw [hm]; exact one_le_pow₀ (by norm_num)
  have hpos := theta_pos N ρ₀ s
  calc theta N ρ₀ s = ((theta N ρ₀ s)⁻¹)⁻¹ := (inv_inv _).symm
    _ ≤ 1 := inv_le_one_of_one_le₀ h1

/-- **Multi-world homogenization.** -/
theorem multiworld_homogenization
    (N K : ℕ → ℝ) (hN : ∀ n, 2 ≤ N n) (hNt : Tendsto N atTop atTop)
    (hK : (∀ n, 1 ≤ K n) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, K n ≤ N n ^ ε)
    (W : ℕ → ℕ) (a : (n : ℕ) → Fin (W n) → ℝ) (ν : (n : ℕ) → Fin (W n) → Measure Traj)
    (E : (n : ℕ) → Fin (W n) → Set Inc) (B : (n : ℕ) → Fin (W n) → ℝ) (M D : ℕ)
    (hW : ∀ n, 0 < W n ∧ (W n : ℝ) ≤ N n ^ M)
    (ha : ∀ n c, 0 ≤ a n c) (hasum : ∀ n, ∑ c, a n c = 1)
    (hν : ∀ n c, IsProbabilityMeasure (ν n c) ∧ PriorFormat (N n ^ M) D (ν n c))
    (hE : ∀ n c, EventFormat (N n ^ M) D (E n c))
    (hB : ∀ n c, 0 < B n c ∧ B n c ≤ N n ^ M ∧ (B n c)⁻¹ ≤ N n ^ M)
    (hnat : ∀ n c, ∀ᵐ l ∂(ν n c), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4] : EuclideanSpace ℝ (Fin 2))‖ +
        ‖(WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2))‖ ≤ K n ∧
      |B n c * (l.2 2 + t * l.2 5)| ≤ N n ^ M)
    (hmass : ∀ n, ENNReal.ofReal (K n)⁻¹ ≤
      ∑ c, ENNReal.ofReal (a n c) * ((ν n c).prod volume) (E n c))
    (R U : ℝ) (hR : 0 < R) (hU : 0 < U) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (K' : ℕ → ℝ) (E' : (n : ℕ) → Fin (W (ψ n)) → Set Inc)
      (F : ℝ → ℝ → ℝ),
      ((∀ n, 1 ≤ K' n) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, K' n ≤ N (ψ n) ^ ε) ∧
      (∀ n, K (ψ n) ≤ K' n) ∧
      (∀ n c, E' n c ⊆ E (ψ n) c) ∧
      (∃ M' D' : ℕ, ∀ n c, EventFormat (N (ψ n) ^ M') D' (E' n c)) ∧
      (∀ n, ENNReal.ofReal (K' n)⁻¹ ≤
        ∑ c, ENNReal.ofReal (a (ψ n) c) * ((ν (ψ n) c).prod volume) (E' n c)) ∧
      ((∀ r r' u : ℝ, 0 ≤ r → r ≤ r' → r' ≤ ((2 * M + 5 : ℕ) : ℝ) + R → 0 ≤ u → u ≤ U →
          0 ≤ F r' u - F r u ∧ F r' u - F r u ≤ r' - r) ∧
        (∀ r u u' : ℝ, 0 ≤ r → r ≤ ((2 * M + 5 : ℕ) : ℝ) + R → 0 ≤ u → u ≤ u' → u' ≤ U →
          0 ≤ F r u' - F r u ∧ F r u' - F r u ≤ 2 * (u' - u))) ∧
      (∀ s u τ : ℝ, 0 ≤ s → s ≤ R → 0 ≤ u → u ≤ U → 0 < τ → ∃ cc : ℝ, 0 < cc ∧
        ∀ᶠ n in atTop, ∀ G : Fin (W (ψ n)) → JObs → ℝ≥0∞,
          (∀ c, Measurable (G c) ∧
            Measure.map (jobs (B (ψ n) c) (theta (N (ψ n)) ((2 * M + 5 : ℕ) : ℝ) s)
              (dl (N (ψ n)) u)) (((ν (ψ n) c).prod volume).restrict (E' n c)) =
              jref.withDensity (G c)) →
          ∑ c, ENNReal.ofReal (a (ψ n) c) * (((ν (ψ n) c).prod volume).restrict (E' n c))
            {q | ENNReal.ofReal (a (ψ n) c) * G c (jobs (B (ψ n) c)
                (theta (N (ψ n)) ((2 * M + 5 : ℕ) : ℝ) s) (dl (N (ψ n)) u) q) <
                  ENNReal.ofReal (N (ψ n) ^ (-F (((2 * M + 5 : ℕ) : ℝ) + s) u - τ)) ∨
              ENNReal.ofReal (N (ψ n) ^ (-F (((2 * M + 5 : ℕ) : ℝ) + s) u + τ)) <
                ENNReal.ofReal (a (ψ n) c) * G c (jobs (B (ψ n) c)
                (theta (N (ψ n)) ((2 * M + 5 : ℕ) : ℝ) s) (dl (N (ψ n)) u) q)} ≤
            ENNReal.ofReal (N (ψ n) ^ (-cc))) := by
  classical
  set ρ₀ : ℕ := 2 * M + 5 with hρ₀
  set σ : ℕ → ℝ := fun n => dl (N n) (ρ₀ : ℝ) with hσdef
  have hNpos : ∀ n, (0 : ℝ) < N n := fun n => by linarith [hN n]
  have hN1 : ∀ n, (1 : ℝ) ≤ N n := fun n => by linarith [hN n]
  have hσ0 : ∀ n, 0 < σ n := fun n => dl_pos _ _
  have hσ1 : ∀ n, σ n ≤ 1 := fun n => dl_le_one (hN1 n) (by positivity)
  have hσinv : ∀ n, (σ n)⁻¹ ≤ N n ^ ρ₀ := fun n => by
    have := dl_inv_le_rpow (N := N n) (r := (ρ₀ : ℝ)) (hNpos n)
    rwa [Real.rpow_natCast] at this
  have hσbig : ∀ n, σ n * N n ^ (2 * M + 4) ≤ 1 := fun n => by
    have h1 := dl_le_two_mul_rpow (N := N n) (r := (ρ₀ : ℝ)) (hNpos n)
    have h2 : (N n : ℝ) ^ (-(ρ₀ : ℝ)) * N n ^ (2 * M + 4) = (N n)⁻¹ := by
      rw [← Real.rpow_natCast (N n) (2 * M + 4), ← Real.rpow_add (hNpos n),
        ← Real.rpow_neg_one]
      congr 1; simp [hρ₀]; ring
    have h3 : 2 * (N n)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (hNpos n)]; exact hN n
    calc σ n * N n ^ (2 * M + 4) ≤ (2 * N n ^ (-(ρ₀ : ℝ))) * N n ^ (2 * M + 4) :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (hNpos n).le _)
      _ = 2 * (N n)⁻¹ := by rw [mul_assoc, h2]
      _ ≤ 1 := h3
  have hfmt := encoded_format075 N K hN hK.1 W a ν E B M D ρ₀ σ hσ0 hσ1 hσinv hσbig hW
    ha hasum hν hE hB hnat hmass
  obtain ⟨ψ, hψ, K', Es', hK', hsub, hfmt', F, hreg, -, htyp⟩ :=
    Submission.k4_joint_homogenization N K hN hNt hK _ _ hfmt ((ρ₀ : ℝ) + R) U
      (by positivity) hU
  set bb : (n : ℕ) → Fin (W n) → ℝ := fun n c => B n c * σ n with hbb
  set oo : (n : ℕ) → Fin (W n) → ℝ := fun n c => (spacing (N n) M : ℝ) * (c : ℕ) * σ n
    with hoo
  have hbb0 : ∀ n c, bb n c ≠ 0 := fun n c => (mul_pos (hB n c).1 (hσ0 n)).ne'
  let E' : (n : ℕ) → Fin (W (ψ n)) → Set Inc := fun n c =>
    encInc (W (ψ n)) c (bb (ψ n) c) (oo (ψ n) c) ⁻¹' Es' n
  have hEs'sub : ∀ n, Es' n ⊆ encEvent (hW (ψ n)).1 (bb (ψ n)) (oo (ψ n)) (E (ψ n)) :=
    fun n => (hsub n).2
  have hE'sub : ∀ n c, E' n c ⊆ E (ψ n) c := by
    intro n c q hq
    exact (encInc_mem_encEvent (hW (ψ n)).1 (E (ψ n)) c (hbb0 (ψ n) c) q).1 (hEs'sub n hq)
  obtain ⟨M', D', hfmt''⟩ := hfmt'
  have hEs'm : ∀ n, MeasurableSet (Es' n) := fun n => (hfmt'' n).2.2.1
  refine ⟨ψ, hψ, K', E', F, hK', fun n => (hsub n).1, hE'sub, ⟨max M M', max D D', ?_⟩, ?_,
    hreg, ?_⟩
  · intro n c
    have hsl : ∀ i, BoolFormat (N (ψ n) ^ M') D'
        {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ Es' n} :=
      fun i => (hfmt'' n).2.2.2.2.2.1 i
    have h := eventFormat_decoded (W := W (ψ n)) c (b := bb (ψ n) c) (o := oo (ψ n) c)
      (hE (ψ n) c) (hEs'm n) hsl (hE'sub n c)
    refine h.mono ?_
    exact max_le (pow_le_pow_right₀ (hN1 _) (le_max_left _ _))
      (pow_le_pow_right₀ (hN1 _) (le_max_right _ _))
  · intro n
    have hm := (hfmt'' n).2.2.2.2.2.2.2
    have : ∀ c : Fin (W (ψ n)), SFinite (ν (ψ n) c) := fun c =>
      have := (hν (ψ n) c).1; inferInstance
    refine hm.trans (le_of_eq ?_)
    rw [encLaw_restrict (W (ψ n)) (a (ψ n)) (bb (ψ n)) (oo (ψ n)) (ν (ψ n)) (hEs'm n)]
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_encInc _ _ _ _)
      MeasurableSet.univ, preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  · intro s u τ hs hsR hu huU hτ
    obtain ⟨cc, hcc, hev⟩ := htyp ((ρ₀ : ℝ) + s) u τ (by positivity) (by linarith) hu huU hτ
    refine ⟨cc, hcc, ?_⟩
    filter_upwards [hev] with n hn
    intro G hG
    have : ∀ c : Fin (W (ψ n)), SFinite (ν (ψ n) c) := fun c =>
      have := (hν (ψ n) c).1; inferInstance
    set θ := theta (N (ψ n)) (ρ₀ : ℝ) s with hθ
    obtain ⟨m, hm⟩ := theta_inv_eq_two_pow (ρ₀ := (ρ₀ : ℝ)) (hN1 (ψ n)) hs
    set H : ℤ := (((⌈N (ψ n) ^ M⌉₊ + 2) * 2 ^ m : ℕ) : ℤ) with hH
    have hθpos : 0 < θ := theta_pos _ _ _
    have ho : ∀ c : Fin (W (ψ n)), oo (ψ n) c =
        ((2 * H * (c : ℤ) : ℤ) : ℝ) * (σ (ψ n) * θ) := by
      intro c
      have hθm : θ * (2 : ℝ) ^ m = 1 := by
        rw [← hm]; exact mul_inv_cancel₀ hθpos.ne'
      simp only [hoo, hH, spacing]
      push_cast
      calc (2 * ((⌈N (ψ n) ^ M⌉₊ : ℝ) + 2)) * (c : ℝ) * σ (ψ n) =
          (2 * ((⌈N (ψ n) ^ M⌉₊ : ℝ) + 2)) * (c : ℝ) * σ (ψ n) * (θ * (2 : ℝ) ^ m) := by
            rw [hθm, mul_one]
        _ = _ := by ring
    have hhome : ∀ c : Fin (W (ψ n)), ∀ᵐ q ∂(((ν (ψ n) c).prod volume).restrict
        (encInc (W (ψ n)) c (B (ψ n) c * σ (ψ n)) (oo (ψ n) c) ⁻¹' Es' n)),
        jobs (B (ψ n) c) θ (dl (N (ψ n)) u) q ∈ homeWin H := by
      intro c
      have hqm : MeasurableSet (encInc (W (ψ n)) c (B (ψ n) c * σ (ψ n)) (oo (ψ n) c) ⁻¹' Es' n) :=
        (measurable_encInc _ _ _ _) (hEs'm n)
      have hfst : ∀ᵐ q ∂((ν (ψ n) c).prod (volume : Measure ℝ)), ∀ t ∈ Icc (0 : ℝ) 1,
          |B (ψ n) c * (q.1.2 2 + t * q.1.2 5)| ≤ N (ψ n) ^ M := by
        have := (hν (ψ n) c).1
        have hq := Measure.QuasiMeasurePreserving.ae
          (Measure.quasiMeasurePreserving_fst (μ := ν (ψ n) c) (ν := (volume : Measure ℝ)))
          (p := fun l : Traj => ∀ t ∈ Icc (0 : ℝ) 1,
            |B (ψ n) c * (l.2 2 + t * l.2 5)| ≤ N (ψ n) ^ M)
          ((hnat (ψ n) c).mono fun l hl t ht => (hl t ht).2)
        exact hq
      have hrestr := ae_restrict_of_ae (s := encInc (W (ψ n)) c (B (ψ n) c * σ (ψ n))
        (oo (ψ n) c) ⁻¹' Es' n) hfst
      filter_upwards [hrestr, ae_restrict_mem hqm] with q hq hqS
      have hqE : q ∈ E (ψ n) c := hE'sub n c hqS
      have ht : q.2 ∈ Icc (0 : ℝ) 1 := ((hE (ψ n) c).2.1 hqE).2
      have hbw := hq q.2 ht
      apply jobs_mem_homeWin hθpos
      have hθ1 : θ ≤ 1 := theta_le_one (hN1 _) hs
      have hceil : N (ψ n) ^ M ≤ (⌈N (ψ n) ^ M⌉₊ : ℝ) := Nat.le_ceil _
      have hHθ : (H : ℝ) * θ = (⌈N (ψ n) ^ M⌉₊ : ℝ) + 2 := by
        have hθm : θ * (2 : ℝ) ^ m = 1 := by rw [← hm]; exact mul_inv_cancel₀ hθpos.ne'
        simp only [hH]; push_cast
        calc ((⌈N (ψ n) ^ M⌉₊ : ℝ) + 2) * (2 : ℝ) ^ m * θ =
            ((⌈N (ψ n) ^ M⌉₊ : ℝ) + 2) * (θ * (2 : ℝ) ^ m) := by ring
          _ = _ := by rw [hθm, mul_one]
      rw [hHθ]
      linarith
    obtain ⟨Gs, hGsm, hGslaw, hGsae⟩ := decode_density (W (ψ n)) (a (ψ n)) (B (ψ n))
      (oo (ψ n)) (ν (ψ n)) (hEs'm n) (hσ0 (ψ n)) hθpos H ho G (fun c => (hG c).1)
      (fun c => (hG c).2) hhome
    have hlaw : Measure.map (Submission.Obl.k4_joint_homogenization.Observation (N (ψ n))
        ((ρ₀ : ℝ) + s) u) (((encPrior (W (ψ n)) (a (ψ n)) (fun c => B (ψ n) c * σ (ψ n))
          (oo (ψ n)) (ν (ψ n))).prod volume).restrict (Es' n)) = jref.withDensity Gs := by
      rw [observation075_eq, dl_eq_mul_theta]
      exact hGslaw
    have h1 := hn Gs hGsm hlaw
    refine le_trans (le_of_eq ?_) h1
    set P : ℝ≥0∞ → Prop := fun x =>
      x < ENNReal.ofReal (N (ψ n) ^ (-F ((ρ₀ : ℝ) + s) u - τ)) ∨
        ENNReal.ofReal (N (ψ n) ^ (-F ((ρ₀ : ℝ) + s) u + τ)) < x with hP
    have hPm : MeasurableSet {x : ℝ≥0∞ | P x} :=
      (measurableSet_lt measurable_id measurable_const).union
        (measurableSet_lt measurable_const measurable_id)
    have hSm : MeasurableSet {p : Inc | P (Gs (jobs 1 (dl (N (ψ n)) ((ρ₀ : ℝ) + s))
        (dl (N (ψ n)) u) p))} :=
      (hGsm.comp (measurable_jobs _ _ _)) hPm
    rw [← observation075_eq] at hSm
    show _ = (((encPrior (W (ψ n)) (a (ψ n)) (fun c => B (ψ n) c * σ (ψ n)) (oo (ψ n))
      (ν (ψ n))).prod volume).restrict (Es' n))
        {p | P (Gs (Submission.Obl.k4_joint_homogenization.Observation (N (ψ n))
          ((ρ₀ : ℝ) + s) u p))}
    rw [encLaw_restrict (W (ψ n)) (a (ψ n)) _ (oo (ψ n)) (ν (ψ n)) (hEs'm n),
      Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_encInc _ _ _ _) hSm]
    congr 1
    apply measure_congr
    filter_upwards [hGsae c] with q hq
    simp only [mem_preimage, eq_iff_iff, mem_ofPred_eq]
    rw [observation075_eq, dl_eq_mul_theta, hq]

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
