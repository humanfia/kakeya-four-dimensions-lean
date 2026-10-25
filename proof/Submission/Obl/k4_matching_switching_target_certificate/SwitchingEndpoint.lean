-- Adapted from this LOT tree, o040, session x0118, Submission/Obl/k4_matching_refinement_exponent/SwitchingEndpoint.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.NormalizedArms

/-!
# The endpoint of a switching path, from record data

The deterministic part of the switching experiment (paper, `a02:controlled-jets` to
`a02:endpoint-polynomial`). On a coarse interval `[lo, hi]` of length comparable to
`N^(-r(a))` in an active `m`-piece with margin `γ`, consider arms `φ 0, ..., φ m`, times
`t 0, ..., t (m + 1)` in the interval, with

* every arm a coarse neighbor of the reference jets `c` at the center,
* consecutive arms close at a fine level `f` near each switch time,
* controls `u p` approximating the normalized `m`-th derivatives at the center.

After normalization (`normArm` with reference polynomial `taylorPoly J c`), the final
low jets minus the free evolution of the first arm are within an explicit error of the
frozen endpoint polynomial at (final time, switch times).
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

theorem switching_endpoint {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ}
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hk₀J : k₀ ≤ J) (hβk₀ : β k₀ = 0)
    {m : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J)
    {N ε K γ κ e₀ : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K) (he₀ : 0 ≤ e₀)
    {a f : ℝ} (ha : 0 ≤ a) (hf : 0 ≤ f)
    (hact : jetRadius J β a = (a - β m) / (m : ℝ))
    (hγ1 : γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a - jetAccuracy (jetRadius J β) m a)
    (hγ2 : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) a + (i : ℝ) * jetRadius J β a - β m)
    (hκ : ∀ j : ℕ, j < m →
      jetAccuracy (jetRadius J β) j a - jetAccuracy (jetRadius J β) j f ≤ -κ)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hlen : N ^ (-jetRadius J β a) / 2 ≤ hi - lo) (hlen' : hi - lo ≤ N ^ (-jetRadius J β a))
    (φ : ℕ → ℝ → ℝ)
    (hφ : ∀ p, p ≤ m → ContDiffOn ℝ (J + 1 : ℕ) (φ p) (Ioo (-1 : ℝ) 2))
    (hφB : ∀ p, p ≤ m → ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) (φ p) t| ≤ N ^ ε)
    (c : ℕ → ℝ)
    (hc : ∀ p, p ≤ m → ∀ i, i ≤ J → |iteratedDeriv i (φ p) ((lo + hi) / 2) - c i| ≤
      K * N ^ (-jetAccuracy (jetRadius J β) i a))
    (t : ℕ → ℝ) (ht : ∀ p, p ≤ m + 1 → t p ∈ Icc lo hi)
    (cf : ℕ → ℝ)
    (hcf : ∀ p, 1 ≤ p → p ≤ m → cf p ∈ Icc (0 : ℝ) 1 ∧
      |t p - cf p| ≤ N ^ (-jetRadius J β f) ∧
      ∀ i, i ≤ J → |iteratedDeriv i (φ p) (cf p) - iteratedDeriv i (φ (p - 1)) (cf p)| ≤
        K * N ^ (-jetAccuracy (jetRadius J β) i f))
    (u : ℕ → ℝ)
    (hu : ∀ p, p ≤ m →
      |N ^ β m * (iteratedDeriv m (φ p) ((lo + hi) / 2) - c m) - u p| ≤ e₀)
    (j : Fin m) :
    |(iteratedDeriv (m - 1 - (j : ℕ))
          (normArm (φ m) (taylorPoly J c ((lo + hi) / 2)) ((lo + hi) / 2) (hi - lo)
            (N ^ β m) m) ((t (m + 1) - (lo + hi) / 2) / (hi - lo))
        - freeJet m (fun i => iteratedDeriv i
            (normArm (φ 0) (taylorPoly J c ((lo + hi) / 2)) ((lo + hi) / 2) (hi - lo)
              (N ^ β m) m) ((t 0 - (lo + hi) / 2) / (hi - lo)))
          ((t 0 - (lo + hi) / 2) / (hi - lo)) ((t (m + 1) - (lo + hi) / 2) / (hi - lo)) j)
      - (endpointMap m (fun p => u p) ((t 0 - (lo + hi) / 2) / (hi - lo))
          ((t (m + 1) - (lo + hi) / 2) / (hi - lo),
            fun p => (t ((p : ℕ) + 1) - (lo + hi) / 2) / (hi - lo))).2 j|
      ≤ 9 ^ (m + 1) * (8 * (2 ^ m * (3 * K + 2 * N ^ ε) * N ^ (-κ)) +
          2 ^ m * (e₀ + (3 * K + N ^ ε) * N ^ (-γ))) := by
  have hN0 : 0 < N := by linarith
  set ta := (lo + hi) / 2 with hta_def
  set lam := hi - lo with hlam_def
  have hlam0 : 0 < lam := (by positivity : (0 : ℝ) < N ^ (-jetRadius J β a) / 2).trans_le hlen
  have hlo_hi : lo ≤ hi := by linarith
  have hta : ta ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set T := taylorPoly J c ta with hT_def
  set W := N ^ β m with hW_def
  set ψ : ℕ → ℝ → ℝ := fun p => normArm (φ p) T ta lam W m with hψ_def
  set s : ℕ → ℝ := fun p => (t p - ta) / lam with hs_def
  have hts : ∀ p, ta + lam * s p = t p := by
    intro p; simp only [hs_def]; field_simp; ring
  -- the normalized interval
  set V := (fun x : ℝ => ta + lam * x) ⁻¹' Ioo (-1 : ℝ) 2 with hV_def
  have hVo : IsOpen V := isOpen_Ioo.preimage (by fun_prop)
  have hmem : ∀ x ∈ Icc (-(1:ℝ) / 2) (1 / 2), ta + lam * x ∈ Icc lo hi := by
    intro x hx
    have h1 : lam * (-(1:ℝ) / 2) ≤ lam * x := mul_le_mul_of_nonneg_left hx.1 hlam0.le
    have h2 : lam * x ≤ lam * (1 / 2) := mul_le_mul_of_nonneg_left hx.2 hlam0.le
    constructor <;> nlinarith
  have hIV : Icc (-(1:ℝ) / 2) (1 / 2) ⊆ V := fun x hx =>
    let h := hmem x hx
    ⟨by linarith [h.1], by linarith [h.2]⟩
  have hlh : (1:ℝ) / 2 - (-(1:ℝ) / 2) ≤ 2 := by norm_num
  have hsI : ∀ p, p ≤ m + 1 → s p ∈ Icc (-(1:ℝ) / 2) (1 / 2) := by
    intro p hp
    have h := ht p hp
    simp only [hs_def, mem_Icc]
    constructor
    · rw [le_div_iff₀ hlam0]; linarith [h.1]
    · rw [div_le_iff₀ hlam0]; linarith [h.2]
  have hTsmooth : ContDiff ℝ ⊤ T := contDiff_taylorPoly J c ta
  have hlm : jetAccuracy (jetRadius J β) m a = β m :=
    jetAccuracy_active_order hJ β ha hm hmJ hact
  -- smoothness of the normalized arms
  have hψs : ∀ p, p ≤ m → ContDiffOn ℝ m (ψ p) V := fun p hp =>
    (contDiffOn_normArm (hφ p hp) hTsmooth ta lam W m).of_le (by exact_mod_cast (by omega : m ≤ J + 1))
  -- control
  set e := e₀ + (3 * K + N ^ ε) * N ^ (-γ) with he_def
  have he : 0 ≤ e := by positivity
  have hctrl : ∀ p, p ≤ m → ∀ x ∈ Icc (-(1:ℝ) / 2) (1 / 2),
      |iteratedDeriv m (ψ p) x - u p| ≤ e := by
    intro p hp x hx
    have hxm := hmem x hx
    have hx01 : ta + lam * x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hxm.1], by linarith [hxm.2]⟩
    have hdist : |lam * x| ≤ N ^ (-jetRadius J β a) := by
      rw [abs_mul, abs_of_pos hlam0]
      have : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      nlinarith
    have h1 := normArm_control hJ hmJ hN hK (hφ p hp) (hφB p hp) hlam0.ne' ha hta
      (hc p hp) hlm hγ1 hγ2 hx01 hdist
    calc |iteratedDeriv m (ψ p) x - u p|
        ≤ |iteratedDeriv m (ψ p) x - W * (iteratedDeriv m (φ p) ta - c m)| +
          |W * (iteratedDeriv m (φ p) ta - c m) - u p| := abs_sub_le _ _ _
      _ ≤ (3 * K + N ^ ε) * N ^ (-γ) + e₀ := add_le_add h1 (hu p hp)
      _ = e := by rw [he_def]; ring
  -- jumps
  set δ := 2 ^ m * (3 * K + 2 * N ^ ε) * N ^ (-κ) with hδ_def
  have hδ : 0 ≤ δ := by positivity
  have hjump : ∀ p, p < m → ∀ j, j < m →
      |iteratedDeriv j (ψ (p + 1)) (s (p + 1)) - iteratedDeriv j (ψ p) (s (p + 1))| ≤ δ := by
    intro p hp j hj
    obtain ⟨hcf1, hcf2, hcf3⟩ := hcf (p + 1) (by omega) (by omega)
    have hsp := hsI (p + 1) (by omega)
    have hU : IsOpen (Ioo (-1 : ℝ) 2) := isOpen_Ioo
    have htp : t (p + 1) ∈ Icc (0 : ℝ) 1 := by
      have := ht (p + 1) (by omega); exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have htpU : ta + lam * s (p + 1) ∈ Ioo (-1 : ℝ) 2 := by
      rw [hts]; exact ⟨by linarith [htp.1], by linarith [htp.2]⟩
    rw [normArm_gap hU (hφ (p + 1) (by omega)) (hφ p (by omega)) hTsmooth ta lam W m
      (by omega : j ≤ J + 1) htpU, hts, abs_mul]
    have hgap := gap_translate_at_level hJ hk₀ hk₀J hβk₀ hN hK (hφ (p + 1) (by omega))
      (hφ p (by omega)) (hφB (p + 1) (by omega)) (hφB p (by omega)) hf hcf1 htp
      (by simpa using hcf3) hcf2 (by omega : j ≤ J)
    have hscale := scale_factor_le (N := N) (lam := lam) (βm := β m)
      (ra := jetRadius J β a) (lja := jetAccuracy (jetRadius J β) j a) hN hlen hj.le
      (jetAccuracy_eq_beta_add hJ β ha hm hmJ hj.le hact)
    have hpos : 0 ≤ W * (lam ^ m)⁻¹ * lam ^ j := by positivity
    rw [abs_of_nonneg hpos]
    calc W * (lam ^ m)⁻¹ * lam ^ j *
          |iteratedDeriv j (φ (p + 1)) (t (p + 1)) - iteratedDeriv j (φ p) (t (p + 1))|
        ≤ (2 ^ m * N ^ jetAccuracy (jetRadius J β) j a) *
          ((3 * K + 2 * N ^ ε) * N ^ (-jetAccuracy (jetRadius J β) j f)) :=
          mul_le_mul hscale hgap (abs_nonneg _) (by positivity)
      _ = 2 ^ m * (3 * K + 2 * N ^ ε) *
          N ^ (jetAccuracy (jetRadius J β) j a - jetAccuracy (jetRadius J β) j f) := by
          rw [sub_eq_add_neg, Real.rpow_add hN0]; ring
      _ ≤ δ := by
          rw [hδ_def]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (hκ j hj))
            (by positivity)
  have hmain := alternating_path_endpoint hVo hIV hlh ψ u s he hδ hψs hctrl hsI hjump j
  simpa [hψ_def, hs_def] using hmain

end Submission.Obl.k4_matching_switching_target_certificate

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- The jet of order `i` reconstructed from the left ends of the floor bins of `φ` at
the center `tc` of a level-`c` interval, evaluated at time `t`. It depends on `φ` only
through these bins (a record). -/
noncomputable def binJet (J : ℕ) (β : ℕ → ℝ) (N c : ℝ) (bins : ℕ → ℤ) (tc : ℝ) (i : ℕ)
    (t : ℝ) : ℝ :=
  ∑ i' ∈ Finset.range (J + 1 - i),
    (bins (i + i') : ℝ) / N ^ jetAccuracy (jetRadius J β) (i + i') c * (t - tc) ^ i' /
      (i'.factorial : ℝ)

lemma continuous_binJet (J : ℕ) (β : ℕ → ℝ) (N c : ℝ) (bins : ℕ → ℤ) (tc : ℝ) (i : ℕ) :
    Continuous (binJet J β N c bins tc i) := by
  unfold binJet; fun_prop

/-- **Final target.** The normalized jets of the last arm at the final time lie within
`2^m (3 + 2N^ε) N^(l_i(a) - l_i(c))` of the normalized bin reconstruction from its own
level-`c` record. -/
theorem final_jet_near_binJet {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ}
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hk₀J : k₀ ≤ J) (hβk₀ : β k₀ = 0)
    {m : ℕ} (hm : 1 ≤ m) (hmJ : m ≤ J)
    {N ε : ℝ} (hN : 1 ≤ N) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hact : jetRadius J β a = (a - β m) / (m : ℝ))
    {lo hi : ℝ} (hlen : N ^ (-jetRadius J β a) / 2 ≤ hi - lo)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ (J + 1 : ℕ) φ (Ioo (-1 : ℝ) 2))
    (hφB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) φ t| ≤ N ^ ε)
    (cref : ℕ → ℝ) {tc tf : ℝ} (htc : tc ∈ Icc (0 : ℝ) 1) (htf : tf ∈ Icc (0 : ℝ) 1)
    (hdist : |tf - tc| ≤ N ^ (-jetRadius J β c)) {i : ℕ} (him : i < m) :
    |iteratedDeriv i (normArm φ (taylorPoly J cref ((lo + hi) / 2)) ((lo + hi) / 2) (hi - lo)
          (N ^ β m) m) ((tf - (lo + hi) / 2) / (hi - lo)) -
        N ^ β m * ((hi - lo) ^ m)⁻¹ * (hi - lo) ^ i *
          (binJet J β N c (fun i' => Int.floor (N ^ jetAccuracy (jetRadius J β) i' c *
              iteratedDeriv i' φ tc)) tc i tf -
            iteratedDeriv i (taylorPoly J cref ((lo + hi) / 2)) tf)| ≤
      2 ^ m * (3 + 2 * N ^ ε) *
        N ^ (jetAccuracy (jetRadius J β) i a - jetAccuracy (jetRadius J β) i c) := by
  have hN0 : 0 < N := by linarith
  set ta := (lo + hi) / 2
  set lam := hi - lo with hlam_def
  have hlam0 : 0 < lam := (by positivity : (0 : ℝ) < N ^ (-jetRadius J β a) / 2).trans_le hlen
  have hts : ta + lam * ((tf - ta) / lam) = tf := by field_simp; ring
  have htfU : ta + lam * ((tf - ta) / lam) ∈ Ioo (-1 : ℝ) 2 := by
    rw [hts]; exact ⟨by linarith [htf.1], by linarith [htf.2]⟩
  rw [iteratedDeriv_normArm isOpen_Ioo hφ (contDiff_taylorPoly J cref ta) ta lam (N ^ β m) m
    (by omega : i ≤ J + 1) htfU, hts, ← mul_sub, abs_mul]
  have hrec := floor_reconstruct_at_level hJ hk₀ hk₀J hβk₀ hN hφ hφB hc htc htf hdist
    (by omega : i ≤ J)
  have hscale := scale_factor_le (N := N) (lam := lam) (βm := β m)
    (ra := jetRadius J β a) (lja := jetAccuracy (jetRadius J β) i a) hN hlen him.le
    (jetAccuracy_eq_beta_add hJ β ha hm hmJ him.le hact)
  have hpos : 0 ≤ N ^ β m * (lam ^ m)⁻¹ * lam ^ i := by positivity
  rw [abs_of_nonneg hpos]
  have hsub : iteratedDeriv i φ tf - iteratedDeriv i (taylorPoly J cref ta) tf -
      (binJet J β N c (fun i' => Int.floor (N ^ jetAccuracy (jetRadius J β) i' c *
          iteratedDeriv i' φ tc)) tc i tf - iteratedDeriv i (taylorPoly J cref ta) tf) =
      iteratedDeriv i φ tf - ∑ i' ∈ Finset.range (J + 1 - i),
        (Int.floor (N ^ jetAccuracy (jetRadius J β) (i + i') c *
            iteratedDeriv (i + i') φ tc) : ℝ) / N ^ jetAccuracy (jetRadius J β) (i + i') c *
          (tf - tc) ^ i' / (i'.factorial : ℝ) := by
    simp only [binJet]; ring
  rw [hsub]
  calc N ^ β m * (lam ^ m)⁻¹ * lam ^ i * |iteratedDeriv i φ tf - _|
      ≤ (2 ^ m * N ^ jetAccuracy (jetRadius J β) i a) *
        ((3 + 2 * N ^ ε) * N ^ (-jetAccuracy (jetRadius J β) i c)) :=
        mul_le_mul hscale hrec (abs_nonneg _) (by positivity)
    _ = 2 ^ m * (3 + 2 * N ^ ε) *
        N ^ (jetAccuracy (jetRadius J β) i a - jetAccuracy (jetRadius J β) i c) := by
        rw [sub_eq_add_neg, Real.rpow_add hN0]; ring

end Submission.Obl.k4_matching_switching_target_certificate
