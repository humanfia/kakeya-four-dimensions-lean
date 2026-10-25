-- Adapted from this LOT tree, o070/x0236 commit 12c7648, Target.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Endpoint
import Submission.Obl.k4_matching_switching_target_certificate.Tubes

/-!
# The target tube of a final record

`ptube … a y κ` is the tube (x0118's `tube`) over the normalized level-`(k+1)` interval of
`y`, with centers `tcen … a y κ` and widths `Wd * N^(-((j+1)/m)/q)` in the reverse jet
order. It depends on `y ∈ S` only through its record `F (k+1) y` (`ptube_congr`).

`Det.path_endpoint_mem`: the endpoint polynomial of every alternating path from `a` with
`e₀`-accurate controls lies in the tube of its final event and final colour, with
`Wd = pathWidth m N ε E₀` when `e₀ ≤ E₀ N^(-1/q)`. The time set has volume at most
`2 N^(-(1/m)/q)` (`volume_tset_le`), so these tubes have exactly the shape of
`TargetGeometry.volume_step_target_le`.

Written for o070 by session x0236.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory

variable {n₁ n₂ : ℕ}

/-- The normalized level-`(k+1)` interval of `y`, relative to the start `a`. -/
def tset (h : ℕ → ℕ) (k : ℕ) (a y : (Fin n₁ × Fin n₂) × ℝ) : Set ℝ :=
  {σ | dcenter h k a.2 + lamk h k * σ ∈
    Icc (dleft h (k + 1) y.2) (dleft h (k + 1) y.2 + ((2 : ℝ) ^ h (k + 1))⁻¹)}

/-- The constant of the tube widths. -/
noncomputable def pathWidth (m : ℕ) (N ε E₀ : ℝ) : ℝ :=
  9 ^ (m + 1) * (8 * (2 ^ m * (3 * (((m : ℝ) + 1) * (5 * N ^ ε + 1)) + 2 * N ^ ε)) +
      2 ^ m * (E₀ + (3 * (((m : ℝ) + 1) * (5 * N ^ ε + 1)) + N ^ ε))) +
    2 ^ m * (3 + 2 * N ^ ε) + 3 * (2 ^ m * (3 * (5 * N ^ ε + 1) + 2 * N ^ ε))

/-- The widths of the target tubes, in reverse jet order. -/
noncomputable def twidth (m q : ℕ) (N W : ℝ) (j : Fin m) : ℝ :=
  W * N ^ (-((((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ)))

/-- The target tube of the final event `y` and final colour `κ`, relative to the start `a`. -/
def ptube (J : ℕ) (β : ℕ → ℝ) (q k m : ℕ) (N W : ℝ) (f₁ : Fin n₁ → ℝ → ℝ)
    (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) (a y : (Fin n₁ × Fin n₂) × ℝ) (κ : Bool) :
    Set (ℝ × (Fin m → ℝ)) :=
  tube (tset h k a y) (tcen J β q k m N f₁ f₂ h a y κ) (twidth m q N W)

lemma measurableSet_tset (h : ℕ → ℕ) (k : ℕ) (a y : (Fin n₁ × Fin n₂) × ℝ) :
    MeasurableSet (tset h k a y) :=
  measurableSet_Icc.preimage (by fun_prop : Measurable fun σ : ℝ => dcenter h k a.2 + lamk h k * σ)

lemma measurableSet_ptube (J : ℕ) (β : ℕ → ℝ) (q k m : ℕ) (N W : ℝ) (f₁ : Fin n₁ → ℝ → ℝ)
    (f₂ : Fin n₂ → ℝ → ℝ) (h : ℕ → ℕ) (a y : (Fin n₁ × Fin n₂) × ℝ) (κ : Bool) :
    MeasurableSet (ptube J β q k m N W f₁ f₂ h a y κ) :=
  measurableSet_tube _ (measurableSet_tset h k a y)
    (fun j => (continuous_tcen J β q k m N f₁ f₂ h a y κ j).measurable)

/-- The normalized child interval has length `2^(h k - h (k+1))`. -/
lemma volume_tset (h : ℕ → ℕ) (k : ℕ) (a y : (Fin n₁ × Fin n₂) × ℝ) :
    volume (tset h k a y) = ENNReal.ofReal (((2 : ℝ) ^ h (k + 1))⁻¹ / lamk h k) := by
  have hl := lamk_pos h k
  have hset : tset h k a y = Icc ((dleft h (k + 1) y.2 - dcenter h k a.2) / lamk h k)
      ((dleft h (k + 1) y.2 + ((2 : ℝ) ^ h (k + 1))⁻¹ - dcenter h k a.2) / lamk h k) := by
    ext σ
    simp only [tset, Set.mem_ofPred_eq, mem_Icc]
    rw [div_le_iff₀ hl, le_div_iff₀ hl]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset, Real.volume_Icc]
  congr 1
  field_simp
  ring

/-- Records at level `k+1` determine the time set and the center of the target tube. -/
lemma tset_congr {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
    {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (H : Det J β γ q k m z N ε f₁ f₂ h F S) (a : (Fin n₁ × Fin n₂) × ℝ)
    {y y' : (Fin n₁ × Fin n₂) × ℝ} (hy : y ∈ S) (hy' : y' ∈ S)
    (hyy : F (k + 1) y = F (k + 1) y') : tset h k a y = tset h k a y' := by
  have hk1 : k + 1 ≤ q := by have := H.hkq; omega
  have hfl := H.rec_floor hk1 hy hy' hyy le_rfl
  unfold tset
  rw [dleft_congr hfl]

lemma tcen_congr {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
    {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (H : Det J β γ q k m z N ε f₁ f₂ h F S) (a : (Fin n₁ × Fin n₂) × ℝ)
    {y y' : (Fin n₁ × Fin n₂) × ℝ} (hy : y ∈ S) (hy' : y' ∈ S)
    (hyy : F (k + 1) y = F (k + 1) y') (κ : Bool) :
    tcen J β q k m N f₁ f₂ h a y κ = tcen J β q k m N f₁ f₂ h a y' κ := by
  have hk1 : k + 1 ≤ q := by have := H.hkq; omega
  have hfl := H.rec_floor hk1 hy hy' hyy le_rfl
  have hc : dcenter h (k + 1) y.2 = dcenter h (k + 1) y'.2 := dcenter_congr hfl
  have hb : ∀ (i : ℕ) (t : ℝ), binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ))
      (finBins J β q k N f₁ f₂ h y κ) (dcenter h (k + 1) y.2) i t =
      binJet J β N (((k + 1 : ℕ) : ℝ) / (q : ℝ))
      (finBins J β q k N f₁ f₂ h y' κ) (dcenter h (k + 1) y'.2) i t := by
    intro i t
    unfold binJet
    rw [hc]
    refine Finset.sum_congr rfl fun i' hi' => ?_
    have hle : i + i' ≤ J := by have := Finset.mem_range.mp hi'; omega
    have := H.rec_bin hk1 hy hy' hyy le_rfl hle κ
    unfold finBins
    unfold Det.bin at this
    rw [this]
  funext j σ
  unfold tcen
  rw [hb]


namespace Det

variable {J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

/-- The normalized child interval has volume at most `2 N^(-(1/m)/q)`. -/
lemma volume_tset_le (a y : (Fin n₁ × Fin n₂) × ℝ) :
    volume (tset h k a y) ≤ ENNReal.ofReal (2 * N ^ (-((1 / (m : ℝ)) / (q : ℝ)))) := by
  rw [volume_tset]
  refine ENNReal.ofReal_le_ofReal ?_
  have hk1 : k + 1 ≤ q := by have := H.hkq; omega
  have h1 := (H.hdepth k H.k_le_q).2
  have h2 := (H.hdepth (k + 1) hk1).1
  have hra := H.active_at H.hzk (Nat.le_add_right k (6 * (J + 1)))
  have hrc := H.active_at (v := k + 1) (H.hzk.trans (Nat.le_succ k)) (by omega)
  have hN0 := H.N_pos
  have hm : (0 : ℝ) < m := by exact_mod_cast H.hm
  have hq := H.q_pos
  have hdiff : jetRadius J β (((k + 1 : ℕ) : ℝ) / q) - jetRadius J β ((k : ℝ) / q) =
      (1 / (m : ℝ)) / (q : ℝ) := by
    rw [hra, hrc]; push_cast; field_simp; ring
  have hpos1 : (0 : ℝ) < (2 : ℝ) ^ h (k + 1) := by positivity
  have hpos0 : (0 : ℝ) < (2 : ℝ) ^ h k := by positivity
  rw [lamk, div_inv_eq_mul, inv_mul_eq_div, div_le_iff₀ hpos1]
  calc (2 : ℝ) ^ h k ≤ 2 * N ^ jetRadius J β ((k : ℝ) / q) := h1
    _ = 2 * N ^ (-((1 / (m : ℝ)) / (q : ℝ))) * N ^ jetRadius J β (((k + 1 : ℕ) : ℝ) / q) := by
        rw [mul_assoc, ← Real.rpow_add hN0, ← hdiff]; ring_nf
    _ ≤ 2 * N ^ (-((1 / (m : ℝ)) / (q : ℝ))) * (2 : ℝ) ^ h (k + 1) := by
        gcongr

/-- **The endpoint of an alternating path lies in the target tube of its final event.** -/
theorem path_endpoint_mem {E W : ℕ → (Fin n₁ × Fin n₂) × ℝ} {κ : ℕ → Bool}
    (hP : IsPath F S f₁ f₂ h k (6 * (J + 1)) m E W κ) (u : ℕ → ℝ) {e₀ E₀ : ℝ} (he₀ : 0 ≤ e₀)
    (hE₀ : e₀ ≤ E₀ * N ^ (-(1 / (q : ℝ))))
    (hu : ∀ p, p ≤ m → |N ^ β m * (iteratedDeriv m (arm f₁ f₂ (κ p) (W p))
        (dcenter h k (E 0).2) - cref f₁ h k (E 0) m) - u p| ≤ e₀) :
    endpointMap m (fun p => u p) (ntime h k (E 0) (E 0).2)
        (ntime h k (E 0) (E (m + 1)).2, fun p => ntime h k (E 0) (E ((p : ℕ) + 1)).2) ∈
      ptube J β q k m N (pathWidth m N ε E₀) f₁ f₂ h (E 0) (E (m + 1)) (κ m) := by
  refine ⟨?_, fun j => ?_⟩
  · -- the final time lies in its own child interval
    change dcenter h k (E 0).2 + lamk h k * ntime h k (E 0) (E (m + 1)).2 ∈
      Icc (dleft h (k + 1) (E (m + 1)).2) (dleft h (k + 1) (E (m + 1)).2 +
        ((2 : ℝ) ^ h (k + 1))⁻¹)
    have hl := lamk_pos h k
    have : dcenter h k (E 0).2 + lamk h k * ntime h k (E 0) (E (m + 1)).2 = (E (m + 1)).2 := by
      unfold ntime; field_simp; ring
    rw [this]
    exact ⟨dleft_le h _ _, (lt_dleft_add h _ _).le⟩
  · have hb := H.path_endpoint hP u he₀ hu j
    refine hb.trans ?_
    have hN0 := H.N_pos
    have hNε := H.Npow_pos ε
    have hq := H.q_pos
    have hm : (0 : ℝ) < m := by exact_mod_cast H.hm
    set x : ℝ := (((j : ℕ) : ℝ) + 1) / (m : ℝ) / (q : ℝ) with hx
    have hx1 : x ≤ 1 / (q : ℝ) := by
      rw [hx, div_le_div_iff_of_pos_right hq, div_le_one hm]
      exact_mod_cast j.isLt
    have hx0 : 0 ≤ x := by positivity
    have h6 : N ^ (-(6 / (q : ℝ))) ≤ N ^ (-x) := by
      refine Real.rpow_le_rpow_of_exponent_le H.hN ?_
      have : 1 / (q : ℝ) ≤ 6 / q := by gcongr; norm_num
      linarith
    have hγ : N ^ (-γ) ≤ N ^ (-x) := by
      refine Real.rpow_le_rpow_of_exponent_le H.hN ?_
      have h4 : 4 / (q : ℝ) ≤ γ := by rw [div_le_iff₀ hq]; linarith [H.hγq]
      have : 1 / (q : ℝ) ≤ 4 / q := by gcongr; norm_num
      linarith
    have he : e₀ ≤ E₀ * N ^ (-x) := by
      refine hE₀.trans ?_
      have hE0 : 0 ≤ E₀ := by
        by_contra hneg
        push Not at hneg
        have : E₀ * N ^ (-(1 / (q : ℝ))) < 0 := mul_neg_of_neg_of_pos hneg (H.Npow_pos _)
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le H.hN (by linarith)) hE0
    have hNx := H.Npow_pos (-x)
    unfold twidth pathWidth
    rw [← hx]
    set K := ((m : ℝ) + 1) * (5 * N ^ ε + 1)
    have hK : 0 ≤ K := by positivity
    have hA : 0 ≤ 2 ^ m * (3 * K + 2 * N ^ ε) := by positivity
    have hB : 0 ≤ 3 * K + N ^ ε := by positivity
    have hC : 0 ≤ 2 ^ m * (3 * (5 * N ^ ε + 1) + 2 * N ^ ε) := by positivity
    have t1 := mul_le_mul_of_nonneg_left h6 hA
    have t2 := mul_le_mul_of_nonneg_left hγ hB
    have t3 := mul_le_mul_of_nonneg_left h6 hC
    have h9 : (0 : ℝ) ≤ 9 ^ (m + 1) := by positivity
    have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
    have hA' : 8 * (2 ^ m * (3 * K + 2 * N ^ ε) * N ^ (-(6 / (q : ℝ)))) ≤
        8 * (2 ^ m * (3 * K + 2 * N ^ ε)) * N ^ (-x) := by nlinarith
    have hB' : 2 ^ m * (e₀ + (3 * K + N ^ ε) * N ^ (-γ)) ≤
        2 ^ m * (E₀ + (3 * K + N ^ ε)) * N ^ (-x) := by
      have h1 : e₀ + (3 * K + N ^ ε) * N ^ (-γ) ≤ (E₀ + (3 * K + N ^ ε)) * N ^ (-x) := by
        nlinarith
      nlinarith
    have key : 9 ^ (m + 1) * (8 * (2 ^ m * (3 * K + 2 * N ^ ε) * N ^ (-(6 / (q : ℝ)))) +
          2 ^ m * (e₀ + (3 * K + N ^ ε) * N ^ (-γ))) ≤
        9 ^ (m + 1) * (8 * (2 ^ m * (3 * K + 2 * N ^ ε)) + 2 ^ m * (E₀ + (3 * K + N ^ ε))) *
          N ^ (-x) := by
      have := mul_le_mul_of_nonneg_left (add_le_add hA' hB') h9
      linarith
    have t3' := mul_le_mul_of_nonneg_left t3 (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith

end Det

end Submission.Obl.k4_matching_switching_target_certificate
