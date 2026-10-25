import Submission.Obl.k4_matching_switching_target_certificate.ControlSeparation
import Submission.Obl.k4_matching_switching_target_certificate.ControlNumerics
import Submission.Obl.k4_matching_switching_target_certificate.Records

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

namespace Det

variable {n₁ n₂ J : ℕ} {β : ℕ → ℝ} {γ : ℝ} {q k m z : ℕ} {N ε : ℝ}
  {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ} {h : ℕ → ℕ}
  {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}

variable (H : Det J β γ q k m z N ε f₁ f₂ h F S)
include H

lemma reference_margins :
    γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β ((z : ℝ) / (q : ℝ)) - β m ∧
    ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) ((z : ℝ) / (q : ℝ)) +
        (i : ℝ) * jetRadius J β ((z : ℝ) / (q : ℝ)) - β m := by
  have had := H.hadm ((z : ℝ) / q) (H.level_mem le_rfl (by have := H.hzk; omega))
  have hacc := jetAccuracy_active_order H.hJ β (H.level_nonneg z) H.hm H.hmJ had.1
  constructor
  · simpa only [hacc] using had.2.2.1 m H.hmJ
  · exact had.2.2.2

lemma coarse_center_reference_dist {a e : (Fin n₁ × Fin n₂) × ℝ}
    (hfloor : Int.floor (a.2 * (2 : ℝ) ^ h k) = Int.floor (e.2 * (2 : ℝ) ^ h k)) :
    |dcenter h k a.2 - e.2| ≤ N ^ (-jetRadius J β ((z : ℝ) / (q : ℝ))) ∧
    |dcenter h k a.2 - dcenter h z e.2| ≤ N ^ (-jetRadius J β ((z : ℝ) / (q : ℝ))) := by
  have hkq : k ≤ q := by have := H.hkq; omega
  have hzq : z ≤ q := H.hzk.trans hkq
  have htime : |dcenter h k a.2 - e.2| ≤ ((2 : ℝ) ^ h k)⁻¹ / 2 := by
    rw [abs_sub_comm]
    exact abs_sub_dcenter_of_floor_eq hfloor
  have hcenter := abs_dcenter_sub_le h z e.2
  have hle : ((2 : ℝ) ^ h k)⁻¹ ≤ ((2 : ℝ) ^ h z)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (H.hmono z k H.hzk hkq))
  have hrad := H.inv_pow_le hzq
  have hpos : 0 ≤ ((2 : ℝ) ^ h k)⁻¹ := by positivity
  constructor
  · linarith
  · have ht := abs_sub_le (dcenter h k a.2) e.2 (dcenter h z e.2)
    rw [abs_sub_comm e.2] at ht
    linarith

lemma coded_control_eq {e : (Fin n₁ × Fin n₂) × ℝ} (he : e ∈ S) (ta frame : ℝ) (κ : Bool) :
    codedControl J m k z q β N ta frame h F S f₁ f₂ (F k e)
        (referencePalette m z q β N h f₁ f₂ e) κ =
      referenceControl J m (h z) β N ((z : ℝ) / (q : ℝ)) (6 / (q : ℝ)) ta frame
        (f₁ e.1.1) (f₂ e.1.2) e.2 κ := by
  apply codedControl_eq_referenceControl f₁ f₂ _ he κ
  intro x hx y hy hxy
  exact (H.hrec k (by have := H.hkq; omega) x hx y hy).mp hxy z H.hzk

lemma coded_control_error {a e : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S) (he : e ∈ S)
    (hfloor : Int.floor (a.2 * (2 : ℝ) ^ h k) = Int.floor (e.2 * (2 : ℝ) ^ h k))
    (frame : ℝ) (κ : Bool) :
    |N ^ β m * (iteratedDeriv m (if κ then f₁ e.1.1 else f₂ e.1.2) (dcenter h k a.2) - frame) -
      codedControl J m k z q β N (dcenter h k a.2) frame h F S f₁ f₂ (F k e)
        (referencePalette m z q β N h f₁ f₂ e) κ| ≤
      N ^ (-(6 / (q : ℝ))) + (3 + N ^ ε) * N ^ (-γ) := by
  rw [H.coded_control_eq he]
  have hs : ContDiffOn ℝ (J + 1 : ℕ) (if κ then f₁ e.1.1 else f₂ e.1.2) (Ioo (-1 : ℝ) 2) := by
    cases κ
    · exact H.hf₂ _
    · exact H.hf₁ _
  have hb : ∀ x ∈ Icc (0 : ℝ) 1,
      |iteratedDeriv (J + 1) (if κ then f₁ e.1.1 else f₂ e.1.2) x| ≤ N ^ ε := by
    cases κ
    · exact H.hB₂ _ (J + 1) le_rfl
    · exact H.hB₁ _ (J + 1) le_rfl
  exact referenceControl_error H.hmJ H.hN H.reference_margins.1 H.reference_margins.2
    _ _ κ hs hb (H.hS e he).1 (dcenter_mem_Icc h k (H.hS a ha).1)
    (H.coarse_center_reference_dist hfloor).2

lemma coded_control_error_small (hεq : ε ≤ 1 / (q : ℝ)) (hroot : 32 ≤ N ^ (1 / (q : ℝ)))
    {a e : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S) (he : e ∈ S)
    (hfloor : Int.floor (a.2 * (2 : ℝ) ^ h k) = Int.floor (e.2 * (2 : ℝ) ^ h k))
    (frame : ℝ) (κ : Bool) :
    |N ^ β m * (iteratedDeriv m (if κ then f₁ e.1.1 else f₂ e.1.2) (dcenter h k a.2) - frame) -
      codedControl J m k z q β N (dcenter h k a.2) frame h F S f₁ f₂ (F k e)
        (referencePalette m z q β N h f₁ f₂ e) κ| ≤ N ^ (-(2 / (q : ℝ))) := by
  exact (H.coded_control_error ha he hfloor frame κ).trans
    (control_errors_small H.hq H.hN H.hε.le hεq ((div_le_iff₀ H.q_pos).mpr H.hγq) hroot).1

lemma coded_control_separation (hεq : ε ≤ 1 / (q : ℝ)) (hroot : 32 ≤ N ^ (1 / (q : ℝ)))
    {a e : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S) (he : e ∈ S)
    (hfloor : Int.floor (a.2 * (2 : ℝ) ^ h k) = Int.floor (e.2 * (2 : ℝ) ^ h k))
    (frame : ℝ) :
    N ^ (-ε) / 2 ≤
      |codedControl J m k z q β N (dcenter h k a.2) frame h F S f₁ f₂ (F k e)
          (referencePalette m z q β N h f₁ f₂ e) true -
        codedControl J m k z q β N (dcenter h k a.2) frame h F S f₁ f₂ (F k e)
          (referencePalette m z q β N h f₁ f₂ e) false| := by
  rw [H.coded_control_eq he, H.coded_control_eq he]
  have hlow : N ^ (-(β m + ε)) ≤
      |iteratedDeriv m (f₁ e.1.1) e.2 - iteratedDeriv m (f₂ e.1.2) e.2| := by
    have hl := ((H.hS e he).2.2 m H.hm H.hmJ).2 H.hβm
    convert hl using 1 <;> congr 1 <;> ring
  have hgap : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      |iteratedDeriv (m + i) (f₁ e.1.1) e.2 - iteratedDeriv (m + i) (f₂ e.1.2) e.2| ≤
        N ^ (-β (m + i) + ε) := by
    intro i hi hiJ
    exact ((H.hS e he).2.2 (m + i) (by omega) hiJ).1
  have hs := referenceControl_separation H.hmJ H.hN H.hε.le (H.level_nonneg z)
    H.reference_margins.1 H.reference_margins.2 (H.hf₁ e.1.1) (H.hf₂ e.1.2)
    (H.hB₁ _ (J + 1) le_rfl) (H.hB₂ _ (J + 1) le_rfl) (H.hS e he).1
    (dcenter_mem_Icc h k (H.hS a ha).1)
    (H.coarse_center_reference_dist hfloor).1 (H.coarse_center_reference_dist hfloor).2 hlow hgap
    (frame := frame) (b := 6 / (q : ℝ))
  have herr := (control_errors_small H.hq H.hN H.hε.le hεq
    ((div_le_iff₀ H.q_pos).mpr H.hγq) hroot).2
  linarith

lemma coded_control_bound (hεq : ε ≤ 1 / (q : ℝ)) (hroot : 32 ≤ N ^ (1 / (q : ℝ)))
    {a e : (Fin n₁ × Fin n₂) × ℝ} (ha : a ∈ S) (he : e ∈ S)
    (hfloor : Int.floor (a.2 * (2 : ℝ) ^ h k) = Int.floor (e.2 * (2 : ℝ) ^ h k))
    (frame M : ℝ) (κ : Bool)
    (hcenter : |iteratedDeriv m (if κ then f₁ e.1.1 else f₂ e.1.2) (dcenter h k a.2) - frame| ≤
      M * N ^ (-β m)) :
    |codedControl J m k z q β N (dcenter h k a.2) frame h F S f₁ f₂ (F k e)
      (referencePalette m z q β N h f₁ f₂ e) κ| ≤ M + 1 := by
  have herr := H.coded_control_error_small hεq hroot ha he hfloor frame κ
  have hW : 0 < N ^ β m := H.Npow_pos _
  have hctr : |N ^ β m *
      (iteratedDeriv m (if κ then f₁ e.1.1 else f₂ e.1.2) (dcenter h k a.2) - frame)| ≤ M := by
    rw [abs_mul, abs_of_pos hW]
    calc _ ≤ N ^ β m * (M * N ^ (-β m)) := mul_le_mul_of_nonneg_left hcenter hW.le
      _ = M := by rw [mul_left_comm, ← Real.rpow_add H.N_pos]; simp
  have hrem : N ^ (-(2 / (q : ℝ))) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le H.hN
      (show -(2 / (q : ℝ)) ≤ 0 from neg_nonpos.mpr (div_nonneg (by norm_num) H.q_pos.le))
  have htri := abs_sub_le
    (codedControl J m k z q β N (dcenter h k a.2) frame h F S f₁ f₂ (F k e)
      (referencePalette m z q β N h f₁ f₂ e) κ)
    (N ^ β m * (iteratedDeriv m (if κ then f₁ e.1.1 else f₂ e.1.2) (dcenter h k a.2) - frame)) 0
  rw [sub_zero, sub_zero, abs_sub_comm] at htri
  linarith

end Det

end Submission.Obl.k4_matching_switching_target_certificate
