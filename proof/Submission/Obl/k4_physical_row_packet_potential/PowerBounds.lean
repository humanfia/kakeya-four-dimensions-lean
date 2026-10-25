import Mathlib
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourcePowerSelection

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.PowerBudget

open Submission.Obl.k4_physical_parent_potential_candidates.SourceNormalization

/-- A nonnegative numerical cost controlled by one fixed power, uniformly for
all original packet constants at least two. -/
def Bound (f : ℝ → ℝ) : Prop :=
  ∃ e : ℕ, ∀ K : ℝ, 2 ≤ K → 0 ≤ f K ∧ f K ≤ K ^ e

namespace Bound

theorem const (C : ℝ) (hC : 0 ≤ C) : Bound (fun _ => C) := by
  obtain ⟨e, he⟩ := exists_uniform_constant_power C
  exact ⟨e, fun K hK => ⟨hC, he K hK⟩⟩

theorem id : Bound (fun K => K) :=
  ⟨1, fun K hK => ⟨by linarith, by simp⟩⟩

theorem mono {f g : ℝ → ℝ} (hf : Bound f)
    (h : ∀ K : ℝ, 2 ≤ K → 0 ≤ g K ∧ g K ≤ f K) : Bound g := by
  obtain ⟨e, he⟩ := hf
  exact ⟨e, fun K hK => ⟨(h K hK).1, (h K hK).2.trans (he K hK).2⟩⟩

theorem add {f g : ℝ → ℝ} (hf : Bound f) (hg : Bound g) : Bound (fun K => f K + g K) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨e + b + 1, ?_⟩
  intro K hK
  obtain ⟨hf0, hf⟩ := he K hK
  obtain ⟨hg0, hg⟩ := hb K hK
  have hK1 : 1 ≤ K := by linarith
  have hfe : f K ≤ K ^ (e + b) := hf.trans (pow_le_pow_right₀ hK1 (by omega))
  have hge : g K ≤ K ^ (e + b) := hg.trans (pow_le_pow_right₀ hK1 (by omega))
  refine ⟨add_nonneg hf0 hg0, ?_⟩
  calc
    _ ≤ 2 * K ^ (e + b) := by linarith
    _ ≤ K * K ^ (e + b) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem mul {f g : ℝ → ℝ} (hf : Bound f) (hg : Bound g) : Bound (fun K => f K * g K) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨e + b, ?_⟩
  intro K hK
  obtain ⟨hf0, hf⟩ := he K hK
  obtain ⟨hg0, hg⟩ := hb K hK
  refine ⟨mul_nonneg hf0 hg0, ?_⟩
  rw [pow_add]
  exact mul_le_mul hf hg hg0 (by positivity)

theorem pow {f : ℝ → ℝ} (hf : Bound f) (n : ℕ) : Bound (fun K => f K ^ n) := by
  obtain ⟨e, he⟩ := hf
  refine ⟨e * n, ?_⟩
  intro K hK
  obtain ⟨hf0, hf⟩ := he K hK
  refine ⟨pow_nonneg hf0 n, ?_⟩
  rw [pow_mul]
  exact pow_le_pow_left₀ hf0 hf n

theorem max {f g : ℝ → ℝ} (hf : Bound f) (hg : Bound g) : Bound (fun K => max (f K) (g K)) := by
  apply (hf.add hg).mono
  intro K hK
  obtain ⟨e, he⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have hf0 := (he K hK).1
  have hg0 := (hb K hK).1
  exact ⟨hf0.trans (le_max_left _ _), max_le (le_add_of_nonneg_right hg0)
    (le_add_of_nonneg_left hf0)⟩

theorem rpow {f : ℝ → ℝ} (hf : Bound f) (s : ℝ) (hs : 0 ≤ s) :
    Bound (fun K => f K ^ s) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨n, hn⟩ := exists_nat_ge s
  refine ⟨e * n, ?_⟩
  intro K hK
  obtain ⟨hf0, hf⟩ := he K hK
  have hK1 : 1 ≤ K := by linarith
  have hpow1 : 1 ≤ K ^ e := one_le_pow₀ hK1
  refine ⟨Real.rpow_nonneg hf0 _, ?_⟩
  calc
    _ ≤ (K ^ e) ^ s := Real.rpow_le_rpow hf0 hf hs
    _ ≤ (K ^ e) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hpow1 hn
    _ = _ := by rw [Real.rpow_natCast, ← pow_mul]

end Bound

/-- A sufficiently high common natural power is below any prescribed fixed
positive power of a height-to-loss ratio. -/
theorem exists_small_ratio_power (n : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ E : ℕ, ∀ K ζ : ℝ, 2 ≤ K → 0 < ζ → ζ ≤ 1 →
      ζ ^ E / K ^ E ≤ (ζ / K ^ n) ^ s := by
  obtain ⟨E, hE⟩ := exists_nat_ge (max s ((n : ℝ) * s))
  refine ⟨E, ?_⟩
  intro K ζ hK hζ hζ1
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hEs : s ≤ (E : ℝ) := (le_max_left _ _).trans hE
  have hEn : (n : ℝ) * s ≤ (E : ℝ) := (le_max_right _ _).trans hE
  rw [Real.div_rpow hζ.le (by positivity), ← Real.rpow_natCast K n,
    ← Real.rpow_mul hK0.le]
  have hz : ζ ^ (E : ℝ) ≤ ζ ^ s :=
    Real.rpow_le_rpow_of_exponent_ge hζ hζ1 hEs
  have hk : K ^ ((n : ℝ) * s) ≤ K ^ (E : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hK1 hEn
  simpa only [Real.rpow_natCast] using div_le_div₀ (Real.rpow_nonneg hζ.le s) hz
    (Real.rpow_pos_of_pos hK0 _) hk

/-- A census mesh produced from polynomially bounded costs and inverse
radii is bounded below by a fixed common power of the target accuracy. -/
theorem exists_height_power (cost radius : ℝ → ℝ)
    (hcost : Bound cost) (hrad : Bound (fun K => (radius K)⁻¹))
    (hcostPos : ∀ K : ℝ, 2 ≤ K → 0 < cost K)
    (hradPos : ∀ K : ℝ, 2 ≤ K → 0 < radius K)
    (d : ℝ) (hd : d < 1) :
    ∃ E : ℕ, ∀ K ζ : ℝ, 2 ≤ K → 0 < ζ → ζ ≤ 1 →
      ζ ^ E / K ^ E ≤ min 1 ((ζ * radius K ^ 9 / cost K) ^ (1 / (1 - d))) := by
  obtain ⟨n, hn⟩ := hcost.mul (hrad.pow 9)
  have hs : 0 < 1 / (1 - d) := by positivity
  obtain ⟨E, hE⟩ := exists_small_ratio_power n (1 / (1 - d)) hs
  refine ⟨E, ?_⟩
  intro K ζ hK hζ hζ1
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hcp := hcostPos K hK
  have hrp := hradPos K hK
  have hratio : cost K / radius K ^ 9 ≤ K ^ n := by
    simpa only [div_eq_mul_inv, inv_pow] using (hn K hK).2
  have hbase : ζ / K ^ n ≤ ζ * radius K ^ 9 / cost K := by
    have h := div_le_div_of_nonneg_left hζ.le (by positivity : 0 < cost K / radius K ^ 9) hratio
    apply h.trans_eq
    field_simp
  apply le_min
  · apply (div_le_one (by positivity : 0 < K ^ E)).mpr
    exact (pow_le_one₀ hζ.le hζ1).trans (one_le_pow₀ hK1)
  · exact (hE K ζ hK hζ hζ1).trans (Real.rpow_le_rpow (by positivity) hbase hs.le)

/-- Common ratio powers decrease when their natural exponent increases. -/
theorem ratio_power_mono {K ζ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    {e E : ℕ} (he : e ≤ E) : ζ ^ E / K ^ E ≤ ζ ^ e / K ^ e := by
  rw [← div_pow, ← div_pow]
  apply pow_le_pow_of_le_one
  · exact div_nonneg hζ (by linarith)
  · exact (div_le_one (by linarith : 0 < K)).mpr (hζ1.trans hK)
  · exact he

/-- A fixed polynomial amplification and a fixed target ratio power can
both be paid for by one exponent selected before the packet is given. -/
theorem exists_amplified_ratio_power (cost : ℝ → ℝ) (hcost : Bound cost) (e : ℕ) :
    ∃ E : ℕ, e ≤ E ∧ ∀ K ζ : ℝ, 2 ≤ K → 0 < ζ → ζ ≤ 1 →
      cost K * (ζ ^ E / K ^ E) ≤ ζ ^ e / K ^ e := by
  obtain ⟨b, hb⟩ := hcost
  refine ⟨e + b, by omega, ?_⟩
  intro K ζ hK hζ hζ1
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  calc
    _ ≤ K ^ b * (ζ ^ (e + b) / K ^ (e + b)) :=
      mul_le_mul_of_nonneg_right (hb K hK).2 (by positivity)
    _ = ζ ^ e / K ^ e * ζ ^ b := by
      rw [pow_add, pow_add]
      field_simp
    _ ≤ ζ ^ e / K ^ e * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hζ.le hζ1) (by positivity)
    _ = _ := mul_one _

/-- A positive numerical scale with a uniform lower bound by one common
power of the target accuracy over the original loss. -/
def Lower (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ e : ℕ, ∀ K ζ : ℝ, 2 ≤ K → 0 < ζ → ζ ≤ 1 → ζ ^ e / K ^ e ≤ f K ζ

namespace Lower

theorem one : Lower (fun _ _ => 1) := ⟨0, by intros; simp⟩

theorem accuracy : Lower (fun _ ζ => ζ) := by
  refine ⟨1, ?_⟩
  intro K ζ hK hζ hζ1
  simpa only [pow_one] using div_le_self hζ.le (by linarith : 1 ≤ K)

theorem mono {f g : ℝ → ℝ → ℝ} (hf : Lower f)
    (h : ∀ K ζ : ℝ, 2 ≤ K → 0 < ζ → ζ ≤ 1 → f K ζ ≤ g K ζ) : Lower g := by
  obtain ⟨e, he⟩ := hf
  exact ⟨e, fun K ζ hK hζ hζ1 => (he K ζ hK hζ hζ1).trans (h K ζ hK hζ hζ1)⟩

theorem min {f g : ℝ → ℝ → ℝ} (hf : Lower f) (hg : Lower g) :
    Lower (fun K ζ => min (f K ζ) (g K ζ)) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨max e b, ?_⟩
  intro K ζ hK hζ hζ1
  apply le_min
  · exact (ratio_power_mono (by linarith : 1 ≤ K) hζ.le hζ1 (le_max_left _ _)).trans
      (he K ζ hK hζ hζ1)
  · exact (ratio_power_mono (by linarith : 1 ≤ K) hζ.le hζ1 (le_max_right _ _)).trans
      (hb K ζ hK hζ hζ1)

theorem mul {f g : ℝ → ℝ → ℝ} (hf : Lower f) (hg : Lower g) :
    Lower (fun K ζ => f K ζ * g K ζ) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨e + b, ?_⟩
  intro K ζ hK hζ hζ1
  have hfe := he K ζ hK hζ hζ1
  have hgb := hb K ζ hK hζ hζ1
  calc
    _ = (ζ ^ e / K ^ e) * (ζ ^ b / K ^ b) := by rw [pow_add, pow_add]; ring
    _ ≤ f K ζ * g K ζ := mul_le_mul hfe hgb (by positivity) ((show (0 : ℝ) ≤ ζ ^ e / K ^ e by positivity).trans hfe)

theorem pow {f : ℝ → ℝ → ℝ} (hf : Lower f) (n : ℕ) :
    Lower (fun K ζ => f K ζ ^ n) := by
  obtain ⟨e, he⟩ := hf
  refine ⟨e * n, ?_⟩
  intro K ζ hK hζ hζ1
  have hfe := he K ζ hK hζ hζ1
  calc
    _ = (ζ ^ e / K ^ e) ^ n := by rw [div_pow, ← pow_mul, ← pow_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hfe n

theorem rpow {f : ℝ → ℝ → ℝ} (hf : Lower f) (s : ℝ) (hs : 0 < s) :
    Lower (fun K ζ => f K ζ ^ s) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨b, hb⟩ := exists_nat_ge ((e : ℝ) * s)
  refine ⟨b, ?_⟩
  intro K ζ hK hζ hζ1
  have hK0 : 0 < K := by linarith
  have hzK : 0 < ζ / K := div_pos hζ hK0
  have hzK1 : ζ / K ≤ 1 := (div_le_one hK0).mpr (by linarith)
  have hsmall : ζ ^ b / K ^ b ≤ (ζ ^ e / K ^ e) ^ s := by
    rw [← div_pow, ← div_pow, ← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_mul hzK.le]
    exact Real.rpow_le_rpow_of_exponent_ge hzK hzK1 hb
  exact hsmall.trans
    (Real.rpow_le_rpow (by positivity) (he K ζ hK hζ hζ1) hs.le)

theorem inv_cost (cost : ℝ → ℝ) (hcost : Bound cost)
    (hpos : ∀ K : ℝ, 2 ≤ K → 0 < cost K) : Lower (fun K _ => (cost K)⁻¹) := by
  obtain ⟨e, he⟩ := hcost
  refine ⟨e, ?_⟩
  intro K ζ hK hζ hζ1
  have hK0 : 0 < K := by linarith
  calc
    _ ≤ 1 / K ^ e := div_le_div_of_nonneg_right (pow_le_one₀ hζ.le hζ1) (by positivity)
    _ ≤ 1 / cost K := one_div_le_one_div_of_le (hpos K hK) (he K hK).2
    _ = _ := one_div _

theorem div_cost {f : ℝ → ℝ → ℝ} (hf : Lower f) (cost : ℝ → ℝ)
    (hcost : Bound cost) (hpos : ∀ K : ℝ, 2 ≤ K → 0 < cost K) :
    Lower (fun K ζ => f K ζ / cost K) := by
  simpa only [div_eq_mul_inv] using hf.mul (inv_cost cost hcost hpos)

theorem of_inv_bound (f : ℝ → ℝ) (hf : Bound (fun K => (f K)⁻¹))
    (hpos : ∀ K : ℝ, 2 ≤ K → 0 < f K) : Lower (fun K _ => f K) := by
  have h := inv_cost (fun K => (f K)⁻¹) hf (fun K hK => inv_pos.mpr (hpos K hK))
  simpa only [inv_inv] using h

/-- A ratio factor at most the original loss can be inserted into a lower
bound at the cost of one further accuracy power. -/
theorem with_ratio {f : ℝ → ℝ → ℝ} (hf : Lower f) :
    ∃ E : ℕ, ∀ K ζ R : ℝ, 2 ≤ K → 0 < ζ → ζ ≤ 1 → 0 ≤ R → R ≤ K →
      R * (ζ ^ E / K ^ E) ≤ f K ζ := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨E, _, hE⟩ := exists_amplified_ratio_power (fun K => K) Bound.id e
  refine ⟨E, ?_⟩
  intro K ζ R hK hζ hζ1 hR hRK
  exact (mul_le_mul_of_nonneg_right hRK (by positivity)).trans
    ((hE K ζ hK hζ hζ1).trans (he K ζ hK hζ hζ1))

end Lower

end Submission.Obl.k4_physical_row_packet_potential.PowerBudget
