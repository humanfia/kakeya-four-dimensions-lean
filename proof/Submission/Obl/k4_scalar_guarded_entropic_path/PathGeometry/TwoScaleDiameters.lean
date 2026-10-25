/-
Adapted from this LOT tree, obligation o093, session x0535, commit 05931f40,
Submission/Obl/k4_scalar_critical_path_terminal/TwoScaleDiameters.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TubeVariation
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ActualPacketGraphs

/-! Two incidences in a fine original packet have small base diameter.
Their common coarser quadratic predictor then controls their hidden
diameter, at the ratio of the two ACTUAL dyadic time scales. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ActualPacketGraphs

open Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)

noncomputable section

theorem actual_chart_base_diameter {p : Code} {B k : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) (hN : 0 < N p k)
    (K : ℝ) (hK : 1 ≤ K) (hXK : N p k ^ ε ≤ K) (d : Fin Q.n)
    (l l' : Coeff) (hl : l ∈ Q.A d) (hl' : l' ∈ Q.A d)
    (t s : ℝ) (ht : t ∈ I Q.T (Q.j d)) (hs : s ∈ I Q.T (Q.j d)) :
    |t - s| ≤ ((2 : ℝ) ^ Q.T)⁻¹ ∧
      |spatial l t - spatial l' s| ≤ 3 * K ^ 2 * ((2 : ℝ) ^ Q.T)⁻¹ := by
  let q : ℝ := ((2 : ℝ) ^ Q.T)⁻¹
  let X := N p k ^ ε
  have hX : 0 < X := Real.rpow_pos_of_pos hN _
  have hq : 0 < q := by dsimp [q]; positivity
  have hdt : |t - s| ≤ q := by
    have htl := ht.1
    have htu := ht.2
    have hsl := hs.1
    have hsu := hs.2
    change ((Q.j d : ℕ) : ℝ) / (2 : ℝ) ^ Q.T ≤ t at htl
    change t ≤ (((Q.j d : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Q.T at htu
    change ((Q.j d : ℕ) : ℝ) / (2 : ℝ) ^ Q.T ≤ s at hsl
    change s ≤ (((Q.j d : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Q.T at hsu
    rw [add_div, one_div] at htu hsu
    apply abs_le.mpr
    dsimp [q]
    constructor <;> linarith
  have hK0 : 0 ≤ K := by linarith
  have hKsq : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  obtain ⟨_, hJ, _, hJfit, huv, _, _, _, _, _, hfit, _⟩ := Q.hcd.2.2.2.2.2.1 d
  have hJX : Q.J d ≤ X * q := by simpa only [X, q, div_eq_mul_inv] using hJfit
  have hwidth : X * Q.J d ≤ K ^ 2 * q := by
    calc
      _ ≤ X * (X * q) := mul_le_mul_of_nonneg_left hJX hX.le
      _ ≤ K * (K * q) := by gcongr
      _ = _ := by ring
  have hv : |Q.v d| ≤ K := (le_add_of_nonneg_left (abs_nonneg _)).trans (huv.trans hXK)
  have hcenter : |(Q.u d + t * Q.v d) - (Q.u d + s * Q.v d)| ≤ K * q := by
    rw [show (Q.u d + t * Q.v d) - (Q.u d + s * Q.v d) = Q.v d * (t - s) by ring, abs_mul]
    exact mul_le_mul hv hdt (abs_nonneg _) hK0
  have hfit' (l : Coeff) (hl : l ∈ Q.A d) (t : ℝ) (ht : t ∈ I Q.T (Q.j d)) :
      |spatial l t - (Q.u d + t * Q.v d)| ≤ K ^ 2 * q := by
    have hh := (hfit l hl t ht).1
    have heq : spatial l t - (Q.u d + t * Q.v d) =
        Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y l t - Q.u d - t * Q.v d := by
      dsimp [spatial, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y]
      ring
    rw [heq]
    exact hh.trans hwidth
  refine ⟨hdt, ?_⟩
  have htri := abs_sub_le (spatial l t) (Q.u d + t * Q.v d) (spatial l' s)
  have htri' := abs_sub_le (Q.u d + t * Q.v d) (Q.u d + s * Q.v d) (spatial l' s)
  have hlast : |Q.u d + s * Q.v d - spatial l' s| ≤ K ^ 2 * q := by
    rw [abs_sub_comm]
    exact hfit' l' hl' s hs
  have hsq := mul_le_mul_of_nonneg_right hKsq hq.le
  change |spatial l t - spatial l' s| ≤ 3 * K ^ 2 * q
  linarith [hfit' l hl t ht]

/-- A coarse predictor and a much finer base packet give a hidden
diameter bound. All scales and fits are literal finite-sample data. -/
theorem two_scale_hidden_diameter {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f)
    {t₀ q a u v M K q' E t s y y' x x' : ℝ}
    (hq : 0 < q) (ha : 0 < a) (hK : 1 ≤ K)
    (hq' : 0 ≤ q') (hM : 0 ≤ M) (hv : |v| ≤ K)
    (hwidth : q / K ≤ a)
    (hbound : ∀ τ ∈ Icc t₀ (t₀ + q), ∀ z ∈ Icc (-2 : ℝ) 2,
      |f τ (u + τ * v + a * z)| ≤ M)
    (ht : t ∈ Icc t₀ (t₀ + q)) (hs : s ∈ Icc t₀ (t₀ + q))
    (hfit : |y - (u + t * v)| ≤ a) (hfit' : |y' - (u + s * v)| ≤ a)
    (hdt : |t - s| ≤ q') (hdy : |y - y'| ≤ 3 * K ^ 2 * q')
    (hx : |x - f t y| ≤ E) (hx' : |x' - f s y'| ≤ E) :
    |x - x'| ≤ 2 * E + 255 * M * K ^ 3 * q' / q := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hKsq : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  have hKcube : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have hnorm (z : ℝ) (hz : |z| ≤ a) : z / a ∈ Icc (-2 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ ha).mpr
      linarith [(abs_le.mp hz).1]
    · apply (div_le_iff₀ ha).mpr
      linarith [(abs_le.mp hz).2]
  have hgraph := tube_variation hf hq ha hbound ht hs (hnorm _ hfit) (hnorm _ hfit')
  have hcross : |(y - y') - v * (t - s)| ≤ 4 * K ^ 2 * q' := by
    have hmul : |v * (t - s)| ≤ K * q' := by
      rw [abs_mul]
      exact mul_le_mul hv hdt (abs_nonneg _) hK0.le
    have hsq := mul_le_mul_of_nonneg_right hKsq hq'
    have htri := abs_sub_le (y - y') 0 (v * (t - s))
    simp only [sub_zero, zero_sub, abs_neg] at htri
    linarith
  have hmass : q ≤ a * K := (div_le_iff₀ hK0).mp hwidth
  have hspace : |(y - y') - v * (t - s)| / a ≤ 4 * K ^ 3 * (q' / q) := by
    apply (div_le_iff₀ ha).mpr
    apply hcross.trans
    calc
      _ = (4 * K ^ 2 * q' * q) / q := by field_simp
      _ ≤ ((4 * K ^ 2 * q') * (a * K)) / q := by
        apply div_le_div_of_nonneg_right _ hq.le
        exact mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by ring
  have hsum : |t - s| / q + |(y - y') - v * (t - s)| / a ≤ 5 * K ^ 3 * (q' / q) := by
    have ht' := div_le_div_of_nonneg_right hdt hq.le
    have hc := mul_le_mul_of_nonneg_right hKcube (div_nonneg hq' hq.le)
    nlinarith
  have hgraph' : |f t y - f s y'| ≤ 255 * M * K ^ 3 * q' / q := by
    apply hgraph.trans
    have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 51 * M by positivity)
    convert hm using 1
    ring
  have htri := abs_sub_le x (f t y) x'
  have htri' := abs_sub_le (f t y) (f s y') x'
  have hlast : |f s y' - x'| ≤ E := by rwa [abs_sub_comm]
  linarith

/-- Two ACTUAL root charts give the geometric hidden-state diameter
needed for finite point-state ambiguity. Full assignments and current
coarse floors are unchanged; no candidate or new conditioning is used. -/
theorem actual_two_scale_hidden_diameter {p : Code} (hp : Exact p)
    {Bc Bf k : ℕ} {rc bc hc εc rf bf hf εf : ℝ} {flag : Bool}
    (Qc : ChartW p Bc rc bc hc εc true k) (Qf : ChartW p Bf rf bf hf εf flag k)
    (hrc : 0 ≤ rc) (hεc : 0 ≤ εc) (dc : Fin Qc.n) (df : Fin Qf.n)
    (ρ : MeasureTheory.Measure (Coeff × ℝ)) (B H K : ℝ)
    (hB : 0 < B) (hH : 0 < H) (hK : 1 ≤ K)
    (hXc : N p k ^ εc ≤ K) (hXf : N p k ^ εf ≤ K) (hBK : B ≤ K) (hHK : H ≤ K)
    (hwidth : (K * (2 : ℝ) ^ Qc.T)⁻¹ ≤ Qc.J dc)
    (hcap : ρ.map (obsL (N p k ^ (-rc))) ≤
      ENNReal.ofReal (B * N p k ^ (-f p rc)) • (MeasureTheory.volume.prod MeasureTheory.Measure.count))
    (hfloor : (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ Qc.T)⁻¹) *
      ν p k (Qc.γ dc) (Qc.A dc) ≤ ρ (Qc.A dc ×ˢ I Qc.T (Qc.j dc)))
    (l l' : Coeff) (hlc : l ∈ Qc.A dc) (hlc' : l' ∈ Qc.A dc)
    (hlf : l ∈ Qf.A df) (hlf' : l' ∈ Qf.A df)
    (t s : ℝ) (htc : t ∈ I Qc.T (Qc.j dc)) (hsc : s ∈ I Qc.T (Qc.j dc))
    (htf : t ∈ I Qf.T (Qf.j df)) (hsf : s ∈ I Qf.T (Qf.j df)) :
    |hidden l t - hidden l' s| ≤ 2 * K * N p k ^ (-rc) +
      47589120000000 * K ^ 26 * (((2 : ℝ) ^ Qf.T)⁻¹) / (((2 : ℝ) ^ Qc.T)⁻¹) := by
  let q : ℝ := ((2 : ℝ) ^ Qc.T)⁻¹
  let q' : ℝ := ((2 : ℝ) ^ Qf.T)⁻¹
  let a := N p k ^ εc * Qc.J dc
  let M := 186624000000 * K ^ 23
  let t₀ : ℝ := ((Qc.j dc : ℕ) : ℝ) / (2 : ℝ) ^ Qc.T
  have hN : 0 < N p k := by linarith [hp.1.1 k]
  have hN1 : 1 ≤ N p k := by linarith [hp.1.1 k]
  have hX1 : 1 ≤ N p k ^ εc := Real.one_le_rpow hN1 hεc
  have hq : 0 < q := by dsimp [q]; positivity
  have hq' : 0 < q' := by dsimp [q']; positivity
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hJ : 0 < Qc.J dc := (Qc.hcd.2.2.2.2.2.1 dc).2.1
  have ha : 0 < a := mul_pos (Real.rpow_pos_of_pos hN _) hJ
  have hI : I Qc.T (Qc.j dc) = Icc t₀ (t₀ + q) := by
    dsimp [I, t₀, q]
    rw [← one_div, add_div]
  have hwidth' : q / K ≤ a := by
    calc
      _ = (K * (2 : ℝ) ^ Qc.T)⁻¹ := by dsimp [q]; field_simp
      _ ≤ Qc.J dc := hwidth
      _ ≤ _ := by dsimp [a]; nlinarith
  obtain ⟨_, _, _, _, huv, hP, _, _, _, _, hfit, _⟩ := Qc.hcd.2.2.2.2.2.1 dc
  have hv : |Qc.v dc| ≤ K :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans (huv.trans hXc)
  have hfit' (l : Coeff) (hl : l ∈ Qc.A dc) (t : ℝ) (ht : t ∈ I Qc.T (Qc.j dc)) :
      |spatial l t - (Qc.u dc + t * Qc.v dc)| ≤ a ∧
      |hidden l t - MvPolynomial.eval ![t, spatial l t] (Qc.P dc)| ≤
        N p k ^ εc * N p k ^ (-rc) := by
    have hh := hfit l hl t ht
    refine ⟨?_, hh.2⟩
    have heq : spatial l t - (Qc.u dc + t * Qc.v dc) =
        Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y l t - Qc.u dc - t * Qc.v dc := by
      dsimp [spatial, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y]
      ring
    rw [heq]
    exact hh.1
  have hbound : ∀ τ ∈ Icc t₀ (t₀ + q), ∀ z ∈ Icc (-2 : ℝ) 2,
      |MvPolynomial.eval ![τ, Qc.u dc + τ * Qc.v dc + a * z] (Qc.P dc)| ≤ M := by
    intro τ hτ z hz
    exact actual_packet_assignment_tube_bound hp Qc hrc hεc dc ρ B H K hB hH hK
      hXc hBK hHK hcap hfloor τ (by rwa [hI]) z hz
  have hbase := actual_chart_base_diameter Qf hN K hK hXf df l l' hlf hlf' t s htf hsf
  have h := two_scale_hidden_diameter (isQuad2_eval (Qc.P dc) hP) hq ha hK hq'.le
    (show 0 ≤ M by dsimp [M]; positivity) hv hwidth' hbound
    (show t ∈ Icc t₀ (t₀ + q) by rwa [← hI])
    (show s ∈ Icc t₀ (t₀ + q) by rwa [← hI])
    (hfit' l hlc t htc).1 (hfit' l' hlc' s hsc).1 hbase.1 hbase.2
    (hfit' l hlc t htc).2 (hfit' l' hlc' s hsc).2
  apply h.trans
  have herror := mul_le_mul_of_nonneg_right hXc (Real.rpow_nonneg hN.le (-rc))
  calc
    _ ≤ 2 * K * N p k ^ (-rc) + 255 * M * K ^ 3 * q' / q := by
      nlinarith
    _ = _ := by dsimp [M, q, q']; ring

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ActualPacketGraphs
