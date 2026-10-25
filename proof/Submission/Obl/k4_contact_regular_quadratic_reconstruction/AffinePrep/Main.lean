import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.Sample
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.MainNumerics
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.CoreAbsorption
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.ContactAdapter
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.SourceCoreAssembly
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.MassFloors
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.AffineResidualCaps
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.ContactRows
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# The second affine preparation on a fixed small horizon

`Model.Valid.secondAffineCore`: every late shifted regular quadratic candidate on the contact
horizon yields a fine affine source with the original mass floor (`Model.SecondAffineCore`).
The per-sample argument is `affine_candidate_at`; here we choose the tolerances and meshes and
verify its numerical hypotheses eventually.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4QuadraticSheetCore
open Submission.Obl.k4_critical_switching_state_preparation.Data
open Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α] {cfg : Model α}

theorem kpow_le_rpow {K N δ : ℝ} (hK : 0 ≤ K) (hN : 0 < N) (h : K ≤ N ^ δ) (n : ℕ) :
    K ^ n ≤ N ^ ((n : ℝ) * δ) := by
  calc K ^ n ≤ (N ^ δ) ^ n := pow_le_pow_left₀ hK h n
    _ = N ^ ((n : ℝ) * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, mul_comm]

theorem sq_rpow {N a : ℝ} (hN : 0 < N) : (N ^ a) ^ 2 = N ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  norm_num
  ring_nf

set_option maxHeartbeats 8000000 in
/-- **The second affine preparation.** -/
theorem Valid.secondAffineCore (h : cfg.Valid) : cfg.SecondAffineCore := by
  obtain ⟨V, hV, hVU, hκV⟩ := h.exists_contact_horizon
  refine ⟨V, hV, hVU, ?_⟩
  intro R hR ε hε
  obtain ⟨Cs, hCs0, hCs⟩ := exists_coefCtrl
  have hS0 : 0 < cfg.S := h.palette_pos
  have hS1 : cfg.S ≤ 1 := h.palette_le_one
  have he₀ : 0 < cfg.e₀ := h.defect_pos
  have hκ0 : 0 < cfg.κ := h.rate_pos
  have hκ1 : cfg.κ ≤ 1 := h.rate_le_one
  have hd0 : 0 ≤ cfg.d := h.dimension_nonneg
  have hd1 : cfg.d < 1 := h.dimension_lt_one
  have hU0 : 0 < cfg.U := h.depth_pos
  have hR0 : 0 < R := by linarith only [hR]
  have hRinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR.le
  have hRinv0 : 0 < R⁻¹ := inv_pos.mpr hR0
  -- tolerances, meshes and bins
  set τ : ℝ := min (min (ε / 81) (cfg.e₀ / 328)) 1 with hτdef
  have hτ0 : 0 < τ := lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hτε : 81 * τ ≤ ε := by
    have h1 := min_le_left (min (ε / 81) (cfg.e₀ / 328)) 1
    have h2 := min_le_left (ε / 81) (cfg.e₀ / 328)
    linarith only [h1, h2]
  have hτe : 82 * τ ≤ cfg.e₀ / 4 := by
    have h1 := min_le_left (min (ε / 81) (cfg.e₀ / 328)) 1
    have h2 := min_le_right (ε / 81) (cfg.e₀ / 328)
    linarith only [h1, h2, he₀]
  have hτ1 : τ ≤ 1 := min_le_right _ _
  set η : ℝ := τ * cfg.S / 20 with hηdef
  have hη0 : 0 < η := by positivity
  have hητ : η ≤ τ / 20 := by
    rw [hηdef]
    have := mul_le_mul_of_nonneg_left hS1 hτ0.le
    linarith only [this]
  have hη1 : η ≤ 1 := by linarith only [hητ, hτ1]
  have hηε : η < ε := by linarith only [hητ, hτε, hτ0]
  set εc : ℝ := η / 10 with hεcdef
  have hεc0 : 0 < εc := by positivity
  set vsep : ℝ := τ / 5 with hvsepdef
  have hvsep0 : 0 < vsep := by positivity
  have hSv : -cfg.S * vsep = -(4 * η) := by rw [hvsepdef, hηdef]; ring
  set M : ℝ := 81 * τ + 3 * R + 10 with hMdef
  have hM : 81 * τ + 1 ≤ M := by rw [hMdef]; linarith only [hR0]
  set Rc : ℝ := M + 2 * R + 5 / τ + 10 with hRcdef
  have h5τ : 0 < 5 / τ := by positivity
  have hRc : 1 < Rc := by rw [hRcdef, hMdef]; linarith only [hR0, hτ0, h5τ]
  have hRc0 : 0 < Rc := by linarith only [hRc]
  have hRcinv1 : Rc⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hRc.le
  have hMRc : M ≤ Rc := by rw [hRcdef]; linarith only [hR0, h5τ]
  have hRcM : Rc⁻¹ ≤ M := by
    have : 1 ≤ M := by rw [hMdef]; linarith only [hR0, hτ0]
    linarith only [this, hRcinv1]
  have hvsepRc : vsep ≤ Rc := by
    rw [hRcdef, hMdef, hvsepdef]; linarith only [hR0, hτ0, h5τ, hτ1]
  have hRcvsep : Rc⁻¹ ≤ vsep := by
    have h1 : vsep⁻¹ ≤ Rc := by
      rw [hvsepdef, inv_div]
      rw [hRcdef]; linarith only [hR0, hτ0, hM, h5τ]
    have := inv_anti₀ (inv_pos.mpr hvsep0) h1
    rwa [inv_inv] at this
  have h2RRc : 2 * R ≤ Rc := by rw [hRcdef, hMdef]; linarith only [hR0, hτ0, h5τ]
  have hNpos : ∀ k, 1 ≤ cfg.N k := fun k => by linarith only [h.scale k]
  -- the eventual facts
  have F3 := Transfer.affine_residual_mesh_caps cfg (h.toContactProblem).parameters h.basic
    h.caps (B := 5 * cfg.U + 10) (A := 2 * R + 1) (by positivity) (by positivity) hRc
  have F5 := eventually_core_absorption cfg.N cfg.K h.scale_limit he₀ hτ0 hτe hM hCs0
    (h.subpower.2 τ hτ0)
  have NA := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 8 (a := 3 * η + 4 * εc) (b := τ)
    (by rw [hεcdef]; linarith only [hητ, hη0, hτ0]) (A := 497664 * 5 * 11 * 100) (by norm_num)
  have NB := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 9 (a := 3 * η + 4 * εc) (b := 4 * η)
    (by rw [hεcdef]; linarith only [hη0]) (A := 15925248 * 5 * 11 * 100) (by norm_num)
  have NC := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 2 (a := 2 * εc + vsep) (b := τ)
    (by rw [hεcdef, hvsepdef]; linarith only [hητ, hη0, hτ0]) (A := 160) (by norm_num)
  have NF := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 4 (a := R + 4 * εc - M) (b := -(2 * R))
    (by rw [hεcdef, hMdef]; linarith only [hη1, hτ0]) (A := 486 * 129600) (by norm_num)
  have NG := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 4 (a := R + 4 * εc - M) (b := -2)
    (by rw [hεcdef, hMdef]; linarith only [hη1, hτ0, hR0]) (A := 2 * (972 * 129600))
    (by norm_num)
  have NH := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 3 (a := 2 * R) (b := 2 * R + 1)
    (by linarith only) (A := 8) (by norm_num)
  have NE := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 1 (a := -M) (b := -R - 1)
    (by rw [hMdef]; linarith only [hτ0, hR0]) (A := 4) (by norm_num)
  have NJ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 0 (a := 0) (b := ε - η)
    (by linarith only [hηε]) (A := 36) (by norm_num)
  have N8 := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hNpos
    h.scale_limit h.subpower.1 h.subpower.2 0 (a := -M) (b := 0)
    (by rw [hMdef]; linarith only [hτ0, hR0]) (A := 8) (by norm_num)
  refine ⟨η, hη0, ?_⟩
  filter_upwards [h.atlas R hR, (h.toContactProblem).eventually_centered_rows hεc0 hR, F3,
    h.caps Rc hRc, F5, h.subpower.2 1 one_pos, NA, NB, NC, NF, NG, NH, NE, NJ, N8]
    with k hatlas hcent hres hcaps hcore hKN hNA hNB hNC hNF hNG hNH hNE hNJ hN8
  intro s v i hs hsR hv hvR hsv hshift
  set N := cfg.N k with hNdef
  set K := cfg.K k with hKdef
  have hN2 : 2 ≤ N := h.scale k
  have hN0 : 0 < N := by linarith only [hN2]
  have hN1 : 1 ≤ N := by linarith only [hN2]
  have hK1 : 1 ≤ K := h.subpower.1 k
  have hK0 : 0 < K := by linarith only [hK1]
  have hKN' : K ≤ N := by simpa only [Real.rpow_one] using hKN
  have hv0 : 0 < v := lt_of_lt_of_le hRinv0 hv
  have hs0 : 0 < s := lt_of_lt_of_le hRinv0 hs
  have hsU : s ≤ cfg.U := by linarith only [hsv, hVU, hv0]
  have hκs : cfg.κ * s ≤ cfg.e₀ / 4 := by
    have : cfg.κ * s ≤ cfg.κ * V :=
      mul_le_mul_of_nonneg_left (by linarith only [hsv, hv0]) hκ0.le
    linarith only [this, hκV]
  have hκsR : cfg.κ * s ≤ R := by
    have : cfg.κ * s ≤ 1 * s := mul_le_mul_of_nonneg_right hκ1 hs0.le
    linarith only [this, hsR]
  have hℓ : cfg.ℓ = cfg.κ := h.equal_rate
  -- the atlas at the coarse label
  have ha := hatlas s hs hsU
  have hTlo : N ^ (cfg.κ * s) / K ≤ (2 : ℝ) ^ cfg.T k s := ha.1
  have hTup : (2 : ℝ) ^ cfg.T k s ≤ K * N ^ (cfg.κ * s) := ha.2.1
  obtain ⟨-, hBm, hBA⟩ := ha.2.2.1 i
  have hlab := ha.2.2.2.2.1 i
  simp only [zpow_neg, zpow_natCast] at hlab
  obtain ⟨hνA, -, -, hcl, -, hrows, -⟩ := hlab
  set q : ℝ := ((2 : ℝ) ^ cfg.T k s)⁻¹ with hqdef
  have hT0 : 0 < (2 : ℝ) ^ cfg.T k s := by positivity
  have hq0 : 0 < q := by positivity
  have hNκs : 0 < N ^ (cfg.κ * s) := Real.rpow_pos_of_pos hN0 _
  have hgq : N ^ (-cfg.ℓ * s) ≤ K * q := by
    rw [hℓ, neg_mul, Real.rpow_neg hN0.le, hqdef]
    rw [inv_le_iff_one_le_mul₀ hNκs]
    have := mul_le_mul_of_nonneg_left hTup (inv_pos.mpr hT0).le
    rw [inv_mul_cancel₀ hT0.ne'] at this
    calc (1 : ℝ) ≤ ((2 : ℝ) ^ cfg.T k s)⁻¹ * (K * N ^ (cfg.κ * s)) := this
      _ = K * ((2 : ℝ) ^ cfg.T k s)⁻¹ * N ^ (cfg.κ * s) := by ring
  have hqg : q ≤ K * N ^ (-cfg.ℓ * s) := by
    rw [hℓ, neg_mul, Real.rpow_neg hN0.le, hqdef]
    rw [inv_le_iff_one_le_mul₀ hT0]
    have := mul_le_mul_of_nonneg_left hTlo (by positivity : (0 : ℝ) ≤ K * (N ^ (cfg.κ * s))⁻¹)
    calc (1 : ℝ) = K * (N ^ (cfg.κ * s))⁻¹ * (N ^ (cfg.κ * s) / K) := by field_simp
      _ ≤ K * (N ^ (cfg.κ * s))⁻¹ * (2 : ℝ) ^ cfg.T k s := this
      _ = K * (N ^ (cfg.κ * s))⁻¹ * (2 : ℝ) ^ cfg.T k s := by ring
  have hqinv : q⁻¹ ≤ K * N ^ (cfg.e₀ / 4) := by
    rw [hqdef, inv_inv]
    exact hTup.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 hκs) hK0.le)
  -- centering of the label
  have hc := hcent s hs hsU (by linarith only [hκs, he₀]) i
  dsimp only at hc
  set t₀ : ℝ := ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s with ht₀def
  set J : ℝ := N ^ εc + K with hJdef
  have hNεc : 1 ≤ N ^ εc := Real.one_le_rpow hN1 hεc0.le
  have hJ0 : 0 ≤ J := by positivity
  have hmq : ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q = t₀ + q / 2 := by
    rw [ht₀def, hqdef, div_eq_mul_inv]; ring
  rw [hmq] at hc
  have hc0 := hcl 0
  have hc1 := hcl 1
  have hcenter : |cfg.c k s i 3 + (cfg.c k s i 0 + t₀ * cfg.c k s i 1)| ≤ J * q := by
    have e : cfg.c k s i 3 + (cfg.c k s i 0 + t₀ * cfg.c k s i 1) =
        (cfg.c k s i 3 + cfg.c k s i 0 + (t₀ + q / 2) * cfg.c k s i 1) - q / 2 * cfg.c k s i 1 := by
      ring
    rw [e]
    have h1 := abs_sub (cfg.c k s i 3 + cfg.c k s i 0 + (t₀ + q / 2) * cfg.c k s i 1)
      (q / 2 * cfg.c k s i 1)
    have h2 : |q / 2 * cfg.c k s i 1| ≤ q / 2 * K := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < q / 2)]
      exact mul_le_mul_of_nonneg_left hc1 (by positivity)
    have h3 := abs_nonneg (cfg.c k s i 4 - (t₀ + q / 2))
    have h4 : N ^ εc * q + q / 2 * K ≤ J * q := by
      have h5 : q / 2 * K ≤ K * q := by nlinarith only [hq0, hK0]
      rw [hJdef, add_mul]; linarith only [h5]
    linarith only [h1, h2, h3, h4, hc]
  have hpivot : |cfg.c k s i 4 - t₀| ≤ J * q := by
    have e : cfg.c k s i 4 - t₀ = (cfg.c k s i 4 - (t₀ + q / 2)) + q / 2 := by ring
    rw [e]
    have h1 := abs_add_le (cfg.c k s i 4 - (t₀ + q / 2)) (q / 2)
    have h2 : |q / 2| = q / 2 := abs_of_pos (by positivity)
    have h3 := abs_nonneg (cfg.c k s i 3 + cfg.c k s i 0 + (t₀ + q / 2) * cfg.c k s i 1)
    have h4 : N ^ εc * q + q / 2 ≤ J * q := by
      have h5 : q / 2 ≤ K * q := by nlinarith only [hq0, hK1]
      rw [hJdef, add_mul]; linarith only [h5]
    linarith only [h1, h2, h3, h4, hc]
  -- envelopes
  set E := K * N ^ εc with hEdef
  have hKE : K ≤ E := le_mul_of_one_le_right hK0.le hNεc
  have hJE : J ≤ 2 * E := by
    have h5 : N ^ εc ≤ K * N ^ εc := le_mul_of_one_le_left (by positivity) hK1
    have h6 : K ≤ K * N ^ εc := le_mul_of_one_le_right hK0.le hNεc
    rw [hJdef, hEdef]; linarith only [h5, h6]
  set Bz : ℝ := 2 * K + 2 * K ^ 2 + 2 * J * K + J with hBzdef
  have hBzE : Bz ≤ 10 * E ^ 2 := unitBox_le hK1 hKE hJE hJ0
  have hBz1 : 1 ≤ Bz := by
    have : 0 ≤ 2 * K ^ 2 + 2 * J * K + J := by positivity
    rw [hBzdef]; linarith only [this, hK1]
  have hBz0 : 0 < Bz := by linarith only [hBz1]
  have hE2 : E ^ 2 = K ^ 2 * N ^ (2 * εc) := by rw [hEdef, mul_pow, sq_rpow hN0]
  have hE4 : E ^ 4 = K ^ 4 * N ^ (4 * εc) := by
    rw [hEdef, mul_pow, ← Real.rpow_natCast (N ^ εc), ← Real.rpow_mul hN0.le]
    push_cast
    ring_nf
  have hBz2 : Bz ^ 2 ≤ 100 * (K ^ 4 * N ^ (4 * εc)) := by
    rw [← hE4]
    calc Bz ^ 2 ≤ (10 * E ^ 2) ^ 2 := pow_le_pow_left₀ hBz0.le hBzE 2
      _ = 100 * E ^ 4 := by ring
  -- the core numerics at this sample
  have hcorek := hcore q Bz hq0 hBz1 hqinv
  dsimp only at hcorek
  obtain ⟨hΛ1, hcon, hs1, hs2, hs3, -, hfinal⟩ := hcorek
  -- the residual caps in the form of the sample theorem
  have e1 : N ^ (-(s + v)) = N ^ (-s - v) := by ring_nf
  have e2 : N ^ (-3 * M - cfg.d * (s + v)) = (N ^ (-M)) ^ 3 * (N ^ (-s - v)) ^ cfg.d := by
    rw [← Real.rpow_natCast (N ^ (-M)), ← Real.rpow_mul hN0.le, ← Real.rpow_mul hN0.le,
      ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  have hres' := fun (τ' : Measure (α × ℝ)) (hτ' : τ' ≤ cfg.μ k)
      (hmass : ENNReal.ofReal (N ^ (-(5 * cfg.U + 10))) ≤ τ' univ) (L' : Fin 4 → ℝ)
      (hql : ∀ᵐ x ∂τ', |eval (cfg.x k x.1 x.2) (affineBase L') - (cfg.x k x.1 x.2) 3| ≤ 1 / 4)
      (Mm : Matrix (Fin 3) (Fin 3) ℝ) (bb : Fin 3 → ℝ) (hdet : Mm.det ≠ 0)
      (hrow : ∀ r, ∑ m, |Mm r m| ≤ N ^ (2 * R + 1)) => by
    have h0 := hres τ' hτ' hmass L' hql Mm bb hdet hrow M (s + v) vsep hRcM hMRc
      (by linarith only [hs0, hv0]) (by linarith only [h2RRc, hsR, hvR]) hRcvsep hvsepRc
    dsimp only at h0
    rw [e1, e2] at h0
    exact h0
  have hpal : ∀ a : ℤ, cfg.π k {w : ℝ | ⌊w / N ^ (-vsep)⌋ = a} ≤
      ENNReal.ofReal (K * (N ^ (-vsep)) ^ cfg.S) := by
    have h0 := (hcaps M 0 vsep hRcM hMRc le_rfl (by linarith only [hRc]) hRcvsep hvsepRc).1
    intro a
    have e3 : (N ^ (-vsep)) ^ cfg.S = N ^ (-cfg.S * vsep) := by
      rw [← Real.rpow_mul hN0.le]; ring_nf
    rw [e3]
    exact h0 a
  -- the remaining numerical conditions
  have hH1 : 1 ≤ N ^ η := Real.one_le_rpow hN1 hη0.le
  have hH2 : 1 + 4 * (N ^ η) ^ 2 ≤ 5 * N ^ (2 * η) := by
    rw [sq_rpow hN0]
    have : 1 ≤ N ^ (2 * η) := Real.one_le_rpow hN1 (by positivity)
    linarith only [this]
  have h6K : 6 * K + 5 ≤ 11 * K := by linarith only [hK1]
  have hrvS : (N ^ (-vsep)) ^ cfg.S = N ^ (-(4 * η)) := by
    rw [← Real.rpow_mul hN0.le, ← hSv]; ring_nf
  set c : ℝ := N ^ (-s - v) with hcdef
  have hc0 : 0 < c := by positivity
  have hg0 : 0 < N ^ (-cfg.ℓ * s) := by positivity
  set mE : ℝ := N ^ (-cfg.d * v - η) * q * ((N ^ (-s)) ^ cfg.d * q ^ 2 *
    N ^ (-cfg.ℓ * s) / K) with hmEdef
  have hmE : mE = N ^ (-η) * c ^ cfg.d * q ^ 3 * N ^ (-cfg.ℓ * s) / K := by
    rw [hmEdef, hcdef]
    have := rpow_mass_identity (N := N) (d := cfg.d) (s := s) (v := v) (η := η) hN0
    calc N ^ (-cfg.d * v - η) * q * ((N ^ (-s)) ^ cfg.d * q ^ 2 * N ^ (-cfg.ℓ * s) / K)
        = (N ^ (-cfg.d * v - η) * (N ^ (-s)) ^ cfg.d) * q ^ 3 * N ^ (-cfg.ℓ * s) / K := by ring
      _ = _ := by rw [this]
  have nvol := nvol_of (Λ := N ^ τ) (τ := τ) (η := η) (mE := mE) (d := cfg.d) (hm := N ^ (-M))
    hN0 hK1 hq0 hg0 hqg hH1 hBz0 (by positivity) hc0 rfl hmE (by
      have hA := hNA
      calc 497664 * K ^ 3 * (1 + 4 * (N ^ η) ^ 2) * (6 * K + 5) * Bz ^ 2 * N ^ η
          ≤ 497664 * K ^ 3 * (5 * N ^ (2 * η)) * (11 * K) * (100 * (K ^ 4 * N ^ (4 * εc))) *
              N ^ η := by gcongr
        _ = 497664 * 5 * 11 * 100 * K ^ 8 * (N ^ (2 * η) * N ^ (4 * εc) * N ^ η) := by ring
        _ = 497664 * 5 * 11 * 100 * K ^ 8 * N ^ (3 * η + 4 * εc) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
        _ ≤ N ^ τ := hA.le)
  have nvel := nvel_of (S := cfg.S) (η := η) (mE := mE) (d := cfg.d) (hm := N ^ (-M))
    (rv := N ^ (-vsep)) hN0 hK1 hq0 hg0 hqg hH1 hBz0 (by positivity) hc0 (by positivity) hmE (by
      have hB := hNB
      have hNη4 : 0 < N ^ (-(4 * η)) := by positivity
      calc 15925248 * (1 + 4 * (N ^ η) ^ 2) * (6 * K + 5) * K ^ 4 * Bz ^ 2 *
            (N ^ (-vsep)) ^ cfg.S * N ^ η
          ≤ 15925248 * (5 * N ^ (2 * η)) * (11 * K) * K ^ 4 *
              (100 * (K ^ 4 * N ^ (4 * εc))) * N ^ (-(4 * η)) * N ^ η := by
            rw [hrvS]; gcongr
        _ = (15925248 * 5 * 11 * 100 * K ^ 9 * (N ^ (2 * η) * N ^ (4 * εc) * N ^ η)) *
              N ^ (-(4 * η)) := by ring
        _ = (15925248 * 5 * 11 * 100 * K ^ 9 * N ^ (3 * η + 4 * εc)) * N ^ (-(4 * η)) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
        _ < N ^ (4 * η) * N ^ (-(4 * η)) := mul_lt_mul_of_pos_right hB hNη4
        _ = 1 := by rw [← Real.rpow_add hN0]; simp)
  have nmass : N ^ (-(5 * cfg.U + 10)) ≤ N ^ (-cfg.d * v - η) * q *
      ((N ^ (-s)) ^ cfg.d * q ^ 2 * N ^ (-cfg.ℓ * s) / K) / 18 := by
    have h0 := retained_original_reference_power_floor hN2 hK1 hKN' hd0 hd1.le hκ0.le hκ1
      hs0.le hv0.le (hsv.trans hVU) hη1 hTup
    rw [hℓ]
    exact h0
  have hNR : N ^ (cfg.κ * s) ≤ N ^ R := Real.rpow_le_rpow_of_exponent_le hN1 hκsR
  have hNR0 : 0 < N ^ R := by positivity
  have hNR2 : N ^ R ≤ N ^ (2 * R) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hR0])
  have hRsq : (N ^ R) ^ 2 = N ^ (2 * R) := sq_rpow hN0
  have nrows : (1 + |t₀| + |cfg.c k s i 0 + t₀ * cfg.c k s i 1|) * (q⁻¹ + (q ^ 2)⁻¹) ≤
      N ^ (2 * R + 1) := by
    have ht0 : 0 ≤ t₀ := by positivity
    have ht1 : t₀ ≤ 1 := by
      rw [ht₀def, div_le_one hT0]
      exact_mod_cast (cfg.j k s i).isLt.le
    have hZ : |cfg.c k s i 0 + t₀ * cfg.c k s i 1| ≤ 2 * K := by
      calc _ ≤ |cfg.c k s i 0| + |t₀ * cfg.c k s i 1| := abs_add_le _ _
        _ ≤ K + 1 * K := by
          rw [abs_mul, abs_of_nonneg ht0]
          gcongr
        _ = 2 * K := by ring
    have hqi : q⁻¹ ≤ K * N ^ R := by
      rw [hqdef, inv_inv]
      exact hTup.trans (mul_le_mul_of_nonneg_left hNR hK0.le)
    have hqi2 : (q ^ 2)⁻¹ ≤ K ^ 2 * N ^ (2 * R) := by
      rw [← inv_pow]
      calc q⁻¹ ^ 2 ≤ (K * N ^ R) ^ 2 := pow_le_pow_left₀ (by positivity) hqi 2
        _ = K ^ 2 * N ^ (2 * R) := by rw [mul_pow, hRsq]
    have hsum : q⁻¹ + (q ^ 2)⁻¹ ≤ 2 * K ^ 2 * N ^ (2 * R) := by
      have : K * N ^ R ≤ K ^ 2 * N ^ (2 * R) := by
        have hKK : K ≤ K ^ 2 := by nlinarith only [hK1]
        exact mul_le_mul hKK hNR2 hNR0.le (by positivity)
      linarith only [hqi, hqi2, this]
    have hfirst : 1 + |t₀| + |cfg.c k s i 0 + t₀ * cfg.c k s i 1| ≤ 4 * K := by
      rw [abs_of_nonneg ht0]; linarith only [ht1, hZ, hK1]
    have hH := hNH
    calc (1 + |t₀| + |cfg.c k s i 0 + t₀ * cfg.c k s i 1|) * (q⁻¹ + (q ^ 2)⁻¹)
        ≤ (4 * K) * (2 * K ^ 2 * N ^ (2 * R)) := by
          gcongr
      _ = 8 * K ^ 3 * N ^ (2 * R) := by ring
      _ ≤ N ^ (2 * R + 1) := hH.le
  -- the frozen-fiber Lipschitz conditions
  set SB : ℝ := 7 + 4 * (K + K) + (K + K + K * (K + K)) + 34 * Bz with hSBdef
  have hSB : SB ≤ 360 * E ^ 2 := by
    have hKE2 : K ≤ E ^ 2 := by nlinarith only [hKE, hK1]
    have hK2E2 : K ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hK0.le hKE 2
    have h1E : 1 ≤ E ^ 2 := by nlinarith only [hKE, hK1]
    rw [hSBdef]; linarith only [hKE2, hK2E2, h1E, hBzE]
  have hSB0 : 0 ≤ SB := by rw [hSBdef]; positivity
  have hSB2 : SB ^ 2 ≤ 129600 * (K ^ 4 * N ^ (4 * εc)) := by
    rw [← hE4]
    calc SB ^ 2 ≤ (360 * E ^ 2) ^ 2 := pow_le_pow_left₀ hSB0 hSB 2
      _ = 129600 * E ^ 4 := by ring
  have hNM : N ^ R * N ^ (-M) * N ^ (4 * εc) = N ^ (R + 4 * εc - M) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
  have nlip : 2 * (81 * N ^ R * SB ^ 2) * (3 * N ^ (-M)) ≤ N ^ η * N ^ (-s - v) := by
    have hF := hNF
    have hlow : N ^ (-(2 * R)) ≤ N ^ η * N ^ (-s - v) := by
      rw [← Real.rpow_add hN0]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hsR, hvR, hη0])
    calc 2 * (81 * N ^ R * SB ^ 2) * (3 * N ^ (-M))
        ≤ 2 * (81 * N ^ R * (129600 * (K ^ 4 * N ^ (4 * εc)))) * (3 * N ^ (-M)) := by gcongr
      _ = 486 * 129600 * K ^ 4 * (N ^ R * N ^ (-M) * N ^ (4 * εc)) := by ring
      _ = 486 * 129600 * K ^ 4 * N ^ (R + 4 * εc - M) := by rw [hNM]
      _ ≤ N ^ (-(2 * R)) := hF.le
      _ ≤ _ := hlow
  have nlip' : 2 * (2 * (81 * N ^ R * SB ^ 2)) * (3 * N ^ (-M)) ≤ (N ^ η)⁻¹ / 2 := by
    have hG := hNG
    have hlow : N ^ (-2 : ℝ) ≤ (N ^ η)⁻¹ := by
      rw [← Real.rpow_neg hN0.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hη1])
    calc 2 * (2 * (81 * N ^ R * SB ^ 2)) * (3 * N ^ (-M))
        ≤ 2 * (2 * (81 * N ^ R * (129600 * (K ^ 4 * N ^ (4 * εc))))) * (3 * N ^ (-M)) := by
          gcongr
      _ = (2 * (972 * 129600) * K ^ 4 * (N ^ R * N ^ (-M) * N ^ (4 * εc))) / 2 := by ring
      _ = (2 * (972 * 129600) * K ^ 4 * N ^ (R + 4 * εc - M)) / 2 := by rw [hNM]
      _ ≤ N ^ (-2 : ℝ) / 2 := by gcongr
      _ ≤ (N ^ η)⁻¹ / 2 := by gcongr
  -- separation, scale and remaining conditions
  have nsep : (N ^ τ)⁻¹ ≤ N ^ (-vsep) / 2 / (8 * Bz) := by
    have hC := hNC
    have h16 : 16 * Bz ≤ 160 * (K ^ 2 * N ^ (2 * εc)) := by
      rw [← hE2]; linarith only [hBzE]
    have hprod : 16 * Bz * N ^ vsep ≤ N ^ τ := by
      calc 16 * Bz * N ^ vsep ≤ 160 * (K ^ 2 * N ^ (2 * εc)) * N ^ vsep := by gcongr
        _ = 160 * K ^ 2 * N ^ (2 * εc + vsep) := by rw [Real.rpow_add hN0]; ring
        _ ≤ N ^ τ := hC.le
    have hNτ : 0 < N ^ τ := by positivity
    have hNv : 0 < N ^ vsep := by positivity
    rw [Real.rpow_neg hN0.le, div_div, le_div_iff₀ (by positivity),
      inv_mul_le_iff₀ hNτ]
    calc 2 * (8 * Bz) = 16 * Bz * N ^ vsep * (N ^ vsep)⁻¹ := by field_simp; ring
      _ ≤ N ^ τ * (N ^ vsep)⁻¹ := by gcongr
  have nH : N ^ η ≤ N ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hητ, hτ0])
  have ntrim : 2 * K * (2 * N ^ (-M)) ≤ N ^ (-cfg.d * v - η) := by
    have hE' := hNE
    have hdv : cfg.d * v ≤ R := by
      have : cfg.d * v ≤ 1 * v := mul_le_mul_of_nonneg_right hd1.le hv0.le
      linarith only [this, hvR]
    calc 2 * K * (2 * N ^ (-M)) = 4 * K ^ 1 * N ^ (-M) := by ring
      _ ≤ N ^ (-R - 1) := hE'.le
      _ ≤ N ^ (-cfg.d * v - η) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hdv, hη1])
  have nfinm : 36 * N ^ (-cfg.d * v - ε) ≤ N ^ (-cfg.d * v - η) := by
    have hJ' := hNJ
    simp only [pow_zero, mul_one, Real.rpow_zero] at hJ'
    calc 36 * N ^ (-cfg.d * v - ε) ≤ N ^ (ε - η) * N ^ (-cfg.d * v - ε) := by
          gcongr
      _ = N ^ (-cfg.d * v - η) := by rw [← Real.rpow_add hN0]; ring_nf
  have hhm8 : N ^ (-M) ≤ 1 / 8 := by
    have h8' := hN8
    simp only [pow_zero, mul_one, Real.rpow_zero] at h8'
    linarith only [h8']
  have nfin : N ^ (-s - v) * coreLoss Cs (N ^ τ) ≤ N ^ ε * N ^ (-s - v) :=
    hfinal ε (N ^ (-s - v)) hτε (by positivity)
  exact affine_candidate_at h (hm := N ^ (-M)) (rv := N ^ (-vsep)) (Λ := N ^ τ) (Cs := Cs)
    (J := J) (B₀ := 5 * cfg.U + 10) (A₀ := 2 * R + 1) (by positivity) hhm8 (by positivity)
    hΛ1 hCs hCs0 hJ0 hN2 hK1 hη0.le hBm hBA hcl hgq hqg hνA hrows hcenter hpivot hres' hpal
    nmass nrows nlip nlip' nvel nvol nsep nH hcon hs1 hs2 hs3 ntrim nfin nfinm hshift

end Model

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
