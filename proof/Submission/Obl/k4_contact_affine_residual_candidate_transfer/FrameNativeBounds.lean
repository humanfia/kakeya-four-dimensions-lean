import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FramePriors
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameLaw
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameSourceNumerics
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ContactMatrixBounds

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- Every original grid label has its contact-volume prior floor, before
the successful history is selected. -/
theorem FrameGood.original_node_profile (hg : FrameGood f Rk θ K₂ e₀')
    {h : ℕ} (hh : h ≤ f.m) (i : Fin (f.nl h)) :
    (D.N k ^ (-f.depth h)) ^ D.d * f.ql h ^ 3 ≤
      D.K k ^ 2 * (D.ν k).real (D.A k (f.depth h) i) := by
  have hK : 0 < D.K k := by linarith [hg.K_ge]
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hcount : D.N k ^ (D.κ * f.depth h) / D.K k ≤ (f.ql h)⁻¹ := by
    simpa [Frame.ql, zpow_neg, zpow_natCast] using (hg.count h hh).1
  have hqg : f.ql h ≤ D.K k * D.N k ^ (-D.ℓ * f.depth h) := by
    simpa only [hg.ℓ_eq] using parent_length_upper hN hK (f.ql_pos h) hcount
  have hf := hg.floor_real hh i
  have hfm := (div_le_iff₀ hK).mp hf
  have hq := mul_le_mul_of_nonneg_left hqg
    (mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hN.le (-f.depth h)) D.d)
      (sq_nonneg (f.ql h)))
  have hh := mul_le_mul_of_nonneg_left hfm hK.le
  nlinarith only [hq, hh]

/-- The full original parent prior has its fourth-dimensional reference
scale, before the successful history is selected. -/
theorem FrameGood.original_parent_profile (hg : FrameGood f Rk θ K₂ e₀') :
    f.a₀ ^ D.d * f.q₀ ^ 3 ≤ D.K k ^ 2 * (D.ν k).real (D.A k (f.depth 0) f.i₀) := by
  simpa only [Frame.a₀, f.q₀_eq] using hg.original_node_profile (Nat.zero_le _) f.i₀

/-- The inverse parent reference costs only `K^3 / theta`, after its
contact-chart determinant and its coarse scalar thickness cancel. -/
theorem FrameGood.native_reference_bound (hg : FrameGood f Rk θ K₂ e₀') :
    |(contactFrameMatrix f.t₀ f.q₀ f.Z₀).det|⁻¹ * D.N k ^ (-D.d * s₀) ≤
      (D.K k ^ 3 / θ) * (f.q₀ * (D.ν k).real f.parentSet) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hp := hg.prior_floor_real (Nat.zero_le _) f.i₀ f.u₀ hg.parent_retained
  change θ * (D.ν k).real (D.A k (f.depth 0) f.i₀) ≤
    D.K k * (D.ν k).real f.parentSet at hp
  have hbase := mul_le_mul_of_nonneg_left hg.original_parent_profile hg.θ_pos.le
  have hprior := mul_le_mul_of_nonneg_left hp (sq_nonneg (D.K k))
  have hscaled : θ * (f.a₀ ^ D.d * f.q₀ ^ 3) ≤ D.K k ^ 3 * (D.ν k).real f.parentSet := by
    nlinarith only [hbase, hprior]
  have hpower : f.a₀ ^ D.d = D.N k ^ (-D.d * s₀) := by
    rw [Frame.a₀, hg.depth_zero, ← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [det_contactFrameMatrix, abs_inv, inv_inv,
    abs_of_nonneg (pow_nonneg f.q₀_pos.le 4), ← hpower,
    div_mul_eq_mul_div, le_div_iff₀ hg.θ_pos]
  have hh := mul_le_mul_of_nonneg_left hscaled f.q₀_pos.le
  nlinarith only [hh]

/-- A source-mass floor in original units follows from the parent event
floor. It can be compared with a fixed power before invoking native
calibration, without using successful incidence mass as a normalizer. -/
theorem FrameGood.native_core_mass (hg : FrameGood f Rk θ K₂ e₀') :
    ENNReal.ofReal (θ * f.a₀ ^ D.d * f.q₀ ^ 4 / D.K k ^ 2) ≤ D.μ k f.core := by
  letI : IsProbabilityMeasure (D.ν k) := hg.νprob
  have hK : 0 < D.K k := by linarith [hg.K_ge]
  have hm := hg.core_floor 0 (Nat.zero_le _) f.i₀ f.u₀ hg.parent_retained
  have heq : f.event 0 f.i₀ f.u₀ ∩ f.core = f.core :=
    inter_eq_right.mpr hg.core_parent_event
  rw [heq] at hm
  have hnumeric : θ * f.a₀ ^ D.d * f.q₀ ^ 4 / D.K k ^ 2 ≤
      (θ * f.q₀) * (D.ν k).real (D.A k (f.depth 0) f.i₀) := by
    apply (div_le_iff₀ (sq_pos_of_pos hK)).mpr
    have hh := mul_le_mul_of_nonneg_left hg.original_parent_profile
      (mul_nonneg hg.θ_pos.le f.q₀_pos.le)
    nlinarith only [hh]
  calc
    _ ≤ ENNReal.ofReal ((θ * f.q₀) * (D.ν k).real (D.A k (f.depth 0) f.i₀)) :=
      ENNReal.ofReal_le_ofReal hnumeric
    _ = ENNReal.ofReal (θ * f.ql 0) * D.ν k (D.A k (f.depth 0) f.i₀) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hg.θ_pos.le f.q₀_pos.le),
        ofReal_measureReal, ← f.q₀_eq]
    _ ≤ _ := hm

/-- A retained child's source has a fixed-power floor in ORIGINAL units.
The bound is uniform over every node at depth at most `S`. -/
theorem FrameGood.native_node_fixed_power (hg : FrameGood f Rk θ K₂ e₀')
    {h : ℕ} (hh : h ≤ f.m) (i : Fin (f.nl h)) (u : EntryHistory f.M h)
    (hne : (f.event h i u ∩ f.core).Nonempty) {S : ℝ}
    (hs : 0 ≤ f.depth h) (hsS : f.depth h ≤ S) (hd : D.d ≤ 1) (hκ : D.κ ≤ 1)
    (hKN : D.K k ≤ D.N k) (hθ : D.N k ^ (-1 : ℝ) ≤ θ) :
    ENNReal.ofReal (D.N k ^ (-(5 * S + 7))) ≤ D.μ k (f.event h i u ∩ f.core) := by
  letI : IsProbabilityMeasure (D.ν k) := hg.νprob
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hK : 0 < D.K k := by linarith [hg.K_ge]
  have hcount : (f.ql h)⁻¹ ≤ D.K k * D.N k ^ (D.κ * f.depth h) := by
    simpa [Frame.ql, zpow_neg, zpow_natCast] using (hg.count h hh).2
  have hq := parent_length_power_lower hN (f.ql_pos h) hKN hcount
  have hnum := fixed_parent_mass_power_bound hg.N_ge hg.K_ge hKN hθ hs hd hκ hq
  have hprofile := mul_le_mul_of_nonneg_left (hg.original_node_profile hh i)
    (mul_nonneg hg.θ_pos.le (f.ql_pos h).le)
  have hscaled : θ * (D.N k ^ (-f.depth h)) ^ D.d * f.ql h ^ 4 / D.K k ^ 2 ≤
      (θ * f.ql h) * (D.ν k).real (D.A k (f.depth h) i) := by
    apply (div_le_iff₀ (sq_pos_of_pos hK)).mpr
    nlinarith only [hprofile]
  calc
    _ ≤ ENNReal.ofReal (D.N k ^ (-(5 * f.depth h + 7))) := ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (by linarith [hg.N_ge]) (by linarith))
    _ ≤ ENNReal.ofReal (θ * (D.N k ^ (-f.depth h)) ^ D.d * f.ql h ^ 4 / D.K k ^ 2) :=
      ENNReal.ofReal_le_ofReal hnum
    _ ≤ ENNReal.ofReal ((θ * f.ql h) * (D.ν k).real (D.A k (f.depth h) i)) :=
      ENNReal.ofReal_le_ofReal hscaled
    _ = ENNReal.ofReal (θ * f.ql h) * D.ν k (D.A k (f.depth h) i) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hg.θ_pos.le (f.ql_pos h).le), ofReal_measureReal]
    _ ≤ _ := hg.core_floor h hh i u hne

/-- A fixed-power floor for the actual retained source, uniform in the
affine parent and its coefficients. The two extra assumptions hold late
for a subpower atlas constant and a subpower history loss. -/
theorem FrameGood.native_core_fixed_power (hg : FrameGood f Rk θ K₂ e₀')
    (hs₀ : 0 ≤ s₀) (hd : D.d ≤ 1) (hκ : D.κ ≤ 1)
    (hKN : D.K k ≤ D.N k) (hθ : D.N k ^ (-1 : ℝ) ≤ θ) :
    ENNReal.ofReal (D.N k ^ (-(5 * s₀ + 7))) ≤ D.μ k f.core := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have hq := parent_length_power_lower hN f.q₀_pos hKN hg.q₀_le_K.2
  have hh := fixed_parent_mass_power_bound hg.N_ge hg.K_ge hKN hθ hs₀ hd hκ hq
  have ha : f.a₀ = D.N k ^ (-s₀) := by rw [Frame.a₀, hg.depth_zero]
  calc
    _ ≤ ENNReal.ofReal (θ * f.a₀ ^ D.d * f.q₀ ^ 4 / D.K k ^ 2) :=
      ENNReal.ofReal_le_ofReal (by simpa only [ha] using hh)
    _ ≤ _ := hg.native_core_mass

/-- Parent matrix rows have a fixed-power bound, uniformly in every
palette entry. In particular the unbounded hidden affine coefficients do
not enter the mesh-transport cost. -/
theorem FrameGood.native_matrix_rows (hg : FrameGood f Rk θ K₂ e₀')
    (hs₀ : 0 ≤ s₀) (hκ : D.κ ≤ 1) (hKN : D.K k ≤ D.N k) (i : Fin 3) :
    (∑ j, |contactFrameMatrix f.t₀ f.q₀ f.Z₀ i j|) ≤ D.N k ^ (2 * s₀ + 5) := by
  have hpow : 0 < (2 : ℝ) ^ f.T₀ := by positivity
  have hpow₁ : 1 ≤ (2 : ℝ) ^ f.T₀ := one_le_pow₀ (by norm_num)
  have hq₁ : f.q₀ ≤ 1 := by
    change ((2 : ℝ) ^ f.T₀)⁻¹ ≤ 1
    exact (inv_le_one₀ hpow).mpr hpow₁
  have ht₀ : 0 ≤ f.t₀ := by unfold Frame.t₀ Frame.left; positivity
  have ht₁ : f.t₀ ≤ 1 := by
    change ((D.j k (f.depth 0) f.i₀ : ℕ) : ℝ) / (2 : ℝ) ^ f.T₀ ≤ 1
    apply (div_le_one hpow).mpr
    have hh := (D.j k (f.depth 0) f.i₀).isLt
    have hh' : ((D.j k (f.depth 0) f.i₀ : ℕ) : ℝ) < (2 : ℝ) ^ f.T₀ := by
      exact_mod_cast hh
    exact hh'.le
  have ht : |f.t₀| ≤ 1 := by rw [abs_of_nonneg ht₀]; exact ht₁
  have hZ : |f.Z₀| ≤ 2 * D.K k := by
    change |D.c k (f.depth 0) f.i₀ 0 + f.t₀ * D.c k (f.depth 0) f.i₀ 1| ≤ _
    calc
      _ ≤ |D.c k (f.depth 0) f.i₀ 0| + |f.t₀| * |D.c k (f.depth 0) f.i₀ 1| := by
        simpa only [abs_mul] using abs_add_le (D.c k (f.depth 0) f.i₀ 0)
          (f.t₀ * D.c k (f.depth 0) f.i₀ 1)
      _ ≤ D.K k + 1 * D.K k := add_le_add (hg.cbound 0 (Nat.zero_le _) f.i₀ 0)
        (mul_le_mul ht (hg.cbound 0 (Nat.zero_le _) f.i₀ 1) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  exact contactFrameMatrix_row_power_bound hg.N_ge hg.K_ge hKN hs₀ hκ f.q₀_pos hq₁ ht hZ
    hg.q₀_le_K.2 i

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
