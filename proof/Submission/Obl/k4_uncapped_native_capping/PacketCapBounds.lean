/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/PacketCapBounds.lean. Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.Definitions
import Submission.Obl.k4_uncapped_native_capping.UWE.PacketCaps

/-!
# Projected caps of a prepared, balanced, tangentially full packet

Fix one sample index `k` and one world `γ` of a valid problem `p` with `p.L = 1`.
For a measurable packet `F ⊆ p.E k γ`, restrict the original incidence law to `F` and to
the complement of the finite density-preparation bad set:

  `ρ := ((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)`.

Any sub-law `law ≤ (ofReal q * ν Aset)⁻¹ • ρ.map (z ↦ (z.1, (z.2 - t₀) / q))` of the
unit-block law of `ρ` then satisfies, with `N := p.N k`, `f := p.f` and the balance
`N ^ (-f 0) * |det Q| ≤ N ^ β * ν(Aset)`:

* `packet_pure_cap`: the continuous projected pure cap
  `law {base ∈ U ∧ signal bin = j} ≤ N ^ (-f r + f 0 + τ + ε + β) * 256 κ² K² * vol U`;
* `packet_mesh_cap`: the same cap on every scalar mesh cell, with `vol U` replaced by `σ ^ 2`;
* `packet_angular_cap` and `packet_mesh_angular_cap`: the angular caps, with the extra
  factor `N ^ (-S θ + 2 τ + S ε) * (8 K₀ + 2) ^ 2`.

All analytical inputs are taken from the frozen problem `p.Valid S η` and from the
`UWE` cap package of this obligation.
-/

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.PacketCapBounds

open MeasureTheory Set
open Submission.Obl.k4_uncapped_native_capping.UWE hiding scalarX scalarY

/-! ### Clauses of the frozen problem at one sample index and one world -/

section Clauses

variable {p : Problem} {S η : ℝ}

theorem valid_two_le_N (hp : p.Valid S η) (k : ℕ) : 2 ≤ p.N k := hp.1 k

theorem valid_L_pos (hp : p.Valid S η) : 0 < p.L := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  exact hL

theorem valid_S_pos (hp : p.Valid S η) : 0 < S := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  exact hS

theorem valid_world (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) :
    0 < p.B k γ ∧ (p.P k γ).totalDegree ≤ 2 := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  obtain ⟨M, D, hreg⟩ := hdata
  rcases (hreg k).2.2.2.1 γ with
    ⟨hν, hB, hBu, hBi, hP, hPc, hνfmt, hE, hEI, hEb, hEf, hprior, hfloor⟩
  exact ⟨hB, hP⟩

theorem valid_pure_law (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) {r : ℝ}
    (hr0 : 0 ≤ r) (hrL : r ≤ p.L) :
    Measurable (p.g k γ r) ∧
      (((p.ν k γ).prod volume).restrict (p.E k γ)).map (obs (p.B k γ) (δ (p.N k) r)) =
        (volume.prod Measure.count).withDensity (p.g k γ r) := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  exact hg k γ r hr0 hrL

theorem valid_angular_law (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ η * p.L) :
    Measurable (p.G k γ u) ∧
      (((p.ν k γ).prod volume).restrict (p.E k γ)).map
          (fun z : Incidence => (obs (p.B k γ) (δ (p.N k) p.L) z,
            nativeAngularBin (δ (p.N k) u) z)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (p.G k γ u) := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  exact hG k γ u hu huη

theorem valid_profile_lipschitz (hp : p.Valid S η) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ p.L) : p.f b - p.f a ≤ b - a := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  exact (hmono a b ha hab hb).2

/-- The native a.e. bounds of the original incidence law, with any `κ ≥ K k`. -/
theorem ae_native_bounds (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k))
    {κ : ℝ} (hKκ : p.K k ≤ κ) :
    ∀ᵐ z ∂(((p.ν k γ).prod volume).restrict (p.E k γ)),
      z.2 ∈ Icc (0 : ℝ) 1 ∧ ‖y z.1 z.2‖ ≤ κ ∧
      |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ))| ≤
        κ * p.B k γ ∧
      |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ)))| ≤ κ * p.B k γ ^ 2 ∧
      p.B k γ / κ ≤
        |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ))| := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hdata, hg, hG, hmono, htyp, hcap, hang⟩
  obtain ⟨M, D, hreg⟩ := hdata
  rcases (hreg k).2.2.2.1 γ with
    ⟨hν, hB, hBu, hBi, hP, hPc, hνfmt, hE, hEI, hEb, hEf, hprior, hfloor⟩
  have hprior' := ae_restrict_of_ae (s := p.E k γ)
    ((Measure.quasiMeasurePreserving_fst (μ := p.ν k γ) (ν := (volume : Measure ℝ))).ae hprior)
  have hK0 : 0 < p.K k := lt_of_lt_of_le zero_lt_one (hK.1 k)
  filter_upwards [ae_restrict_mem hE, hprior', hfloor] with z hz hpr hfl
  have ht := (hEI hz).2
  obtain ⟨hy, -, hdv, hddv⟩ := hpr z.2 ht
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · linarith [norm_nonneg (v z.1)]
  · exact hdv.trans (mul_le_mul_of_nonneg_right hKκ hB.le)
  · exact hddv.trans (mul_le_mul_of_nonneg_right hKκ (by positivity))
  · exact (div_le_div_of_nonneg_left hB.le hK0 hKκ).trans hfl

theorem nativeWidth_zero (N : ℝ) : δ N 0 = 1 := by
  simp [δ]

/-- The three original observation laws of one world, with their densities exposed
definitionally as `g L`, `g 0` and `G u`. -/
def angularSample (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) {u : ℝ} (hu : 0 < u)
    (huη : u ≤ η * p.L) :
    NativeAngularSample (((p.ν k γ).prod volume).restrict (p.E k γ))
      (p.N k) p.L (p.B k γ) (δ (p.N k) u) where
  terminalDensity := p.g k γ p.L
  zeroDensity := p.g k γ 0
  jointDensity := p.G k γ u
  measurable_terminal := (valid_pure_law hp k γ (valid_L_pos hp).le le_rfl).1
  measurable_zero := (valid_pure_law hp k γ le_rfl (valid_L_pos hp).le).1
  measurable_joint := (valid_angular_law hp k γ hu huη).1
  terminal_law := (valid_pure_law hp k γ (valid_L_pos hp).le le_rfl).2
  zero_law := by
    have h := (valid_pure_law hp k γ le_rfl (valid_L_pos hp).le).2
    rwa [nativeWidth_zero] at h
  joint_law := (valid_angular_law hp k γ hu huη).2

end Clauses

/-! ### Caps of the prepared packet restriction of the original law -/

section Original

variable {p : Problem} {S η : ℝ}

/-- The prepared packet restriction lies below the original incidence law. -/
theorem prepared_le_incidence (k : ℕ) (γ : Fin (p.W k)) (R A : Finset ℝ) (τ : ℝ)
    {F : Set Incidence} (hFE : F ⊆ p.E k γ) :
    ((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ) ≤
      ((p.ν k γ).prod volume).restrict (p.E k γ) :=
  Measure.restrict_mono (fun _ hz => hFE hz.1) le_rfl

/-- Almost every point of the prepared packet restriction is a good point of `F`. -/
theorem ae_prepared_mem (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k)) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L) (τ : ℝ)
    {F : Set Incidence} (hF : MeasurableSet F) :
    ∀ᵐ z ∂(((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)),
      z ∈ F ∧ z ∉ densityPreparationBad p S R A τ k γ :=
  ae_restrict_mem (hF.inter (hp.measurableSet_densityPreparationBad R A hR hA τ k γ).compl)

/-- The continuous projected pure cap of the prepared packet restriction of the
original law, at every signal depth `r ∈ [0, s]`. -/
theorem prepared_projected_cap (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k))
    (R A : Finset ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L)
    {s ε τ : ℝ} (hε : 0 < ε) (hsL : s ≤ p.L) (hRgrid : coarseDepthGrid s ε ⊆ R)
    (F : Set Incidence) (hF : MeasurableSet F) (hFE : F ⊆ p.E k γ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (c u e : EuclideanSpace ℝ (Fin 2))
    (t₀ Z : ℝ) {q K κ : ℝ} (hq : 0 < q) (hK : 0 < K) (hκ : 1 ≤ κ) (hKκ : p.K k ≤ κ)
    (hframe : ∀ z ∈ F, ‖Matrix.toEuclideanLin Q⁻¹ (y z.1 z.2 - c - z.2 • u)‖ ≤ K)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (r : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (j : ℤ) (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hU : MeasurableSet U) :
    ((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)
        {z | packetProjection e t₀ Z q z ∈ U ∧
          ⌊MvPolynomial.eval (x z.1 z.2) (p.P k γ) / p.N k ^ (-r)⌋ = j} ≤
      ENNReal.ofReal (p.N k ^ (-p.f r + τ + ε)) * ENNReal.ofReal (64 * κ ^ 2) *
        ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) * volume U := by
  have hρμ := prepared_le_incidence (S := S) k γ R A τ hFE
  have hmem := ae_prepared_mem hp k γ R A hR hA τ hF
  obtain ⟨hB, hP⟩ := valid_world hp k γ
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (valid_two_le_N hp k)
  refine native_grid_projected_cap (((p.ν k γ).prod volume).restrict (p.E k γ)) _ hρμ hN hε
    hκ hB p.f (fun a b ha hab hb => valid_profile_lipschitz hp ha hab (hb.trans hsL))
    (p.P k γ) hP (p.g k γ)
    (fun r hr => (valid_pure_law hp k γ (hR r (hRgrid hr)).1 (hR r (hRgrid hr)).2).1)
    (fun r hr => (valid_pure_law hp k γ (hR r (hRgrid hr)).1 (hR r (hRgrid hr)).2).2)
    (fun r' hr' => ?_) (ae_mono hρμ (ae_native_bounds hp k γ hKκ)) Q hQ e c u t₀ Z hK hq
    hfull ?_ r hr hrs j U hU
  · filter_upwards [hmem] with z hz
    exact (p.pure_density_band_of_not_bad S R A τ k γ z hz.2
      (Finset.mem_insert_of_mem (hRgrid hr'))).2
  · filter_upwards [hmem] with z hz
    exact hframe z hz.1

/-- The continuous projected angular cap of the prepared packet restriction of the
original law, at every signal depth `r ∈ [0, s]` and angular depth `θ ∈ (0, Adepth]`. -/
theorem prepared_projected_angular_cap (hp : p.Valid S η) (k : ℕ) (γ : Fin (p.W k))
    (R A : Finset ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L)
    {s ε τ Adepth : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (hsL : s ≤ p.L)
    (hRgrid : coarseDepthGrid s ε ⊆ R) (hAgrid : ∀ u ∈ coarseDepthGrid Adepth ε, 0 < u → u ∈ A)
    (F : Set Incidence) (hF : MeasurableSet F) (hFE : F ⊆ p.E k γ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (c u e : EuclideanSpace ℝ (Fin 2))
    (he : ‖e‖ = 1) (t₀ Z : ℝ) {q K κ : ℝ} (hq : 0 < q) (hK : 0 < K) (hκ : 1 ≤ κ)
    (hKκ : p.K k ≤ κ)
    (hframe : ∀ z ∈ F, ‖Matrix.toEuclideanLin Q⁻¹ (y z.1 z.2 - c - z.2 • u)‖ ≤ K)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (β' : ℝ) {K₀ g₀ : ℝ} (hK₀ : 1 ≤ K₀) (hg₀ : 0 ≤ g₀) (hg₀A : g₀ ≤ p.N k ^ (-Adepth))
    (hnormal : ∀ z ∈ F, |inner ℝ n (v z.1) - β'| ≤ K₀ * g₀)
    (r θ : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (hθ : 0 < θ) (hθA : θ ≤ Adepth)
    (j kk : ℤ) (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U) :
    ((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)
        {z | packetProjection e t₀ Z q z ∈ U ∧
          ⌊MvPolynomial.eval (x z.1 z.2) (p.P k γ) / p.N k ^ (-r)⌋ = j ∧
          ⌊inner ℝ e (v z.1) / p.N k ^ (-θ)⌋ = kk} ≤
      ENNReal.ofReal (p.N k ^ (-S * θ + 2 * τ + S * ε)) *
        ENNReal.ofReal ((8 * K₀ + 2) ^ 2) * ENNReal.ofReal (p.N k ^ (-p.f r + τ + ε)) *
        ENNReal.ofReal (64 * κ ^ 2) * ENNReal.ofReal (4 * K ^ 2 * q * |Q.det|) *
        volume U := by
  have hρμ := prepared_le_incidence (S := S) k γ R A τ hFE
  have hmem := ae_prepared_mem hp k γ R A hR hA τ hF
  obtain ⟨hB, hP⟩ := valid_world hp k γ
  have hN2 := valid_two_le_N hp k
  have hN : 1 ≤ p.N k := le_trans (by norm_num) hN2
  refine native_grid_projected_angular_cap (((p.ν k γ).prod volume).restrict (p.E k γ)) _
    hρμ hN hε hτ hsL (valid_S_pos hp).le hκ hB p.f
    (fun a b ha hab hb => valid_profile_lipschitz hp ha hab (hb.trans hsL))
    (p.P k γ) hP (p.g k γ)
    (fun r hr => (valid_pure_law hp k γ (hR r (hRgrid hr)).1 (hR r (hRgrid hr)).2).1)
    (fun r hr => (valid_pure_law hp k γ (hR r (hRgrid hr)).1 (hR r (hRgrid hr)).2).2)
    (fun r' hr' => ?_)
    (fun w hw hw0 => angularSample hp k γ hw0 (hA w (hAgrid w hw hw0)).2)
    (fun w hw hw0 => ?_)
    (ae_mono hρμ (ae_native_bounds hp k γ hKκ)) Q hQ e c u t₀ Z hK hq hfull ?_
    n he hn hen β' hK₀ hg₀ hg₀A ?_ r θ hr hrs hθ hθA j kk U hU
  · filter_upwards [hmem] with z hz
    exact (p.pure_density_band_of_not_bad S R A τ k γ z hz.2
      (Finset.mem_insert_of_mem (hRgrid hr'))).2
  · filter_upwards [hmem] with z hz
    exact p.angular_ratio_of_not_bad S R A τ k γ (by linarith) z hz.2 (hAgrid w hw hw0)
  · filter_upwards [hmem] with z hz
    exact hframe z hz.1
  · filter_upwards [hmem] with z hz
    exact hnormal z hz.1

end Original

/-! ### Arithmetic of the full original packet budget -/

section Budget

/-- Division by the full original packet budget `q * a`, with the balance
`N ^ (-f₀) * J ≤ N ^ β * a` between the determinant `J` and the prior mass `a`. -/
theorem packet_budget_le {N q a J K κ x f₀ β y : ℝ} (hN : 0 < N) (hq : 0 < q) (ha : 0 < a)
    (hbal : N ^ (-f₀) * J ≤ N ^ β * a) (hy : x + (f₀ + β) = y) :
    (ENNReal.ofReal q * ENNReal.ofReal a)⁻¹ *
        (ENNReal.ofReal (N ^ x) * ENNReal.ofReal (64 * κ ^ 2) *
          ENNReal.ofReal (4 * K ^ 2 * q * J)) ≤
      ENNReal.ofReal (N ^ y * (256 * κ ^ 2 * K ^ 2)) := by
  have hJ : J / a ≤ N ^ (f₀ + β) := by
    have hpos : 0 < N ^ f₀ := Real.rpow_pos_of_pos hN _
    rw [Real.rpow_neg hN.le] at hbal
    have h := mul_le_mul_of_nonneg_left hbal hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, ← mul_assoc,
      ← Real.rpow_add hN] at h
    exact (div_le_iff₀ ha).2 h
  have hx : 0 ≤ N ^ x := Real.rpow_nonneg hN.le _
  calc (ENNReal.ofReal q * ENNReal.ofReal a)⁻¹ *
        (ENNReal.ofReal (N ^ x) * ENNReal.ofReal (64 * κ ^ 2) *
          ENNReal.ofReal (4 * K ^ 2 * q * J))
      = ENNReal.ofReal (N ^ x) * ENNReal.ofReal (64 * κ ^ 2) *
          ((ENNReal.ofReal q * ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (4 * K ^ 2 * q * J)) := by
        ring
    _ = ENNReal.ofReal (N ^ x) * ENNReal.ofReal (64 * κ ^ 2) *
          ENNReal.ofReal (4 * K ^ 2 * J / a) := by
        rw [fixed_packet_budget_cancel hq ha]
    _ ≤ ENNReal.ofReal (N ^ x) * ENNReal.ofReal (64 * κ ^ 2) *
          ENNReal.ofReal (4 * K ^ 2 * N ^ (f₀ + β)) := by
        refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = ENNReal.ofReal (N ^ y * (256 * κ ^ 2 * K ^ 2)) := by
        rw [← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_mul (mul_nonneg hx (by positivity)),
          ← hy, Real.rpow_add hN x (f₀ + β)]
        congr 1
        ring

/-- The angular interpolation factors pass through the budget division. -/
theorem angular_budget_le {β X Y W : ENNReal} {a₁ a₂ d₁ d₂ : ℝ} (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (h : β * (X * Y * W) ≤ ENNReal.ofReal (d₁ * d₂)) :
    β * (ENNReal.ofReal a₁ * ENNReal.ofReal a₂ * X * Y * W) ≤
      ENNReal.ofReal (a₁ * a₂ * d₁ * d₂) := by
  calc β * (ENNReal.ofReal a₁ * ENNReal.ofReal a₂ * X * Y * W)
      = ENNReal.ofReal a₁ * ENNReal.ofReal a₂ * (β * (X * Y * W)) := by ring
    _ ≤ ENNReal.ofReal a₁ * ENNReal.ofReal a₂ * ENNReal.ofReal (d₁ * d₂) :=
        mul_le_mul' le_rfl h
    _ = ENNReal.ofReal (a₁ * a₂ * d₁ * d₂) := by
        rw [mul_assoc (a₁ * a₂) d₁ d₂, ENNReal.ofReal_mul (mul_nonneg ha₁ ha₂),
          ENNReal.ofReal_mul ha₁]

end Budget

/-! ### From continuous caps to scalar mesh cells -/

/-- A continuous cap in the scalar base `(t, Y)` gives the cap of every scalar mesh
cell `scalarZ = qq`, with `volume U` replaced by `σ ^ 2`. -/
theorem mesh_of_continuous_cap (law : Measure Incidence) (b : Trajectory → Fin 5 → ℝ)
    (V : Set Incidence) {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ U : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet U →
      law {z | (WithLp.toLp 2 ![z.2, scalarY (b z.1) z.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
        z ∈ V} ≤ ENNReal.ofReal C * volume U)
    {σ : ℝ} (hσ : 0 < σ) (qq : Fin 2 → ℤ) :
    law {z | scalarZ (b z.1) z.2 σ = qq ∧ z ∈ V} ≤ ENNReal.ofReal (C * σ ^ 2) := by
  have hmesh := mesh_cell_cap_of_continuous law
    (fun z : Incidence => (WithLp.toLp 2 ![z.2, scalarY (b z.1) z.2] :
      EuclideanSpace ℝ (Fin 2))) V (ENNReal.ofReal C) hcap hσ qq
  rw [ENNReal.ofReal_mul hC]
  refine le_trans (measure_mono ?_) hmesh
  intro z hz
  refine ⟨fun i => ?_, hz.2⟩
  rw [← hz.1]
  fin_cases i <;> rfl

/-! ### Final caps of a sub-law of the unit-block law of one packet -/

section Final

variable {p : Problem} {S η : ℝ}

/-- **Continuous pure cap.** A sub-law of the unit-block law of a prepared, balanced,
tangentially full packet obeys the projected pure cap at every signal depth `r ∈ [0, s]`,
with the explicit constant `N ^ (-f r + f 0 + τ + ε + β) * (256 κ² K²)`. -/
theorem packet_pure_cap (hp : p.Valid S η) (hL : p.L = 1)
    (k : ℕ) (γ : Fin (p.W k)) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L)
    {s ε τ : ℝ} (hε : 0 < ε) (hs1 : s ≤ 1) (hRgrid : coarseDepthGrid s ε ⊆ R)
    (F : Set Incidence) (hF : MeasurableSet F) (hFE : F ⊆ p.E k γ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (c u e : EuclideanSpace ℝ (Fin 2))
    (t₀ Z : ℝ) {q K κ : ℝ} (hq : 0 < q) (hK : 0 < K) (hκ : 1 ≤ κ) (hKκ : p.K k ≤ κ)
    (hframe : ∀ z ∈ F, ‖Matrix.toEuclideanLin Q⁻¹ (y z.1 z.2 - c - z.2 • u)‖ ≤ K)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (Aset : Set Trajectory) (hApos : 0 < (p.ν k γ Aset).toReal) {β : ℝ}
    (hbal : p.N k ^ (-p.f 0) * |Q.det| ≤ p.N k ^ β * (p.ν k γ Aset).toReal)
    (law : Measure Incidence)
    (hlaw : law ≤ (ENNReal.ofReal q * p.ν k γ Aset)⁻¹ •
      (((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)).map
        (fun z : Incidence => (z.1, (z.2 - t₀) / q)))
    (b : Trajectory → Fin 5 → ℝ) (hb : Measurable b)
    (hY : ∀ z ∈ F, scalarY (b z.1) ((z.2 - t₀) / q) = (inner ℝ e (y z.1 z.2) - Z) / q)
    (hX : ∀ z ∈ F, scalarX (b z.1) ((z.2 - t₀) / q) =
      MvPolynomial.eval (x z.1 z.2) (p.P k γ))
    (r : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (j : ℤ) (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hU : MeasurableSet U) :
    law {z | (WithLp.toLp 2 ![z.2, scalarY (b z.1) z.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
        ⌊scalarX (b z.1) z.2 / p.N k ^ (-r)⌋ = j} ≤
      ENNReal.ofReal (p.N k ^ (-p.f r + p.f 0 + τ + ε + β) * (256 * κ ^ 2 * K ^ 2)) *
        volume U := by
  have hsL : s ≤ p.L := hL ▸ hs1
  have hN0 : 0 < p.N k := lt_of_lt_of_le two_pos (valid_two_le_N hp k)
  have hAfin : p.ν k γ Aset = ENNReal.ofReal (p.ν k γ Aset).toReal :=
    (ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.1 hApos).2.ne).symm
  have hmem := ae_prepared_mem hp k γ R A hR hA τ hF
  have hcap := prepared_projected_cap (τ := τ) hp k γ R A hR hA hε hsL hRgrid F hF hFE Q hQ
    c u e t₀ Z hq hK hκ hKκ hframe hfull r hr hrs j U hU
  have htrans := scalar_cap_of_original_packet_cap
    (((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)) _
    (ENNReal.ofReal q * p.ν k γ Aset)⁻¹ t₀ q Z e rfl b hb (p.P k γ)
    (by
      filter_upwards [hmem] with z hz
      exact ⟨hY z hz.1, hX z hz.1⟩) (p.N k ^ (-r)) j U hU _ hcap
  refine (hlaw _).trans (htrans.trans (mul_le_mul' ?_ le_rfl))
  rw [hAfin]
  exact packet_budget_le hN0 hq hApos hbal (by ring)

/-- **Mesh pure cap.** The continuous pure cap on every scalar mesh cell of side `σ`. -/
theorem packet_mesh_cap (hp : p.Valid S η) (hL : p.L = 1)
    (k : ℕ) (γ : Fin (p.W k)) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L)
    {s ε τ : ℝ} (hε : 0 < ε) (hs1 : s ≤ 1) (hRgrid : coarseDepthGrid s ε ⊆ R)
    (F : Set Incidence) (hF : MeasurableSet F) (hFE : F ⊆ p.E k γ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (c u e : EuclideanSpace ℝ (Fin 2))
    (t₀ Z : ℝ) {q K κ : ℝ} (hq : 0 < q) (hK : 0 < K) (hκ : 1 ≤ κ) (hKκ : p.K k ≤ κ)
    (hframe : ∀ z ∈ F, ‖Matrix.toEuclideanLin Q⁻¹ (y z.1 z.2 - c - z.2 • u)‖ ≤ K)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (Aset : Set Trajectory) (hApos : 0 < (p.ν k γ Aset).toReal) {β : ℝ}
    (hbal : p.N k ^ (-p.f 0) * |Q.det| ≤ p.N k ^ β * (p.ν k γ Aset).toReal)
    (law : Measure Incidence)
    (hlaw : law ≤ (ENNReal.ofReal q * p.ν k γ Aset)⁻¹ •
      (((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)).map
        (fun z : Incidence => (z.1, (z.2 - t₀) / q)))
    (b : Trajectory → Fin 5 → ℝ) (hb : Measurable b)
    (hY : ∀ z ∈ F, scalarY (b z.1) ((z.2 - t₀) / q) = (inner ℝ e (y z.1 z.2) - Z) / q)
    (hX : ∀ z ∈ F, scalarX (b z.1) ((z.2 - t₀) / q) =
      MvPolynomial.eval (x z.1 z.2) (p.P k γ))
    (r : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (qq : Fin 2 → ℤ) (j : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    law {z | scalarZ (b z.1) z.2 σ = qq ∧ ⌊scalarX (b z.1) z.2 / p.N k ^ (-r)⌋ = j} ≤
      ENNReal.ofReal (p.N k ^ (-p.f r + p.f 0 + τ + ε + β) * (256 * κ ^ 2 * K ^ 2) *
        σ ^ 2) := by
  have hN0 : 0 < p.N k := lt_of_lt_of_le two_pos (valid_two_le_N hp k)
  exact mesh_of_continuous_cap law b {z | ⌊scalarX (b z.1) z.2 / p.N k ^ (-r)⌋ = j}
    (mul_nonneg (Real.rpow_nonneg hN0.le _) (by positivity))
    (fun U hU => packet_pure_cap hp hL k γ R A hR hA hε hs1 hRgrid F hF hFE Q hQ c u e t₀ Z
      hq hK hκ hKκ hframe hfull Aset hApos hbal law hlaw b hb hY hX r hr hrs j U hU) hσ qq

/-- **Continuous angular cap.** The projected cap with an additional angular bin of
width `N ^ (-θ)`, `0 < θ ≤ Adepth`, gaining `N ^ (-S θ + 2 τ + S ε) * (8 K₀ + 2) ^ 2`. -/
theorem packet_angular_cap (hp : p.Valid S η) (hL : p.L = 1)
    (k : ℕ) (γ : Fin (p.W k)) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L)
    {s ε τ Adepth : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (hs1 : s ≤ 1)
    (hRgrid : coarseDepthGrid s ε ⊆ R) (hAgrid : ∀ u ∈ coarseDepthGrid Adepth ε, 0 < u → u ∈ A)
    (F : Set Incidence) (hF : MeasurableSet F) (hFE : F ⊆ p.E k γ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (c u e : EuclideanSpace ℝ (Fin 2))
    (he : ‖e‖ = 1) (t₀ Z : ℝ) {q K κ : ℝ} (hq : 0 < q) (hK : 0 < K) (hκ : 1 ≤ κ)
    (hKκ : p.K k ≤ κ)
    (hframe : ∀ z ∈ F, ‖Matrix.toEuclideanLin Q⁻¹ (y z.1 z.2 - c - z.2 • u)‖ ≤ K)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (Aset : Set Trajectory) (hApos : 0 < (p.ν k γ Aset).toReal) {β : ℝ}
    (hbal : p.N k ^ (-p.f 0) * |Q.det| ≤ p.N k ^ β * (p.ν k γ Aset).toReal)
    (law : Measure Incidence)
    (hlaw : law ≤ (ENNReal.ofReal q * p.ν k γ Aset)⁻¹ •
      (((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)).map
        (fun z : Incidence => (z.1, (z.2 - t₀) / q)))
    (b : Trajectory → Fin 5 → ℝ) (hb : Measurable b)
    (hY : ∀ z ∈ F, scalarY (b z.1) ((z.2 - t₀) / q) = (inner ℝ e (y z.1 z.2) - Z) / q)
    (hX : ∀ z ∈ F, scalarX (b z.1) ((z.2 - t₀) / q) =
      MvPolynomial.eval (x z.1 z.2) (p.P k γ))
    (hV : ∀ z ∈ F, b z.1 1 = inner ℝ e (v z.1))
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (β' : ℝ) {K₀ g₀ : ℝ} (hK₀ : 1 ≤ K₀) (hg₀ : 0 ≤ g₀) (hg₀A : g₀ ≤ p.N k ^ (-Adepth))
    (hnormal : ∀ z ∈ F, |inner ℝ n (v z.1) - β'| ≤ K₀ * g₀)
    (r : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (θ : ℝ) (hθ : 0 < θ) (hθA : θ ≤ Adepth)
    (j kk : ℤ) (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : MeasurableSet U) :
    law {z | (WithLp.toLp 2 ![z.2, scalarY (b z.1) z.2] : EuclideanSpace ℝ (Fin 2)) ∈ U ∧
        ⌊scalarX (b z.1) z.2 / p.N k ^ (-r)⌋ = j ∧ ⌊b z.1 1 / p.N k ^ (-θ)⌋ = kk} ≤
      ENNReal.ofReal (p.N k ^ (-S * θ + 2 * τ + S * ε) * (8 * K₀ + 2) ^ 2 *
        p.N k ^ (-p.f r + p.f 0 + τ + ε + β) * (256 * κ ^ 2 * K ^ 2)) * volume U := by
  have hsL : s ≤ p.L := hL ▸ hs1
  have hN0 : 0 < p.N k := lt_of_lt_of_le two_pos (valid_two_le_N hp k)
  have hAfin : p.ν k γ Aset = ENNReal.ofReal (p.ν k γ Aset).toReal :=
    (ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.1 hApos).2.ne).symm
  have hmem := ae_prepared_mem hp k γ R A hR hA τ hF
  have hcap := prepared_projected_angular_cap hp k γ R A hR hA hε hτ hsL hRgrid hAgrid
    F hF hFE Q hQ c u e he t₀ Z hq hK hκ hKκ hframe hfull n hn hen β' hK₀ hg₀ hg₀A hnormal
    r θ hr hrs hθ hθA j kk U hU
  have htrans := scalar_angular_cap_of_original_packet_cap
    (((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)) _
    (ENNReal.ofReal q * p.ν k γ Aset)⁻¹ t₀ q Z e rfl b hb (p.P k γ)
    (by
      filter_upwards [hmem] with z hz
      exact ⟨hY z hz.1, hX z hz.1, hV z hz.1⟩) (p.N k ^ (-r)) (p.N k ^ (-θ)) j kk U hU _ hcap
  refine (hlaw _).trans (htrans.trans (mul_le_mul' ?_ le_rfl))
  rw [hAfin]
  exact angular_budget_le (Real.rpow_nonneg hN0.le _) (by positivity)
    (packet_budget_le hN0 hq hApos hbal (by ring))

/-- **Mesh angular cap.** The continuous angular cap on every scalar mesh cell of
side `σ`. -/
theorem packet_mesh_angular_cap (hp : p.Valid S η) (hL : p.L = 1)
    (k : ℕ) (γ : Fin (p.W k)) (R A : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L) (hA : ∀ u ∈ A, 0 < u ∧ u ≤ η * p.L)
    {s ε τ Adepth : ℝ} (hε : 0 < ε) (hτ : 0 ≤ τ) (hs1 : s ≤ 1)
    (hRgrid : coarseDepthGrid s ε ⊆ R) (hAgrid : ∀ u ∈ coarseDepthGrid Adepth ε, 0 < u → u ∈ A)
    (F : Set Incidence) (hF : MeasurableSet F) (hFE : F ⊆ p.E k γ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (c u e : EuclideanSpace ℝ (Fin 2))
    (he : ‖e‖ = 1) (t₀ Z : ℝ) {q K κ : ℝ} (hq : 0 < q) (hK : 0 < K) (hκ : 1 ≤ κ)
    (hKκ : p.K k ≤ κ)
    (hframe : ∀ z ∈ F, ‖Matrix.toEuclideanLin Q⁻¹ (y z.1 z.2 - c - z.2 • u)‖ ≤ K)
    (hfull : q / K ≤ ‖Matrix.toEuclideanLin Q.transpose e‖)
    (Aset : Set Trajectory) (hApos : 0 < (p.ν k γ Aset).toReal) {β : ℝ}
    (hbal : p.N k ^ (-p.f 0) * |Q.det| ≤ p.N k ^ β * (p.ν k γ Aset).toReal)
    (law : Measure Incidence)
    (hlaw : law ≤ (ENNReal.ofReal q * p.ν k γ Aset)⁻¹ •
      (((p.ν k γ).prod volume).restrict (F ∩ (densityPreparationBad p S R A τ k γ)ᶜ)).map
        (fun z : Incidence => (z.1, (z.2 - t₀) / q)))
    (b : Trajectory → Fin 5 → ℝ) (hb : Measurable b)
    (hY : ∀ z ∈ F, scalarY (b z.1) ((z.2 - t₀) / q) = (inner ℝ e (y z.1 z.2) - Z) / q)
    (hX : ∀ z ∈ F, scalarX (b z.1) ((z.2 - t₀) / q) =
      MvPolynomial.eval (x z.1 z.2) (p.P k γ))
    (hV : ∀ z ∈ F, b z.1 1 = inner ℝ e (v z.1))
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (β' : ℝ) {K₀ g₀ : ℝ} (hK₀ : 1 ≤ K₀) (hg₀ : 0 ≤ g₀) (hg₀A : g₀ ≤ p.N k ^ (-Adepth))
    (hnormal : ∀ z ∈ F, |inner ℝ n (v z.1) - β'| ≤ K₀ * g₀)
    (r : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (θ : ℝ) (hθ : 0 < θ) (hθA : θ ≤ Adepth)
    (qq : Fin 2 → ℤ) (j kk : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    law {z | scalarZ (b z.1) z.2 σ = qq ∧ ⌊scalarX (b z.1) z.2 / p.N k ^ (-r)⌋ = j ∧
        ⌊b z.1 1 / p.N k ^ (-θ)⌋ = kk} ≤
      ENNReal.ofReal (p.N k ^ (-S * θ + 2 * τ + S * ε) * (8 * K₀ + 2) ^ 2 *
        p.N k ^ (-p.f r + p.f 0 + τ + ε + β) * (256 * κ ^ 2 * K ^ 2) * σ ^ 2) := by
  have hN0 : 0 < p.N k := lt_of_lt_of_le two_pos (valid_two_le_N hp k)
  exact mesh_of_continuous_cap law b
    {z | ⌊scalarX (b z.1) z.2 / p.N k ^ (-r)⌋ = j ∧ ⌊b z.1 1 / p.N k ^ (-θ)⌋ = kk}
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (by positivity))
      (Real.rpow_nonneg hN0.le _)) (by positivity))
    (fun U hU => packet_angular_cap hp hL k γ R A hR hA hε hτ hs1 hRgrid hAgrid F hF hFE Q
      hQ c u e he t₀ Z hq hK hκ hKκ hframe hfull Aset hApos hbal law hlaw b hb hY hX hV n hn
      hen β' hK₀ hg₀ hg₀A hnormal r hr hrs θ hθ hθA j kk U hU) hσ qq

end Final

end Submission.Obl.k4_uncapped_native_capping.PacketCapBounds
